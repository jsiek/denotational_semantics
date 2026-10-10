open import Data.Empty using (⊥-elim) renaming (⊥ to False)
open import Data.List using (List ; _∷_ ; []; _++_; length; replicate)
open import Data.List.Properties using (++-conicalˡ)
open import Data.List.Membership.Propositional renaming (_∈_ to _⋵_)
open import Data.List.Membership.Propositional.Properties
  using (∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any using (here; there) 
open import Data.Nat using (ℕ; zero; suc; _≟_; _<_; s≤s; _+_)
open import Data.Product using (_×_; Σ; Σ-syntax; proj₁; proj₂)
    renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt) renaming (⊤ to True)
open import Data.Unit.Polymorphic using () renaming (tt to ptt; ⊤ to pTrue)
open import Level renaming (zero to lzero; suc to lsuc; _⊔_ to _l⊔_)
open import Relation.Binary.PropositionalEquality
    using (_≡_; _≢_; refl; sym; subst)
open import Relation.Nullary using (¬_; Dec; yes; no)

open import Primitives
open import abt.ScopedTuple hiding (𝒫)
open import SetsAsPredicates
open import abt.Sig
open import abt.Var
open import abt.GSubst using (_•_)
open import NewSigUtil
open import NewSyntaxUtil
open import NewDOpSig
open import NewDenotProperties

module NewEnv where



{- ================ Set-valued environments ================================ -}

Env : (A : Set) → Set₁
Env A = Var → 𝒫 A

nonempty-env : ∀ {A} → Env A → Set
nonempty-env ρ = ∀ x → nonempty (ρ x)

infix 5 _~ₑ[_]_
_~ₑ[_]_ : ∀ {A}{B} → Env A → (R : 𝒫 A → 𝒫 B → Set) → Env B → Set
ρ ~ₑ[ R ] ρ' = ∀ x → R (ρ x) (ρ' x)

infix 5 _⊆ₑ_
_⊆ₑ_ : ∀ {A} → Env A → Env A → Set
ρ₁ ⊆ₑ ρ₂ = ρ₁ ~ₑ[ _⊆_ ] ρ₂

⊆ₑ-trans : ∀{A}{ρ₁ ρ₂ ρ₃ : Env A} → ρ₁ ⊆ₑ ρ₂ → ρ₂ ⊆ₑ ρ₃ → ρ₁ ⊆ₑ ρ₃
⊆ₑ-trans {ρ₁}{ρ₂}{ρ₃} r12 r23 x = λ d z → r23 x d (r12 x d z)

∀ₑ : ∀ {A} (P : 𝒫 A → Set) → Env A → Set
∀ₑ P ρ = ∀ i → P (ρ i)

∀ₑ-ext : ∀ {A ρ D} P → ∀ₑ {A} P ρ → P D → ∀ₑ P (D • ρ)
∀ₑ-ext P Pρ PD zero = PD
∀ₑ-ext P Pρ PD (suc i) = Pρ i

extend-nonempty-env : ∀{A}{ρ : Env A}{X}
   → nonempty-env ρ  →  nonempty X  →  nonempty-env (X • ρ)
extend-nonempty-env {ρ} {X} NE-ρ NE-X zero = NE-X
extend-nonempty-env {ρ} {X} NE-ρ V≢[] (suc x) = NE-ρ x

•-~ : ∀ {A}{B}{ρ : Env A}{ρ' : Env B}{D : 𝒫 A}{E : 𝒫 B} R
        → ρ ~ₑ[ R ] ρ' → R D E → (D • ρ) ~ₑ[ R ] (E • ρ')
•-~ {A} {B} {ρ} {ρ'} {D} {E} R ρ~ρ' D~E zero = D~E
•-~ {A} {B} {ρ} {ρ'} {D} {E} R ρ~ρ' D~E (suc x) = ρ~ρ' x

env-ext : ∀{A}{ρ ρ′ : Env A}{X} → ρ ⊆ₑ ρ′ → (x : Var) → (X • ρ) x ⊆ (X • ρ′) x
env-ext ρ<ρ′ zero d d∈ = d∈
env-ext ρ<ρ′ (suc x) = ρ<ρ′ x

finiteNE : ∀ {A} → 𝒫 A → Set
finiteNE {A} S = Σ[ V ∈ List A ] S ≃ (mem V) × V ≢ []

{- environments whose codomain are finite nonempty sets -}
finiteNE-env : ∀ {A} → Env A → Set
finiteNE-env {A} ρ = ∀ x → finiteNE (ρ x)

extend-finiteNE-env : ∀ {A}{ρ : Env A}{X}
  → finiteNE-env ρ → finiteNE X → finiteNE-env (X • ρ)
extend-finiteNE-env fin-ρ fin-X zero = fin-X
extend-finiteNE-env fin-ρ fin-X (suc i) = fin-ρ i

infix 6 _⊔ₑ_
_⊔ₑ_ : ∀ {A} → Env A → Env A → Env A
(ρ₁ ⊔ₑ ρ₂) x v = ρ₁ x v ⊎ ρ₂ x v

join-finiteNE-env : ∀{A} {ρ₁ ρ₂ : Env A} → finiteNE-env ρ₁  →  finiteNE-env ρ₂
   → finiteNE-env (ρ₁ ⊔ₑ ρ₂)
join-finiteNE-env {A}{ρ₁}{ρ₂} f1 f2 x
    with f1 x
... | ⟨ E1 , ⟨ ρ₁=E1 , NE-E1 ⟩ ⟩
    with f2 x
... | ⟨ E2 , ⟨ ρ₂=E2 , NE-E2 ⟩ ⟩ =
    ⟨ (E1 ++ E2) , ⟨ ⟨ G , (H {E1} λ d z → z) ⟩ ,
      (λ E12=[] → NE-E1 (++-conicalˡ E1 E2 E12=[])) ⟩ ⟩
    where
    G : (v : A ) → ρ₁ x v ⊎ ρ₂ x v → mem (E1 ++ E2) v
    G v (inj₁ ρ1x) = ∈-++⁺ˡ ((proj₁ ρ₁=E1) v ρ1x)
    G v (inj₂ ρ2x) = ∈-++⁺ʳ E1 ((proj₁ ρ₂=E2) v ρ2x)

    H : ∀{E} → mem E ⊆ mem E1 → mem (E ++ E2) ⊆ (λ v → ρ₁ x v ⊎ ρ₂ x v)
    H {[]} E<E1 v v∈E++E2 = inj₂ ((proj₂ ρ₂=E2) v v∈E++E2)
    H {x ∷ E} E<E1 .x (here refl) = inj₁ ((proj₂ ρ₁=E1) x (E<E1 x (here refl)))
    H {x ∷ E} E<E1 v (there v∈E++E2) =
       H (λ v z → E<E1 v (there z)) v v∈E++E2

join-lub : ∀{A}{ρ ρ₁ ρ₂ : Env A} → ρ₁ ⊆ₑ ρ → ρ₂ ⊆ₑ ρ → ρ₁ ⊔ₑ ρ₂ ⊆ₑ ρ
join-lub {ρ} {ρ₁} {ρ₂} ρ₁⊆ρ ρ₂⊆ρ x v (inj₁ v∈ρ₁x) = ρ₁⊆ρ x v v∈ρ₁x
join-lub {ρ} {ρ₁} {ρ₂} ρ₁⊆ρ ρ₂⊆ρ x v (inj₂ v∈ρ₂x) = ρ₂⊆ρ x v v∈ρ₂x

join-⊆-left : ∀{A}{ρ₁ ρ₂ : Env A} → ρ₁ ⊆ₑ ρ₁ ⊔ₑ ρ₂
join-⊆-left {ρ₁}{ρ₂} = λ x d z → inj₁ z

join-⊆-right : ∀{A}{ρ₁ ρ₂ : Env A} → ρ₂ ⊆ₑ ρ₁ ⊔ₑ ρ₂
join-⊆-right {ρ₁}{ρ₂} = λ x d z → inj₂ z

monotone-env : ∀ {A} → (Env A → 𝒫 A) → Set₁
monotone-env D = ∀ {ρ ρ′} → (∀ x → ρ x ⊆ ρ′ x)  →  D ρ ⊆ D ρ′


{- creates an environment that maps each variable x to
   a singleton set of some element in ρ x.  -}
initial-finiteNE-env : ∀ {A} (ρ : Env A) → (NE-ρ : nonempty-env ρ) → Env A
initial-finiteNE-env ρ NE-ρ x
    with NE-ρ x
... | ⟨ v , v∈ρx ⟩ = ⌈ v ⌉

initial-fin : ∀ {A} (ρ : Env A) → (NE-ρ : nonempty-env ρ)
   → finiteNE-env (initial-finiteNE-env ρ NE-ρ)
initial-fin ρ NE-ρ x
    with NE-ρ x
... | ⟨ v , v∈ρx ⟩ =
      ⟨ v ∷ [] ,
      ⟨ ⟨ (λ {w refl → (here refl)}) , (λ {w (here refl) → refl}) ⟩ , (λ ()) ⟩ ⟩

initial-fin-⊆ : ∀ {A} (ρ : Env A) → (NE-ρ : nonempty-env ρ)
  → initial-finiteNE-env ρ NE-ρ ⊆ₑ ρ
initial-fin-⊆ ρ NE-ρ x v v∈initial
    with NE-ρ x
... | ⟨ w , w∈ρx ⟩ rewrite v∈initial = w∈ρx

{- single-env maps x to D and any other variable y to something in ρ y. -}
single-env : ∀ {A} Var → 𝒫 A → (ρ : Env A) → (NE-ρ : nonempty-env ρ) → Env A
single-env x D ρ NE-ρ y
    with x ≟ y
... | yes refl = D
... | no neq
    with NE-ρ y
... | ⟨ v , v∈ρy ⟩ = ⌈ v ⌉    

single-fin : ∀{A}{v}{x}{ρ : Env A}{NE-ρ} → finiteNE-env (single-env x ⌈ v ⌉ ρ NE-ρ)
single-fin {A}{v}{x}{ρ}{NE-ρ} y
    with x ≟ y
... | yes refl =
    ⟨ v ∷ [] ,
    ⟨ ⟨ (λ{v₁ refl → (here refl)}) , (λ{v₁ (here refl) → refl}) ⟩ , (λ ()) ⟩ ⟩
... | no neq
    with NE-ρ y
... | ⟨ w , w∈ρy ⟩ =
    ⟨ w ∷ [] ,
    ⟨ ⟨ (λ{v₁ refl → here refl}) , (λ{v₁ (here refl) → refl}) ⟩ , (λ ()) ⟩ ⟩

single-⊆ : ∀{A}{ρ x v}{NE-ρ : nonempty-env {A} ρ}
  →  v ∈ ρ x  →  single-env x ⌈ v ⌉ ρ NE-ρ ⊆ₑ ρ
single-⊆ {A}{ρ}{x}{v}{NE-ρ} v∈ρx y w sing 
    with x ≟ y
... | yes refl rewrite sing = v∈ρx
... | no neq
    with NE-ρ y
... | ⟨ u , u∈ρy ⟩ rewrite sing = u∈ρy

v∈single[xv]x : ∀{A}{v}{x}{ρ : Env A}{NE-ρ} → v ∈ single-env x ⌈ v ⌉ ρ NE-ρ x
v∈single[xv]x {A}{v}{x}
    with x ≟ x
... | yes refl = refl
... | no neq = ⊥-elim (neq refl)
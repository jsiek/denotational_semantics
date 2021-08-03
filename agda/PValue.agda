module PValue where

{-

  This one is closer to Scott and Engeler.

-}

open import Primitives
open import Syntax using (Rename)
open import ISWIM hiding (subst-zero; _[_]; id; _—→_)
open import Fold2 Op sig
open import ScopedTuple hiding (𝒫)
open import Sig
open import Utilities using (extensionality)

open import Data.Empty using (⊥-elim) renaming (⊥ to False)
open import Data.List using (List ; _∷_ ; []; _++_) 
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; _≟_; _<?_)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt) renaming (⊤ to True)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; sym; cong; cong₂; cong-app; subst)
open import Relation.Nullary using (¬_; Dec; yes; no)

module PValue where

{- Set notation for predicates -}

𝒫 : Set → Set₁
𝒫 V = V → Set

∅ : ∀{T} → 𝒫 T
∅ = λ v → False 

⌈_⌉ : ∀ {T} → T → 𝒫 T
⌈ v ⌉ w = w ≡ v

infix 9 _∈_
_∈_ : ∀{T : Set} → T → 𝒫 T → Set
v ∈ D = D v

infix 9 _⊆_
_⊆_ : ∀{T : Set} → 𝒫 T → 𝒫 T → Set
D ⊆ E = ∀ d → d ∈ D → d ∈ E

⊆-trans : ∀{T : Set}{D E F : 𝒫 T} → D ⊆ E → E ⊆ F → D ⊆ F
⊆-trans {T}{D}{E}{F} DE EF = λ d z → EF d (DE d z)

{- Values -}

data Value : Set where
  const : {b : Base} → base-rep b → Value
  _↦_ : List Value → Value → Value

data mem : ∀{T : Set} → List T → T → Set where
  mem-here : ∀{T}{x : T}{ls} → mem (x ∷ ls) x
  mem-there : ∀{T}{x y : T}{ls} → mem ls x → mem (y ∷ ls) x

mem-++-left : ∀{T}{xs ys : List T}{x} → mem xs x → mem (xs ++ ys) x
mem-++-left {T} {x ∷ xs} mem-here = mem-here
mem-++-left {T} {x ∷ xs} (mem-there x∈xs) = mem-there (mem-++-left x∈xs)

mem-++-right : ∀{T}{xs ys : List T}{x} → mem ys x → mem (xs ++ ys) x
mem-++-right {T} {[]} m = m
mem-++-right {T} {x ∷ xs} m = mem-there (mem-++-right m)

{- Abstraction and Application -}

Λ : (𝒫 Value → 𝒫 Value) → 𝒫 Value
Λ f (const k) = False
Λ f (V ↦ w) = w ∈ f (mem V)

infix 10 _▪_
_▪_ : 𝒫 Value → 𝒫 Value → 𝒫 Value
D₁ ▪ D₂ = λ w → Σ[ V ∈ List Value ] (V ↦ w ∈ D₁)  ×  (mem V ⊆ D₂)

℘ : ∀{P : Prim} → rep P → 𝒫 Value
℘ {base B} k (const {B′} k′)
    with base-eq? B B′
... | yes refl = k ≡ k′
... | no neq = False
℘ {base B} k (V ↦ w) = False
℘ {B ⇒ P} f (const k) = False
℘ {B ⇒ P} f (V ↦ w) =
   Σ[ k ∈ base-rep B ] V ≡ (const {B} k) ∷ []  ×  w ∈ ℘ {P} (f k)

{-
  Denotational Equality and Inequality
 -}

infix 6 _≲_
_≲_ : 𝒫 Value → 𝒫 Value → Set
D₁ ≲ D₂ = ∀ (v : Value) → D₁ v → D₂ v

≲-refl : {D : 𝒫 Value} → D ≲ D
≲-refl {D} v Dv = Dv

≲-trans : {D₁ D₂ D₃ : 𝒫 Value} → D₁ ≲ D₂ → D₂ ≲ D₃ → D₁ ≲ D₃
≲-trans D12 D23 v D₁v = D23 v (D12 v D₁v)

infix 6 _≃_
data _≃_ : 𝒫 Value → 𝒫 Value → Set where
  equal : ∀{D₁ D₂} → D₁ ≲ D₂  →  D₂ ≲ D₁  → D₁ ≃ D₂

to : ∀{D₁ D₂} → D₁ ≃ D₂ → D₁ ≲ D₂
to (equal a b) = a

from : ∀{D₁ D₂} → D₁ ≃ D₂ → D₂ ≲ D₁
from (equal a b) = b

≃-refl : {D : 𝒫 Value} → D ≃ D
≃-refl {D} = equal ≲-refl ≲-refl

≃-reflexive : {D₁ D₂ : 𝒫 Value} → D₁ ≡ D₂ → D₁ ≃ D₂
≃-reflexive refl = equal ≲-refl ≲-refl

≃-sym : {D₁ D₂ : 𝒫 Value} → D₁ ≃ D₂ → D₂ ≃ D₁
≃-sym (equal t f) = equal f t

≃-trans : {D₁ D₂ D₃ : 𝒫 Value} → D₁ ≃ D₂ → D₂ ≃ D₃ → D₁ ≃ D₃
≃-trans (equal d12 d21) (equal d23 d32) =
    equal (≲-trans d12 d23) (≲-trans d32 d21)

module ≃-Reasoning where

  infixr 2 _≃⟨_⟩_
  infix 3 _∎

  _≃⟨_⟩_ : ∀ (D₁ : 𝒫 Value) {D₂ D₃ : 𝒫 Value}
     → D₁ ≃ D₂ → D₂ ≃ D₃ → D₁ ≃ D₃
  D₁ ≃⟨ D₁≃D₂ ⟩ D₂≃D₃ = ≃-trans D₁≃D₂ D₂≃D₃

  _∎ : ∀ (D : 𝒫 Value)
     → D ≃ D
  D ∎  =  ≃-refl

▪-cong-≲ : ∀{D₁ D₂ D₁′ D₂′ : 𝒫 Value}
  → D₁ ≲ D₁′  →  D₂ ≲ D₂′
  → D₁ ▪ D₂ ≲ D₁′ ▪ D₂′
▪-cong-≲ D11 D22 w ⟨ V , ⟨ wv∈D1 , V<D2 ⟩ ⟩ =
   ⟨ V , ⟨ (D11 (V ↦ w) wv∈D1) , (λ d z → D22 d (V<D2 d z)) ⟩ ⟩

▪-cong : ∀{D₁ D₂ D₁′ D₂′ : 𝒫 Value}
  → D₁ ≃ D₁′  →  D₂ ≃ D₂′
  → D₁ ▪ D₂ ≃ D₁′ ▪ D₂′
▪-cong (equal x x₁) (equal x₂ x₃) = equal (▪-cong-≲ x x₂) (▪-cong-≲ x₁ x₃)

continuous : (F : 𝒫 Value → 𝒫 Value) → Set₁
continuous F = ∀ X E → mem E ⊆ F X
    → Σ[ D ∈ List Value ] mem D ≲ X  ×  mem E ⊆ F (mem D)

monotone : (F : 𝒫 Value → 𝒫 Value) → Set₁
monotone F = ∀ D₁ D₂ → D₁ ≲ D₂ → F D₁ ≲ F D₂

Λ-▪-≲ : ∀ {F : 𝒫 Value → 𝒫 Value}{D : 𝒫 Value}
  → monotone F
  → (Λ F) ▪ D ≲ F D
Λ-▪-≲ {F} {D} Fmono w ⟨ V , ⟨ w∈FV , V<D ⟩ ⟩ =
   Fmono (mem V) D V<D w w∈FV

≲-Λ-▪ : ∀ {F : 𝒫 Value → 𝒫 Value}{D : 𝒫 Value}
  → continuous F
  → F D ≲ (Λ F) ▪ D
≲-Λ-▪ {F}{D} Fcont w w∈FD
    with Fcont D (w ∷ []) λ { d mem-here → w∈FD }
... | ⟨ E , ⟨ E<D , w∈FE ⟩ ⟩ = ⟨ E , ⟨ w∈FE w mem-here , E<D ⟩ ⟩

Λ-▪ : ∀ {F : 𝒫 Value → 𝒫 Value}{D : 𝒫 Value}
  → continuous F → monotone F
  → (Λ F) ▪ D ≃ F D
Λ-▪ {F}{D} Fcont Fmono = equal (Λ-▪-≲ Fmono) (≲-Λ-▪ Fcont)


{- ISWIM -}

Env : Set₁
Env = Var → 𝒫 Value

interp  : (op : Op) → Tuple (sig op) (ArgTy (𝒫 Value)) → 𝒫 Value
interp lam ⟨ F , _ ⟩ = Λ F
interp app ⟨ D₁ , ⟨ D₂ , _ ⟩ ⟩ = D₁ ▪ D₂
interp (lit P k) _ = ℘ {P} k

infix 10 ⟦_⟧_
⟦_⟧_ : Term → Env → 𝒫 Value
⟦ M ⟧ ρ = fold interp ∅ ρ M


{- Substitution Lemma -}

⟦⟧-rename : ∀ {M : Term}{σ : Rename}{ρ : Var → 𝒫 Value}
  → ⟦ rename σ M ⟧ ρ ≡ ⟦ M ⟧ (λ x → ⟦ ` σ x ⟧ ρ)
⟦⟧-rename {M}{ρ} = fold-rename-fusion M

⟦⟧-subst : ∀ {M : Term}{σ : Subst}{ρ : Var → 𝒫 Value}
  → ⟦ ⟪ σ ⟫ M ⟧ ρ ≡ ⟦ M ⟧ (λ x → ⟦ σ x ⟧ ρ)
⟦⟧-subst {M}{ρ} = fold-subst-fusion M

id : Subst
id = (λ x → ` x)

_[_] : Term → Term → Term
N [ M ] =  ⟪ M • id ⟫ N

⟦⟧-substitution : ∀ {M N : Term}{ρ : Var → 𝒫 Value}
  → ⟦ M [ N ] ⟧ ρ ≡ ⟦ M ⟧ ((⟦ N ⟧ ρ) • ρ)
⟦⟧-substitution {M}{N}{ρ} =
  subst (λ X → ⟦ M [ N ] ⟧ ρ ≡ ⟦ M ⟧ X) (extensionality EQ)
        (⟦⟧-subst {M}{N • id})
  where 
  EQ : (x : Var) → ⟦ (N • id) x ⟧ ρ ≡ (⟦ N ⟧ ρ • ρ) x
  EQ zero = refl
  EQ (suc x) = refl


{- Semantics is monotone -}

⟦⟧-monotone : ∀{M : Term}{ρ ρ′}
  → (∀ x → ρ x ≲ ρ′ x)
  → ⟦ M ⟧ ρ ≲ ⟦ M ⟧ ρ′ 
⟦⟧-monotone {` x} ρ<ρ′ = ρ<ρ′ x
⟦⟧-monotone {L · M} ρ<ρ′ w ⟨ V , ⟨ Vw∈L , V⊆M ⟩ ⟩ =
   let vw∈Lρ′ = ⟦⟧-monotone {L} ρ<ρ′ (V ↦ w) Vw∈L in
   let v∈Mρ′ = ⟦⟧-monotone {M} ρ<ρ′ in
   ⟨ V , ⟨ vw∈Lρ′ , (λ v v∈V → v∈Mρ′ v (V⊆M v v∈V)) ⟩ ⟩
⟦⟧-monotone {ƛ N}{ρ}{ρ′} ρ<ρ′ (const k) ()
⟦⟧-monotone {ƛ N}{ρ}{ρ′} ρ<ρ′ (V ↦ w) w∈⟦N⟧V•ρ =
  ⟦⟧-monotone {N}{mem V • ρ}{mem V • ρ′} G w w∈⟦N⟧V•ρ
  where
  G : (x : Var) → (mem V • ρ) x ≲ (mem V • ρ′) x
  G zero = λ v z → z
  G (suc x) = ρ<ρ′ x
⟦⟧-monotone {$ p k} ρ<ρ′ v v∈℘k = v∈℘k

⟦⟧-monotone-one : ∀{N : Term}{ρ} → monotone (λ D → ⟦ N ⟧ (D • ρ))
⟦⟧-monotone-one {N}{ρ} D₁ D₂ D12 = ⟦⟧-monotone {N} G
  where
  G : (x : Var) → (D₁ • ρ) x ≲ (D₂ • ρ) x
  G zero = D12
  G (suc x) = λ v z → z

{- Semantics is continuous -}

fin-env : Env → Set
fin-env ρ = ∀ x → Σ[ E ∈ List Value ] ρ x ≲ mem E

empty-fin : ∀{T : Set} → fin-env (λ x → ∅)
empty-fin x = ⟨ [] , (λ v ()) ⟩

infix 6 _⊔ₑ_
_⊔ₑ_ : Env → Env → Env
(ρ₁ ⊔ₑ ρ₂) x v = ρ₁ x v ⊎ ρ₂ x v

join-fin-env : ∀{ρ₁ ρ₂}
  → fin-env ρ₁ → fin-env ρ₂
  → fin-env (ρ₁ ⊔ₑ ρ₂)
join-fin-env {ρ₁}{ρ₂} f1 f2 x
    with f1 x
... | ⟨ E1 , ρ₁<E1 ⟩
    with f2 x
... | ⟨ E2 , ρ₂<E2 ⟩ =
    ⟨ (E1 ++ E2) , G ⟩
    where
    G : (v : Value) → ρ₁ x v ⊎ ρ₂ x v → mem (E1 ++ E2) v
    G v (inj₁ ρ1x) = mem-++-left (ρ₁<E1 v ρ1x)
    G v (inj₂ ρ2x) = mem-++-right (ρ₂<E2 v ρ2x)

single-env : Var → 𝒫 Value → Env
single-env x D y
    with x ≟ y
... | yes refl = D
... | no neq = ∅

single-fin : ∀{E}{x} → fin-env (single-env x (mem E))
single-fin {E}{x} y = ⟨ E , G ⟩
  where G : single-env x (mem E) y ≲ mem E
        G v x₁
            with x ≟ y
        ... | yes refl = x₁
        ... | no neq = ⊥-elim x₁

infix 5 _⊆ₑ_
_⊆ₑ_ : Env → Env → Set
ρ₁ ⊆ₑ ρ₂ = ∀ x → ρ₁ x ⊆ ρ₂ x

⊆ₑ-trans : ∀{ρ₁ ρ₂ ρ₃} → ρ₁ ⊆ₑ ρ₂ → ρ₂ ⊆ₑ ρ₃ → ρ₁ ⊆ₑ ρ₃
⊆ₑ-trans {ρ₁}{ρ₂}{ρ₃} r12 r23 x = λ d z → r23 x d (r12 x d z)

single-⊆ : ∀{ρ x E}
   → mem E ⊆ ρ x
   → single-env x (mem E) ⊆ₑ ρ
single-⊆ {ρ}{x}{E} E⊆ρx y v sing[xE]yv
    with x ≟ y
... | yes refl = E⊆ρx v sing[xE]yv
... | no neq = ⊥-elim sing[xE]yv

E⊆sing[xE]x : ∀{E}{x} → mem E ⊆ single-env x (mem E) x
E⊆sing[xE]x {E}{x}
    with x ≟ x
... | yes refl = λ d z → z
... | no neq = ⊥-elim (neq refl)

join-lub : ∀{ρ ρ₁ ρ₂} → ρ₁ ⊆ₑ ρ → ρ₂ ⊆ₑ ρ → ρ₁ ⊔ₑ ρ₂ ⊆ₑ ρ
join-lub {ρ} {ρ₁} {ρ₂} ρ₁⊆ρ ρ₂⊆ρ x v (inj₁ v∈ρ₁x) = ρ₁⊆ρ x v v∈ρ₁x
join-lub {ρ} {ρ₁} {ρ₂} ρ₁⊆ρ ρ₂⊆ρ x v (inj₂ v∈ρ₂x) = ρ₂⊆ρ x v v∈ρ₂x

join-⊆-left : ∀{ρ₁ ρ₂} → ρ₁ ⊆ₑ ρ₁ ⊔ₑ ρ₂
join-⊆-left {ρ₁}{ρ₂} = λ x d z → inj₁ z

join-⊆-right : ∀{ρ₁ ρ₂} → ρ₂ ⊆ₑ ρ₁ ⊔ₑ ρ₂
join-⊆-right {ρ₁}{ρ₂} = λ x d z → inj₂ z

⟦⟧-continuous-env : ∀{M : Term}{ρ}{E}
  → mem E ⊆ ⟦ M ⟧ ρ
  → Σ[ ρ′ ∈ Env ] fin-env ρ′  ×  ρ′ ⊆ₑ ρ  ×  mem E ⊆ ⟦ M ⟧ ρ′
  
⟦⟧-continuous-env {` x}{ρ}{E} E⊆⟦M⟧ρ =
   ⟨ single-env x (mem E) ,
   ⟨ single-fin{E}{x} ,
   ⟨ single-⊆ E⊆⟦M⟧ρ ,
     E⊆sing[xE]x{E}{x} ⟩ ⟩ ⟩
     
⟦⟧-continuous-env {L · M}{ρ}{[]} E⊆⟦M⟧ρ =
   ⟨ (λ x → ∅) , ⟨ (λ x → ⟨ [] , (λ x₁ ()) ⟩) , ⟨ (λ x d ()) , (λ d ()) ⟩ ⟩ ⟩
   
⟦⟧-continuous-env {L · M}{ρ}{w ∷ E} E⊆⟦M⟧ρ
    with ⟦⟧-continuous-env {L · M}{ρ}{E} λ d z → E⊆⟦M⟧ρ d (mem-there z)
... | ⟨ ρ′ , ⟨ fρ′ , ⟨ ρ′⊆ρ , E⊆⟦L·M⟧ρ′ ⟩ ⟩ ⟩ 
    with E⊆⟦M⟧ρ w mem-here
... | ⟨ V , ⟨ V↦w∈⟦L⟧ρ , V⊆⟦M⟧ρ ⟩ ⟩ 
    with ⟦⟧-continuous-env{L}{ρ}{(V ↦ w) ∷ []} λ { d mem-here → V↦w∈⟦L⟧ρ }
... | ⟨ ρ₂ , ⟨ fρ₂ , ⟨ ρ₂⊆ρ , [V↦w]⊆⟦L⟧ρ₂ ⟩ ⟩ ⟩
    with ⟦⟧-continuous-env{M}{ρ}{V} V⊆⟦M⟧ρ
... | ⟨ ρ₃ , ⟨ fρ₃ , ⟨ ρ₃⊆ρ , V⊆⟦M⟧ρ₃ ⟩ ⟩ ⟩ =
    ⟨ ρ₄ , ⟨ fin-ρ₄ , ⟨ ρ₄⊆ρ , w∷E⊆⟦L·M⟧ρ₄ ⟩ ⟩ ⟩
    where
    ρ₄ = (ρ′ ⊔ₑ ρ₂) ⊔ₑ ρ₃
    fin-ρ₄ : fin-env ρ₄
    fin-ρ₄ = join-fin-env (join-fin-env fρ′ fρ₂) fρ₃
    ρ₄⊆ρ : ρ₄ ⊆ₑ ρ
    ρ₄⊆ρ = join-lub (join-lub ρ′⊆ρ ρ₂⊆ρ) ρ₃⊆ρ
    ρ′⊆ρ₄ : ρ′ ⊆ₑ ρ₄
    ρ′⊆ρ₄ = ⊆ₑ-trans join-⊆-left join-⊆-left
    ρ₂⊆ρ₄ : ρ₂ ⊆ₑ ρ₄
    ρ₂⊆ρ₄ = ⊆ₑ-trans join-⊆-right join-⊆-left
    ρ₃⊆ρ₄ : ρ₃ ⊆ₑ ρ₄
    ρ₃⊆ρ₄ = join-⊆-right
    V↦w∈⟦L⟧ρ₄ : V ↦ w ∈ ⟦ L ⟧ ρ₄
    V↦w∈⟦L⟧ρ₄ = ⟦⟧-monotone{L}{ρ₂}{ρ₄} ρ₂⊆ρ₄ (V ↦ w)
                    ([V↦w]⊆⟦L⟧ρ₂ (V ↦ w) mem-here)
    V⊆⟦M⟧ρ₄ : mem V ⊆ ⟦ M ⟧ ρ₄
    V⊆⟦M⟧ρ₄ v v∈V = ⟦⟧-monotone{M}{ρ₃}{ρ₄} ρ₃⊆ρ₄ v (V⊆⟦M⟧ρ₃ v v∈V)
    w∈⟦L·M⟧ρ₄ : w ∈ ⟦ L · M ⟧ ρ₄
    w∈⟦L·M⟧ρ₄ = ⟨ V , ⟨ V↦w∈⟦L⟧ρ₄ , V⊆⟦M⟧ρ₄ ⟩ ⟩
    E⊆⟦L·M⟧ρ₄ : mem E ⊆ ⟦ L · M ⟧ ρ₄
    E⊆⟦L·M⟧ρ₄ w′ w′∈E =
       let w′∈⟦L·M⟧ρ′ = E⊆⟦L·M⟧ρ′ w′ w′∈E in
       ⟦⟧-monotone {L · M}{ρ′}{ρ₄} ρ′⊆ρ₄ w′ w′∈⟦L·M⟧ρ′ 
    w∷E⊆⟦L·M⟧ρ₄ : mem (w ∷ E) ⊆ ⟦ L · M ⟧ ρ₄
    w∷E⊆⟦L·M⟧ρ₄ v mem-here = w∈⟦L·M⟧ρ₄
    w∷E⊆⟦L·M⟧ρ₄ v (mem-there v∈E) = E⊆⟦L·M⟧ρ₄ v v∈E

⟦⟧-continuous-env {ƛ N}{ρ}{E} E⊆⟦M⟧ρ = {!!}
⟦⟧-continuous-env {$ p k}{ρ}{E} E⊆⟦M⟧ρ = {!!}


update : Env → ℕ → 𝒫 Value → Env → Env
update ρ n D ρ′ x
    with x <? n
... | yes lt = ρ x
... | no nlt
    with x ≟ n
... | yes refl = D
... | no ne = ρ′ x

⟦⟧-continuous-aux : ∀{N : Term}{ρ ρ′}{n}
  → continuous (λ D → ⟦ N ⟧ (update ρ n D ρ′))
⟦⟧-continuous-aux {` x}{ρ}{ρ′}{n} X E E⊆
    with x <? n
... | yes lt = ⟨ [] , ⟨ (λ { v () }) , E⊆ ⟩ ⟩
... | no nlt
    with x ≟ n
... | yes refl = ⟨ E , ⟨ E⊆ , (λ d z → z) ⟩ ⟩
... | no ne = ⟨ [] , ⟨ (λ { v () }) , E⊆ ⟩ ⟩
⟦⟧-continuous-aux {L · M}{ρ}{ρ′}{n} X E E⊆
    with ⟦⟧-continuous-aux {L}{ρ}{ρ′}{n} X {!!} {!!}
... | ⟨ D₁ , ⟨ D<X , E<FD₁ ⟩ ⟩ =

    {!!}

⟦⟧-continuous-aux {ƛ N}{ρ} = {!!}
⟦⟧-continuous-aux {$ p k}{ρ} = {!!}

⟦⟧-continuous : ∀{N : Term}{ρ}
  → continuous (λ D → ⟦ N ⟧ (D • ρ))
⟦⟧-continuous {N}{ρ} =
  {!!}

{- Reduction -}

infix 2 _—→_

data _—→_ : Term → Term → Set where

  ξ₁-rule : ∀  {L L′ M : Term}
    → L —→ L′
      ----------------
    → L · M —→ L′ · M

  ξ₂-rule : ∀  {L M M′ : Term}
    → TermValue L
    → M —→ M′
      ----------------
    → L · M —→ L · M′

  β-rule : ∀  {N : Term} {M : Term}
    → TermValue M
      ---------------------------------
    → (ƛ N) · M —→ N [ M ]

  δ-rule : ∀ {B}{P} {f : base-rep B → rep P} {k : base-rep B}
      ------------------------------------------------------------
    → _—→_  (($ (B ⇒ P) f) · ($ (base B) k)) ($ P (f k))

{- Soundness of the Semantics -}

⟦⟧—→ : ∀{M N : Term}{ρ : Var → 𝒫 Value}
   → M —→ N
   → ⟦ M ⟧ ρ ≃ ⟦ N ⟧ ρ
   
⟦⟧—→ {L · M} {L′ · M} {ρ} (ξ₁-rule L—→L′) =
  let IH = ⟦⟧—→{ρ = ρ} L—→L′ in
    ⟦ L · M ⟧ ρ
  ≃⟨ ≃-refl ⟩
    (⟦ L ⟧ ρ) ▪ (⟦ M ⟧ ρ)
  ≃⟨ ▪-cong IH ≃-refl ⟩
    (⟦ L′ ⟧ ρ) ▪ (⟦ M ⟧ ρ)
  ≃⟨ ≃-refl ⟩
    ⟦ L′ · M ⟧ ρ
  ∎
  where open ≃-Reasoning  
⟦⟧—→ {V · M} {.(_ · _)} {ρ} (ξ₂-rule {M′ = M′} v M—→M′) =
  let IH = ⟦⟧—→{ρ = ρ} M—→M′ in
    ⟦ V · M ⟧ ρ
  ≃⟨ ≃-refl ⟩
    (⟦ V ⟧ ρ) ▪ (⟦ M ⟧ ρ)
  ≃⟨ ▪-cong (≃-refl{D = ⟦ V ⟧ ρ}) IH ⟩
    (⟦ V ⟧ ρ) ▪ (⟦ M′ ⟧ ρ)
  ≃⟨ ≃-refl ⟩
    ⟦ V · M′ ⟧ ρ
  ∎
  where open ≃-Reasoning  
⟦⟧—→ {ƛ N · V} {_} {ρ} (β-rule v) =
    ⟦ ƛ N · V ⟧ ρ
  ≃⟨ ≃-refl ⟩
     (Λ (λ D → ⟦ N ⟧ (D • ρ))) ▪ (⟦ V ⟧ ρ)
  ≃⟨ Λ-▪ {λ D → ⟦ N ⟧ (D • ρ)} (⟦⟧-continuous{N}{ρ}) (⟦⟧-monotone-one{N}) ⟩
     ⟦ N ⟧ (⟦ V ⟧ ρ • ρ)
  ≃⟨ ≃-reflexive (sym (⟦⟧-substitution {N} {V} {ρ})) ⟩
    ⟦ N [ V ] ⟧ ρ
  ∎
  where open ≃-Reasoning
⟦⟧—→ {($ (B ⇒ P) f · $ (base B) k)} {_} {ρ} δ-rule = {!!}

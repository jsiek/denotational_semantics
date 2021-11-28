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
open import Level renaming (zero to lzero; suc to lsuc; _⊔_ to _l⊔_)
open import Relation.Binary.PropositionalEquality
    using (_≡_; _≢_; refl; sym; subst)
open import Relation.Nullary using (¬_; Dec; yes; no)

open import Primitives
open import ScopedTuple hiding (𝒫)
open import SetsAsPredicates
open import Syntax hiding (⌈_⌉)
open import NewSigUtil
open import NewSyntaxUtil
open import NewDOpSig
open import Utilities using (extensionality)
open import NewDenotProperties

module NewSemantics (Op : Set) (sig : Op → List Sig) where

open Syntax.OpSig Op sig
open import Fold2 Op sig



{- ================ Set-valued environments ================================ -}

Env : (A : Set) → Set₁
Env A = Var → 𝒫 A

nonempty-env : ∀ {A} → Env A → Set
nonempty-env ρ = ∀ x → nonempty (ρ x)

infix 5 _⊆ₑ_
_⊆ₑ_ : ∀ {A} → Env A → Env A → Set
ρ₁ ⊆ₑ ρ₂ = ∀ x → ρ₁ x ⊆ ρ₂ x

⊆ₑ-trans : ∀{A}{ρ₁ ρ₂ ρ₃ : Env A} → ρ₁ ⊆ₑ ρ₂ → ρ₂ ⊆ₑ ρ₃ → ρ₁ ⊆ₑ ρ₃
⊆ₑ-trans {ρ₁}{ρ₂}{ρ₃} r12 r23 x = λ d z → r23 x d (r12 x d z)

extend-nonempty-env : ∀{A}{ρ : Env A}{X}
   → nonempty-env ρ  →  nonempty X  →  nonempty-env (X • ρ)
extend-nonempty-env {ρ} {X} NE-ρ NE-X zero = NE-X
extend-nonempty-env {ρ} {X} NE-ρ V≢[] (suc x) = NE-ρ x

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


{- =================== Monotonic Semantics ================================= -}

record Semantics {A : Set} : Set₁ where
  field 
    error : A 
    interp-op : DOpSig (𝒫 A) sig

  init : 𝒫 A
  init = ⌈ error ⌉

  ⟦_⟧ : ABT → Env A → 𝒫 A
  ⟦ M ⟧ ρ = fold interp-op init ρ M

  ⟦_⟧ₐ : ∀{b} → Arg b → Env A → Result (𝒫 A) b
  ⟦ arg ⟧ₐ ρ = fold-arg interp-op init ρ arg

  ⟦_⟧₊ : ∀{bs} → Args bs → Env A → Tuple bs (Result (𝒫 A))
  ⟦ args ⟧₊ ρ = fold-args interp-op init ρ args

  field 
    mono-op : 𝕆-monotone sig interp-op

open Semantics {{...}}

{- =================== Consistent Semantics =============================== -}

record ConsistentSemantics {A : Set} : Set₁ where
  field 
    {{Sem}} : Semantics {A}
    consistency : A → A → Set
    consistent-op : 𝕆-consistent consistency sig (Semantics.interp-op Sem)

open ConsistentSemantics {{...}}

{- =================== Continuous Semantics ====================== -}

continuous-∈ : ∀ {A} → (Env A → 𝒫 A) → Env A → A → Set₁
continuous-∈ {A} D ρ v = v ∈ D ρ
   → Σ[ ρ′ ∈ Env A ] finiteNE-env ρ′ × ρ′ ⊆ₑ ρ  × v ∈ D ρ′

continuous-env : ∀ {A} → (Env A → 𝒫 A) → Env A → Set₁
continuous-env {A} D ρ = ∀ v → v ∈ D ρ
                     → Σ[ ρ′ ∈ Env A ] finiteNE-env ρ′ × ρ′ ⊆ₑ ρ  × v ∈ D ρ′

tracebound-result : ∀ {A : Set} b (F : Env A → Result (𝒫 A) b) (ρ : Env A) (ρ∁ : Env A) → Set₁
tracebound-result {A} ■ F ρ ρ∁ = continuous-env F ρ
tracebound-result {A} (ν b) F ρ ρ∁ = ∀ V → V ≢ [] → tracebound-result b (λ ρ' → F ρ' (mem V)) ((mem V) • ρ) ρ∁
tracebound-result {A} (∁ b) F ρ ρ∁ = tracebound-result b F ρ∁ ρ∁

all-results-tracebound : ∀ {A} b F ρ (ρ∁ : Env A) → finiteNE-env ρ → finiteNE-env ρ∁ → tracebound-result b F ρ ρ∁
all-results-tracebound ■ F ρ ρ∁ fin-ρ fin-ρ∁ d d∈ = ⟨ ρ , ⟨ fin-ρ , ⟨ (λ i d d∈ρi → d∈ρi) , d∈ ⟩ ⟩ ⟩
all-results-tracebound (ν b) F ρ ρ∁ fin-ρ fin-ρ∁ V Vne = 
  all-results-tracebound b (λ ρ → F ρ (mem V)) (mem V • ρ) ρ∁ 
                         (extend-finiteNE-env fin-ρ ⟨ V , ⟨ ≃-refl , Vne ⟩ ⟩) fin-ρ∁
all-results-tracebound (∁ b) F ρ ρ∁ fin-ρ fin-ρ∁ = all-results-tracebound b F ρ∁ ρ∁ fin-ρ∁ fin-ρ∁




continuous-∈⇒⊆ : ∀ {A} E (ρ : Env A) (NE-ρ : nonempty-env ρ)
   → monotone-env E
   → ∀ V → mem V ⊆ E ρ
   → (∀ v → v ∈ mem V → continuous-∈ E ρ v)
   → Σ[ ρ′ ∈ Env A ] finiteNE-env ρ′ × ρ′ ⊆ₑ ρ  × mem V ⊆ E ρ′
continuous-∈⇒⊆ E ρ NE-ρ mE [] V⊆E ∀v∈V⇒cont =
   ⟨ initial-finiteNE-env ρ NE-ρ , ⟨ initial-fin ρ NE-ρ ,
   ⟨ initial-fin-⊆ ρ NE-ρ , (λ d ()) ⟩ ⟩ ⟩
continuous-∈⇒⊆ {A} E ρ NE-ρ mE (v ∷ V) v∷V⊆Eρ v∈V⇒cont
    with continuous-∈⇒⊆ E ρ NE-ρ mE V (λ d z → v∷V⊆Eρ d (there z))
                (λ w w∈V w∈Mρ → v∈V⇒cont w (there w∈V) w∈Mρ)
... | ⟨ ρ₁ , ⟨ fρ₁ , ⟨ ρ₁⊆ρ , V⊆Eρ₁ ⟩ ⟩ ⟩
    with v∈V⇒cont v (here refl) (v∷V⊆Eρ v (here refl))
... | ⟨ ρ₂ , ⟨ fρ₂ , ⟨ ρ₂⊆ρ , v∈Eρ₂ ⟩ ⟩ ⟩ =    
    ⟨ ρ₃ , ⟨ (join-finiteNE-env fρ₁ fρ₂) , ⟨ (join-lub ρ₁⊆ρ ρ₂⊆ρ) ,
    G ⟩ ⟩ ⟩
    where
    ρ₃ = ρ₁ ⊔ₑ ρ₂
    G : (d : A) → mem (v ∷ V) d → d ∈ E ρ₃
    G d (here refl) = mE {ρ₂}{ρ₃} join-⊆-right v v∈Eρ₂
    G d (there m) = mE {ρ₁}{ρ₃} join-⊆-left d (V⊆Eρ₁ d m)






{- here I'm hoping that all semantics are continuous...
   or at least that the type signature for continuous-op can be much simplified.

all-args : (∀ b → Arg b → Set₁) → ∀ bs → Args bs → Set₁
all-args P [] args = Lift (lsuc lzero) True
all-args P (b ∷ bs) (cons arg args) = P b arg × all-args P bs args

Cont-Env-Arg : ∀ {{_ : Semantics {A}}} (ρ : Env A) (NE-ρ : nonempty-env ρ)
    → ∀ b → (arg : Arg b) → Set₁
  Cont-Env-Arg ρ NE-ρ ■ (ast M) = continuous-env ⟦ M ⟧ ρ
  Cont-Env-Arg ρ NE-ρ (ν b) (bind arg) =
    ∀ V → (ne : V ≢ [])
    → Cont-Env-Arg (mem V • ρ)
          (extend-nonempty-env NE-ρ (E≢[]⇒nonempty-mem ne)) b arg
  Cont-Env-Arg ρ NE-ρ (∁ b) (clear arg) =
      Cont-Env-Arg (λ x → init) (λ i → ⟨ error , refl ⟩) b arg

record ContinuousSemantics {A : Set} : Set₁ where
  field 
    {{Sem}} : Semantics {A}

    {- continuous-op : ∀{op}{ρ : Env A}{NE-ρ}{v}{args} → v ∈ ⟦ op ⦅ args ⦆ ⟧ ρ → all-args (Cont-Env-Arg ρ NE-ρ) (sig op) args → Σ[ ρ′ ∈ Env A ] finite-env ρ′ × ρ′ ⊆ₑ ρ × v ∈ (⟦ op ⦅ args ⦆ ⟧ ρ′)
    -}

open ContinuousSemantics {{...}}
-}










{-
record ContinuousSemantics : Set₁ where
  field {{Sem}} : Semantics
  field continuous-op : ∀{op}{ρ}{NE-ρ}{v}{args} → v ∈ ⟦ op ⦅ args ⦆ ⟧ ρ → all-args (Cont-Env-Arg ρ NE-ρ) (sig op) args  →   Σ[ ρ′ ∈ Env ] finite-env ρ′ × ρ′ ⊆ₑ ρ × v ∈ (⟦ op ⦅ args ⦆ ⟧ ρ′)

open ContinuousSemantics {{...}}


{- Monotone -------------------------------------------------------------------}

⟦⟧-monotone : ∀{{_ : Semantics}} {ρ ρ′} (M : ABT)
  →  ρ ⊆ₑ ρ′ →  ⟦ M ⟧ ρ ⊆ ⟦ M ⟧ ρ′
⟦⟧-monotone-arg : ∀{{_ : Semantics}} {b}{ρ ρ′} (arg : Arg b)
  →  ρ ⊆ₑ ρ′ →  ⊆-result b (⟦ arg ⟧ₐ ρ) (⟦ arg ⟧ₐ ρ′)
⟦⟧-monotone-args : ∀{{_ : Semantics}} {bs}{ρ ρ′} (args : Args bs)
  →  ρ ⊆ₑ ρ′  →  ⊆-results bs (⟦ args ⟧₊ ρ) (⟦ args ⟧₊ ρ′)
  
⟦⟧-monotone {ρ}{ρ′} (` x) ρ<ρ′ = ρ<ρ′ x
⟦⟧-monotone {ρ}{ρ′} (op ⦅ args ⦆) ρ<ρ′ = mono-op (⟦⟧-monotone-args  args ρ<ρ′)

⟦⟧-monotone-arg {■} (ast M) ρ<ρ′ = lift (⟦⟧-monotone M ρ<ρ′)
⟦⟧-monotone-arg {ν b}{ρ}{ρ′} (bind arg) ρ<ρ′ X =
    ⟦⟧-monotone-arg {b}{X • ρ}{X • ρ′} arg (env-ext ρ<ρ′)
⟦⟧-monotone-arg {∁ b} (clear arg) ρ<ρ′ =
    ⟦⟧-monotone-arg {b}{λ x → init}{λ x → init} arg λ x d z → z

⟦⟧-monotone-args {bs = []} nil ρ<ρ′ = lift tt
⟦⟧-monotone-args {bs = b ∷ bs} (cons arg args) ρ<ρ′ =
  ⟨ ⟦⟧-monotone-arg arg ρ<ρ′ , ⟦⟧-monotone-args args ρ<ρ′ ⟩

⟦⟧-monotone-one : ∀{{_ : Semantics}}{N : ABT}{ρ}
   → monotone (λ D → ⟦ N ⟧ (D • ρ))
⟦⟧-monotone-one {N}{ρ} D₁ D₂ D12 = ⟦⟧-monotone N G
  where G : (x : Var) → (D₁ • ρ) x ⊆ (D₂ • ρ) x
        G zero = D12
        G (suc x) = λ v z → z



{- Continuous -----------------------------------------------------------------}

⟦⟧-continuous : ∀{{_ : ContinuousSemantics}}{ρ}{NE-ρ : nonempty-env ρ}
    (M : ABT)
  → continuous-env ⟦ M ⟧ ρ 
⟦⟧-cont-env-arg : ∀{{_ : ContinuousSemantics}}
    {ρ}{NE-ρ : nonempty-env ρ} {b}(arg : Arg b)
  → Cont-Env-Arg ρ NE-ρ b arg 
⟦⟧-cont-env-args : ∀{{_ : ContinuousSemantics}}
    {ρ}{NE-ρ : nonempty-env ρ}{bs} (args : Args bs)
  → all-args (Cont-Env-Arg ρ NE-ρ) bs args

⟦⟧-continuous {ρ}{NE-ρ} (` x) v v∈⟦M⟧ρ =
   ⟨ (single-env x ⌈ v ⌉ ρ NE-ρ) , ⟨ (single-fin {v}{x}) , ⟨ (single-⊆ v∈⟦M⟧ρ) ,
     (v∈single[xv]x {v}{x}) ⟩ ⟩ ⟩

⟦⟧-continuous {ρ}{NE-ρ} (op ⦅ args ⦆) v v∈⟦M⟧ρ =
    continuous-op{NE-ρ = NE-ρ} v∈⟦M⟧ρ (⟦⟧-cont-env-args {ρ}{NE-ρ} args)
⟦⟧-cont-env-arg {ρ} {NE-ρ} {■} (ast M) v v∈⟦M⟧ρ =
    ⟦⟧-continuous {ρ}{NE-ρ = NE-ρ} M v v∈⟦M⟧ρ
⟦⟧-cont-env-arg {ρ} {NE-ρ} {ν b} (bind arg) V V≢[] =
    let NE-V•ρ = (extend-nonempty-env NE-ρ (E≢[]⇒nonempty-mem V≢[])) in
    ⟦⟧-cont-env-arg {mem V • ρ}{NE-V•ρ} {b} arg
⟦⟧-cont-env-arg {ρ} {NE-ρ} {∁ b} (clear arg) =
    ⟦⟧-cont-env-arg {λ x → init} {λ x → ⟨ ν , refl ⟩}{b} arg

⟦⟧-cont-env-args {ρ} {NE-ρ} {[]} nil = lift tt
⟦⟧-cont-env-args {ρ} {NE-ρ} {b ∷ bs} (cons arg args) =
    ⟨ ⟦⟧-cont-env-arg {ρ}{NE-ρ}{b} arg ,
      ⟦⟧-cont-env-args {ρ} {NE-ρ} {bs} args ⟩

⟦⟧-continuous-⊆  : ∀{{_ : ContinuousSemantics}}{ρ}{NE-ρ : nonempty-env ρ}
    (M : ABT)
  → ∀ V → mem V ⊆ ⟦ M ⟧ ρ
  → Σ[ ρ′ ∈ Env ] finite-env ρ′ × ρ′ ⊆ₑ ρ  × mem V ⊆ ⟦ M ⟧ ρ′
⟦⟧-continuous-⊆ {ρ}{NE-ρ} M V V⊆Eρ =
    continuous-∈⇒⊆ ⟦ M ⟧ ρ NE-ρ (⟦⟧-monotone M) V V⊆Eρ
        (λ v v∈V → ⟦⟧-continuous {NE-ρ = NE-ρ} M v)

⟦⟧-continuous-one : ∀{{_ : ContinuousSemantics}}{N : ABT}
    {ρ}{NE-ρ : nonempty-env ρ}
  → continuous (λ D → ⟦ N ⟧ (D • ρ))
⟦⟧-continuous-one {N}{ρ}{NE-ρ} X E E⊆⟦N⟧X•ρ NE-X
    with ⟦⟧-continuous-⊆ {X • ρ}{extend-nonempty-env NE-ρ NE-X} N E E⊆⟦N⟧X•ρ
... | ⟨ ρ′ , ⟨ fρ′ , ⟨ ρ′⊆X•ρ , E⊆⟦N⟧ρ′ ⟩ ⟩ ⟩
    with fρ′ 0
... | ⟨ D , ⟨ ρ′x=D , NE-D ⟩ ⟩ =
    ⟨ D , ⟨ (λ v v∈D → ρ′⊆X•ρ 0 v ((proj₂ ρ′x=D) v v∈D)) ,
    ⟨ (λ d d∈E → ⟦⟧-monotone {ρ′}{mem D • ρ} N G d (E⊆⟦N⟧ρ′ d d∈E)) , NE-D ⟩ ⟩ ⟩
    where
    G : (x : Var) → ρ′ x ⊆ (mem D • ρ) x
    G zero d d∈ρ0 = (proj₁ ρ′x=D) d d∈ρ0 
    G (suc x) d m = ρ′⊆X•ρ (suc x) d m

Λ⟦⟧-▪-id : ∀ {{_ : ContinuousSemantics}}{N : ABT}{ρ}{NE-ρ : nonempty-env ρ}
    {X : 𝒫 Value}
  → nonempty X
  → (Λ λ X → ⟦ N ⟧ (X • ρ)) ▪ X ≃ ⟦ N ⟧ (X • ρ)
Λ⟦⟧-▪-id {N}{ρ}{NE-ρ}{X} NE-X =
    Λ-▪-id {λ D → ⟦ N ⟧ (D • ρ)} (⟦⟧-continuous-one{N}{ρ}{NE-ρ})
        (⟦⟧-monotone-one{N}) NE-X

{- The following is annoying. Can it be simplified? -}
all-Cont-Env-Arg⇒cont-envs : ∀{{_ : Semantics}}
    {n}{args : Args (replicate n ■)}{ρ}{NE-ρ}
    → all-args (Cont-Env-Arg ρ NE-ρ) (replicate n ■) args
    → continuous-envs (⟦ args ⟧₊) ρ
all-Cont-Env-Arg⇒cont-envs {zero} {nil}{ρ}{NE-ρ} (lift tt) v v∈𝒯nil =
    ⟨ initial-finite-env ρ NE-ρ , ⟨ initial-fin ρ NE-ρ ,
    ⟨ initial-fin-⊆ ρ NE-ρ , v∈𝒯nil ⟩ ⟩ ⟩
all-Cont-Env-Arg⇒cont-envs {suc n} {cons (ast M) args}{ρ}{NE-ρ}
    ⟨ cM , cont-args ⟩ ⟬ v ∷ vs ⟭ ⟨ v∈ , vs∈ ⟩
    with all-Cont-Env-Arg⇒cont-envs {n} {args}{ρ}{NE-ρ} cont-args ⟬ vs ⟭ vs∈
... | ⟨ ρ₁ , ⟨ fρ₁ , ⟨ ρ₁⊆ρ , vs∈𝒯argsρ₁ ⟩ ⟩ ⟩
    with cM v v∈
... | ⟨ ρ₂ , ⟨ fρ₂ , ⟨ ρ₂⊆ρ , v∈𝒯Mρ₂ ⟩ ⟩ ⟩ =
    ⟨ ρ₁ ⊔ₑ ρ₂ , ⟨ join-finite-env fρ₁ fρ₂ , ⟨ join-lub ρ₁⊆ρ ρ₂⊆ρ ,
    ⟨ ⟦⟧-monotone M (λ x d z → inj₂ z) v v∈𝒯Mρ₂ ,
      𝒯-mono-⊆ (rel-results⇒rel-∏ ⊆-result⇒⊆
       (⟦⟧-monotone-args args (λ x d z → inj₁ z))) ⟬ vs ⟭ vs∈𝒯argsρ₁ ⟩ ⟩ ⟩ ⟩


-}
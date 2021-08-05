module PValue where
{-

  A denotational semantics of ISWIM, adapting the call-by-name models
  P(ω) of Scott (1976) and Dₐ of Engeler (1981) to call-by-value.

-}

open import Primitives
open import Syntax using (Rename)
open import ISWIM hiding (_[_]; id; _—→_; _—↠_)
open import Fold2 Op sig
open import ScopedTuple hiding (𝒫)
open import Sig
open import Utilities using (extensionality)

open import Data.Empty using (⊥-elim) renaming (⊥ to False)
open import Data.List using (List ; _∷_ ; []; _++_; length) 
open import Data.Nat using (ℕ; zero; suc; _≟_; _<_; s≤s)
open import Data.Product using (_×_; Σ; Σ-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt) renaming (⊤ to True)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; subst)
open import Relation.Nullary using (¬_; Dec; yes; no)

module PValue where

{- Set notation for predicates -------------------------------------------------}

𝒫 : Set → Set₁
𝒫 V = V → Set

∅ : ∀{T} → 𝒫 T
∅ = λ v → False 


⌈_⌉ : ∀ {T} → T → 𝒫 T     {- the singleton set containing only v -}
⌈ v ⌉ w = w ≡ v

infix 9 _∈_
_∈_ : ∀{T : Set} → T → 𝒫 T → Set
v ∈ D = D v

infix 9 _⊆_
_⊆_ : ∀{T : Set} → 𝒫 T → 𝒫 T → Set
D ⊆ E = ∀ d → d ∈ D → d ∈ E

nonempty : ∀{T : Set} → 𝒫 T → Set
nonempty{T} S = Σ[ x ∈ T ] x ∈ S


{- Finite Sets represented by Lists --------------------------------------------}

data mem : ∀{T : Set} → List T → T → Set where
  mem-here : ∀{T}{x : T}{ls} → mem (x ∷ ls) x
  mem-there : ∀{T}{x y : T}{ls} → mem ls x → mem (y ∷ ls) x

mem-++-left : ∀{T}{xs ys : List T}{x} → mem xs x → mem (xs ++ ys) x
mem-++-left {T} {x ∷ xs} mem-here = mem-here
mem-++-left {T} {x ∷ xs} (mem-there x∈xs) = mem-there (mem-++-left x∈xs)

mem-++-right : ∀{T}{xs ys : List T}{x} → mem ys x → mem (xs ++ ys) x
mem-++-right {T} {[]} m = m
mem-++-right {T} {x ∷ xs} m = mem-there (mem-++-right m)

++-nonempty : ∀{T : Set}{E1 E2 : List T}
  → E1 ≢ [] → E1 ++ E2 ≢ []
++-nonempty {T} {[]} {E2} NE-E1 = λ _ → NE-E1 refl
++-nonempty {T} {x ∷ E1} {E2} NE-E1 = λ ()

E≢[]⇒nonempty-mem : ∀{T}{E : List T}
  → E ≢ [] → nonempty (mem E)
E≢[]⇒nonempty-mem {T} {[]} E≢[] = ⊥-elim (E≢[] refl)
E≢[]⇒nonempty-mem {T} {x ∷ E} E≢[] = ⟨ x , mem-here ⟩


{- Denotational Values ---------------------------------------------------------}

data Value : Set where
  const : {B : Base} → base-rep B → Value   {- A primitive constant of type B. -}
  _↦_ : List Value → Value → Value         {- An entry in a function's graph. -}
  ν : Value       {- A function. Needed for CBV to distinguish from diverging. -}


{- Abstraction and Application -------------------------------------------------}

Λ : (𝒫 Value → 𝒫 Value) → 𝒫 Value
Λ f (const k) = False
Λ f (V ↦ w) = w ∈ f (mem V)  ×  V ≢ []
Λ f ν = True

infix 10 _▪_
_▪_ : 𝒫 Value → 𝒫 Value → 𝒫 Value
D₁ ▪ D₂ = λ w → Σ[ V ∈ List Value ] (V ↦ w ∈ D₁)  ×  (mem V ⊆ D₂)  ×  V ≢ []

℘ : (P : Prim) → rep P → 𝒫 Value
℘ (base B) k (const {B′} k′)
    with base-eq? B B′
... | yes refl = k ≡ k′
... | no neq = False
℘ (base B) k (V ↦ w) = False
℘ (base B) k ν = False
℘ (B ⇒ P) f (const k) = False
℘ (B ⇒ P) f (V ↦ w) =
   Σ[ k ∈ base-rep B ] V ≡ (const {B} k) ∷ []  ×  w ∈ ℘ P (f k)
℘ (B ⇒ P) f ν = True

k∈℘k : ∀{B}{k} → const {B} k ∈ ℘ (base B) k
k∈℘k {B}{k}
    with base-eq? B B
... | yes refl = refl
... | no neq = neq refl

k′∈℘k⇒P≡B : ∀{P B}{k}{k′} → const {B} k′ ∈ ℘ P k → P ≡ base B
k′∈℘k⇒P≡B {base B′} {B} {k} {k′} k′∈℘k
    with base-eq? B′ B
... | yes refl = refl
... | no neq = ⊥-elim k′∈℘k

k′∈℘k⇒k′≡k : ∀{B}{k}{k′} → const {B} k′ ∈ ℘ (base B) k → k′ ≡ k
k′∈℘k⇒k′≡k {B}{k}{k′} m
    with base-eq? B B
... | yes refl = sym m
... | no neq = ⊥-elim m


{- Denotational Equality and Approximation (less-than) -------------------------}

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
  _≃⟨_⟩_ : ∀ (D₁ : 𝒫 Value) {D₂ D₃ : 𝒫 Value} → D₁ ≃ D₂ → D₂ ≃ D₃ → D₁ ≃ D₃
  D₁ ≃⟨ D₁≃D₂ ⟩ D₂≃D₃ = ≃-trans D₁≃D₂ D₂≃D₃

  infix 3 _∎
  _∎ : ∀ (D : 𝒫 Value) → D ≃ D
  D ∎  =  ≃-refl


{- Application is a Congruence -------------------------------------------------}

▪-cong : ∀{D₁ D₂ D₁′ D₂′ : 𝒫 Value}
  → D₁ ≃ D₁′  →  D₂ ≃ D₂′
  → D₁ ▪ D₂ ≃ D₁′ ▪ D₂′
▪-cong (equal x x₁) (equal x₂ x₃) = equal (▪-cong-≲ x x₂) (▪-cong-≲ x₁ x₃)
  where
  ▪-cong-≲ : ∀{D₁ D₂ D₁′ D₂′ : 𝒫 Value}
    → D₁ ≲ D₁′  →  D₂ ≲ D₂′
    → D₁ ▪ D₂ ≲ D₁′ ▪ D₂′
  ▪-cong-≲ D11 D22 w ⟨ V , ⟨ wv∈D1 , ⟨ V<D2 , V≢[] ⟩ ⟩ ⟩ =
     ⟨ V , ⟨ (D11 (V ↦ w) wv∈D1) , ⟨ (λ d z → D22 d (V<D2 d z)) , V≢[] ⟩ ⟩ ⟩
  
{- Abstraction followed by Application is the identity -------------------------}

continuous : (F : 𝒫 Value → 𝒫 Value) → Set₁
continuous F = ∀ X E → mem E ⊆ F X → nonempty X
    → Σ[ D ∈ List Value ] mem D ≲ X  ×  mem E ⊆ F (mem D)  ×  D ≢ []

monotone : (F : 𝒫 Value → 𝒫 Value) → Set₁
monotone F = ∀ D₁ D₂ → D₁ ≲ D₂ → F D₁ ≲ F D₂

Λ-▪-id : ∀ {F : 𝒫 Value → 𝒫 Value}{X : 𝒫 Value}
  → continuous F → monotone F → nonempty X
  → (Λ F) ▪ X ≃ F X
Λ-▪-id {F}{X} Fcont Fmono NE-X = equal (Λ-▪-≲ Fmono) (≲-Λ-▪ Fcont NE-X)
  where
  Λ-▪-≲ : ∀ {F : 𝒫 Value → 𝒫 Value}{X : 𝒫 Value}
    → monotone F  →  (Λ F) ▪ X ≲ F X
  Λ-▪-≲ {F} {X} Fmono w ⟨ V , ⟨ ⟨ w∈FV , _ ⟩ , ⟨ V<X , V≢[] ⟩ ⟩ ⟩ =
      Fmono (mem V) X V<X w w∈FV

  ≲-Λ-▪ : ∀ {F : 𝒫 Value → 𝒫 Value}{X : 𝒫 Value}
    → continuous F  → nonempty X →  F X ≲ (Λ F) ▪ X
  ≲-Λ-▪ {F}{X} Fcont NE-X w w∈FX 
      with Fcont X (w ∷ []) (λ { d mem-here → w∈FX }) NE-X
  ... | ⟨ D , ⟨ D<X , ⟨ w∈FD , NE-D ⟩ ⟩ ⟩ =
        ⟨ D , ⟨ ⟨ w∈FD w mem-here , NE-D ⟩ , ⟨ D<X , NE-D ⟩ ⟩ ⟩

  
{- Denotational Semantics of the ISWIM Language via fold -----------------------}

interp-op  : (op : Op) → Tuple (sig op) (ArgTy (𝒫 Value)) → 𝒫 Value
interp-op lam ⟨ F , _ ⟩ = Λ F
interp-op app ⟨ D₁ , ⟨ D₂ , _ ⟩ ⟩ = D₁ ▪ D₂
interp-op (lit P k) _ = ℘ P k

Env : Set₁
Env = Var → 𝒫 Value

infix 11 ⟦_⟧_
⟦_⟧_ : Term → Env → 𝒫 Value
⟦ M ⟧ ρ = fold interp-op ∅ ρ M

⟦⟧-app : ∀{L M : Term}{ρ : Env}
  → ⟦ L · M ⟧ ρ ≡ ⟦ L ⟧ ρ ▪ ⟦ M ⟧ ρ
⟦⟧-app = refl

⟦⟧-lam : ∀{N : Term}{ρ : Env}
  → ⟦ ƛ N ⟧ ρ ≡ Λ (λ D → ⟦ N ⟧ (D • ρ))
⟦⟧-lam = refl

⟦⟧-prim : ∀{P : Prim}{k : rep P}{ρ : Env}
  → ⟦ $ P k ⟧ ρ ≡ ℘ P k
⟦⟧-prim = refl


{- Syntactic values terminate (i.e., have nonempty denotations) ----------------}

nonempty-env : Env → Set
nonempty-env ρ = ∀ x → nonempty (ρ x)

value-nonempty : ∀{V : Term}{ρ}
  → nonempty-env ρ → TermValue V → nonempty (⟦ V ⟧ ρ)
value-nonempty NE-ρ (V-var {x}) = NE-ρ x
value-nonempty NE-ρ (V-ƛ) = ⟨ ν , tt ⟩
value-nonempty NE-ρ (V-lit {base B} {k}) = ⟨ const k , k∈℘k ⟩
value-nonempty NE-ρ (V-lit {B ⇒ P} {k}) = ⟨ ν , tt ⟩


{- Substitution Lemma (via fold-subst-fusion) ----------------------------------}

⟦⟧-par-subst : ∀ {M : Term}{σ : Subst}{ρ : Var → 𝒫 Value}
  → ⟦ ⟪ σ ⟫ M ⟧ ρ ≡ ⟦ M ⟧ (λ x → ⟦ σ x ⟧ ρ)
⟦⟧-par-subst {M}{ρ} = fold-subst-fusion M

id : Subst
id = (λ x → ` x)

_[_] : Term → Term → Term
N [ M ] =  ⟪ M • id ⟫ N

⟦⟧-subst : ∀ {M N : Term}{ρ : Var → 𝒫 Value}
  → ⟦ M [ N ] ⟧ ρ ≡ ⟦ M ⟧ ((⟦ N ⟧ ρ) • ρ)
⟦⟧-subst {M}{N}{ρ} =
  subst (λ X → ⟦ M [ N ] ⟧ ρ ≡ ⟦ M ⟧ X) (extensionality EQ) (⟦⟧-par-subst {M}{N • id})
  where 
  EQ : (x : Var) → ⟦ (N • id) x ⟧ ρ ≡ (⟦ N ⟧ ρ • ρ) x
  EQ zero = refl
  EQ (suc x) = refl


{- Denotations are monotone ----------------------------------------------------}

⟦⟧-monotone : ∀{M : Term}{ρ ρ′}  →  (∀ x → ρ x ≲ ρ′ x)  →  ⟦ M ⟧ ρ ≲ ⟦ M ⟧ ρ′ 
⟦⟧-monotone {` x} ρ<ρ′ = ρ<ρ′ x
⟦⟧-monotone {L · M} ρ<ρ′ w ⟨ V , ⟨ Vw∈L , ⟨ V⊆M , V≢[] ⟩ ⟩ ⟩ =
   let vw∈Lρ′ = ⟦⟧-monotone {L} ρ<ρ′ (V ↦ w) Vw∈L in
   let v∈Mρ′ = ⟦⟧-monotone {M} ρ<ρ′ in
   ⟨ V , ⟨ vw∈Lρ′ , ⟨ (λ v v∈V → v∈Mρ′ v (V⊆M v v∈V)) , V≢[] ⟩ ⟩ ⟩
⟦⟧-monotone {ƛ N}{ρ}{ρ′} ρ<ρ′ (const k) ()
⟦⟧-monotone {ƛ N}{ρ}{ρ′} ρ<ρ′ (V ↦ w) ⟨ w∈⟦N⟧V•ρ , V≢[] ⟩ =
  ⟨ ⟦⟧-monotone {N}{mem V • ρ}{mem V • ρ′} G w w∈⟦N⟧V•ρ , V≢[] ⟩
  where G : (x : Var) → (mem V • ρ) x ≲ (mem V • ρ′) x
        G zero = λ v z → z
        G (suc x) = ρ<ρ′ x
⟦⟧-monotone {ƛ N}{ρ}{ρ′} ρ<ρ′ ν _ = tt
⟦⟧-monotone {$ p k} ρ<ρ′ v v∈℘k = v∈℘k

⟦⟧-monotone-one : ∀{N : Term}{ρ} → monotone (λ D → ⟦ N ⟧ (D • ρ))
⟦⟧-monotone-one {N}{ρ} D₁ D₂ D12 = ⟦⟧-monotone {N} G
  where G : (x : Var) → (D₁ • ρ) x ≲ (D₂ • ρ) x
        G zero = D12
        G (suc x) = λ v z → z


{- Denotations are continuous --------------------------------------------------}

infix 5 _⊆ₑ_
_⊆ₑ_ : Env → Env → Set
ρ₁ ⊆ₑ ρ₂ = ∀ x → ρ₁ x ⊆ ρ₂ x

⊆ₑ-trans : ∀{ρ₁ ρ₂ ρ₃} → ρ₁ ⊆ₑ ρ₂ → ρ₂ ⊆ₑ ρ₃ → ρ₁ ⊆ₑ ρ₃
⊆ₑ-trans {ρ₁}{ρ₂}{ρ₃} r12 r23 x = λ d z → r23 x d (r12 x d z)

{- environments whose codomain are finite nonempty sets -}
fin-env : Env → Set
fin-env ρ = ∀ x → Σ[ E ∈ List Value ] ρ x ≃ mem E × E ≢ []

initial-fin-env : (ρ : Env) → (NE-ρ : nonempty-env ρ) → Env
initial-fin-env ρ NE-ρ x
    with NE-ρ x
... | ⟨ v , v∈ρx ⟩ = ⌈ v ⌉

initial-fin : (ρ : Env) → (NE-ρ : nonempty-env ρ)
   → fin-env (initial-fin-env ρ NE-ρ)
initial-fin ρ NE-ρ x
    with NE-ρ x
... | ⟨ v , v∈ρx ⟩ =
      ⟨ v ∷ [] ,
      ⟨ equal (λ {w refl → mem-here}) (λ {w mem-here → refl}) , (λ ()) ⟩ ⟩

initial-fin-⊆ : (ρ : Env) → (NE-ρ : nonempty-env ρ)
  → initial-fin-env ρ NE-ρ ⊆ₑ ρ
initial-fin-⊆ ρ NE-ρ x v v∈initial
    with NE-ρ x
... | ⟨ w , w∈ρx ⟩ rewrite v∈initial = w∈ρx

extend-nonempty-env : ∀{ρ}{X}
   → nonempty-env ρ  →  nonempty X  →  nonempty-env (X • ρ)
extend-nonempty-env {ρ} {X} NE-ρ NE-X zero = NE-X
extend-nonempty-env {ρ} {X} NE-ρ V≢[] (suc x) = NE-ρ x

infix 6 _⊔ₑ_
_⊔ₑ_ : Env → Env → Env
(ρ₁ ⊔ₑ ρ₂) x v = ρ₁ x v ⊎ ρ₂ x v

join-fin-env : ∀{ρ₁ ρ₂}  → fin-env ρ₁  →  fin-env ρ₂  →  fin-env (ρ₁ ⊔ₑ ρ₂)
join-fin-env {ρ₁}{ρ₂} f1 f2 x
    with f1 x
... | ⟨ E1 , ⟨ ρ₁=E1 , NE-E1 ⟩ ⟩
    with f2 x
... | ⟨ E2 , ⟨ ρ₂=E2 , NE-E2 ⟩ ⟩ =
    ⟨ (E1 ++ E2) , ⟨ equal G (H {E1} ≲-refl) , ++-nonempty NE-E1 ⟩ ⟩
    where
    G : (v : Value) → ρ₁ x v ⊎ ρ₂ x v → mem (E1 ++ E2) v
    G v (inj₁ ρ1x) = mem-++-left ((to ρ₁=E1) v ρ1x)
    G v (inj₂ ρ2x) = mem-++-right ((to ρ₂=E2) v ρ2x)

    H : ∀{E} → mem E ≲ mem E1 → mem (E ++ E2) ≲ (λ v → ρ₁ x v ⊎ ρ₂ x v)
    H {[]} E<E1 v v∈E++E2 = inj₂ ((from ρ₂=E2) v v∈E++E2)
    H {x ∷ E} E<E1 .x mem-here = inj₁ ((from ρ₁=E1) x (E<E1 x mem-here))
    H {x ∷ E} E<E1 v (mem-there v∈E++E2) =
       H (λ v z → E<E1 v (mem-there z)) v v∈E++E2

{- single-env maps x to D and another variable y to something in ρ y. -}
single-env : Var → 𝒫 Value → (ρ : Env) → (NE-ρ : nonempty-env ρ) → Env
single-env x D ρ NE-ρ y
    with x ≟ y
... | yes refl = D
... | no neq
    with NE-ρ y
... | ⟨ v , v∈ρy ⟩ = ⌈ v ⌉    

single-fin : ∀{v}{x}{ρ}{NE-ρ} → fin-env (single-env x ⌈ v ⌉ ρ NE-ρ)
single-fin {v}{x}{ρ}{NE-ρ} y
    with x ≟ y
... | yes refl =
    ⟨ v ∷ [] ,
    ⟨ equal (λ { v₁ refl → mem-here}) (λ { v₁ mem-here → refl}) , (λ ()) ⟩ ⟩
... | no neq
    with NE-ρ y
... | ⟨ w , w∈ρy ⟩ =
    ⟨ w ∷ [] ,
    ⟨ equal (λ { v₁ refl → mem-here}) (λ { v₁ mem-here → refl}) , (λ ()) ⟩ ⟩

single-⊆ : ∀{ρ x v}{NE-ρ : nonempty-env ρ}
  →  v ∈ ρ x  →  single-env x ⌈ v ⌉ ρ NE-ρ ⊆ₑ ρ
single-⊆ {ρ}{x}{v}{NE-ρ} v∈ρx y w sing 
    with x ≟ y
... | yes refl rewrite sing = v∈ρx
... | no neq
    with NE-ρ y
... | ⟨ u , u∈ρy ⟩ rewrite sing = u∈ρy

v∈single[xv]x : ∀{v}{x}{ρ}{NE-ρ} → v ∈ single-env x ⌈ v ⌉ ρ NE-ρ x
v∈single[xv]x {v}{x}
    with x ≟ x
... | yes refl = refl
... | no neq = ⊥-elim (neq refl)

join-lub : ∀{ρ ρ₁ ρ₂} → ρ₁ ⊆ₑ ρ → ρ₂ ⊆ₑ ρ → ρ₁ ⊔ₑ ρ₂ ⊆ₑ ρ
join-lub {ρ} {ρ₁} {ρ₂} ρ₁⊆ρ ρ₂⊆ρ x v (inj₁ v∈ρ₁x) = ρ₁⊆ρ x v v∈ρ₁x
join-lub {ρ} {ρ₁} {ρ₂} ρ₁⊆ρ ρ₂⊆ρ x v (inj₂ v∈ρ₂x) = ρ₂⊆ρ x v v∈ρ₂x

join-⊆-left : ∀{ρ₁ ρ₂} → ρ₁ ⊆ₑ ρ₁ ⊔ₑ ρ₂
join-⊆-left {ρ₁}{ρ₂} = λ x d z → inj₁ z

join-⊆-right : ∀{ρ₁ ρ₂} → ρ₂ ⊆ₑ ρ₁ ⊔ₑ ρ₂
join-⊆-right {ρ₁}{ρ₂} = λ x d z → inj₂ z

⟦⟧-continuous-⊆ : ∀{M : Term}{ρ}{E}{NE-ρ : nonempty-env ρ}
  → mem E ⊆ ⟦ M ⟧ ρ
  → Σ[ ρ′ ∈ Env ] fin-env ρ′  ×  ρ′ ⊆ₑ ρ  ×  mem E ⊆ ⟦ M ⟧ ρ′

{- The Main Lemma -}
⟦⟧-continuous-env : ∀{M : Term}{ρ}{v}{NE-ρ : nonempty-env ρ}
  → v ∈ ⟦ M ⟧ ρ
  → Σ[ ρ′ ∈ Env ] fin-env ρ′  ×  ρ′ ⊆ₑ ρ  ×  v ∈ ⟦ M ⟧ ρ′
⟦⟧-continuous-env {` x}{ρ}{v}{NE-ρ} v∈⟦x⟧ρ =
   ⟨ (single-env x ⌈ v ⌉ ρ NE-ρ) , ⟨ single-fin {v}{x} , ⟨ single-⊆ v∈⟦x⟧ρ ,
     v∈single[xv]x {v}{x} ⟩ ⟩ ⟩
⟦⟧-continuous-env {L · M}{ρ}{w}{NE-ρ} ⟨ V , ⟨ V↦w∈⟦L⟧ρ , ⟨ V⊆⟦M⟧ρ , V≢[] ⟩ ⟩ ⟩
    with ⟦⟧-continuous-env{L}{ρ}{V ↦ w}{NE-ρ} V↦w∈⟦L⟧ρ
... | ⟨ ρ₁ , ⟨ fρ₁ , ⟨ ρ₁⊆ρ , V↦w∈⟦L⟧ρ₁ ⟩ ⟩ ⟩ = G
    where
    G : Σ[ ρ′ ∈ Env ] fin-env ρ′  ×  ρ′ ⊆ₑ ρ  ×  w ∈ ⟦ L · M ⟧ ρ′
    G   with ⟦⟧-continuous-⊆{M}{ρ = ρ}{NE-ρ = NE-ρ} V⊆⟦M⟧ρ
    ... | ⟨ ρ₂ , ⟨ fρ₂ , ⟨ ρ₂⊆ρ , V⊆⟦M⟧ρ₂ ⟩ ⟩ ⟩ =
          ⟨ ρ₃ , ⟨ join-fin-env fρ₁ fρ₂ , ⟨ join-lub ρ₁⊆ρ ρ₂⊆ρ ,
            w∈⟦L·M⟧ρ₃ ⟩ ⟩ ⟩
        where
        ρ₃ = ρ₁ ⊔ₑ ρ₂
        ρ₁⊆ρ₃ = λ x v z → inj₁ z
        V↦w∈⟦L⟧ρ₃ : V ↦ w ∈ ⟦ L ⟧ ρ₃
        V↦w∈⟦L⟧ρ₃ = ⟦⟧-monotone{L}{ρ₁}{ρ₃} ρ₁⊆ρ₃ (V ↦ w) V↦w∈⟦L⟧ρ₁
        ρ₂⊆ρ₄ = λ x v z → inj₂ z
        V⊆⟦M⟧ρ₃ : mem V ⊆ ⟦ M ⟧ ρ₃
        V⊆⟦M⟧ρ₃ v v∈V = ⟦⟧-monotone{M}{ρ₂}{ρ₃} ρ₂⊆ρ₄ v (V⊆⟦M⟧ρ₂ v v∈V)
        w∈⟦L·M⟧ρ₃ : w ∈ ⟦ L · M ⟧ ρ₃
        w∈⟦L·M⟧ρ₃ = ⟨ V , ⟨ V↦w∈⟦L⟧ρ₃ , ⟨ V⊆⟦M⟧ρ₃ , V≢[] ⟩ ⟩ ⟩
⟦⟧-continuous-env {ƛ N}{ρ}{V ↦ w}{NE-ρ} ⟨ w∈⟦N⟧V•ρ , V≢[] ⟩
    with ⟦⟧-continuous-env{N}{mem V • ρ}{w}
             {extend-nonempty-env NE-ρ (E≢[]⇒nonempty-mem V≢[])} w∈⟦N⟧V•ρ
... | ⟨ ρ′ , ⟨ fρ′ , ⟨ ρ′⊆V•ρ , w∈⟦N⟧V•ρ′ ⟩ ⟩ ⟩ =    
    ⟨ (λ x → ρ′ (suc x)) , ⟨ (λ x → fρ′ (suc x)) , ⟨ (λ x → ρ′⊆V•ρ (suc x)) ,
    ⟨ ⟦⟧-monotone{N}{ρ′}{mem V • (λ z → ρ′ (suc z))} G w w∈⟦N⟧V•ρ′ , V≢[] ⟩ ⟩ ⟩ ⟩
    where G : (x : Var) → ρ′ x ≲ (mem V • (λ x₁ → ρ′ (suc x₁))) x
          G zero v v∈ρ′x = ρ′⊆V•ρ 0 v v∈ρ′x
          G (suc x) v v∈ρ′x = v∈ρ′x
⟦⟧-continuous-env {ƛ N}{ρ}{ν}{NE-ρ} _ =
    ⟨ initial-fin-env ρ NE-ρ , ⟨ initial-fin ρ NE-ρ , ⟨ initial-fin-⊆ ρ NE-ρ ,
      tt ⟩ ⟩ ⟩
⟦⟧-continuous-env {$ P k}{ρ}{v}{NE-ρ} v∈⟦M⟧ρ =
  ⟨ initial-fin-env ρ NE-ρ , ⟨ initial-fin ρ NE-ρ , ⟨ initial-fin-⊆ ρ NE-ρ ,
    v∈⟦M⟧ρ ⟩ ⟩ ⟩

⟦⟧-continuous-⊆ {M}{ρ}{[]}{NE-ρ} []⊆⟦M⟧ρ =
  ⟨ initial-fin-env ρ NE-ρ , ⟨ initial-fin ρ NE-ρ , ⟨ initial-fin-⊆ ρ NE-ρ ,
    (λ d ()) ⟩ ⟩ ⟩
⟦⟧-continuous-⊆ {M}{ρ}{v ∷ E}{NE-ρ} v∷E⊆⟦M⟧ρ
    with ⟦⟧-continuous-⊆ {M}{ρ}{E}{NE-ρ} λ d z → v∷E⊆⟦M⟧ρ d (mem-there z)
... | ⟨ ρ₁ , ⟨ fρ₁ , ⟨ ρ₁⊆ρ , E⊆⟦M⟧ρ₁ ⟩ ⟩ ⟩
    with ⟦⟧-continuous-env {M}{ρ}{v}{NE-ρ} (v∷E⊆⟦M⟧ρ v mem-here)
... | ⟨ ρ₂ , ⟨ fρ₂ , ⟨ ρ₂⊆ρ , v∈⟦M⟧ρ₂ ⟩ ⟩ ⟩ =
    ⟨ ρ₃ , ⟨ (join-fin-env fρ₁ fρ₂) , ⟨ (join-lub ρ₁⊆ρ ρ₂⊆ρ) ,
    G ⟩ ⟩ ⟩
    where
    ρ₃ = ρ₁ ⊔ₑ ρ₂
    G : (d : Value) → mem (v ∷ E) d → d ∈ ⟦ M ⟧ ρ₃
    G d mem-here = ⟦⟧-monotone {M}{ρ₂}{ρ₃} join-⊆-right v v∈⟦M⟧ρ₂
    G d (mem-there m) = ⟦⟧-monotone {M}{ρ₁}{ρ₃} join-⊆-left d (E⊆⟦M⟧ρ₁ d m)

⟦⟧-continuous : ∀{N : Term}{ρ}{NE-ρ : nonempty-env ρ}
  → continuous (λ D → ⟦ N ⟧ (D • ρ))
⟦⟧-continuous {N}{ρ}{NE-ρ} X E E⊆⟦N⟧X•ρ NE-X
    with ⟦⟧-continuous-⊆ {N}{X • ρ}{E}{extend-nonempty-env NE-ρ NE-X} E⊆⟦N⟧X•ρ
... | ⟨ ρ′ , ⟨ fρ′ , ⟨ ρ′⊆X•ρ , E⊆⟦N⟧ρ′ ⟩ ⟩ ⟩
    with fρ′ 0
... | ⟨ D , ⟨ ρ′x=D , NE-D ⟩ ⟩ =
    ⟨ D , ⟨ (λ v v∈D → ρ′⊆X•ρ 0 v ((from ρ′x=D) v v∈D)) ,
    ⟨ (λ d d∈E → ⟦⟧-monotone {N}{ρ′}{mem D • ρ} G d (E⊆⟦N⟧ρ′ d d∈E)) , NE-D ⟩ ⟩ ⟩
    where
    G : (x : Var) → ρ′ x ≲ (mem D • ρ) x
    G zero d d∈ρ0 = (to ρ′x=D) d d∈ρ0 
    G (suc x) d m = ρ′⊆X•ρ (suc x) d m

ISWIM-Λ-▪-id : ∀ {N : Term}{ρ}{NE-ρ : nonempty-env ρ}{X : 𝒫 Value}
  → nonempty X
  → (Λ λ X → ⟦ N ⟧ (X • ρ)) ▪ X ≃ ⟦ N ⟧ (X • ρ)
ISWIM-Λ-▪-id {N}{ρ}{NE-ρ}{X} NE-X =
    Λ-▪-id {λ D → ⟦ N ⟧ (D • ρ)} (⟦⟧-continuous{N}{ρ}{NE-ρ}) (⟦⟧-monotone-one{N})
        NE-X

{- Primitive Abstraction followed by Application is the identity ---------------}

℘-▪-≃ : ∀{B}{P}{f}{k}  →  (℘ (B ⇒ P) f) ▪ (℘ (base B) k) ≃ ℘ P (f k)
℘-▪-≃ {B}{P}{f}{k} = equal fwd back
  where
  fwd : ℘ (B ⇒ P) f ▪ ℘ (base B) k ≲ ℘ P (f k)
  fwd w ⟨ V , ⟨ ⟨ k′ , ⟨ refl , w∈fk′ ⟩ ⟩ , ⟨ k′∈pk , _ ⟩ ⟩ ⟩
      with k′∈pk (const k′) mem-here
  ... | pkk′ rewrite k′∈℘k⇒k′≡k pkk′ = w∈fk′
  back : ℘ P (f k) ≲ ℘ (B ⇒ P) f ▪ ℘ (base B) k
  back w w∈fk = ⟨ (const k ∷ []) , ⟨ ⟨ k , ⟨ refl , w∈fk ⟩ ⟩ ,
                ⟨ (λ {d mem-here → k∈℘k}) , (λ ()) ⟩ ⟩ ⟩


{- Reduction semantics of ISWIM ------------------------------------------------}

infix 2 _—→_
data _—→_ : Term → Term → Set where
  ξ₁-rule : ∀  {L L′ M : Term}
    → L —→ L′
      ----------------
    → L · M —→ L′ · M
  ξ₂-rule : ∀  {L M M′ : Term}
    → TermValue L  →  M —→ M′
      -----------------------
    → L · M —→ L · M′
  β-rule : ∀  {N M : Term}
    → TermValue M
      --------------------
    → (ƛ N) · M —→ N [ M ]
  δ-rule : ∀ {B}{P} {f : base-rep B → rep P} {k}
      ---------------------------------------------
    → ($ (B ⇒ P) f) · ($ (base B) k)  —→  $ P (f k)


{- Soundness of Reduction with respect to Denotations --------------------------}

⟦⟧—→ : ∀{M N : Term}{ρ : Var → 𝒫 Value} {NE-ρ : nonempty-env ρ}
   → M —→ N
   → ⟦ M ⟧ ρ ≃ ⟦ N ⟧ ρ
⟦⟧—→ {L · M} {L′ · M} {ρ}{NE-ρ} (ξ₁-rule L—→L′) =
    let IH = ⟦⟧—→{ρ = ρ}{NE-ρ} L—→L′ in
    ⟦ L · M ⟧ ρ              ≃⟨ ≃-refl ⟩
    (⟦ L ⟧ ρ) ▪ (⟦ M ⟧ ρ)    ≃⟨ ▪-cong IH ≃-refl ⟩
    (⟦ L′ ⟧ ρ) ▪ (⟦ M ⟧ ρ)   ≃⟨ ≃-refl ⟩
    ⟦ L′ · M ⟧ ρ             ∎ where open ≃-Reasoning  
⟦⟧—→ {V · M} {.(_ · _)} {ρ}{NE-ρ} (ξ₂-rule {M′ = M′} v M—→M′) =
    let IH = ⟦⟧—→{ρ = ρ}{NE-ρ} M—→M′ in
    ⟦ V · M ⟧ ρ              ≃⟨ ≃-refl ⟩
    (⟦ V ⟧ ρ) ▪ (⟦ M ⟧ ρ)    ≃⟨ ▪-cong (≃-refl{D = ⟦ V ⟧ ρ}) IH ⟩
    (⟦ V ⟧ ρ) ▪ (⟦ M′ ⟧ ρ)   ≃⟨ ≃-refl ⟩
    ⟦ V · M′ ⟧ ρ             ∎ where open ≃-Reasoning  
⟦⟧—→ {ƛ N · V} {_} {ρ} {NE-ρ} (β-rule v) =
    ⟦ ƛ N · V ⟧ ρ                         ≃⟨ ≃-refl ⟩
    (Λ (λ D → ⟦ N ⟧ (D • ρ))) ▪ (⟦ V ⟧ ρ) ≃⟨ ISWIM-Λ-▪-id {N}{ρ}{NE-ρ}
                                                   (value-nonempty NE-ρ v) ⟩
    ⟦ N ⟧ (⟦ V ⟧ ρ • ρ)             ≃⟨ ≃-reflexive (sym (⟦⟧-subst {N} {V} {ρ})) ⟩
    ⟦ N [ V ] ⟧ ρ                   ∎ where open ≃-Reasoning
⟦⟧—→ {($ (B ⇒ P) f · $ (base B) k)} {_} {ρ} δ-rule =
    ⟦ $ (B ⇒ P) f · $ (base B) k ⟧ ρ        ≃⟨ ≃-refl ⟩
    (℘ (B ⇒ P) f) ▪ (℘ (base B) k)         ≃⟨ ℘-▪-≃ {B}{P} ⟩
    ⟦ $ P (f k) ⟧ ρ                         ∎ where open ≃-Reasoning

open import MultiStep Op sig _—→_ public

soundness : ∀ {M N : Term} {ρ : Env}{NE-ρ : nonempty-env ρ}
  → M —↠ ƛ N
    -------------------
  → ⟦ M ⟧ ρ ≃ ⟦ ƛ N ⟧ ρ
soundness {M}{_}{ρ} (M □) = ⟦ M ⟧ ρ ≃⟨ ≃-refl ⟩ ⟦ M ⟧ ρ ∎ where open ≃-Reasoning
soundness {M}{N}{ρ}{NE-ρ} (_—→⟨_⟩_ M {M = M′} M—→M′ M′—↠N) =
    ⟦ M ⟧ ρ      ≃⟨ ⟦⟧—→{ρ = ρ}{NE-ρ} M—→M′ ⟩ 
    ⟦ M′ ⟧ ρ     ≃⟨ soundness{ρ = ρ}{NE-ρ} M′—↠N ⟩ 
    ⟦ ƛ N ⟧ ρ    ∎ where open ≃-Reasoning

{- Adequacy of Denotations -----------------------------------------------------}

open import EvalISWIM

𝕍 : Value → Val → Set
𝕍s : List Value → Val → Set

𝕍 (const {B} k) (val-const {P} p) = ℘ P p (const {B} k)
𝕍 (const {B} k) (val-clos N γ) = False
𝕍 (const {B} k) bogus = False
𝕍 (V ↦ w) (val-const {P} f) = ℘ P f (V ↦ w)
𝕍 (V ↦ w) (val-clos N γ) =
    (∀{c : Val} → 𝕍s V c → Σ[ c' ∈ Val ] (γ ,' c) ⊢ N ⇓ c'  ×  𝕍 w c')
𝕍 (V ↦ w) bogus = False
𝕍 ν (val-const {base B} k) = False
𝕍 ν (val-const {B ⇒ P} f) = True
𝕍 ν (val-clos N γ) = True
𝕍 ν bogus = False

𝕍s [] c = True
𝕍s (v ∷ V) c = 𝕍 v c × 𝕍s V c

𝕍kc⇒c≡k : ∀{B}{k}{c}
  → 𝕍 (const {B} k) c
  → c ≡ val-const {base B} k
𝕍kc⇒c≡k {B} {k} {val-const {P} k′} 𝕍kc
    with k′∈℘k⇒P≡B {P}{B} 𝕍kc
... | refl
    with k′∈℘k⇒k′≡k 𝕍kc
... | refl = refl

℘⇒𝕍 : ∀{P}{k}{w}
   → ℘ P k w
   → 𝕍 w (val-const {P} k)
℘⇒𝕍 {P} {k} {const x} w∈k = w∈k
℘⇒𝕍 {P} {k} {x ↦ w} w∈k = w∈k
℘⇒𝕍 {B ⇒ P} {k} {ν} w∈k = tt

V⊆𝕍c⇒𝕍sV : ∀{V}{c} → (∀ u → mem V u → 𝕍 u c) → 𝕍s V c
V⊆𝕍c⇒𝕍sV {[]} V⊆𝕍c = tt
V⊆𝕍c⇒𝕍sV {v ∷ V} V⊆𝕍c =
    ⟨ V⊆𝕍c v mem-here , V⊆𝕍c⇒𝕍sV (λ u z → V⊆𝕍c u (mem-there z)) ⟩

𝕍sV⇒V⊆𝕍c : ∀{V}{c} → 𝕍s V c → (∀ u → mem V u → 𝕍 u c)
𝕍sV⇒V⊆𝕍c {[]} {c} vs u ()
𝕍sV⇒V⊆𝕍c {x ∷ V} {c} ⟨ 𝕍c , 𝕍sc ⟩ .x mem-here = 𝕍c
𝕍sV⇒V⊆𝕍c {x ∷ V} {c} ⟨ 𝕍c , 𝕍sc ⟩ u (mem-there u∈V) = 𝕍sV⇒V⊆𝕍c 𝕍sc u u∈V

data 𝔾 : Env → ValEnv → Set₁ where
  𝔾-∅ : 𝔾 (λ x → ∅) ∅'
  𝔾-ext : ∀{γ : Env}{γ' : ValEnv}{D c} → 𝔾 γ γ' → (∀ v → v ∈ D → 𝕍 v c)
     → 𝔾 (D • γ) (γ' ,' c)

𝔾→𝕍 : ∀ {ρ : Env}{γ : ValEnv}{x}{lt : x < length γ}{v}
   → 𝔾 ρ γ  →  v ∈ ρ x  →  𝕍 v (nth γ x)
𝔾→𝕍 {.(_ • _)} {.(_ ∷ _)} {zero} {s≤s lt} {v} (𝔾-ext 𝔾ργ D⊆V) v∈D = D⊆V v v∈D
𝔾→𝕍 {.(_ • _)} {.(_ ∷ _)} {suc x} {s≤s lt} {v} (𝔾-ext 𝔾ργ D⊆V) v∈ρx =
  𝔾→𝕍{lt = lt} 𝔾ργ v∈ρx

¬𝕍[bogus] : ∀ v → ¬ 𝕍 v bogus
¬𝕍[bogus] (const k) x = x
¬𝕍[bogus] (V ↦ w) x = x

℘pv→𝕍vp : ∀ {P}{p}{v} →  ℘ P p v  →  𝕍 v (val-const {P} p)
℘pv→𝕍vp {v = const k} ℘pv = ℘pv
℘pv→𝕍vp {v = V ↦ w} ℘pv = ℘pv
℘pv→𝕍vp {B ⇒ P} {p} {ν} ℘pv = tt

⟦⟧⇒⇓ : ∀{M : Term}{γ}{wfM : WF (length γ) M}{ρ}{v}
   → 𝔾 ρ γ  →  v ∈ ⟦ M ⟧ ρ
   → Σ[ c ∈ Val ] γ ⊢ M ⇓ c  ×  (∀ u → u ∈ ⟦ M ⟧ ρ → 𝕍 u c)
⟦⟧⇒⇓ {` x}{γ}{WF-var ∋x lt}{ρ}{v} 𝔾ργ v∈⟦M⟧ρ =
    let lt' = subst (λ □ → x < □) (ISWIM.ASTMod.len-mk-list (length γ)) lt in
   ⟨ nth γ x , ⟨ ⇓-var , (λ v v∈ρx → 𝔾→𝕍{lt = lt'} 𝔾ργ v∈ρx) ⟩ ⟩
⟦⟧⇒⇓ {L · M}{γ}{WF-op (WF-cons (WF-ast wfL) (WF-cons (WF-ast wfM) WF-nil)) _}{ρ}
    {w} 𝔾ργ w∈LMρ = G
    where
    Part1 : ∀{L}{M}{ρ}{w}{wfL}{wfM}
      → 𝔾 ρ γ  →  w ∈ ⟦ L · M ⟧ ρ
      → Σ[ c ∈ Val ] γ ⊢ L · M ⇓ c × 𝕍 w c
    Part2 : ∀{c₁ c₂}{L M}{γ}{V w}
       → γ ⊢ L ⇓ c₁  →  𝕍 (V ↦ w) c₁
       → γ ⊢ M ⇓ c₂  →  𝕍s V c₂
       → Σ[ c ∈ Val ] γ ⊢ L · M ⇓ c × 𝕍 w c
       
    Part1 {L}{M}{ρ}{w}{wfL}{wfM} 𝔾ργ ⟨ V , ⟨ V↦w∈⟦L⟧ρ , ⟨ V⊆⟦M⟧ρ , V≢[] ⟩ ⟩ ⟩ 
        with V
    ... | [] = ⊥-elim (V≢[] refl)    
    ... | v ∷ V′
        with ⟦⟧⇒⇓ {L}{γ}{wfL}{ρ}{(v ∷ V′) ↦ w} 𝔾ργ V↦w∈⟦L⟧ρ
    ... | ⟨ c₁ , ⟨ L⇓c₁ , ⟦L⟧⊆𝕍c₁ ⟩ ⟩ 
        with ⟦⟧⇒⇓ {M}{γ}{wfM}{ρ}{v} 𝔾ργ (V⊆⟦M⟧ρ v mem-here)
    ... | ⟨ c₂ , ⟨ M⇓c₂ , ⟦M⟧⊆𝕍c₂ ⟩ ⟩ =
        Part2 L⇓c₁ 𝕍Vwc₁ M⇓c₂ 𝕍sc₂
        where
        𝕍Vwc₁ : 𝕍 ((v ∷ V′) ↦ w) c₁
        𝕍Vwc₁ = ⟦L⟧⊆𝕍c₁ ((v ∷ V′) ↦ w) V↦w∈⟦L⟧ρ
        𝕍sc₂ : 𝕍s (v ∷ V′) c₂
        𝕍sc₂ = ⟨ (⟦M⟧⊆𝕍c₂ v (V⊆⟦M⟧ρ v mem-here)) ,
                 (V⊆𝕍c⇒𝕍sV (λ u u∈V′ → ⟦M⟧⊆𝕍c₂ u (V⊆⟦M⟧ρ u (mem-there u∈V′)) )) ⟩
        
    Part2 {val-const {B ⇒ P} f}{c₂}{L}{M}{γ}{V}{w}
        L⇓c₁ ⟨ k , ⟨ refl , w∈fk ⟩ ⟩ M⇓ ⟨ 𝕍kc₂ , _ ⟩ 
           rewrite 𝕍kc⇒c≡k {B}{k}{c₂} 𝕍kc₂ =
       ⟨ (val-const {P} (f k)) , ⟨ (⇓-prim L⇓c₁ M⇓) , ℘⇒𝕍 {P} w∈fk ⟩ ⟩
    Part2 {val-clos N γ′{wfN}}{c₂}{L}{M}{γ}{V}{w} L⇓c₁ 𝕍Vwc₁ M⇓ 𝕍sVc₂
       with 𝕍Vwc₁ {c₂} 𝕍sVc₂
    ... | ⟨ c₃ , ⟨ N⇓c₃ , 𝕍wc₃ ⟩ ⟩ =
        ⟨ c₃ , ⟨ (⇓-app{wf = ISWIM.ASTMod.WF-rel N wfN} L⇓c₁ M⇓ N⇓c₃) , 𝕍wc₃ ⟩ ⟩
          
    G : Σ[ c ∈ Val ] γ ⊢ L · M ⇓ c  ×  (∀ u → u ∈ ⟦ L · M ⟧ ρ → 𝕍 u c)
    G   with Part1{L}{M}{wfL = wfL}{wfM} 𝔾ργ w∈LMρ
    ... | ⟨ c , ⟨ LM⇓c , 𝕍wc ⟩ ⟩ = ⟨ c , ⟨ LM⇓c , H ⟩ ⟩
        where
        H : ∀ u → u ∈ ⟦ L · M ⟧ ρ → 𝕍 u c
        H u u∈LM
            with Part1{L}{M}{wfL = wfL}{wfM} 𝔾ργ u∈LM
        ... | ⟨ c′ , ⟨ LM⇓c′ , 𝕍wc′ ⟩ ⟩ rewrite ⇓-determ LM⇓c′ LM⇓c = 𝕍wc′
⟦⟧⇒⇓ {ƛ N}{γ}{WF-op (WF-cons (WF-bind (WF-ast wfN)) WF-nil) _}{ρ}{v}
    𝔾ργ v∈⟦M⟧ρ =
    ⟨ (val-clos N γ {wfN}) , ⟨ ⇓-lam {wf = wfN} , G ⟩ ⟩
    where
    G : (u : Value) → u ∈ ⟦ ƛ N ⟧ ρ → 𝕍 u (val-clos N γ {wfN})
    G ν u∈ƛN = tt
    G (V ↦ w) ⟨ w∈⟦N⟧[V•ρ] , V≠[] ⟩ {c} 𝕍sVc
        with ⟦⟧⇒⇓ {N}{c ∷ γ}{wfN}{mem V • ρ}{w}
                   (𝔾-ext{c = c} 𝔾ργ (𝕍sV⇒V⊆𝕍c 𝕍sVc)) w∈⟦N⟧[V•ρ]
    ... | ⟨ c′ , ⟨ N⇓c′ , ⟦N⟧⊆𝕍c′ ⟩ ⟩ =
          ⟨ c′ , ⟨ N⇓c′ , ⟦N⟧⊆𝕍c′ w w∈⟦N⟧[V•ρ] ⟩ ⟩
⟦⟧⇒⇓ {$ P k}{γ}{wfPk}{ρ}{v} 𝔾ργ v∈⟦M⟧ρ =
    ⟨ val-const {P} k , ⟨ ⇓-lit , (λ u ℘pu → ℘pv→𝕍vp {P} ℘pu) ⟩ ⟩


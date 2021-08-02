{-

Yet Another Formulation of Denotational Values

-}

open import Primitives

open import Utilities using (extensionality)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; sym; cong; cong₂; cong-app)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.List using (List ; _∷_ ; []; _++_) 
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Empty using (⊥-elim) renaming (⊥ to False)
open import Data.Unit using (tt) renaming (⊤ to True)

module ValueTable where

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

_⊆_ : ∀{T : Set} → 𝒫 T → 𝒫 T → Set
D ⊆ E = ∀ d → d ∈ D → d ∈ E

{- List utilities -}

data mem : ∀{T : Set} → List T → T → Set where
  mem-here : ∀{T}{x : T}{ls} → mem (x ∷ ls) x
  mem-there : ∀{T}{x y : T}{ls} → mem ls x → mem (y ∷ ls) x

{- Values -}

data Value : Set

Table : Set
Table = List (Value × Value)

data Value where
  const : {b : Base} → base-rep b → Value
  fun : Table → Value

infixr 10 _↦_
_↦_ : Value → Value → Value × Value
v ↦ w = ⟨ v , w ⟩

infix 4 _⊑_
data _⊑_ : Value → Value → Set where
  ⊑-const : ∀ {B}{k} → const {B} k ⊑ const {B} k
  ⊑-fun : ∀{t₁ t₂ : Table} → mem t₁ ⊆ mem t₂ → fun t₁ ⊑ fun t₂

⊑-refl : ∀{v} → v ⊑ v
⊑-refl {const k} = ⊑-const
⊑-refl {fun t} = ⊑-fun (λ d z → z)

{- Abstraction and Application -}

Λ : (𝒫 Value → 𝒫 Value) → 𝒫 Value
Λ f (const k) = False
Λ f (fun t) = ∀ v w → ⟨ v , w ⟩ ∈ mem t → w ∈ f ⌈ v ⌉

infix 10 _▪_
_▪_ : 𝒫 Value → 𝒫 Value → 𝒫 Value
D₁ ▪ D₂ = λ w → Σ[ t ∈ Table ] (fun t ∈ D₁)
                × Σ[ v ∈ Value ] v ↦ w ∈ mem t × (v ∈ D₂)

℘ : ∀{P : Prim} → rep P → 𝒫 Value
℘ {base B} k (const {B′} k′)
    with base-eq? B B′
... | yes refl = k ≡ k′
... | no neq = False
℘ {base B} k (fun t) = False
℘ {B ⇒ P} f (const k) = False
℘ {B ⇒ P} f (fun t) =
  ∀ v w → ⟨ v , w ⟩ ∈ mem t
        → Σ[ k ∈ base-rep B ] v ≡ const {B} k × w ∈ ℘ {P} (f k)

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
data _≃_ : 𝒫 Value → 𝒫 Value → Set₁ where
  equal : ∀{D₁ D₂} → D₁ ≲ D₂  →  D₂ ≲ D₁  → D₁ ≃ D₂

to : ∀{D₁ D₂} → D₁ ≃ D₂ → D₁ ≲ D₂
to (equal a b) = a

from : ∀{D₁ D₂} → D₁ ≃ D₂ → D₂ ≲ D₁
from (equal a b) = b

≃-refl : {D : 𝒫 Value} → D ≃ D
≃-refl {D} = equal ≲-refl ≲-refl

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
▪-cong-≲ D11 D22 w ⟨ t , ⟨ t∈D1 , ⟨ v , ⟨ vw∈t , v∈D2 ⟩ ⟩ ⟩ ⟩ =
  ⟨ t , ⟨ D11 (fun t) t∈D1 , ⟨ v , ⟨ vw∈t , D22 v v∈D2 ⟩ ⟩ ⟩ ⟩

▪-cong : ∀{D₁ D₂ D₁′ D₂′ : 𝒫 Value}
  → D₁ ≃ D₁′  →  D₂ ≃ D₂′
  → D₁ ▪ D₂ ≃ D₁′ ▪ D₂′
▪-cong (equal x x₁) (equal x₂ x₃) = equal (▪-cong-≲ x x₂) (▪-cong-≲ x₁ x₃)

{- 

Regarding the definition of continuous, do we need the other direction
too?  Or should we use the neighborhood version?

-}

continuous : (F : 𝒫 Value → 𝒫 Value) → Set₁
continuous F = ∀ X e → e ∈ F X
    → Σ[ D ∈ List Value ] D ≢ []  ×  mem D ≲ X  ×  e ∈ F (mem D)

_⊏_ : 𝒫 Value → 𝒫 Value → Set
E ⊏ D = ∀ e → e ∈ D → Σ[ d ∈ Value ] d ∈ D × e ⊑ d

join-closed : (D : 𝒫 Value) → Set
join-closed D = ∀ V → V ≢ [] →  mem V ≲ D → Σ[ v ∈ Value ] v ∈ D × mem V ⊏ ⌈ v ⌉

monotone-⊏ : (F : 𝒫 Value → 𝒫 Value) → Set₁
monotone-⊏ F = ∀ D₁ D₂ → D₁ ⊏ D₂ → F D₁ ≲ F D₂

cont-join-monotone-⊏ : ∀ {F : 𝒫 Value → 𝒫 Value} {D : 𝒫 Value}
  → continuous F → monotone-⊏ F → join-closed D
  → ∀ w → w ∈ F D → Σ[ v ∈ Value ] w ∈ F ⌈ v ⌉ × v ∈ D  
cont-join-monotone-⊏ {F}{D} Fcont Fmono Djoin w w∈FD 
    with Fcont D w w∈FD
... | ⟨ E , ⟨ E≢[] , ⟨ E<D , w∈FE ⟩ ⟩ ⟩
    with Djoin E E≢[] E<D
... | ⟨ v , ⟨ v∈D , E⊏v ⟩ ⟩ =
    let w∈Fv = Fmono (mem E) ⌈ v ⌉ E⊏v w w∈FE in
    ⟨ v , ⟨ w∈Fv , v∈D ⟩ ⟩

≲-Λ-▪ : ∀ {F : 𝒫 Value → 𝒫 Value}{D : 𝒫 Value}
  → continuous F → monotone-⊏ F → join-closed D
  → F D ≲ (Λ F) ▪ D
≲-Λ-▪ Fcont Fmono Djoin w w∈FD
    with cont-join-monotone-⊏ Fcont Fmono Djoin w w∈FD
... | ⟨ v , ⟨ w∈Fv , v∈D ⟩ ⟩ =
      ⟨ (⟨ v , w ⟩ ∷ []) ,
      ⟨ (λ { v₁ w₁ mem-here → w∈Fv}) ,
      ⟨ v ,
      ⟨ mem-here , v∈D ⟩ ⟩ ⟩ ⟩

Λ-▪-≲ : ∀ {F : 𝒫 Value → 𝒫 Value}{D : 𝒫 Value}
  → monotone-⊏ F
  → (Λ F) ▪ D ≲ F D
Λ-▪-≲ {F} {D} Fmono w ⟨ t , ⟨ t∈ΛF , ⟨ v , ⟨ v↦w∈t , v∈D ⟩ ⟩ ⟩ ⟩ =
  let w∈Fv = t∈ΛF v w v↦w∈t in
  Fmono ⌈ v ⌉ D (λ { v₁ v₁∈D → ⟨ v₁ , ⟨ v₁∈D , ⊑-refl ⟩ ⟩ }) w w∈Fv

Λ-▪ : ∀ {F : 𝒫 Value → 𝒫 Value}{D : 𝒫 Value}
  → continuous F → monotone-⊏ F → join-closed D
  → (Λ F) ▪ D ≃ F D
Λ-▪ {F}{D} Fcont Fmono Djoin =
  equal (Λ-▪-≲ Fmono) (≲-Λ-▪ Fcont Fmono Djoin)


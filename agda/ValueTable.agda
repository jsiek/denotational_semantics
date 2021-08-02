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

data Value : Set

Table : Set
Table = List (Value × Value)

data Value where
  const : {b : Base} → base-rep b → Value
  fun : Table → Value

infix 3 _↦_∈_
data _↦_∈_ : Value → Value → Table → Set where
  here : ∀ {v w t} → v ↦ w ∈ (⟨ v , w ⟩ ∷ t)
  there : ∀ {v v′ w w′ t} →  v ↦ w ∈ t  →  v ↦ w ∈ (⟨ v′ , w′ ⟩ ∷ t)

𝒫 : Set → Set₁
𝒫 V = V → Set

⌈_⌉ : Value → 𝒫 Value
⌈ v ⌉ w = w ≡ v

_∈_ : Value → 𝒫 Value → Set
v ∈ D = D v

∅ : 𝒫 Value
∅ = λ v → False 

Λᵗ : (𝒫 Value → 𝒫 Value) → Table → Set
Λᵗ f [] = True
Λᵗ f (⟨ v , w ⟩ ∷ t) = w ∈ f ⌈ v ⌉ × Λᵗ f t

Λ : (𝒫 Value → 𝒫 Value) → 𝒫 Value
Λ f (const k) = False
Λ f (fun t) = Λᵗ f t

infix 10 _▪_
_▪_ : 𝒫 Value → 𝒫 Value → 𝒫 Value
D₁ ▪ D₂ = λ w → Σ[ t ∈ Table ] (fun t ∈ D₁)
                × Σ[ v ∈ Value ] (v ↦ w ∈ t) × (v ∈ D₂)

℘ : ∀{P : Prim} → rep P → 𝒫 Value

𝕋 : ∀ {B P} (f : base-rep B → rep P) (t : Table) → Set
𝕋 f [] = True
𝕋 {B}{P} f (⟨ const {B′} k , w ⟩ ∷ t)
    with base-eq? B B′
... | yes refl = w ∈ ℘ {P} (f k)
... | no neq = False
𝕋 f (⟨ fun t′ , w ⟩ ∷ t) = False

℘ {base B} k (const {B′} k′)
    with base-eq? B B′
... | yes refl = k ≡ k′
... | no neq = False
℘ {base B} k (fun t) = False
℘ {B ⇒ P} f (const k) = False
℘ {B ⇒ P} f (fun t) = 𝕋 {B}{P} f t

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

monotone : (F : 𝒫 Value → 𝒫 Value) → Set₁
monotone F = ∀ D₁ D₂ → D₁ ≲ D₂ → F D₁ ≲ F D₂

Λᵗ-↦-∈ : ∀{t v w F D}
   → v ↦ w ∈ t  →  Λᵗ F t
   → v ∈ D  →  monotone F
   → F D w
Λᵗ-↦-∈ {.(⟨ _ , _ ⟩ ∷ _)}{v}{w}{F}{D} here ⟨ w∈Fv , _ ⟩ v∈D F-mono =
  F-mono ⌈ v ⌉ D (λ { v refl → v∈D }) w w∈Fv
Λᵗ-↦-∈ {.(⟨ _ , _ ⟩ ∷ _)}{D = D} (there vw∈t) ⟨ _ , ΛFt ⟩ v∈D F-mono =
  Λᵗ-↦-∈{D = D} vw∈t ΛFt v∈D F-mono

Λ-▪-≲ : ∀ {F : 𝒫 Value → 𝒫 Value}{D : 𝒫 Value}
  → monotone F
  → (Λ F) ▪ D ≲ F D
Λ-▪-≲ {F} {D} Fmono w ⟨ t , ⟨ t∈ΛF , ⟨ v , ⟨ v↦w∈t , v∈D ⟩ ⟩ ⟩ ⟩ =
  Λᵗ-↦-∈ {D = D} v↦w∈t t∈ΛF v∈D Fmono

{- UNDER CONSTRUCTION

continuous : (F : 𝒫 Value → 𝒫 Value) → Set
continuous = ∀ X → e ∈ F X → Σ[ D ∈ List Value ] (mem D) ⊆ X × e ∈ F (mem D)

-}

{- aka continuous? -}
finite : (F : 𝒫 Value → 𝒫 Value) → (D : 𝒫 Value) → Set
finite F D = ∀ w → w ∈ F D → Σ[ v ∈ Value ] w ∈ F ⌈ v ⌉ × v ∈ D

≲-Λ-▪ : ∀ {F : 𝒫 Value → 𝒫 Value}{D : 𝒫 Value}
  → finite F D
  → F D ≲ (Λ F) ▪ D
≲-Λ-▪ {F} {D} Ffin w w∈FD
    with Ffin w w∈FD
... | ⟨ v , ⟨ w∈Fv , v∈D ⟩ ⟩ =    
  ⟨ ⟨ v , w ⟩ ∷ [] , ⟨ ⟨ w∈Fv , tt ⟩ , ⟨ v , ⟨ here , v∈D ⟩ ⟩ ⟩ ⟩

Λ-▪ : ∀ {F : 𝒫 Value → 𝒫 Value}{D : 𝒫 Value}
  → monotone F → finite F D
  → (Λ F) ▪ D ≃ F D
Λ-▪ {F}{D} Fmono Ffin = equal (Λ-▪-≲ Fmono) (≲-Λ-▪ Ffin)


{-
⊥ : Value

infix 4 _⊑_
infix 4 _⊑ᵗ_

data _⊑ᵗ_ : Table → Table → Set

data _⊑_ : Value → Value → Set where
  ⊑-⊥ : ∀{v} → ⊥ ⊑ v
  ⊑-const : ∀ {B}{k} → const {B} k ⊑ const {B} k
  ⊑-fun : ∀{t₁ t₂ : Table} → t₁ ⊑ᵗ t₂ → fun t₁ ⊑ fun t₂

data _⊑ᵗ_ where
  ⊑ᵗ-[] : ∀{t} → [] ⊑ᵗ t
  ⊑ᵗ-here : ∀{v w v′ w′ t₁ t₂}
     → t₁ ⊑ᵗ t₂
     → ⟨ v , w ⟩ ∷ t₁ ⊑ᵗ ⟨ v , w ⟩ ∷ t₂
  ⊑ᵗ-there : ∀{v w t₁ t₂} →  t₁ ⊑ᵗ t₂
     → t₁ ⊑ᵗ ⟨ v , w ⟩ ∷ t₂
-}
{-

⊑-refl : ∀{v} → v ⊑ v 
⊑ᵗ-refl : ∀{t} → t ⊑ᵗ t

⊑-refl {const k} = ⊑-const
⊑-refl {fun t} = ⊑-fun ⊑ᵗ-refl
⊑-refl {⊥} = ⊑-⊥

⊑ᵗ-refl {[]} = ⊑ᵗ-[]
⊑ᵗ-refl {⟨ v , w ⟩ ∷ t} = ⊑ᵗ-match ⊑ᵗ-refl
-}

{-
join : Value → Value → Value
join (const {B} x) (const {B′} y)
    with base-eq? B B′
... | no neq = ⊥
... | yes refl
    with base-rep-eq? x y
... | yes refl = const {B} x
... | no neq = ⊥
join (const x) (fun t) = ⊥
join (const x) ⊥ = const x
join (fun t₁) (const x) = ⊥
join (fun t₁) (fun t₂) = fun (t₁ ++ t₂)
join (fun t₁) ⊥ = fun t₁
join ⊥ v = v

{- Table lookup -}

infix 3 _[_]⩦_
data _[_]⩦_ : Table → Value → Value → Set where
     {- u ≢ v ?? -}
  done : ∀{v} → [] [ v ]⩦ ⊥
  search : ∀ {u v w w′ t} → t [ v ]⩦ w′ → (⟨ u , w ⟩ ∷ t) [ v ]⩦ w′
  found : ∀ {v w w′ t}
    → t [ v ]⩦ w′
    → (⟨ v , w ⟩ ∷ t) [ v ]⩦ (join w w′)

data _⊑ᵗ_ where
  ⊑ᵗ-[] : ∀{t} → [] ⊑ᵗ t
  ⊑ᵗ-↦ : ∀{v w w′ t₁ t₂}
     → t₂ [ v ]⩦ w′  →  w ⊑ w′  →  t₁ ⊑ᵗ t₂
     → ⟨ v , w ⟩ ∷ t₁ ⊑ᵗ t₂

⊑-refl : ∀{v} → v ⊑ v 
⊑ᵗ-refl : ∀{t} → t ⊑ᵗ t

⊑-refl {const k} = ⊑-const
⊑-refl {fun t} = ⊑-fun ⊑ᵗ-refl
⊑-refl {⊥} = ⊑-⊥

{- hmm, this is pointless -}
lookup : ∀ t v → Σ[ w ∈ Value ] t [ v ]⩦ w
lookup [] v = ⟨ ⊥ , done ⟩
lookup (⟨ v′ , w ⟩ ∷ t) v
    with lookup t v
... | ⟨ w′ , tvw′ ⟩ = ⟨ w′ , (search tvw′) ⟩

⊑ᵗ-refl {[]} = ⊑ᵗ-[]
⊑ᵗ-refl {⟨ v , w ⟩ ∷ t} = ⊑ᵗ-↦ {!!} {!!} {!!}
-}

{-

value-eq? : (u : Value) → (v : Value) → Dec (u ≡ v)

pair-eq? : (x : Value × Value) (y : Value × Value) → Dec (x ≡ y)
pair-eq? ⟨ u , v ⟩ ⟨ u′ , v′ ⟩
    with value-eq? u u′
... | no neq = no λ { refl → neq refl }
... | yes refl
    with value-eq? v v′
... | no neq = no λ { refl → neq refl }
... | yes refl = yes refl
    
table-eq? : (t₁ : Table) → (t₂ : Table) → Dec (t₁ ≡ t₂)
table-eq? [] [] = yes refl
table-eq? [] (x ∷ t₂) = no λ ()
table-eq? (x ∷ t₁) [] = no λ ()
table-eq? (x ∷ t₁) (y ∷ t₂)
    with pair-eq? x y
... | no neq = no λ { refl → neq refl }
... | yes refl
    with table-eq? t₁ t₂
... | no neq = no λ { refl → neq refl }
... | yes refl = yes refl
    
value-eq? (const {B} x) (const {B′} y)
    with base-eq? B B′
... | no neq = no λ { refl → neq refl }
... | yes refl
    with base-rep-eq? x y
... | yes refl = yes refl
... | no neq = no λ { refl → neq refl }
value-eq? (const x) (fun x₁) = no (λ ())
value-eq? (const x) ⊥ = no λ ()
value-eq? (fun t₁) (const x₁) = no (λ ())
value-eq? (fun t₁) (fun t₂)
    with table-eq? t₁ t₂
... | yes refl = yes refl
... | no neq = no λ { refl → neq refl }
value-eq? (fun x) ⊥ = no (λ ())
value-eq? ⊥ (const x) = no λ ()
value-eq? ⊥ (fun x) = no λ ()
value-eq? ⊥ ⊥ = yes refl

lookup-prepend : ∀{t₁ t₂ v w}
  → t₂ [ v ]⩦ w → (t₁ ++ t₂) [ v ]⩦ w
lookup-prepend {[]} {t₂} {v} {w} t₂[v]⩦w = t₂[v]⩦w
lookup-prepend {⟨ v′ , w′ ⟩ ∷ t₁} {t₂} {v} {w} t₂[v]⩦w =
  search (lookup-prepend t₂[v]⩦w)

⊑ᵗ-prepend : ∀{t₁ t₂} → t₂ ⊑ᵗ t₁ ++ t₂
-}

{-
⊑ᵗ-prepend {t₁} {[]} = ⊑ᵗ-[]
⊑ᵗ-prepend {t₁} {⟨ v , w ⟩ ∷ t₂} =
  let IH = ⊑ᵗ-prepend {t₁}{t₂} in
  
  ⊑ᵗ-↦ {!!} {!!}
-}
{-
⊑ᵗ-refl {⟨ v , w ⟩ ∷ []} = ⊑ᵗ-↦ found ⊑ᵗ-[]
    with value-eq? v v′
... | no neq = ⊑ᵗ-↦ found (⊑ᵗ-↦ (search neq found) {!!})
... | yes refl = {!!}  
-}

{- ⊑ᵗ-↦ found {!!} -}

{-


_[_] : Table → Value → Value 
[] [ u ] = ⊥
(⟨ v , w ⟩ ∷ t) [ u ]
    with value-eq? v u
... | yes refl = join w (t [ u ])
... | no neq = t [ u ]

  
⊑-refl : ∀{v}
  → v ⊑ v 
⊑-refl {v} = {!!}

⊑ᵗ-dist : ∀{v w w′}
  → ⟨ v , join w w′ ⟩ ∷ [] ⊑ᵗ ⟨ v , w ⟩ ∷ ⟨ v , w′ ⟩ ∷ []
⊑ᵗ-dist {v}{w}{w′}
     with value-eq? v v
... | no neq = ⊥-elim (neq refl)
... | yes eq =
      ⊑ᵗ-↦ G ⊑ᵗ-[]  
    where
    G : join w w′ ⊑  (⟨ v , w ⟩ ∷ ⟨ v , w′ ⟩ ∷ []) [ v ]
    G = {!!}

    H : join w w′ ⊑  join w ((⟨ v , w′ ⟩ ∷ []) [ v ])
    H = {!!}

    I : (⟨ v , w ⟩ ∷ ⟨ v , w′ ⟩ ∷ []) [ v ] ≡ join w ((⟨ v , w′ ⟩ ∷ []) [ v ])
    I
        with value-eq? v v
    ... | no neq = ⊥-elim (neq refl)
    ... | yes eq = {!refl!}
-}

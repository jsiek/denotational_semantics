{-# OPTIONS --without-K #-}
{- Extracted from the abt library (github.com/jsiek/abstract-binding-trees,
   commit 1387c40); the lemmas are in proof/Framework/abt/ScopedTuple.agda. -}
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩ )
open import Data.Unit.Polymorphic using (⊤; tt)
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Framework.abt.Sig

module Framework.abt.ScopedTuple where

{- Scet: A scoped Set -}
Scet : {ℓ : Level} → Set (lsuc ℓ)
Scet {ℓ} = Sig → Set ℓ

_⇨_ : {ℓ : Level} → Scet {ℓ} → Scet {ℓ} → Set ℓ
A ⇨ B = (∀ {b : Sig} → A b → B b)

𝒫 : {ℓ : Level} → Scet {ℓ} → Set (lsuc ℓ)
𝒫 {ℓ} A = (∀ {b : Sig} → A b → Set ℓ)

_✖_ : {ℓ : Level} → Scet {ℓ} → Scet {ℓ} → Set (lsuc ℓ)
_✖_ {ℓ} A B = (∀ {b : Sig} → A b → B b → Set ℓ)

Sigs : Set
Sigs = List Sig

Tuple : {ℓ : Level} → Sigs → Scet {ℓ} → Set ℓ
Tuple [] A = ⊤
Tuple (b ∷ bs) A = A b × Tuple bs A

map : ∀{ℓ : Level}{A : Scet {ℓ}}{B : Scet {ℓ}} → (A ⇨ B) → {bs : Sigs}
   → Tuple {ℓ} bs A → Tuple {ℓ} bs B
map f {[]} ⊤ = tt
map f {b ∷ bs} ⟨ x , xs ⟩ = ⟨ f x , map f xs ⟩

foldr : ∀{ℓ : Level}{A}{B : Set} → (∀ {b} → A b → B → B)
   → B → {bs : Sigs} → Tuple {ℓ} bs A → B
foldr c n {[]} tt = n
foldr c n {b ∷ bs} ⟨ x , xs ⟩ = c x (foldr c n xs)

all : ∀{A} → 𝒫 A → {bs : Sigs} → Tuple bs A → Set
all {A} P {[]} tt = ⊤
all {A} P {b ∷ bs} ⟨ x , xs ⟩ = P x × (all P xs)

zip : ∀{ℓ}{A B : Scet {ℓ}} → A ✖ B → {bs : Sigs}
   → Tuple bs A → Tuple bs B → Set ℓ
zip R {[]} tt tt = ⊤
zip R {b ∷ bs} ⟨ a₁ , as₁ ⟩ ⟨ a₂ , as₂ ⟩ = R a₁ a₂ × zip R as₁ as₂

module Framework.GraphModel.SetsAsPredicates where

open import Data.Empty renaming (⊥ to False)
open import Data.Product using (_×_; Σ; Σ-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.List using (List)
open import Data.List.Membership.Propositional renaming (_∈_ to _⋵_)

𝒫 : Set → Set₁
𝒫 V = V → Set

∅ : ∀{T} → 𝒫 T
∅ = λ v → False

⌈_⌉ : ∀ {T} → T → 𝒫 T     {- the singleton set containing only v -}
⌈ v ⌉ w = w ≡ v

infix 9 _∈_
_∈_ : ∀{T : Set} → T → 𝒫 T → Set
v ∈ D = D v

nonempty : ∀{T : Set} → 𝒫 T → Set
nonempty{T} S = Σ[ x ∈ T ] x ∈ S

infix 9 _⊆_
_⊆_ : ∀{T : Set} → 𝒫 T → 𝒫 T → Set
D ⊆ E = ∀ d → d ∈ D → d ∈ E

infix 6 _≃_
_≃_ : ∀{T : Set} → 𝒫 T → 𝒫 T → Set
D₁ ≃ D₂ = D₁ ⊆ D₂  ×  D₂ ⊆ D₁

{- Finite Sets represented by Lists -------------------------------------------}

mem : ∀{T : Set} → List T → T → Set
mem {T} ls x = x ⋵ ls

open import Structures
open import ValueBCDConst
open DomainAux domain
open OrderingAux domain ordering

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Nat using (suc)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)


module ModelISWIM where

open import ModelCallByValue domain ordering ℱ model_curry public


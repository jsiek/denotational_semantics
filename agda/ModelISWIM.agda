open import Primitives
open import Structures
open import ISWIM

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥-elim) renaming (⊥ to Bot)
open import Relation.Nullary using (¬_; Dec; yes; no)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong; cong₂; cong-app)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)

module ModelISWIM where

open import ValueConst 
open import ValueStructAux value_struct 
open import OrderingAux value_struct ordering
open import Consistency
open import ModelCurryConst

open import ModelCallByValue value_struct ordering consistent ℱ model_curry public


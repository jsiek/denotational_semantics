open import Primitives
open import Structures
open import ISWIM

{-
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥-elim) renaming (⊥ to Bot)
open import Relation.Nullary using (¬_; Dec; yes; no)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong; cong₂; cong-app)
-}

module ModelISWIM where

open import ValueConst public
open import ValueStructAux value_struct public
open import OrderingAux value_struct ordering public
open import Consistency public
open import CurryConst public
open import ModelCurryConst public

open import ModelCallByValue value_struct ordering consistent ℱ model_curry
     public


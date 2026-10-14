{-

  Collecting the values of n subterms, left to right, into a vector, for
  machines whose values are typed by the length of a tuple: the values
  so far are kept in reverse in a list vs, with the equation
  length vs + j ≡ n for the j subterms still to evaluate.

-}

module Framework.VecUtil where

open import Data.List using (List; []; _∷_; length; reverse)
open import Data.List.Properties using (length-reverse)
open import Data.Nat using (ℕ; suc; _+_)
open import Data.Nat.Properties using (+-suc; +-identityʳ)
open import Data.Vec using (Vec; fromList)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

private variable
  A : Set
  n j : ℕ

{- a list of length n as a vector -}
toVec : (vs : List A) → length vs ≡ n → Vec A n
toVec vs refl = fromList vs

{- one more value -}
more : ∀ {v : A} vs → length vs + suc j ≡ n → length (v ∷ vs) + j ≡ n
more {j = j} vs e = trans (sym (+-suc (length vs) j)) e

{- all n values, in order -}
collected : (vs : List A) → length vs + 0 ≡ n → Vec A n
collected vs e = toVec (reverse vs) (trans (length-reverse vs) (trans (sym (+-identityʳ _)) e))

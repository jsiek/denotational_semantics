module Language.Prim where

{-
 The primitive operations on integers, shared by every language:
   prim p ⦅ L , M ⦆ applies p to the integers that L and M produce, and
   goes wrong on anything else.
 There are no booleans: eq produces a sum, inl ⟨⟩ for true and inr ⟨⟩
   for false (⟨⟩ is the empty tuple), so that case serves as if.
-}

open import Data.Bool using (Bool)
open import Data.Integer using (ℤ; _-_; _≟_)
open import Relation.Nullary using (does)

data Prim : Set where
  sub : Prim      {- subtraction -}
  eq : Prim       {- equality -}

{- the result of a primitive: an integer or a truth value -}
data Out : Set where
  int : ℤ → Out
  bool : Bool → Out

δ : Prim → ℤ → ℤ → Out
δ sub n m = int (n - m)
δ eq n m = bool (does (n ≟ m))

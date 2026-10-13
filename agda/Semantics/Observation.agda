{-

  What a run of a program can be seen to do, shared by every language
  and by both operational styles of semantics: the small-step machines
  (Semantics/CEK/) and the clocked interpreters (Semantics/Interp/).

  A finished run is observed through its final value, forgetting the code
  and environment inside closures, or as going wrong.

  The shape of an end theorem: two programs have the same observations
  when each terminates with o exactly when the other does.

-}

module Semantics.Observation where

open import Framework.Primitives using (Base; base-rep; Int)
open import Language.Prim using (Prim; Out; δ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List)
open import Data.Product using (_×_; Σ-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (¬_)
open import Framework.Iff using (_⇔_) public

data Obs : Set where
  o-const : (B : Base) → base-rep B → Obs
  o-fun : Obs
  o-tuple : List Obs → Obs
  o-inl : Obs → Obs
  o-inr : Obs → Obs
  o-wrong : Obs

{- a primitive operation looks at its operands only through their
   observations: it applies to two integers, and is undefined otherwise -}
δ? : Prim → Obs → Obs → Maybe Out
δ? p (o-const Int n) (o-const Int m) = just (δ p n m)
δ? p _ _ = nothing

{- a successful result: anything but going wrong -}
Answer : Obs → Set
Answer o = ¬ (o ≡ o-wrong)

{- terminating with some answer -}
Converges : (Obs → Set) → Set
Converges T = Σ[ o ∈ Obs ] Answer o × T o

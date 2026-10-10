{-

  What a run of a program can be seen to do, shared by every language
  and by every style of semantics (small-step machines here; a big-step
  semantics with fuel or logical relations could reuse it).

  A finished run is observed through its final value, forgetting the code
  and environment inside closures, or as going wrong.

  The shape of an end theorem: two programs have the same observations
  when each terminates with o exactly when the other does.

-}

module Compiler.Operational.Observation where

open import Primitives using (Base; base-rep)
open import Data.List using (List)
open import Data.Product using (_×_; Σ-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (¬_)

data Obs : Set where
  o-const : (B : Base) → base-rep B → Obs
  o-fun : Obs
  o-tuple : List Obs → Obs
  o-inl : Obs → Obs
  o-inr : Obs → Obs
  o-wrong : Obs

{- a successful result: anything but going wrong -}
Answer : Obs → Set
Answer o = ¬ (o ≡ o-wrong)

_⇔_ : Set → Set → Set
A ⇔ B = (A → B) × (B → A)

{- the end-theorem shape, for any notion of "terminates with o" -}
SameObs : (Obs → Set) → (Obs → Set) → Set
SameObs T₁ T₂ = ∀ o → T₁ o ⇔ T₂ o

{- terminating with some answer -}
Converges : (Obs → Set) → Set
Converges T = Σ[ o ∈ Obs ] Answer o × T o

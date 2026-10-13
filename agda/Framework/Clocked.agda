{-

  Functional big-step semantics with a clock, in the style of CakeML, for
  any type Obs of observations with an observation o-error of stopping
  with an error: results of clocked interpreters and the end theorem
  (Equivalent). (Clock-for-clock correctness, clocked, and the other
  lemmas are in proof/Framework/Clocked.agda.)

  Language independent: instantiated at a compiler's observations (for
  this compiler, Semantics/Interp/Clock.agda, which has the design note
  for its interpreters and proofs).

-}

module Framework.Clocked (Obs : Set) (o-error : Obs) where

open import Framework.Iff using (_⇔_)

open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ-syntax; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_)

private variable
  A B A' B' : Set

data Result (A : Set) : Set where
  timeout : Result A
  error : Result A
  ret : A → Result A

infixl 1 _>>=_
_>>=_ : Result A → (A → Result B) → Result B
timeout >>= f = timeout
error >>= f = error
ret v >>= f = f v

{- a lookup or projection, which errors if there is nothing -}
from-maybe : Maybe A → Result A
from-maybe (just v) = ret v
from-maybe nothing = error

{- The end theorem -------------------------------------------------------------}

{- a program, run with a clock -}
record Semantics : Set₁ where
  constructor semantics
  field
    Val : Set
    obs : Val → Obs
    run : ℕ → Result Val
open Semantics using (Val; run)

outcome : (A → Obs) → Result A → Maybe Obs
outcome obs timeout = nothing
outcome obs error = just o-error
outcome obs (ret v) = just (obs v)

module _ (P : Semantics) where
  open Semantics P using (obs)

  Terminates : Obs → Set
  Terminates o = Σ[ ck ∈ ℕ ] outcome obs (run P ck) ≡ just o

  Diverges : Set
  Diverges = ∀ ck → run P ck ≡ timeout

record Equivalent (P₁ P₂ : Semantics) : Set where
  field
    terminates : ∀ o → Terminates P₁ o ⇔ Terminates P₂ o
    diverges : Diverges P₁ ⇔ Diverges P₂

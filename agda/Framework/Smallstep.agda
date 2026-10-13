{-

  Transition systems and their behaviors, in the spirit of CompCert's
  Smallstep library, for any type Obs of observations: a machine is a
  step function that either moves to the next state or stops with an
  observation. Two machines are equivalent (Equivalent, the shape of the
  end theorems) when each terminates with o exactly when the other does,
  and one diverges exactly when the other does. (Lemmas about runs are in
  proof/Framework/Smallstep.agda, forward simulations in
  proof/Framework/Simulation.agda.)

  Language independent: instantiated at a compiler's observations (for
  this compiler, Semantics/CEK/Smallstep.agda, which has the design
  note for its machines and simulation proofs).

-}

module Framework.Smallstep (Obs : Set) where

open import Framework.Iff using (_⇔_)

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; Σ-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_)

{- Machines given by a step function ------------------------------------------}

data Next (S : Set) : Set where
  next : S → Next S
  stop : Obs → Next S

record Machine : Set₁ where
  constructor machine
  field
    State : Set
    step : State → Next State
    start : State
open Machine public using (State; start)

module _ (L : Machine) where
  open Machine L using (step)

  Step : State L → State L → Set
  Step s s' = step s ≡ next s'

  Final : State L → Obs → Set
  Final s o = step s ≡ stop o

  infixr 5 _◅_
  data Star : State L → State L → Set where
    ε : ∀ {s} → Star s s
    _◅_ : ∀ {s s' s''} → Step s s' → Star s' s'' → Star s s''

  {- exactly n steps -}
  data Steps : ℕ → State L → State L → Set where
    zero : ∀ {s} → Steps zero s s
    suc : ∀ {n s s' s''} → Step s s' → Steps n s' s'' → Steps (suc n) s s''

  Terminates : Obs → Set
  Terminates o = Σ[ s ∈ State L ] Star (start L) s × Final s o

  Diverges : Set
  Diverges = ∀ n → Σ[ s ∈ State L ] Steps n (start L) s

{- The end theorem: the two machines terminate with the same observations,
   and one diverges exactly when the other does -}
record Equivalent (L₁ L₂ : Machine) : Set where
  field
    terminates : ∀ o → Terminates L₁ o ⇔ Terminates L₂ o
    diverges : Diverges L₁ ⇔ Diverges L₂

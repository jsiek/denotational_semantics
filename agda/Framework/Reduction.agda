{-

  Reduction semantics, as transition systems (Framework/Smallstep.agda),
  for any type Obs of observations with an observation o-wrong of going
  wrong. (Lemmas, and forward simulations between reduction semantics,
  are in proof/Framework/Reduction.agda.)

  A language's reduction is a function red that says, of a term, whether
  it is a value, is stuck, or reduces to another term (Red). It is
  written with congruence rules: step-in f r k reduces inside the
  context f, by r, if that subterm is not yet a value, and otherwise
  continues with k. So red is deterministic and total by construction.
  The machine of a program runs red from the program, and stops with the
  observation of the value it reaches, or with o-wrong when it is stuck.

-}

module Framework.Reduction (Obs : Set) (o-wrong : Obs) where

open import Framework.Smallstep Obs using (Machine; machine; Next; next; stop)

data Red (A : Set) : Set where
  val : Red A              {- a value -}
  wrong : Red A            {- stuck -}
  to : A → Red A           {- reduces to -}

{- reduce the subterm in the context f, or, if it is a value, continue -}
step-in : ∀ {A B : Set} → (A → B) → Red A → Red B → Red B
step-in f (to M) k = to (f M)
step-in f wrong k = wrong
step-in f val k = k

toNext : ∀ {A : Set} → Obs → Red A → Next A
toNext o val = stop o
toNext o wrong = stop o-wrong
toNext o (to M) = next M

{- the machine that runs the reduction red from M, observing values by obs -}
reduction : ∀ {A : Set} → (A → Obs) → (A → Red A) → A → Machine
reduction {A} obs red M = machine A (λ N → toNext (obs N) (red N)) M

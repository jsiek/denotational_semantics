{-

  Transition systems and their behaviors, in the spirit of CompCert's
  Smallstep library. (Forward simulations are in Simulation.agda.)

  Design note, for the machines of each language and the simulation proof
  of each pass:

  * Each language has a CEK-style machine (Machine/*.agda) with states
      eval M ρ κ   evaluate term M in environment ρ, then continue with κ
      ret v κ      return value v to continuation κ
    Environments are lists of values (variable x is the x-th element),
    and a function value is a syntactic closure: code plus environment.
    Lists of subterms (tuple components, a closure's free variables) are
    evaluated left to right, collecting values in a continuation frame.

  * A machine is a step function, step : State → Next State, which either
    moves to the next state or stops with an observation (see
    Observation.agda): the observation of the value returned to the empty
    continuation, or o-wrong when the machine is stuck (an unbound
    variable, applying a non-function, projecting from a non-tuple, ...).
    So every state either steps or is final, and machines are
    deterministic, by construction (machine-det, machine-progress).

  * A program's semantics (Semantics) has one initial state,
    eval M [] halt. It terminates with o if it reaches a final state with
    observation o, and diverges if it can take n steps for every n.

  * A pass is proved correct by a forward simulation (Simulation.agda):
    one source step is matched by one or more target steps, or by zero or
    more target steps that decrease a well-founded measure. Since both
    machines are deterministic and total, this gives the end theorem
    (Equivalent): the program and its compilation terminate with the same
    observations (including o-wrong), and one diverges iff the other does.
    We never need "terminates or diverges", which is not constructive.
    When no source step is matched by zero target steps (as for enclose),
    plus-simulation builds the forward simulation from one lemma,
      sim : s₁ ~ s₂ → Answers L₂ _~_ (step s₁) s₂
    (the target stops with the same observation, or takes a plus to a
    matching state), proved by cases on the match. When some source
    steps are matched by no target step (as for optimize, where the
    source evaluates free variables that the target drops),
    measure-simulation takes a match indexed by a natural number, and
    such a step must decrease it.

  * Layout: Observation.agda (shared by any semantics), Smallstep.agda and
    Simulation.agda (the framework), Machine/*.agda (one per language),
    Correctness/*Sim.agda (one per pass).

-}

module Compiler.Operational.Smallstep where

open import Compiler.Operational.Observation

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-identityʳ; +-suc)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; subst; cong)
open import Relation.Nullary using (¬_)

{- Transition systems ---------------------------------------------------------}

record Semantics : Set₁ where
  field
    State : Set
    Step : State → State → Set
    Initial : State → Set
    Final : State → Obs → Set
open Semantics public

module _ (L : Semantics) where

  infixr 5 _◅_
  data Star : State L → State L → Set where
    ε : ∀ {s} → Star s s
    _◅_ : ∀ {s s' s''} → Step L s s' → Star s' s'' → Star s s''

  data Plus : State L → State L → Set where
    plus : ∀ {s s' s''} → Step L s s' → Star s' s'' → Plus s s''

  {- exactly n steps -}
  data Steps : ℕ → State L → State L → Set where
    zero : ∀ {s} → Steps zero s s
    suc : ∀ {n s s' s''} → Step L s s' → Steps n s' s'' → Steps (suc n) s s''

  Terminates : Obs → Set
  Terminates o = Σ[ s₀ ∈ State L ] Σ[ s ∈ State L ] Initial L s₀ × Star s₀ s × Final L s o

  Diverges : Set
  Diverges = Σ[ s₀ ∈ State L ] Initial L s₀ × (∀ n → Σ[ s ∈ State L ] Steps n s₀ s)

  record Deterministic : Set where
    field
      initial-unique : ∀ {s s'} → Initial L s → Initial L s' → s ≡ s'
      step-det : ∀ {s s₁ s₂} → Step L s s₁ → Step L s s₂ → s₁ ≡ s₂
      final-nostep : ∀ {s s' o} → Final L s o → Step L s s' → ⊥
      final-det : ∀ {s o o'} → Final L s o → Final L s o' → o ≡ o'

  {- every state is final or steps, and there is an initial state -}
  record Progressive : Set where
    field
      initial-exists : Σ[ s ∈ State L ] Initial L s
      progress : ∀ s → (Σ[ o ∈ Obs ] Final L s o) ⊎ (Σ[ s' ∈ State L ] Step L s s')

module _ {L : Semantics} where

  infixr 5 _◅◅_
  _◅◅_ : ∀ {s s' s''} → Star L s s' → Star L s' s'' → Star L s s''
  ε ◅◅ τ = τ
  (st ◅ σ) ◅◅ τ = st ◅ (σ ◅◅ τ)

  plus-star : ∀ {s s' s''} → Plus L s s' → Star L s' s'' → Plus L s s''
  plus-star (plus st σ) τ = plus st (σ ◅◅ τ)

  plus→star : ∀ {s s'} → Plus L s s' → Star L s s'
  plus→star (plus st σ) = st ◅ σ

  star-plus : ∀ {s s' s''} → Star L s s' → Plus L s' s'' → Plus L s s''
  star-plus ε π = π
  star-plus (st ◅ σ) π = plus st (σ ◅◅ plus→star π)

  star→steps : ∀ {s s'} → Star L s s' → Σ[ n ∈ ℕ ] Steps L n s s'
  star→steps ε = zero , zero
  star→steps (st ◅ σ) with star→steps σ
  ... | n , τ = suc n , suc st τ

  {- In a deterministic system, a run to a final state passes through
     every state reachable from the start -}
  steps-det-skip : Deterministic L → ∀ {k n s s' t o}
    → Steps L k s s' → Steps L n s t → Final L t o
    → Σ[ n' ∈ ℕ ] (n' + k ≡ n) × Steps L n' s' t
  steps-det-skip D {n = n} zero τ fin = n , +-identityʳ n , τ
  steps-det-skip D (suc st σ) zero fin = ⊥-elim (Deterministic.final-nostep D fin st)
  steps-det-skip D (suc st σ) (suc st' τ) fin
    with Deterministic.step-det D st st'
  ... | refl with steps-det-skip D σ τ fin
  ...   | n' , eq , τ' = n' , trans (+-suc n' _) (cong suc eq) , τ'

  {- Divergence, for deterministic and total systems, is never reaching a
     final state -}
  diverges-not-terminates : Deterministic L → ∀ {o} → Diverges L → ¬ Terminates L o
  diverges-not-terminates D (s₀ , i₀ , run) (s₀' , s , i₀' , σ , fin)
    with Deterministic.initial-unique D i₀ i₀'
  ... | refl with star→steps σ
  ...   | k , τ with run (suc k)
  ...     | t , τ' = stuck τ τ'
    where
    stuck : ∀ {k s₁ t} → Steps L k s₁ s → Steps L (suc k) s₁ t → ⊥
    stuck zero (suc st _) = Deterministic.final-nostep D fin st
    stuck (suc st σ) (suc st' τ) with Deterministic.step-det D st st'
    ... | refl = stuck σ τ

  never-final-diverges : Progressive L → ∀ {s₀} → Initial L s₀
    → (∀ {s o} → Star L s₀ s → Final L s o → ⊥) → Diverges L
  never-final-diverges P {s₀} i₀ nf = s₀ , i₀ , go nf
    where
    go : ∀ {s} → (∀ {s' o} → Star L s s' → Final L s' o → ⊥)
       → ∀ n → Σ[ s' ∈ State L ] Steps L n s s'
    go {s} nf zero = s , zero
    go {s} nf (suc n) with Progressive.progress P s
    ... | inj₁ (o , fin) = ⊥-elim (nf ε fin)
    ... | inj₂ (s' , st) with go (λ σ fin → nf (st ◅ σ) fin) n
    ...   | s'' , τ = s'' , suc st τ

{- Machines given by a step function ------------------------------------------}

data Next (S : Set) : Set where
  next : S → Next S
  stop : Obs → Next S

machine : (S : Set) → (S → Next S) → S → Semantics
machine S step s₀ = record
  { State = S
  ; Step = λ s s' → step s ≡ next s'
  ; Initial = λ s → s₀ ≡ s
  ; Final = λ s o → step s ≡ stop o
  }

module _ {S : Set} {step : S → Next S} {s₀ : S} where

  machine-det : Deterministic (machine S step s₀)
  machine-det = record
    { initial-unique = λ { refl refl → refl }
    ; step-det = λ e₁ e₂ → next-inj (trans (sym e₁) e₂)
    ; final-nostep = λ e₁ e₂ → stop≢next (trans (sym e₁) e₂)
    ; final-det = λ e₁ e₂ → stop-inj (trans (sym e₁) e₂)
    }
    where
    next-inj : ∀ {a b : S} → next a ≡ next b → a ≡ b
    next-inj refl = refl
    stop-inj : ∀ {a b} → stop {S} a ≡ stop b → a ≡ b
    stop-inj refl = refl
    stop≢next : ∀ {o} {a : S} → stop o ≡ next a → ⊥
    stop≢next ()

  machine-progress : Progressive (machine S step s₀)
  machine-progress = record
    { initial-exists = s₀ , refl
    ; progress = prog
    }
    where
    prog : ∀ s → (Σ[ o ∈ Obs ] step s ≡ stop o) ⊎ (Σ[ s' ∈ S ] step s ≡ next s')
    prog s with step s
    ... | next s' = inj₂ (s' , refl)
    ... | stop o = inj₁ (o , refl)

{- How a target state answers one step of a source machine: by stopping with
   the same observation, or by taking one or more steps to a state that
   matches the next source state (the common "plus" simulation diagram) -}
data Answers {S₁ : Set} (L₂ : Semantics) (R : S₁ → State L₂ → Set)
  : Next S₁ → State L₂ → Set where
  stops : ∀ {o s₂} → Final L₂ s₂ o → Answers L₂ R (stop o) s₂
  steps : ∀ {s₁' s₂ s₂'} → Plus L₂ s₂ s₂' → R s₁' s₂' → Answers L₂ R (next s₁') s₂

{-

  Transition systems and their behaviors, in the spirit of CompCert's
  Smallstep library, for any type Obs of observations: a machine is a
  step function that either moves to the next state or stops with an
  observation. (Forward simulations are in Simulation.agda.)

  Language independent: instantiated at a compiler's observations (for
  this compiler, Compiler/Operational/Smallstep.agda, which has the design
  note for its machines and simulation proofs).

-}

module Framework.Smallstep (Obs : Set) where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-identityʳ; +-suc)
open import Data.Product using (_×_; Σ-syntax; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; cong)
open import Relation.Nullary using (¬_)

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

  data Plus : State L → State L → Set where
    plus : ∀ {s s' s''} → Step s s' → Star s' s'' → Plus s s''

  {- exactly n steps -}
  data Steps : ℕ → State L → State L → Set where
    zero : ∀ {s} → Steps zero s s
    suc : ∀ {n s s' s''} → Step s s' → Steps n s' s'' → Steps (suc n) s s''

  Terminates : Obs → Set
  Terminates o = Σ[ s ∈ State L ] Star (start L) s × Final s o

  Diverges : Set
  Diverges = ∀ n → Σ[ s ∈ State L ] Steps n (start L) s

module _ {L : Machine} where
  open Machine L using (step)

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

  {- determinism -}
  step-det : ∀ {s s₁ s₂} → Step L s s₁ → Step L s s₂ → s₁ ≡ s₂
  step-det e₁ e₂ with trans (sym e₁) e₂
  ... | refl = refl

  final-det : ∀ {s o o'} → Final L s o → Final L s o' → o ≡ o'
  final-det e₁ e₂ with trans (sym e₁) e₂
  ... | refl = refl

  final-nostep : ∀ {s s' o} → Final L s o → Step L s s' → ⊥
  final-nostep e₁ e₂ with trans (sym e₁) e₂
  ... | ()

  {- a run to a final state passes through every state reachable from the
     start -}
  steps-det-skip : ∀ {k n s s' t o}
    → Steps L k s s' → Steps L n s t → Final L t o
    → Σ[ n' ∈ ℕ ] (n' + k ≡ n) × Steps L n' s' t
  steps-det-skip {n = n} zero τ fin = n , +-identityʳ n , τ
  steps-det-skip (suc st σ) zero fin = ⊥-elim (final-nostep fin st)
  steps-det-skip (suc st σ) (suc st' τ) fin with step-det st st'
  ... | refl with steps-det-skip σ τ fin
  ...   | n' , eq , τ' = n' , trans (+-suc n' _) (cong suc eq) , τ'

  {- Divergence is never reaching a final state -}
  diverges-not-terminates : ∀ {o} → Diverges L → ¬ Terminates L o
  diverges-not-terminates run (s , σ , fin) with star→steps σ
  ... | k , τ with run (suc k)
  ...   | t , τ' = stuck τ τ'
    where
    stuck : ∀ {k s₁ t} → Steps L k s₁ s → Steps L (suc k) s₁ t → ⊥
    stuck zero (suc st _) = final-nostep fin st
    stuck (suc st σ) (suc st' τ) with step-det st st'
    ... | refl = stuck σ τ

  never-final-diverges : (∀ {s o} → Star L (start L) s → Final L s o → ⊥) → Diverges L
  never-final-diverges = go
    where
    go : ∀ {s} → (∀ {s' o} → Star L s s' → Final L s' o → ⊥)
       → ∀ n → Σ[ s' ∈ State L ] Steps L n s s'
    go {s} nf zero = s , zero
    go {s} nf (suc n) with step s in eq
    ... | stop o = ⊥-elim (nf ε eq)
    ... | next s' with go (λ σ fin → nf (eq ◅ σ) fin) n
    ...   | s'' , τ = s'' , suc eq τ

{- How a target state answers one step of a source machine: by stopping with
   the same observation, or by taking one or more steps to a state that
   matches the next source state (the common "plus" simulation diagram) -}
data Answers {S₁ : Set} (L₂ : Machine) (R : S₁ → State L₂ → Set)
  : Next S₁ → State L₂ → Set where
  stops : ∀ {o s₂} → Final L₂ s₂ o → Answers L₂ R (stop o) s₂
  steps : ∀ {s₁' s₂ s₂'} → Plus L₂ s₂ s₂' → R s₁' s₂' → Answers L₂ R (next s₁') s₂

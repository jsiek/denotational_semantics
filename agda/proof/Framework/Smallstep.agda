{-

  Lemmas about the runs of the machines of Framework/Smallstep.agda:
  runs of one or more steps (Plus), composing runs, determinism,
  divergence, and how a target state answers a source step (Answers,
  for plus simulations; see Simulation.agda), directly or after running
  ahead to a matching state (Reach). The runs of a step function from
  any state are in Runs.agda.

-}

module proof.Framework.Smallstep (Obs : Set) where

open import Framework.Smallstep Obs

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe.Relation.Binary.Pointwise as M
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-identityʳ; +-suc)
open import Data.Product using (_×_; Σ-syntax; _,_; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; cong)
open import Relation.Nullary using (¬_)

module _ (L : Machine) where

  data Plus : State L → State L → Set where
    plus : ∀ {s s' s''} → Step L s s' → Star L s' s'' → Plus s s''

module _ {L : Machine} where
  open Machine L using (step)

  infixr 5 _◅◅_
  _◅◅_ : ∀ {s s' s''} → Star L s s' → Star L s' s'' → Star L s s''
  ε ◅◅ τ = τ
  (st ◅ σ) ◅◅ τ = st ◅ (σ ◅◅ τ)

  plus-star : ∀ {s s' s''} → Plus L s s' → Star L s' s'' → Plus L s s''
  plus-star (plus st σ) τ = plus st (σ ◅◅ τ)

  step⁺ : ∀ {s s'} → Step L s s' → Plus L s s'
  step⁺ st = plus st ε

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

  {- two runs from one state to final states have the same observation -}
  final-unique : ∀ {s t' o' n t o} → Star L s t' → Final L t' o' → Steps L n s t → Final L t o
    → o' ≡ o
  final-unique σ fin' τ fin with steps-det-skip (proj₂ (star→steps σ)) τ fin
  ... | zero , _ , zero = final-det fin' fin
  ... | suc _ , _ , suc st _ = ⊥-elim (final-nostep fin' st)

  {- a machine terminates with at most one observation -}
  terminates-det : ∀ {o₁ o₂} → Terminates L o₁ → Terminates L o₂ → o₁ ≡ o₂
  terminates-det (_ , σ₁ , f₁) (_ , σ₂ , f₂) = final-unique σ₁ f₁ (proj₂ (star→steps σ₂)) f₂

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

{- a target state from which the target reaches a state matching s₁ -}
Reach : ∀ {S₁ : Set} (L₂ : Machine) → (S₁ → State L₂ → Set) → S₁ → State L₂ → Set
Reach L₂ R s₁ s₂ = Σ[ t ∈ State L₂ ] Star L₂ s₂ t × R s₁ t

module _ {S₁ : Set} {L₂ : Machine} {R : S₁ → State L₂ → Set} where

  reach : ∀ {s₁ s₂} → R s₁ s₂ → Reach L₂ R s₁ s₂
  reach m = _ , ε , m

  {- one target step to a match, or one step and then on to a match -}
  steps₁ : ∀ {s₁ s₂ s₂'} → Step L₂ s₂ s₂' → R s₁ s₂' → Answers L₂ R (next s₁) s₂
  steps₁ st = steps (step⁺ st)

  after : ∀ {s₁ s₂ s₂'} → Step L₂ s₂ s₂' → Reach L₂ R s₁ s₂' → Answers L₂ R (next s₁) s₂
  after st (_ , σ , m) = steps (plus st σ) m

  {- both machines continue with related things (next?), or both stop -}
  next?-reach : ∀ {A B : Set} {P : A → B → Set} {o f g ma mb s₂} → M.Pointwise P ma mb
    → (∀ {a b} → P a b → Reach L₂ R (f a) (g b)) → Machine.step L₂ s₂ ≡ next? o g mb
    → Answers L₂ R (next? o f ma) s₂
  next?-reach (M.just p) h st = after st (h p)
  next?-reach M.nothing h st = stops st

  next?-answers : ∀ {A B : Set} {P : A → B → Set} {o f g ma mb s₂} → M.Pointwise P ma mb
    → (∀ {a b} → P a b → R (f a) (g b)) → Machine.step L₂ s₂ ≡ next? o g mb
    → Answers L₂ R (next? o f ma) s₂
  next?-answers p h = next?-reach p (λ q → reach (h q))

  {- the same thing in both -}
  next?-same : ∀ {A : Set} {o f g} {ma : Maybe A} {s₂} → (∀ a → Reach L₂ R (f a) (g a))
    → Machine.step L₂ s₂ ≡ next? o g ma → Answers L₂ R (next? o f ma) s₂
  next?-same {ma = just a} h st = after st (h a)
  next?-same {ma = nothing} h st = stops st

{-

  Simulations in which both machines move between related states
  (Both): from related states, either the source stops and the target
  runs to a final state with the same observation, or both take one or
  more steps, to related states or to final states with the same
  observation. This is a forward simulation in which the source may lag
  behind the target (lag-fsim, proof/Framework/Simulation.agda), so it
  gives the end theorem. Related states can be found by running either
  machine ahead (pre₁, pre₂).

-}

module proof.Framework.Both (Obs : Set) where

open import Framework.Smallstep Obs
open import proof.Framework.Smallstep Obs
open import proof.Framework.Simulation Obs

open import Data.Empty using (⊥-elim)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)

module _ {L₁ L₂ : Machine} (R : State L₁ → State L₂ → Set) where

  data Both (s₁ : State L₁) (s₂ : State L₂) : Set where
    halt : ∀ {o t} → Final L₁ s₁ o → Star L₂ s₂ t → Final L₂ t o → Both s₁ s₂
    move : ∀ {s₁' s₂'} → Plus L₁ s₁ s₁' → Plus L₂ s₂ s₂' → R s₁' s₂' → Both s₁ s₂
    ends : ∀ {o t₁ t₂} → Plus L₁ s₁ t₁ → Final L₁ t₁ o → Plus L₂ s₂ t₂ → Final L₂ t₂ o → Both s₁ s₂

  private
    R' : State L₁ → State L₂ → Set
    R' s₁ s₂ = R s₁ s₂ ⊎ Σ[ o ∈ Obs ] Final L₁ s₁ o × Final L₂ s₂ o

    fin : ∀ {i o s₂ t} → Star L₂ s₂ t → Final L₂ t o → Answers≺ L₂ (Lag L₁ R') i (stop o) s₂
    fin ε f = stops f
    fin (st ◅ σ) f = runs (plus st σ) f

  both-fsim : R (start L₁) (start L₂) → (∀ {s₁ s₂} → R s₁ s₂ → Both s₁ s₂) → FSim L₁ L₂
  both-fsim m₀ sim = lag-fsim (lag-now (inj₁ m₀)) go
    where
    go : ∀ {i s₁ s₂} → R' s₁ s₂ → Answers≺ L₂ (Lag L₁ R') i (Machine.step L₁ s₁) s₂
    go (inj₂ (_ , f₁ , f₂)) = answers-at f₁ (stops f₂)
    go (inj₁ m) with sim m
    ... | halt f₁ σ f₂ = answers-at f₁ (fin σ f₂)
    ... | move (plus st σ) π m' = answers-at st (steps π (proj₂ (lag-star σ (inj₁ m'))))
    ... | ends (plus st σ) f₁ π f₂ = answers-at st (steps π (proj₂ (lag-star σ (inj₂ (_ , f₁ , f₂)))))

  {- the target runs ahead -}
  pre₂ : ∀ {s₁ s₂ s₂'} → Step L₂ s₂ s₂' → Both s₁ s₂' → Both s₁ s₂
  pre₂ st (halt f₁ σ f₂) = halt f₁ (st ◅ σ) f₂
  pre₂ st (move π₁ π₂ m) = move π₁ (plus st (plus→star π₂)) m
  pre₂ st (ends π₁ f₁ π₂ f₂) = ends π₁ f₁ (plus st (plus→star π₂)) f₂

  {- the source runs ahead, while the target can step -}
  pre₁ : ∀ {s₁ s₁' s₂ s₂'} → Step L₁ s₁ s₁' → Step L₂ s₂ s₂' → Both s₁' s₂ → Both s₁ s₂
  pre₁ st st₂ (halt f₁ ε f₂) = ⊥-elim (final-nostep {L = L₂} f₂ st₂)
  pre₁ st st₂ (halt f₁ (st' ◅ σ) f₂) = ends (plus st ε) f₁ (plus st' σ) f₂
  pre₁ st st₂ (move π₁ π₂ m) = move (plus st (plus→star π₁)) π₂ m
  pre₁ st st₂ (ends π₁ f₁ π₂ f₂) = ends (plus st (plus→star π₁)) f₁ π₂ f₂

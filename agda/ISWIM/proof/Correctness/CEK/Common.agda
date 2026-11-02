{-

  A lemma shared by the simulation proofs of the typed closure-conversion
  passes (proof/Correctness/CEK/*Sim.agda): two machines that both stop
  with the same observation or both step to related states (Lock).

-}

module proof.Correctness.CEK.Common where

open import proof.Semantics.CEK.Smallstep

{- two machines that both stop with the same observation or both step to
   related states (for project, where both decide the same equation) -}
data Lock {S₁ S₂ : Set} (R : S₁ → S₂ → Set) : Next S₁ → Next S₂ → Set where
  same-stop : ∀ {o} → Lock R (stop o) (stop o)
  same-next : ∀ {s₁ s₂} → R s₁ s₂ → Lock R (next s₁) (next s₂)

lock : ∀ {S₁ : Set} {L₂ : Machine} {R : S₁ → State L₂ → Set} {a s₂}
  → Lock R a (Machine.step L₂ s₂) → Answers L₂ R a s₂
lock {L₂ = L₂} {s₂ = s₂} l with Machine.step L₂ s₂ in eq
lock same-stop | stop o = stops eq
lock (same-next m) | next s = steps₁ eq m

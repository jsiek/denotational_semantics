{-

  A clocked interpreter for FlatClosμ (Mu/Language/FlatClos.agda), as the one
  for EnvClosμ (Mu/Semantics/ClockedInterpreters/EnvClos.agda), with the same values:
  code is a value, pack pairs it with an environment, and callc L M runs
  the code of the closure L with its environment and the argument M,
  after both are evaluated.

-}

module Mu.Semantics.ClockedInterpreters.FlatClos where

open import Mu.Language.Type
open import Mu.Language.FlatClos
open import Mu.Framework.AllUtil using (All; []; _∷_; lookup)
open import Semantics.Interp.Clock

open import Data.List using ([]; _∷_)
open import Data.Nat using (ℕ; zero; suc)

open import Mu.Semantics.ClockedInterpreters.Values (λ Δ A B → Tm (A ∷ tup Δ ∷ []) B) public

eval : ∀ {Γ A} → ℕ → Env Γ → Tm Γ A → Result (Val A)
evals : ∀ {Γ Δ} → ℕ → Env Γ → All (Tm Γ) Δ → Result (All Val Δ)
call : ∀ {A B} → ℕ → Val (A ⇒ B) → Val A → Result (Val B)

eval ck ρ (` x) = ret (lookup ρ x)
eval ck ρ (code N) = ret (code N)
eval ck ρ (pack L M) = do c ← eval ck ρ L; e ← eval ck ρ M; ret (pack c e)
eval ck ρ (callc L M) = do f ← eval ck ρ L; w ← eval ck ρ M; call ck f w
eval ck ρ (lit B c) = ret (const c)
eval ck ρ (tuple Ms) = do vs ← evals ck ρ Ms; ret (tup vs)
eval ck ρ (get i M) = do v ← eval ck ρ M; ret (nth i v)
eval ck ρ (inl M) = do v ← eval ck ρ M; ret (inl v)
eval ck ρ (inr M) = do v ← eval ck ρ M; ret (inr v)
eval ck ρ (case L M N) = eval ck ρ L >>= λ u → either u (λ v → eval ck (v ∷ ρ) M) (λ v → eval ck (v ∷ ρ) N)
eval ck ρ (prim p L M) = do v ← eval ck ρ L; w ← eval ck ρ M; ret (δ p v w)
eval ck ρ (let′ M N) = do v ← eval ck ρ M; eval ck (v ∷ ρ) N
eval ck ρ (fold M) = do v ← eval ck ρ M; ret (fold v)
eval ck ρ (unfold M) = do v ← eval ck ρ M; ret (unfold-v v)

evals ck ρ [] = ret []
evals ck ρ (M ∷ Ms) = do v ← eval ck ρ M; vs ← evals ck ρ Ms; ret (v ∷ vs)

call zero f w = timeout
call (suc ck) (pack (code N) e) w = eval ck (w ∷ e ∷ []) N

sem : ∀ {A} → Tm [] A → Semantics
sem {A} M = semantics (Val A) obs (λ ck → eval ck [] M)

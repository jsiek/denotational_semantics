{-

  A clocked interpreter for ISWIMμ (Mu/Language/ISWIM.agda), as the one
  for ISWIMᵀ (Semantics/Interp/Typed/ISWIM.agda; see the design note in
  Semantics/Interp/Clock.agda): call by value, left to right, and only
  a call ticks the clock. Values and environments are typed
  (Mu/Semantics/Interp/Values.agda), so the interpreter is a total
  function that never errs: it only times out. A function value is the
  closure of its body and the whole environment; unfold takes a fold
  apart.

-}

module Mu.Semantics.Interp.ISWIM where

open import Mu.Language.Type
open import Mu.Language.ISWIM
open import Mu.Framework.AllUtil using (All; []; _∷_; lookup)
open import Semantics.Interp.Clock

open import Data.List using ([]; _∷_)
open import Data.Nat using (ℕ; zero; suc)

open import Mu.Semantics.Interp.Values (λ Δ A B → Tm (A ∷ Δ) B) public

eval : ∀ {Γ A} → ℕ → Env Γ → Tm Γ A → Result (Val A)
evals : ∀ {Γ Δ} → ℕ → Env Γ → All (Tm Γ) Δ → Result (All Val Δ)
call : ∀ {A B} → ℕ → Val (A ⇒ B) → Val A → Result (Val B)

eval ck ρ (` x) = ret (lookup ρ x)
eval ck ρ (lam N) = ret (pack (code N) (tup ρ))
eval ck ρ (app L M) = do f ← eval ck ρ L; w ← eval ck ρ M; call ck f w
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
call (suc ck) (pack (code N) (tup ρ)) w = eval ck (w ∷ ρ) N

sem : ∀ {A} → Tm [] A → Semantics
sem {A} M = semantics (Val A) obs (λ ck → eval ck [] M)

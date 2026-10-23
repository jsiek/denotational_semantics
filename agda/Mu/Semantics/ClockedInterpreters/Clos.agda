{-

  A clocked interpreter for Closμ (Mu/Language/Clos.agda), as the one
  for ISWIMμ (Mu/Semantics/ClockedInterpreters/ISWIM.agda), except that a closure
  evaluates its free variables, left to right, and keeps their values
  as its environment.

-}

module Mu.Semantics.ClockedInterpreters.Clos where

open import Mu.Language.Type
open import Mu.Language.Clos
open import Mu.Framework.AllUtil using (All; []; _∷_; lookup)
open import Semantics.Interp.Clock

open import Data.List using ([]; _∷_)
open import Data.Nat using (ℕ; zero; suc)

open import Mu.Semantics.ClockedInterpreters.Values (λ Δ A B → Tm (A ∷ Δ) B) public

eval : ∀ {Γ A} → ℕ → Env Γ → Tm Γ A → Result (Val A)
evals : ∀ {Γ Δ} → ℕ → Env Γ → All (Tm Γ) Δ → Result (All Val Δ)
call : ∀ {A B} → ℕ → Val (A ⇒ B) → Val A → Result (Val B)

eval ck ρ (` x) = ret (lookup ρ x)
eval ck ρ (clos N Ms) = do vs ← evals ck ρ Ms; ret (pack (code N) (tup vs))
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
call (suc ck) (pack (code N) (tup vs)) w = eval ck (w ∷ vs) N

sem : ∀ {A} → Tm [] A → Semantics
sem {A} M = semantics (Val A) obs (λ ck → eval ck [] M)

{-

  A clocked interpreter for GlobalFunμ (Mu/Language/GlobalFun.agda), as the one
  for Clos5ᵀ (Semantics/Interp/Typed/Clos5.agda): a program runs with
  its table of definitions, the code of a closure is a reference to a
  definition (fun-ref f evaluates to code f), and a call runs definition
  f. A reference to a missing definition cannot be written, so a call
  cannot fail.

  Monμ has no interpreter of its own: a Monμ program runs as its
  embedding into GlobalFunμ (Mu/Language/Mon.agda).

-}

module Mu.Semantics.ClockedInterpreters.GlobalFun where

open import Mu.Language.Type
open import Mu.Language.GlobalFun
open import Mu.Framework.AllUtil using (All; []; _∷_; lookup)
open import Semantics.Interp.Clock

open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)

import Mu.Semantics.ClockedInterpreters.Values
module Vals (Σ : List DSig) = Mu.Semantics.ClockedInterpreters.Values (λ Δ A B → Σ ∋ sig Δ A B)

module _ {Σ : List DSig} (ds : All (Code Σ) Σ) where
  open Vals Σ

  eval : ∀ {Γ A} → ℕ → Env Γ → Tm Σ Γ A → Result (Val A)
  evals : ∀ {Γ Δ} → ℕ → Env Γ → All (Tm Σ Γ) Δ → Result (All Val Δ)
  call : ∀ {A B} → ℕ → Val (A ⇒ B) → Val A → Result (Val B)

  eval ck ρ (` x) = ret (lookup ρ x)
  eval ck ρ (fun-ref f) = ret (code f)
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
  call (suc ck) (pack (code f) e) w = eval ck (w ∷ e ∷ []) (lookup ds f)

sem : ∀ {A} → Program A → Semantics
sem {A} (program {Σ} ds M) = semantics (Val A) obs (λ ck → eval ds ck [] M)
  where open Vals Σ

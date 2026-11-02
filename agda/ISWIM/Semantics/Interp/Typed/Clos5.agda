{-

  A clocked interpreter for Clos5ᵀ (Language/Typed/Clos5.agda), as the
  one for Clos4ᵀ (Semantics/Interp/Typed/Clos4.agda), except that a
  program runs with its table of definitions: the code of a closure is
  a reference to a definition (fun-ref f evaluates to code f), and a
  call runs definition f. A reference to a missing definition cannot be
  written, so a call cannot fail.

  Monᵀ has no interpreter of its own: a Monᵀ program runs as its
  embedding into Clos5ᵀ (Language/Typed/Mon.agda).

-}

module Semantics.Interp.Typed.Clos5 where

open import Language.Typed.Type
open import Language.Typed.Clos5
open import Semantics.Interp.Clock
open import Framework.Lookup using (_!_)

open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Vec using (Vec; []; _∷_)

import Semantics.Interp.Typed.Values
module Vals (Σ : List ℕ) = Semantics.Interp.Typed.Values (Σ ∋_)

module _ {Σ : List ℕ} (ds : All (Code Σ) Σ) where
  open Vals Σ

  eval : ∀ {Γ A} → ℕ → Env Γ → Tm Σ Γ A → Result (Val A)
  evals : ∀ {Γ n} → ℕ → Env Γ → Vec (Tm Σ Γ Any) n → Result (Vec (Val Any) n)
  call : ℕ → Val ⟪ fun ⟫ → Val Any → Result (Val Any)

  eval ck ρ (` x) = ret (ρ ! x)
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
  eval ck ρ (inject G M) = do v ← eval ck ρ M; ret (dyn G v)
  eval ck ρ (project t M) = eval ck ρ M >>= project? t

  evals ck ρ [] = ret []
  evals ck ρ (M ∷ Ms) = do v ← eval ck ρ M; vs ← evals ck ρ Ms; ret (v ∷ vs)

  call zero f w = timeout
  call (suc ck) (pack (code f) e) w = eval ck (w ∷ e ∷ []) (ds ! f)

sem : Program → Semantics
sem (program {Σ} ds M) = semantics (Val Any) obs (λ ck → eval ds ck [] M)
  where open Vals Σ

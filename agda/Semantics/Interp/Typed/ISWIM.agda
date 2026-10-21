{-

  A clocked interpreter for ISWIMᵀ (Language/Typed/ISWIM.agda), as the
  one for ISWIM (Semantics/Interp/ISWIM.agda; see the design note in
  Semantics/Interp/Clock.agda): call by value, left to right, and only
  a call ticks the clock. Values and environments are typed
  (Semantics/Interp/Typed/Values.agda), so the interpreter is a total
  function that errs only where a project fails. A function value is
  the closure of its body and the whole environment.

-}

module Semantics.Interp.Typed.ISWIM where

open import Language.Typed.Type
open import Language.Typed.ISWIM
open import Semantics.Interp.Clock

open import Data.Nat using (ℕ; zero; suc)
open import Data.Vec using (Vec; []; _∷_; lookup)

open import Semantics.Interp.Typed.Values (λ k → Tm (suc k) Any) public
  hiding (Env)

Env : ℕ → Set
Env k = Vec (Val Any) k

eval : ∀ {k A} → ℕ → Env k → Tm k A → Result (Val A)
evals : ∀ {k n} → ℕ → Env k → Vec (Tm k Any) n → Result (Vec (Val Any) n)
call : ℕ → Val ⟪ fun ⟫ → Val Any → Result (Val Any)

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
eval ck ρ (inject G M) = do v ← eval ck ρ M; ret (dyn G v)
eval ck ρ (project t M) = eval ck ρ M >>= project? t

evals ck ρ [] = ret []
evals ck ρ (M ∷ Ms) = do v ← eval ck ρ M; vs ← evals ck ρ Ms; ret (v ∷ vs)

call zero f w = timeout
call (suc ck) (pack (code N) (tup ρ)) w = eval ck (w ∷ ρ) N

sem : Tm 0 Any → Semantics
sem M = semantics (Val Any) obs (λ ck → eval ck [] M)

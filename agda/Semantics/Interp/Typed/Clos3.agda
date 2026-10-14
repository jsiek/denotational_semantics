{-

  A clocked interpreter for Clos3ᵀ (Language/Typed/Clos3.agda), as the
  one for Clos2ᵀ (Semantics/Interp/Typed/Clos2.agda), except that the
  code of a closure runs with the argument and the tuple of its free
  variables, and that environments are typed by contexts.

-}

module Semantics.Interp.Typed.Clos3 where

open import Language.Typed.Type
open import Language.Typed.Clos3
open import Semantics.Interp.Clock

open import Data.List using ([]; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Vec using (Vec; []; _∷_)
open import Data.List.Relation.Unary.All using ([]; _∷_)

open import Semantics.Interp.Typed.Values (λ n → Tm (Any ∷ ⟪ tup n ⟫ ∷ []) Any) public

eval : ∀ {Γ A} → ℕ → Env Γ → Tm Γ A → Result (Val A)
evals : ∀ {Γ n} → ℕ → Env Γ → Vec (Tm Γ Any) n → Result (Vec (Val Any) n)
call : ℕ → Val ⟪ fun ⟫ → Val Any → Result (Val Any)

eval ck ρ (` x) = ret (ρ ! x)
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
eval ck ρ (inject G M) = do v ← eval ck ρ M; ret (dyn G v)
eval ck ρ (project t M) = eval ck ρ M >>= project? t

evals ck ρ [] = ret []
evals ck ρ (M ∷ Ms) = do v ← eval ck ρ M; vs ← evals ck ρ Ms; ret (v ∷ vs)

call zero f w = timeout
call (suc ck) (pack (code N) e) w = eval ck (w ∷ e ∷ []) N

sem : Tm [] Any → Semantics
sem M = semantics (Val Any) obs (λ ck → eval ck [] M)

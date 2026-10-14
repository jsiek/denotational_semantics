{-

  A clocked interpreter for Impᵀ (Language/Typed/Imp.agda), the output
  of typed lift locals. A body runs in a frame typed by its context, the
  values of the slots assigned so far (Env Δ); x := e₁; e₂ (assign)
  assigns the value of e₁ to the next slot, which e₂ sees, and case
  assigns the payload to the next slot. An atom is read from the frame
  and cannot fail. The values are those of Clos5ᵀ
  (Semantics/Interp/Typed/Clos5.agda), and as there a call runs
  definition f, in a frame of its environment (slot 0) and argument
  (slot 1). Simple expressions are shared with CFGᵀ
  (Semantics/Interp/Typed/CFG.agda). See the design note in
  Semantics/Interp/Clock.agda.

-}

module Semantics.Interp.Typed.Imp where

open import Language.Typed.Type
open import Language.Typed.Imp
open import Semantics.Interp.Clock
open import Semantics.Interp.Typed.Clos5 using (module Vals; def)

open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Vec using (Vec; map)

module _ {Σ : List ℕ} where
  open Vals Σ

  atom : ∀ {Δ A} → Env Δ → Atm Σ Δ A → Val A
  atom φ (var x) = φ ! x
  atom φ (lit B c) = const c
  atom φ (ref f) = code f

  {- a simple expression, with call the calls -}
  eval-simple : ∀ {Δ A} → (Val ⟪ fun ⟫ → Val Any → Result (Val Any)) → Env Δ → Simple Σ Δ A → Result (Val A)
  eval-simple call φ (atm a) = ret (atom φ a)
  eval-simple call φ (pack a b) = ret (pack (atom φ a) (atom φ b))
  eval-simple call φ (callc a b) = call (atom φ a) (atom φ b)
  eval-simple call φ (tuple as) = ret (tup (map (atom φ) as))
  eval-simple call φ (get i a) = ret (nth i (atom φ a))
  eval-simple call φ (inl a) = ret (inl (atom φ a))
  eval-simple call φ (inr a) = ret (inr (atom φ a))
  eval-simple call φ (prim p a b) = ret (δ p (atom φ a) (atom φ b))
  eval-simple call φ (inject G a) = ret (dyn G (atom φ a))
  eval-simple call φ (project t a) = project? t (atom φ a)

module _ {Σ : List ℕ} (ds : All (λ n → Exp Σ (Any ∷ ⟪ tup n ⟫ ∷ []) Any) Σ) where
  open Vals Σ

  eval : ∀ {Δ A} → ℕ → Env Δ → Exp Σ Δ A → Result (Val A)
  call : ℕ → Val ⟪ fun ⟫ → Val Any → Result (Val Any)

  eval ck φ (simple s) = eval-simple (call ck) φ s
  eval ck φ (assign e₁ e₂) = do v ← eval ck φ e₁; eval ck (v ∷ φ) e₂
  eval ck φ (case a e₁ e₂) = either (atom φ a) (λ v → eval ck (v ∷ φ) e₁) (λ v → eval ck (v ∷ φ) e₂)

  call zero f w = timeout
  call (suc ck) (pack (code f) e) w = eval ck (w ∷ e ∷ []) (def ds f)

sem : Program → Semantics
sem (program {Σ} ds e) = semantics (Val Any) obs (λ ck → eval ds ck [] e)
  where open Vals Σ

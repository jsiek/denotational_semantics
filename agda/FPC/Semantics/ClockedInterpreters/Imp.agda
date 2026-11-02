{-

  A clocked interpreter for Impμ (Mu/Language/Imp.agda), the output of
  lift locals, as the one for Impᵀ (Semantics/Interp/Typed/Imp.agda). A
  body runs in a frame typed by its context, the values of the slots
  assigned so far (Env Δ); assign e₁ e₂ assigns the value of e₁ to the
  next slot, which e₂ sees, and case assigns the payload to the next
  slot. An atom is read from the frame. The values are those of GlobalFunμ
  (Mu/Semantics/ClockedInterpreters/GlobalFun.agda), and as there a call runs definition
  f, in a frame of its argument and environment. Simple expressions are
  shared with CFGμ (Mu/Semantics/ClockedInterpreters/CFG.agda).

-}

module Mu.Semantics.ClockedInterpreters.Imp where

open import Mu.Language.Type
open import Mu.Language.Imp
open import Mu.Framework.AllUtil using (All; []; _∷_; lookup; map)
open import Semantics.Interp.Clock
open import Mu.Semantics.ClockedInterpreters.GlobalFun using (module Vals)

open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)

module _ {Σ : List DSig} where
  open Vals Σ

  atom : ∀ {Δ A} → Env Δ → Atm Σ Δ A → Val A
  atom φ (var x) = lookup φ x
  atom φ (lit B c) = const c
  atom φ (ref f) = code f

  {- a simple expression, with call the calls -}
  eval-simple : ∀ {Δ A} → (∀ {A B} → Val (A ⇒ B) → Val A → Result (Val B)) → Env Δ → Simple Σ Δ A → Result (Val A)
  eval-simple call φ (atm a) = ret (atom φ a)
  eval-simple call φ (pair a b) = ret (pack (atom φ a) (atom φ b))
  eval-simple call φ (callc a b) = call (atom φ a) (atom φ b)
  eval-simple call φ (tuple as) = ret (tup (map (atom φ) as))
  eval-simple call φ (get i a) = ret (nth i (atom φ a))
  eval-simple call φ (inl a) = ret (inl (atom φ a))
  eval-simple call φ (inr a) = ret (inr (atom φ a))
  eval-simple call φ (prim p a b) = ret (δ p (atom φ a) (atom φ b))
  eval-simple call φ (fold a) = ret (fold (atom φ a))
  eval-simple call φ (unfold a) = ret (unfold-v (atom φ a))

module _ {Σ : List DSig} (ds : All (λ s → Exp Σ (Args s) (DSig.cod s)) Σ) where
  open Vals Σ

  eval : ∀ {Δ A} → ℕ → Env Δ → Exp Σ Δ A → Result (Val A)
  call : ∀ {A B} → ℕ → Val (A ⇒ B) → Val A → Result (Val B)

  eval ck φ (simple s) = eval-simple (call ck) φ s
  eval ck φ (assign e₁ e₂) = do v ← eval ck φ e₁; eval ck (v ∷ φ) e₂
  eval ck φ (case a e₁ e₂) = either (atom φ a) (λ v → eval ck (v ∷ φ) e₁) (λ v → eval ck (v ∷ φ) e₂)

  call zero f w = timeout
  call (suc ck) (pack (code f) e) w = eval ck (w ∷ e ∷ []) (lookup ds f)

sem : ∀ {A} → Program A → Semantics
sem {A} (program {Σ} ds e) = semantics (Val A) obs (λ ck → eval ds ck [] e)
  where open Vals Σ

{-

  A clocked interpreter for Impμ (FPC/Language/Imp.agda), the output of
  lift locals, as the one for Impᵀ (ISWIM/Semantics/Interp/Typed/Imp.agda),
  in a fixed frame. A body runs in a frame that holds a value for each
  initialized slot (Fr Δ I, FPC/Framework/Slots.agda); assign x e₁ e₂
  writes the value of e₁ to slot x and runs e₂, and case writes the
  payload to the slot of its branch. An atom reads its slot. The values
  are those of GlobalFunμ (FPC/Semantics/ClockedInterpreters/GlobalFun.agda),
  and as there a call runs definition f, in a frame of its argument and
  environment. Simple expressions are shared with CFGμ
  (FPC/Semantics/ClockedInterpreters/CFG.agda).

-}

module FPC.Semantics.ClockedInterpreters.Imp where

open import FPC.Language.Type
open import FPC.Language.Imp
open import FPC.Framework.AllUtil using (All; []; _∷_; lookup; map)
open import FPC.Framework.Slots using (Slots; read; write; empty; params)
open import Semantics.Interp.Clock
open import FPC.Semantics.ClockedInterpreters.GlobalFun using (module Vals)

open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)

module _ {Σ : List DSig} where
  open Vals Σ

  {- the values of a frame -}
  Fr : (Δ : Ctx) → Inits Δ → Set
  Fr = Slots Val

  atom : ∀ {Δ I A} → Fr Δ I → Atm Σ Δ I A → Val A
  atom φ (var x i) = read φ x i
  atom φ (lit B c) = const c
  atom φ (ref f) = code f

  {- a simple expression, with call the calls -}
  eval-simple : ∀ {Δ I A} → (∀ {A B} → Val (A ⇒ B) → Val A → Result (Val B))
    → Fr Δ I → Simple Σ Δ I A → Result (Val A)
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

module _ {Σ : List DSig}
  (ds : All (λ s → Body Σ (Args s) (DSig.cod s)) Σ) where
  open Vals Σ

  eval : ∀ {Δ I A} → ℕ → Fr Δ I → Exp Σ Δ I A → Result (Val A)
  run : ∀ {Δ A B} → ℕ → Body Σ (A ∷ tup Δ ∷ []) B → Val (tup Δ) → Val A
    → Result (Val B)
  call : ∀ {A B} → ℕ → Val (A ⇒ B) → Val A → Result (Val B)

  eval ck φ (simple s) = eval-simple (call ck) φ s
  eval ck φ (assign x _ e₁ e₂) =
    do v ← eval ck φ e₁; eval ck (write φ x v) e₂
  eval ck φ (case a x _ y _ e₁ e₂) =
    either (atom φ a) (λ v → eval ck (write φ x v) e₁)
      (λ v → eval ck (write φ y v) e₂)

  run ck (body Δ p e) v w = eval ck (params p v w) e

  call zero f w = timeout
  call (suc ck) (pack (code f) e) w = run ck (lookup ds f) e w

sem : ∀ {A} → Program A → Semantics
sem {A} (program {Σ} ds (body Δ p e)) =
  semantics (Val A) obs (λ ck → eval ds ck (empty Δ) e)
  where open Vals Σ

{-

  A machine for Impμ (Mu/Language/Imp.agda), with the values of the
  GlobalFunμ machine (Mu/Semantics/AbstractMachines/GlobalFun.agda), as the Impᵀ machine
  (Semantics/CEK/Typed/Imp.agda). An expression runs in a frame of
  slots typed by its frame context Δ (slot 0 last), so an atom always
  has a value (atom).

  A simple expression takes one step (run): its operands are atoms, so
  it gives a value or calls a closure; nothing fails. Its value goes to
  the continuation (cont): x := □; e₂ (assignK) runs e₂ with the value
  in the next slot, and the empty continuation stops with its
  observation. case assigns the payload of an injection to the next slot
  and runs a branch. A call runs the definition in a frame of its
  argument and environment, with the caller's continuation. The simple
  expressions and run are shared with the CFGμ machine.

-}

module Mu.Semantics.AbstractMachines.Imp where

open import Mu.Language.Type
open import Mu.Language.Imp
open import Mu.Framework.AllUtil using (All; []; _∷_; lookup; map)
open import Semantics.CEK.Smallstep using (Machine; Next; next; stop; machine)
open import Mu.Semantics.AbstractMachines.GlobalFun
  using (Val; code; pack; const; tup; inl; inr; fold; Env; obs; int; elems; choose; unfoldᵥ; δᵀ) public

open import Data.List using (List; []; _∷_)

Frame : List DSig → Ctx → Set
Frame = Env

module _ {Σ : List DSig} where

  {- the value of an atom in the frame -}
  atom : ∀ {Δ A} → Frame Σ Δ → Atm Σ Δ A → Val Σ A
  atom φ (var x) = lookup φ x
  atom φ (lit B c) = const c
  atom φ (ref f) = code f

  {- what a simple expression gives -}
  data Res : Type → Set where
    value : ∀ {A} → Val Σ A → Res A
    call : ∀ {A B} → Val Σ (A ⇒ B) → Val Σ A → Res B

  run : ∀ {Δ A} → Simple Σ Δ A → Frame Σ Δ → Res A
  run (atm a) φ = value (atom φ a)
  run (pack a b) φ = value (pack (atom φ a) (atom φ b))
  run (callc f a) φ = call (atom φ f) (atom φ a)
  run (tuple as) φ = value (tup (map (atom φ) as))
  run (get i a) φ = value (lookup (elems (atom φ a)) i)
  run (inl a) φ = value (inl (atom φ a))
  run (inr a) φ = value (inr (atom φ a))
  run (prim p a b) φ = value (δᵀ p (int (atom φ a)) (int (atom φ b)))
  run (fold a) φ = value (fold (atom φ a))
  run (unfold a) φ = value (unfoldᵥ (atom φ a))

data Cont (Σ : List DSig) : Type → Set where
  halt : ∀ {A} → Cont Σ A
  assignK : ∀ {Δ A B} → Exp Σ (A ∷ Δ) B → Frame Σ Δ → Cont Σ B → Cont Σ A   {- x := □; e₂ -}

data State (Σ : List DSig) : Set where
  eval : ∀ {Δ A} → Exp Σ Δ A → Frame Σ Δ → Cont Σ A → State Σ

{- the machine for a program with the definitions ds -}
module _ {Σ : List DSig} (ds : All (λ s → Exp Σ (Args s) (DSig.cod s)) Σ) where

  cont : ∀ {A} → Val Σ A → Cont Σ A → Next (State Σ)
  cont v halt = stop (obs v)
  cont v (assignK e φ κ) = next (eval e (v ∷ φ) κ)

  res : ∀ {A} → Res A → Cont Σ A → Next (State Σ)
  res (value v) κ = cont v κ
  res (call (pack (code f) e) w) κ = next (eval (lookup ds f) (w ∷ e ∷ []) κ)

  step : State Σ → Next (State Σ)
  step (eval (simple s) φ κ) = res (run s φ) κ
  step (eval (assign e₁ e₂) φ κ) = next (eval e₁ φ (assignK e₂ φ κ))
  step (eval (case a e₁ e₂) φ κ) =
    next (choose (atom φ a) (λ v → eval e₁ (v ∷ φ) κ) (λ v → eval e₂ (v ∷ φ) κ))

{- a program starts with main, in the empty frame -}
sem : ∀ {A} → Program A → Machine
sem (program ds e) = machine (State _) (step ds) (eval e [] halt)

{-

  A machine for Impᵀ (Language/Typed/Imp.agda), with the values of the
  Clos5ᵀ machine (Semantics/CEK/Typed/Clos5.agda). An expression runs
  in a frame of slots typed by its frame context Δ (Frame Δ, the values
  of the slots assigned so far, slot 0 last), so an atom always has a
  value (atom).

  A simple expression takes one step (run): its operands are atoms, so
  it gives a value, fails (a project to another flat type, the only
  error), or calls a closure. Its value goes to the continuation (cont):
  x := □; e₂ (assignK) runs e₂ with the value in the next slot, and
  the empty continuation stops with its observation. case assigns the
  payload of an injection to the next slot and runs a branch. A call
  runs the definition in a frame of its argument and environment, with
  the caller's continuation (which holds the caller's frame). The
  simple expressions and run are shared with the CFGᵀ machine
  (Semantics/CEK/Typed/CFG.agda).

-}

module Semantics.CEK.Typed.Imp where

open import Language.Typed.Type
open import Language.Typed.Imp
open import Framework.Lookup using (_!_)
open import Semantics.Observation using (o-error)
open import Semantics.CEK.Smallstep using (Machine; Next; next; stop; machine)
open import Semantics.CEK.Typed.Clos5
  using (Val; code; pack; const; tup; inl; inr; dyn; Env; obs; int; elems; choose; δᵀ; proj?) public

open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Vec using (Vec; lookup; map)

Frame : List ℕ → Ctx → Set
Frame = Env

module _ {Σ : List ℕ} where

  {- the value of an atom in the frame -}
  atom : ∀ {Δ A} → Frame Σ Δ → Atm Σ Δ A → Val Σ A
  atom φ (var x) = φ ! x
  atom φ (lit B c) = const c
  atom φ (ref f) = code f

  {- what a simple expression gives -}
  data Res : Ty → Set where
    value : ∀ {A} → Val Σ A → Res A
    fail : ∀ {A} → Res A
    call : Val Σ ⟪ fun ⟫ → Val Σ Any → Res Any

  ok? : ∀ {A} → Maybe (Val Σ A) → Res A
  ok? (just v) = value v
  ok? nothing = fail

  run : ∀ {Δ A} → Simple Σ Δ A → Frame Σ Δ → Res A
  run (atm a) φ = value (atom φ a)
  run (pack a b) φ = value (pack (atom φ a) (atom φ b))
  run (callc f a) φ = call (atom φ f) (atom φ a)
  run (tuple as) φ = value (tup (map (atom φ) as))
  run (get i a) φ = value (lookup (elems (atom φ a)) i)
  run (inl a) φ = value (inl (atom φ a))
  run (inr a) φ = value (inr (atom φ a))
  run (prim p a b) φ = value (δᵀ p (int (atom φ a)) (int (atom φ b)))
  run (inject G a) φ = value (dyn G (atom φ a))
  run (project t a) φ = ok? (proj? t (atom φ a))

data Cont (Σ : List ℕ) : Ty → Set where
  halt : Cont Σ Any
  assignK : ∀ {Δ A B} → Exp Σ (A ∷ Δ) B → Frame Σ Δ → Cont Σ B → Cont Σ A   {- x := □; e₂ -}

data State (Σ : List ℕ) : Set where
  eval : ∀ {Δ A} → Exp Σ Δ A → Frame Σ Δ → Cont Σ A → State Σ

{- the machine for a program with the definitions ds -}
module _ {Σ : List ℕ} (ds : All (λ n → Exp Σ (Any ∷ ⟪ tup n ⟫ ∷ []) Any) Σ) where

  cont : ∀ {A} → Val Σ A → Cont Σ A → Next (State Σ)
  cont v halt = stop (obs v)
  cont v (assignK e φ κ) = next (eval e (v ∷ φ) κ)

  res : ∀ {A} → Res A → Cont Σ A → Next (State Σ)
  res (value v) κ = cont v κ
  res fail κ = stop o-error
  res (call (pack (code f) e) w) κ = next (eval (ds ! f) (w ∷ e ∷ []) κ)

  step : State Σ → Next (State Σ)
  step (eval (simple s) φ κ) = res (run s φ) κ
  step (eval (assign e₁ e₂) φ κ) = next (eval e₁ φ (assignK e₂ φ κ))
  step (eval (case a e₁ e₂) φ κ) =
    next (choose (atom φ a) (λ v → eval e₁ (v ∷ φ) κ) (λ v → eval e₂ (v ∷ φ) κ))

{- a program starts with main, in the empty frame -}
sem : Program → Machine
sem (program ds e) = machine (State _) (step ds) (eval e [] halt)

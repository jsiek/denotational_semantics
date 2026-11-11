{-

  A machine for Impμ (FPC/Language/Imp.agda), with the values of the
  GlobalFunμ machine (FPC/Semantics/AbstractMachines/GlobalFun.agda), as the
  Impᵀ machine (ISWIM/Semantics/CEK/Typed/Imp.agda), in a fixed frame. An
  expression runs in a frame that holds a value for each initialized slot
  (Frame Σ Δ I, FPC/Framework/Slots.agda), so an atom always has a value
  (atom).

  A simple expression takes one step (run): its operands are atoms, so
  it gives a value or calls a closure; nothing fails. Its value goes to
  the continuation (cont): x := □; e₂ (assignK) writes the value to slot
  x of its frame and runs e₂, and the empty continuation stops with its
  observation. case writes the payload of an injection to the slot of
  its branch and runs the branch. A call runs the body of the definition
  in a frame of its argument and environment (params), with the caller's
  continuation. The simple expressions and run are shared with the CFGμ
  machine.

-}

module FPC.Semantics.AbstractMachines.Imp where

open import FPC.Language.Type
open import FPC.Language.Imp
open import FPC.Framework.AllUtil using (All; []; _∷_; lookup; map)
open import FPC.Framework.Slots using (Slots; read; write; empty; params)
open import Semantics.CEK.Smallstep using (Machine; Next; next; stop; machine)
open import FPC.Semantics.AbstractMachines.GlobalFun using (Val; code; pack;
  const; tup; inl; inr; fold; Env; obs; int; elems; choose; unfoldᵥ; δᵀ) public

open import Data.List using (List; []; _∷_)

{- the values of a frame of type Δ, with the slots I initialized -}
Frame : List DSig → (Δ : Ctx) → Inits Δ → Set
Frame Σ = Slots (Val Σ)

module _ {Σ : List DSig} where

  {- the value of an atom in the frame -}
  atom : ∀ {Δ I A} → Frame Σ Δ I → Atm Σ Δ I A → Val Σ A
  atom φ (var x i) = read φ x i
  atom φ (lit B c) = const c
  atom φ (ref f) = code f

  {- what a simple expression gives -}
  data Res : Type → Set where
    value : ∀ {A} → Val Σ A → Res A
    call : ∀ {A B} → Val Σ (A ⇒ B) → Val Σ A → Res B

  run : ∀ {Δ I A} → Simple Σ Δ I A → Frame Σ Δ I → Res A
  run (atm a) φ = value (atom φ a)
  run (pair a b) φ = value (pack (atom φ a) (atom φ b))
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
  {- x := □; e₂, in the frame φ -}
  assignK : ∀ {Δ I A B} (x : Δ ∋ A) → Frame Σ Δ I → Exp Σ Δ (I ⊕ x) B
    → Cont Σ B → Cont Σ A

data State (Σ : List DSig) : Set where
  eval : ∀ {Δ I A} → Exp Σ Δ I A → Frame Σ Δ I → Cont Σ A → State Σ

{- the machine for a program with the definitions ds -}
module _ {Σ : List DSig}
  (ds : All (λ s → Body Σ (Args s) (DSig.cod s)) Σ) where

  {- the start of a body, with its environment e and argument w -}
  enter : ∀ {Δ A B} → Body Σ (A ∷ tup Δ ∷ []) B → Val Σ (tup Δ) → Val Σ A
    → Cont Σ B → State Σ
  enter (body Δ p e) v w κ = eval e (params p v w) κ

  cont : ∀ {A} → Val Σ A → Cont Σ A → Next (State Σ)
  cont v halt = stop (obs v)
  cont v (assignK x φ e κ) = next (eval e (write φ x v) κ)

  res : ∀ {A} → Res A → Cont Σ A → Next (State Σ)
  res (value v) κ = cont v κ
  res (call (pack (code f) e) w) κ = next (enter (lookup ds f) e w κ)

  step : State Σ → Next (State Σ)
  step (eval (simple s) φ κ) = res (run s φ) κ
  step (eval (assign x _ e₁ e₂) φ κ) = next (eval e₁ φ (assignK x φ e₂ κ))
  step (eval (case a x _ y _ e₁ e₂) φ κ) =
    next
      (choose (atom φ a) (λ v → eval e₁ (write φ x v) κ)
        (λ v → eval e₂ (write φ y v) κ))

{- a program starts with main, in its frame with no slot initialized -}
sem : ∀ {A} → Program A → Machine
sem (program ds (body Δ p e)) =
  machine (State _) (step ds) (eval e (empty Δ) halt)

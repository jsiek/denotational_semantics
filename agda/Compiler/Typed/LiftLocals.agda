{-

  Typed lift locals (Monᵀ → Impᵀ): a let becomes an assignment to the
  next slot of the frame, and the variable a case binds the slot its
  payload is assigned to. The frame of a body is typed by its context,
  and a variable is the slot at its level, so the variables and atoms
  stay as they are; what the untyped pass computes (the slot of each
  variable, the frame's size) is in the types here, and select
  instructions reads the slots' levels off them.

-}

module Compiler.Typed.LiftLocals where

open import Language.Typed.Type
import Language.Typed.Mon as M
open import Language.Typed.Imp

open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_) renaming (map to All-map)

lift : ∀ {Σ Δ A} → M.Exp Σ Δ A → Exp Σ Δ A
lift (M.atm a) = simple (atm a)
lift (M.pack a b) = simple (pack a b)
lift (M.callc a b) = simple (callc a b)
lift (M.tuple as) = simple (tuple as)
lift (M.get i a) = simple (get i a)
lift (M.inl a) = simple (inl a)
lift (M.inr a) = simple (inr a)
lift (M.case a e₁ e₂) = case a (lift e₁) (lift e₂)
lift (M.prim p a b) = simple (prim p a b)
lift (M.let′ e₁ e₂) = assign (lift e₁) (lift e₂)
lift (M.inject G a) = simple (inject G a)
lift (M.project t a) = simple (project t a)

{- the pass, for a whole program -}
lift-program : M.Program → Program
lift-program (M.program ds e) = program (All-map lift ds) (lift e)

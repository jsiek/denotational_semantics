{-

  Lift locals (Monμ → Impμ), as typed lift locals
  (Compiler/LiftLocals.agda): a let becomes an assignment to the next
  slot of the frame, and the variable a case binds the slot its payload
  is assigned to. The variables and atoms stay as they are.

-}

module Mu.Compiler.LiftLocals where

open import Mu.Language.Type
import Mu.Language.Mon as M
open import Mu.Language.Imp
open import Mu.Framework.AllUtil using (All; []; _∷_) renaming (map to All-map)

open import Data.List using ([]; _∷_)

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
lift (M.fold a) = simple (fold a)
lift (M.unfold a) = simple (unfold a)

{- the pass, for a whole program -}
lift-program : ∀ {A} → M.Program A → Program A
lift-program (M.program ds e) = program (All-map lift ds) (lift e)

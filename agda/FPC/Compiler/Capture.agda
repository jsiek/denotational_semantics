{-

  Capture (FPC → Closμ), as typed capture (Compiler/Capture.agda):
  each function becomes a closure that captures every variable of its
  context, in order, so its body is unchanged: variable S x of the
  closure's code is the free variable x.

-}

module Mu.Compiler.Capture where

open import Mu.Language.Type
open import Mu.Language.FPC
import Mu.Language.Clos as T
open import Mu.Framework.AllUtil using (All; []; _∷_; tab)

capture : ∀ {Γ A} → Tm Γ A → T.Tm Γ A
encs : ∀ {Γ Δ} → All (Tm Γ) Δ → All (T.Tm Γ) Δ

capture (` x) = T.` x
capture (lam N) = T.clos (capture N) (tab T.`_)
capture (app L M) = T.app (capture L) (capture M)
capture (lit B c) = T.lit B c
capture (tuple Ms) = T.tuple (encs Ms)
capture (get i M) = T.get i (capture M)
capture (inl M) = T.inl (capture M)
capture (inr M) = T.inr (capture M)
capture (case L M N) = T.case (capture L) (capture M) (capture N)
capture (prim p L M) = T.prim p (capture L) (capture M)
capture (let′ M N) = T.let′ (capture M) (capture N)
capture (fold M) = T.fold (capture M)
capture (unfold M) = T.unfold (capture M)

encs [] = []
encs (M ∷ Ms) = capture M ∷ encs Ms

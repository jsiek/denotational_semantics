{-

  Typed capture (ISWIMᵀ → Clos2ᵀ): each function becomes a closure that
  captures every variable of its context, in order, so its body is
  unchanged: variable suc x of the closure's code is the free variable
  x. (The untyped pass captures the shortest prefix of the context that
  covers the body's variables; pruning is prune's job.)

-}

module Compiler.Capture where

open import Language.Typed.Type
open import Language.Typed.ISWIM
import Language.Typed.Clos2 as T

open import Data.Nat using (ℕ)
open import Data.Vec using (Vec; []; _∷_; tabulate)

capture : ∀ {k A} → Tm k A → T.Tm k A
encs : ∀ {k n} → Vec (Tm k Any) n → Vec (T.Tm k Any) n

capture (` x) = T.` x
capture {k} (lam N) = T.clos (capture N) (tabulate T.`_)
capture (app L M) = T.app (capture L) (capture M)
capture (lit B c) = T.lit B c
capture (tuple Ms) = T.tuple (encs Ms)
capture (get i M) = T.get i (capture M)
capture (inl M) = T.inl (capture M)
capture (inr M) = T.inr (capture M)
capture (case L M N) = T.case (capture L) (capture M) (capture N)
capture (prim p L M) = T.prim p (capture L) (capture M)
capture (let′ M N) = T.let′ (capture M) (capture N)
capture (inject G M) = T.inject G (capture M)
capture (project t M) = T.project t (capture M)

encs [] = []
encs (M ∷ Ms) = capture M ∷ encs Ms

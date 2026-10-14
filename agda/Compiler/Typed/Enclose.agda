{-

  Typed enclose (ISWIMᵀ → Clos2ᵀ): each function becomes a closure that
  captures every variable of its context, in order, so its body is
  unchanged: variable suc x of the closure's code is the free variable
  x. (The untyped pass captures the shortest prefix of the context that
  covers the body's variables; pruning is optimize's job.)

-}

module Compiler.Typed.Enclose where

open import Language.Typed.Type
open import Language.Typed.ISWIM
import Language.Typed.Clos2 as T

open import Data.Nat using (ℕ)
open import Data.Vec using (Vec; []; _∷_; tabulate)

enclose : ∀ {k A} → Tm k A → T.Tm k A
encs : ∀ {k n} → Vec (Tm k Any) n → Vec (T.Tm k Any) n

enclose (` x) = T.` x
enclose {k} (lam N) = T.clos (enclose N) (tabulate T.`_)
enclose (app L M) = T.app (enclose L) (enclose M)
enclose (lit B c) = T.lit B c
enclose (tuple Ms) = T.tuple (encs Ms)
enclose (get i M) = T.get i (enclose M)
enclose (inl M) = T.inl (enclose M)
enclose (inr M) = T.inr (enclose M)
enclose (case L M N) = T.case (enclose L) (enclose M) (enclose N)
enclose (prim p L M) = T.prim p (enclose L) (enclose M)
enclose (let′ M N) = T.let′ (enclose M) (enclose N)
enclose (inject G M) = T.inject G (enclose M)
enclose (project t M) = T.project t (enclose M)

encs [] = []
encs (M ∷ Ms) = enclose M ∷ encs Ms

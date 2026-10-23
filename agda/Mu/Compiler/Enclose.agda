{-

  Enclose (ISWIMμ → Closμ), as typed enclose (Compiler/Enclose.agda):
  each function becomes a closure that captures every variable of its
  context, in order, so its body is unchanged: variable S x of the
  closure's code is the free variable x.

-}

module Mu.Compiler.Enclose where

open import Mu.Language.Type
open import Mu.Language.ISWIM
import Mu.Language.Clos as T
open import Mu.Framework.AllUtil using (All; []; _∷_; tab)

enclose : ∀ {Γ A} → Tm Γ A → T.Tm Γ A
encs : ∀ {Γ Δ} → All (Tm Γ) Δ → All (T.Tm Γ) Δ

enclose (` x) = T.` x
enclose (lam N) = T.clos (enclose N) (tab T.`_)
enclose (app L M) = T.app (enclose L) (enclose M)
enclose (lit B c) = T.lit B c
enclose (tuple Ms) = T.tuple (encs Ms)
enclose (get i M) = T.get i (enclose M)
enclose (inl M) = T.inl (enclose M)
enclose (inr M) = T.inr (enclose M)
enclose (case L M N) = T.case (enclose L) (enclose M) (enclose N)
enclose (prim p L M) = T.prim p (enclose L) (enclose M)
enclose (let′ M N) = T.let′ (enclose M) (enclose N)
enclose (fold M) = T.fold (enclose M)
enclose (unfold M) = T.unfold (enclose M)

encs [] = []
encs (M ∷ Ms) = enclose M ∷ encs Ms

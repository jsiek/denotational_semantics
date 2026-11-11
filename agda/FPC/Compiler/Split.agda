{-

  Split (EnvClosμ → PairClosμ), as typed split (ISWIM/Compiler/Split.agda): a
  closure becomes a packed pair of its code and the tuple of its free
  variables, and an application opens the closure and calls its code
  with its environment:

    clos N Ms ⇒ pair (code N') (tuple Ms'),
    app L M   ⇒ callc L' M'.

-}

module FPC.Compiler.Split where

open import FPC.Language.Type
open import FPC.Language.EnvClos
import FPC.Language.PairClos as T
open import FPC.Framework.AllUtil using (All; []; _∷_)

open import Data.List using ([]; _∷_)

split : ∀ {Γ A} → Tm Γ A → T.Tm Γ A
splits : ∀ {Γ Δ} → All (Tm Γ) Δ → All (T.Tm Γ) Δ

split (` x) = T.` x
split (clos N Ms) = T.pair (T.code (split N)) (T.tuple (splits Ms))
split (app L M) = T.callc (split L) (split M)
split (lit B c) = T.lit B c
split (tuple Ms) = T.tuple (splits Ms)
split (get i M) = T.get i (split M)
split (inl M) = T.inl (split M)
split (inr M) = T.inr (split M)
split (case L M N) = T.case (split L) (split M) (split N)
split (prim p L M) = T.prim p (split L) (split M)
split (let′ M N) = T.let′ (split M) (split N)
split (fold M) = T.fold (split M)
split (unfold M) = T.unfold (split M)

splits [] = []
splits (M ∷ Ms) = split M ∷ splits Ms

{- the pass, for a whole program -}
split-program : ∀ {A} → Tm [] A → T.Tm [] A
split-program = split

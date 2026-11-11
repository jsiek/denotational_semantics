{-

  Typed split (Clos3ᵀ → Clos4ᵀ): a closure becomes a packed pair of its
  code and the tuple of its free variables, and an application opens
  the closure and calls its code with its environment:

    clos N Ms ⇒ pack (code N') (tuple Ms'),
    app L M   ⇒ callc L' M'.

-}

module ISWIM.Compiler.Split where

open import ISWIM.Language.Typed.Type
open import ISWIM.Language.Typed.Clos3
import ISWIM.Language.Typed.Clos4 as T

open import Data.List using ([]; _∷_)
open import Data.Vec using (Vec; []; _∷_)

split : ∀ {Γ A} → Tm Γ A → T.Tm Γ A
splits : ∀ {Γ n} → Vec (Tm Γ Any) n → Vec (T.Tm Γ Any) n

split (` x) = T.` x
split (clos N Ms) = T.pack (T.code (split N)) (T.tuple (splits Ms))
split (app L M) = T.callc (split L) (split M)
split (lit B c) = T.lit B c
split (tuple Ms) = T.tuple (splits Ms)
split (get i M) = T.get i (split M)
split (inl M) = T.inl (split M)
split (inr M) = T.inr (split M)
split (case L M N) = T.case (split L) (split M) (split N)
split (prim p L M) = T.prim p (split L) (split M)
split (let′ M N) = T.let′ (split M) (split N)
split (inject G M) = T.inject G (split M)
split (project t M) = T.project t (split M)

splits [] = []
splits (M ∷ Ms) = split M ∷ splits Ms

{- the pass, for a whole program -}
split-program : ∀ {A} → Tm [] A → T.Tm [] A
split-program = split

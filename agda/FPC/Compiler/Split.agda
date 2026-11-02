{-

  Split (EnvClosμ → PairClosμ), as typed split (Compiler/Split.agda): a
  closure becomes a packed pair of its code and the tuple of its free
  variables, and an application opens the closure and calls its code
  with its environment:

    clos N Ms ⇒ pair (code N') (tuple Ms'),
    app L M   ⇒ callc L' M'.

  (It carries a renaming of the variables, the identity for a program.)

-}

module Mu.Compiler.Split where

open import Mu.Language.Type
open import Mu.Language.EnvClos
import Mu.Language.PairClos as T
open import Mu.Framework.AllUtil using (All; []; _∷_)

open import Data.List using ([]; _∷_)

Ren : Ctx → Ctx → Set
Ren Γ Δ = ∀ {A} → Γ ∋ A → Δ ∋ A

{- the renaming for the body of a binder -}
ext : ∀ {Γ Δ B} → Ren Γ Δ → Ren (B ∷ Γ) (B ∷ Δ)
ext r Z = Z
ext r (S x) = S (r x)

split : ∀ {Γ Δ A} → Ren Γ Δ → Tm Γ A → T.Tm Δ A
splits : ∀ {Γ Δ Δ'} → Ren Γ Δ → All (Tm Γ) Δ' → All (T.Tm Δ) Δ'

split r (` x) = T.` r x
split r (clos N Ms) = T.pair (T.code (split (λ x → x) N)) (T.tuple (splits r Ms))
split r (app L M) = T.callc (split r L) (split r M)
split r (lit B c) = T.lit B c
split r (tuple Ms) = T.tuple (splits r Ms)
split r (get i M) = T.get i (split r M)
split r (inl M) = T.inl (split r M)
split r (inr M) = T.inr (split r M)
split r (case L M N) = T.case (split r L) (split (ext r) M) (split (ext r) N)
split r (prim p L M) = T.prim p (split r L) (split r M)
split r (let′ M N) = T.let′ (split r M) (split (ext r) N)
split r (fold M) = T.fold (split r M)
split r (unfold M) = T.unfold (split r M)

splits r [] = []
splits r (M ∷ Ms) = split r M ∷ splits r Ms

{- the pass, for a whole program -}
split-program : ∀ {A} → Tm [] A → T.Tm [] A
split-program = split λ ()

{-

  The Scott-domain semantics of ISWIM: a term means a continuous map from
  environments to 𝔻. A function means the strict function of its argument
  given by its body, which sees the surrounding environment. This
  semantics is before the 'enclose' pass.

-}

open import MLTT.Spartan hiding (inl; inr; cases)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons

import Language.ISWIM as I

module Semantics.Scott.ISWIM
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : propext 𝓤₀)
       where

open import Framework.Scott.Base pt fe
open import Framework.Scott.Domain pt fe pe
open import Framework.Scott.Ops pt fe pe
open import Framework.Scott.Semantics pt fe pe
open import Semantics.Scott.Prim pt fe pe

𝕆-ISWIM : SemOps I.Op I.sig
𝕆-ISWIM I.lam = lamᶜ
𝕆-ISWIM I.app = binary app
𝕆-ISWIM (I.lit B k) = const₁ 𝟙ᵈ 𝔻 (const B k)
𝕆-ISWIM (I.tuple n) = tupleᶜ n
𝕆-ISWIM (I.get i) = unary (proj i)
𝕆-ISWIM I.inl-op = unary inl
𝕆-ISWIM I.inr-op = unary inr
𝕆-ISWIM I.case-op = caseᶜ
𝕆-ISWIM (I.prim p) = binary (primD p)

{- the meaning of a term: the operators, folded over the term; a variable
   not in scope (under a clear) means ω -}
open Semantics I.Op I.sig ω 𝕆-ISWIM public

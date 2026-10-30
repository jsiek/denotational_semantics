{-

  The examples of Mu/proof/Compiler/Examples/RecursionExample.agda
  (countdown 3 by the fixed-point combinator, and Ω) run on the clocked
  interpreters of ISWIMμ, PairClosμ and X86μ, by computation: countdown 3
  returns 0 with enough clock, and Ω times out at every clock tried.

-}

module Mu.proof.Compiler.Examples.RecursionInterp where

open import Framework.Primitives using (Int)
open import Mu.Compiler.Pipeline using (compile-to-PairClos; compile)
open import Mu.proof.Compiler.Examples.RecursionExample using (three; Ω)
open import Semantics.Observation using (Obs; o-const)
open import Semantics.Interp.Clock using (Semantics; outcome)
import Mu.Semantics.ClockedInterpreters.ISWIM as ISWIMμᵢ
import Mu.Semantics.ClockedInterpreters.PairClos as PairClosμᵢ
import Mu.Semantics.ClockedInterpreters.X86 as X86μᵢ

open import Data.Integer using (+_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

{- run a program with clock ck -}
run : ℕ → Semantics → Maybe Obs
run ck P = outcome (Semantics.obs P) (Semantics.run P ck)

three-iswim : run 10 (ISWIMμᵢ.sem three) ≡ just (o-const Int (+ 0))
three-iswim = refl

three-clos4 : run 10 (PairClosμᵢ.sem (compile-to-PairClos three)) ≡ just (o-const Int (+ 0))
three-clos4 = refl

three-x86 : run 10 (X86μᵢ.sem (compile three)) ≡ just (o-const Int (+ 0))
three-x86 = refl

Ω-iswim : run 50 (ISWIMμᵢ.sem Ω) ≡ nothing
Ω-iswim = refl

Ω-clos4 : run 50 (PairClosμᵢ.sem (compile-to-PairClos Ω)) ≡ nothing
Ω-clos4 = refl

Ω-x86 : run 50 (X86μᵢ.sem (compile Ω)) ≡ nothing
Ω-x86 = refl

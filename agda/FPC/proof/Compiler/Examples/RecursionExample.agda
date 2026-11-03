{-

  The recursion examples of FPC/Examples.agda (countdown 3 by the
  fixed-point combinator, and Ω), compiled with compile-to-PairClos
  (FPC/Compiler/Pipeline.agda) and run on the FPC and PairClosμ
  machines, by computation.

-}

module FPC.proof.Compiler.Examples.RecursionExample where

open import Framework.Primitives using (Int)
open import FPC.Examples using (three; Ω)
open import FPC.Compiler.Pipeline using (compile-to-PairClos)
open import Semantics.Observation using (Obs; o-const)
open import Semantics.CEK.Smallstep using (Machine; next; stop)
import FPC.Semantics.AbstractMachines.FPC as FPCₘ
import FPC.Semantics.AbstractMachines.PairClos as PairClosμₘ

open import Data.Integer using (+_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

{- run a machine for at most n steps -}
run : ℕ → (L : Machine) → Maybe Obs
run n L = go n (Machine.start L)
  where
  go : ℕ → Machine.State L → Maybe Obs
  go zero s = nothing
  go (suc n) s with Machine.step L s
  ... | next s' = go n s'
  ... | stop o = just o

three-fpc : run 200 (FPCₘ.sem three) ≡ just (o-const Int (+ 0))
three-fpc = refl

three-clos4 : run 400 (PairClosμₘ.sem (compile-to-PairClos three)) ≡ just (o-const Int (+ 0))
three-clos4 = refl

{- Ω runs on, on both machines -}
Ω-fpc : run 200 (FPCₘ.sem Ω) ≡ nothing
Ω-fpc = refl

Ω-clos4 : run 400 (PairClosμₘ.sem (compile-to-PairClos Ω)) ≡ nothing
Ω-clos4 = refl

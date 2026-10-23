{-

  The correctness of the ISWIMμ compiler in Scott domains: the statement
  of Theorem F.4 (correctness, Scott domains) of the paper. The proofs
  are in Mu/proof/Correctness/ScottDomains/; each theorem here is one of
  them, with its type written out, as Mu/Theorems/GraphModel.agda does
  for the graph model.

  compile (Mu/Compiler/Pipeline.agda) is the composition of the ten
  passes. A term means an element of the domain
  of values 𝔻, a solution of 𝔻 ≅ 𝓛 (Σ t , Payload t 𝔻)
  (Framework/Scott/Domain.agda), whose least element means divergence;
  const B c is the paper's c(), and defined d is d ≠ ⊥. The domain
  theory is Tom de Jong's, in TypeTopology, which assumes propositional
  truncations, function extensionality and propositional
  extensionality; so these theorems are stated, and hold, under those
  assumptions, which are the parameters of this module (consistent with
  the axiom K that this development uses).

  To read them: the languages (Mu/Language/), the passes
  (Mu/Compiler/), the semantics of ISWIMμ and X86μ
  (Mu/Semantics/ScottDomains/), and the domain, its operators and the
  combinators the semantics are built with (Framework/Scott/).

-}

open import MLTT.Spartan using (𝓤₀; _×_; _＝_; pr₁; pr₂)
open import UF.FunExt using (Fun-Ext)
open import UF.PropTrunc using (propositional-truncations-exist)
open import UF.Subsingletons using (propext)

open import Framework.Primitives using (Base; base-rep; Int)
open import Mu.Language.Type using (base)
import Mu.Language.ISWIM as ISWIMμ
open import Mu.Compiler.Pipeline using (compile)

open import Data.List using ([])

module Mu.Theorems.ScottDomains
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : propext 𝓤₀)
       where

open import Framework.Scott.Base pt fe using (_·_)
open import Framework.Scott.Domain pt fe pe using (defined)
open import Framework.Scott.Ops pt fe pe using (const)

open import Mu.Semantics.ScottDomains.ISWIM pt fe pe using (⟦_⟧)
open import Mu.Semantics.ScottDomains.X86 pt fe pe using (⟦_⟧ₜ)

import Mu.proof.Correctness.ScottDomains.CompilerCorrect pt fe pe as Compiler

{- The environment of a closed program: every variable means the empty
   tuple (Mu/Semantics/ScottDomains/Closed.agda). -}
open import Mu.Semantics.ScottDomains.Closed pt fe pe public using (ρ₀)

{- Theorem F.4 (Correctness, Scott domains) -----------------------------------}

{- for a closed ISWIMμ term M of type Int, and every constant c:
   ⟦ M ⟧ ρ₀ = c() if and only if ⟦ compile M ⟧ = c() -}
compile-int-const : ∀ (M : ISWIMμ.Tm [] (base Int)) (B : Base) (c : base-rep B)
  → (⟦ M ⟧ · ρ₀ ＝ const B c → ⟦ compile M ⟧ₜ ＝ const B c)
  × (⟦ compile M ⟧ₜ ＝ const B c → ⟦ M ⟧ · ρ₀ ＝ const B c)
compile-int-const M = pr₁ (Compiler.compile-int M)

{- moreover, ⟦ M ⟧ ρ₀ is defined if and only if ⟦ compile M ⟧ is -}
compile-int-defined : ∀ (M : ISWIMμ.Tm [] (base Int))
  → (defined (⟦ M ⟧ · ρ₀) → defined ⟦ compile M ⟧ₜ)
  × (defined ⟦ compile M ⟧ₜ → defined (⟦ M ⟧ · ρ₀))
compile-int-defined M = pr₂ (Compiler.compile-int M)

{- more generally, the same holds for every closed term M -}

compile-correct-const : ∀ {A} (M : ISWIMμ.Tm [] A) (B : Base) (c : base-rep B)
  → (⟦ M ⟧ · ρ₀ ＝ const B c → ⟦ compile M ⟧ₜ ＝ const B c)
  × (⟦ compile M ⟧ₜ ＝ const B c → ⟦ M ⟧ · ρ₀ ＝ const B c)
compile-correct-const M = pr₁ (Compiler.compile-same M)

compile-correct-defined : ∀ {A} (M : ISWIMμ.Tm [] A)
  → (defined (⟦ M ⟧ · ρ₀) → defined ⟦ compile M ⟧ₜ)
  × (defined ⟦ compile M ⟧ₜ → defined (⟦ M ⟧ · ρ₀))
compile-correct-defined M = pr₂ (Compiler.compile-same M)

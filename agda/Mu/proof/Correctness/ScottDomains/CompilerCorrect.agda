{-

  The ISWIMμ compiler (Mu/Compiler/Pipeline.agda) in Scott domains, as
  in the graph model (Mu/proof/Correctness/GraphModel/CompilerCorrect.agda):
  for a closed ISWIMμ program, the compiled program, in FlatClosμ, GlobalFunμ,
  Monμ (by its embedding), Impμ, CFGμ and X86μ, produces the same
  constants as the source, and is defined exactly when the source is
  (Same). Every pass but delay preserves the meaning exactly (＝); delay
  preserves and reflects constants and definedness.

-}

open import MLTT.Spartan hiding (inl; inr; cases; _+_)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons

open import Framework.Primitives using (Base; base-rep; Int)
open import Mu.Language.Type using (base)
open import Mu.Language.ISWIM using (Tm)
open import Mu.Language.Mon using (⌜_⌝ₚ)
open import Mu.Compiler.Simplify using (simplify)
open import Mu.Compiler.Enclose using (enclose)
open import Mu.Compiler.Optimize using (optimize-program)
open import Mu.Compiler.Concretize using (concretize-program)
open import Mu.Compiler.Pipeline

module Mu.proof.Correctness.ScottDomains.CompilerCorrect
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : propext 𝓤₀)
       where

open import Framework.Scott.Base pt fe
open import proof.Framework.Scott.Ops pt fe pe
open import proof.Framework.Scott.Semantics pt fe pe using (ρ₀)
open import Mu.Semantics.ScottDomains.ISWIM pt fe pe using (⟦_⟧)
open import Mu.Semantics.ScottDomains.FlatClos pt fe pe using () renaming (⟦_⟧ to ⟦_⟧₄)
open import Mu.Semantics.ScottDomains.GlobalFun pt fe pe using () renaming (⟦_⟧ₚ to ⟦_⟧₅)
open import Mu.Semantics.ScottDomains.Imp pt fe pe using () renaming (⟦_⟧ₚ to ⟦_⟧ᵢ)
open import Mu.Semantics.ScottDomains.CFG pt fe pe using () renaming (⟦_⟧ₚ to ⟦_⟧ᶜ)
open import Mu.Semantics.ScottDomains.X86 pt fe pe using (⟦_⟧ₜ)
open import Mu.proof.Correctness.ScottDomains.SimplifyCorrect pt fe pe using (simplify-correct)
open import Mu.proof.Correctness.ScottDomains.EncloseCorrect pt fe pe using (enclose-correct)
open import Mu.proof.Correctness.ScottDomains.OptimizeCorrect pt fe pe using (optimize-correct)
open import Mu.proof.Correctness.ScottDomains.ConcretizeCorrect pt fe pe using (concretize-correct)
open import Mu.proof.Correctness.ScottDomains.DelayCorrect pt fe pe using (delay-correct-const; delay-correct-defined)
open import Mu.proof.Correctness.ScottDomains.GlobalizeCorrect pt fe pe using (globalize-correct)
open import Mu.proof.Correctness.ScottDomains.RCOCorrect pt fe pe using (rco-correct)
open import Mu.proof.Correctness.ScottDomains.LiftLocalsCorrect pt fe pe using (lift-locals-correct)
open import Mu.proof.Correctness.ScottDomains.ExplicateCorrect pt fe pe using (explicate-correct)
open import Mu.proof.Correctness.ScottDomains.SelectCorrect pt fe pe using (select-correct)

open import Data.List using ([])

_⇔_ : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
A ⇔ B = (A → B) × (B → A)

{- the same constants, and defined together -}
Same : ⟨ 𝔻 ⟩ → ⟨ 𝔻 ⟩ → 𝓤₁ ̇
Same d e = ((B : Base) (c : base-rep B) → (d ＝ const B c) ⇔ (e ＝ const B c)) × (defined d ⇔ defined e)

{- Same d e, and e ＝ e' -}
then : (d e e' : ⟨ 𝔻 ⟩) → Same d e → e ＝ e' → Same d e'
then d e .e s refl = s

compile-to-FlatClos-same : ∀ {A} (M : Tm [] A) → Same (⟦ M ⟧ · ρ₀) (⟦ compile-to-FlatClos M ⟧₄ · ρ₀)
compile-to-FlatClos-same M =
  (λ B c → (λ h → pr₁ (delay-correct-const M₃ B c) (eq ⁻¹ ∙ h)) , (λ h → eq ∙ pr₂ (delay-correct-const M₃ B c) h)) ,
  (λ h → pr₁ (delay-correct-defined M₃) (transport defined eq h)) , (λ h → transport defined (eq ⁻¹) (pr₂ (delay-correct-defined M₃) h))
 where
  M₁ = simplify M
  M₂ = optimize-program (enclose M₁)
  M₃ = concretize-program M₂
  eq = simplify-correct M ∙ enclose-correct M₁ ∙ optimize-correct (enclose M₁) ∙ concretize-correct M₂

compile-to-GlobalFun-same : ∀ {A} (M : Tm [] A) → Same (⟦ M ⟧ · ρ₀) ⟦ compile-to-GlobalFun M ⟧₅
compile-to-GlobalFun-same M = then (⟦ M ⟧ · ρ₀) (⟦ compile-to-FlatClos M ⟧₄ · ρ₀) ⟦ compile-to-GlobalFun M ⟧₅ (compile-to-FlatClos-same M) (globalize-correct (compile-to-FlatClos M))

compile-to-Mon-same : ∀ {A} (M : Tm [] A) → Same (⟦ M ⟧ · ρ₀) ⟦ ⌜ compile-to-Mon M ⌝ₚ ⟧₅
compile-to-Mon-same M = then (⟦ M ⟧ · ρ₀) ⟦ compile-to-GlobalFun M ⟧₅ ⟦ ⌜ compile-to-Mon M ⌝ₚ ⟧₅ (compile-to-GlobalFun-same M) (rco-correct (compile-to-GlobalFun M))

compile-to-Imp-same : ∀ {A} (M : Tm [] A) → Same (⟦ M ⟧ · ρ₀) ⟦ compile-to-Imp M ⟧ᵢ
compile-to-Imp-same M = then (⟦ M ⟧ · ρ₀) ⟦ ⌜ compile-to-Mon M ⌝ₚ ⟧₅ ⟦ compile-to-Imp M ⟧ᵢ (compile-to-Mon-same M) (lift-locals-correct (compile-to-Mon M))

compile-to-CFG-same : ∀ {A} (M : Tm [] A) → Same (⟦ M ⟧ · ρ₀) ⟦ compile-to-CFG M ⟧ᶜ
compile-to-CFG-same M = then (⟦ M ⟧ · ρ₀) ⟦ compile-to-Imp M ⟧ᵢ ⟦ compile-to-CFG M ⟧ᶜ (compile-to-Imp-same M) (explicate-correct (compile-to-Imp M))

compile-same : ∀ {A} (M : Tm [] A) → Same (⟦ M ⟧ · ρ₀) ⟦ compile M ⟧ₜ
compile-same M = then (⟦ M ⟧ · ρ₀) ⟦ compile-to-CFG M ⟧ᶜ ⟦ compile M ⟧ₜ (compile-to-CFG-same M) (select-correct (compile-to-CFG M))

{- the end-to-end theorem, for a main program of type Int -}
compile-int : ∀ (M : Tm [] (base Int)) → Same (⟦ M ⟧ · ρ₀) ⟦ compile M ⟧ₜ
compile-int = compile-same

{-

  The ISWIMμ compiler (Mu/Compiler/Pipeline.agda) in Scott domains, as
  in the graph model (Mu/proof/Correctness/Graph/CompilerCorrect.agda):
  for a closed ISWIMμ program, the compiled program, in Clos4μ, Clos5μ,
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

module Mu.proof.Correctness.Scott.CompilerCorrect
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : propext 𝓤₀)
       where

open import Framework.Scott.Base pt fe
open import proof.Framework.Scott.Ops pt fe pe
open import proof.Framework.Scott.Semantics pt fe pe using (ρ₀)
open import Mu.Semantics.Scott.ISWIM pt fe pe using (⟦_⟧)
open import Mu.Semantics.Scott.Clos4 pt fe pe using () renaming (⟦_⟧ to ⟦_⟧₄)
open import Mu.Semantics.Scott.Clos5 pt fe pe using () renaming (⟦_⟧ₚ to ⟦_⟧₅)
open import Mu.Semantics.Scott.Imp pt fe pe using () renaming (⟦_⟧ₚ to ⟦_⟧ᵢ)
open import Mu.Semantics.Scott.CFG pt fe pe using () renaming (⟦_⟧ₚ to ⟦_⟧ᶜ)
open import Mu.Semantics.Scott.X86 pt fe pe using (⟦_⟧ₜ)
open import Mu.proof.Correctness.Scott.SimplifyCorrect pt fe pe using (simplify-correct)
open import Mu.proof.Correctness.Scott.EncloseCorrect pt fe pe using (enclose-correct)
open import Mu.proof.Correctness.Scott.OptimizeCorrect pt fe pe using (optimize-correct)
open import Mu.proof.Correctness.Scott.ConcretizeCorrect pt fe pe using (concretize-correct)
open import Mu.proof.Correctness.Scott.DelayCorrect pt fe pe using (delay-correct-const; delay-correct-defined)
open import Mu.proof.Correctness.Scott.GlobalizeCorrect pt fe pe using (globalize-correct)
open import Mu.proof.Correctness.Scott.RCOCorrect pt fe pe using (rco-correct)
open import Mu.proof.Correctness.Scott.LiftLocalsCorrect pt fe pe using (lift-locals-correct)
open import Mu.proof.Correctness.Scott.ExplicateCorrect pt fe pe using (explicate-correct)
open import Mu.proof.Correctness.Scott.SelectCorrect pt fe pe using (select-correct)

open import Data.List using ([])

_⇔_ : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
A ⇔ B = (A → B) × (B → A)

{- the same constants, and defined together -}
Same : ⟨ 𝔻 ⟩ → ⟨ 𝔻 ⟩ → 𝓤₁ ̇
Same d e = ((B : Base) (c : base-rep B) → (d ＝ const B c) ⇔ (e ＝ const B c)) × (defined d ⇔ defined e)

{- Same d e, and e ＝ e' -}
then : (d e e' : ⟨ 𝔻 ⟩) → Same d e → e ＝ e' → Same d e'
then d e .e s refl = s

compile₄-same : ∀ {A} (M : Tm [] A) → Same (⟦ M ⟧ · ρ₀) (⟦ compile₄ M ⟧₄ · ρ₀)
compile₄-same M =
  (λ B c → (λ h → pr₁ (delay-correct-const M₃ B c) (eq ⁻¹ ∙ h)) , (λ h → eq ∙ pr₂ (delay-correct-const M₃ B c) h)) ,
  (λ h → pr₁ (delay-correct-defined M₃) (transport defined eq h)) , (λ h → transport defined (eq ⁻¹) (pr₂ (delay-correct-defined M₃) h))
 where
  M₁ = simplify M
  M₂ = optimize-program (enclose M₁)
  M₃ = concretize-program M₂
  eq = simplify-correct M ∙ enclose-correct M₁ ∙ optimize-correct (enclose M₁) ∙ concretize-correct M₂

compile-same : ∀ {A} (M : Tm [] A) → Same (⟦ M ⟧ · ρ₀) ⟦ compile M ⟧₅
compile-same M = then (⟦ M ⟧ · ρ₀) (⟦ compile₄ M ⟧₄ · ρ₀) ⟦ compile M ⟧₅ (compile₄-same M) (globalize-correct (compile₄ M))

compile-mon-same : ∀ {A} (M : Tm [] A) → Same (⟦ M ⟧ · ρ₀) ⟦ ⌜ compile-mon M ⌝ₚ ⟧₅
compile-mon-same M = then (⟦ M ⟧ · ρ₀) ⟦ compile M ⟧₅ ⟦ ⌜ compile-mon M ⌝ₚ ⟧₅ (compile-same M) (rco-correct (compile M))

compile-imp-same : ∀ {A} (M : Tm [] A) → Same (⟦ M ⟧ · ρ₀) ⟦ compile-imp M ⟧ᵢ
compile-imp-same M = then (⟦ M ⟧ · ρ₀) ⟦ ⌜ compile-mon M ⌝ₚ ⟧₅ ⟦ compile-imp M ⟧ᵢ (compile-mon-same M) (lift-locals-correct (compile-mon M))

compile-cfg-same : ∀ {A} (M : Tm [] A) → Same (⟦ M ⟧ · ρ₀) ⟦ compile-cfg M ⟧ᶜ
compile-cfg-same M = then (⟦ M ⟧ · ρ₀) ⟦ compile-imp M ⟧ᵢ ⟦ compile-cfg M ⟧ᶜ (compile-imp-same M) (explicate-correct (compile-imp M))

compile-x86-same : ∀ {A} (M : Tm [] A) → Same (⟦ M ⟧ · ρ₀) ⟦ compile-x86 M ⟧ₜ
compile-x86-same M = then (⟦ M ⟧ · ρ₀) ⟦ compile-cfg M ⟧ᶜ ⟦ compile-x86 M ⟧ₜ (compile-cfg-same M) (select-correct (compile-cfg M))

{- the end-to-end theorem, for a main program of type Int -}
compile-x86-int : ∀ (M : Tm [] (base Int)) → Same (⟦ M ⟧ · ρ₀) ⟦ compile-x86 M ⟧ₜ
compile-x86-int = compile-x86-same

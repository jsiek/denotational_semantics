{-

  The FPC compiler in the graph model, observed through the
  machines, as ISWIM/proof/Adequacy/EndToEnd.agda for the typed pipeline: for
  a closed FPC program M,

    FPC machine  ⇔  ⟦ M ⟧ ρ₀             (Adequacy/AbstractMachines/FPC.agda)
                 ⇔  ⟦ compile M ⟧ₜ       (Correctness/GraphModel/CompilerCorrect.agda)
                 ⇔  X86μ machine         (Adequacy/AbstractMachines/X86.agda)

  for constants and for convergence. Since neither machine stops with
  an error (proof/Semantics/AbstractMachines/NoError.agda), a machine that does not
  converge diverges, and so the graph model states, for a main of type
  Int, the theorem the operational columns state
  (Correctness/AbstractMachines/PipelineSim.agda, Correctness/ClockedInterpreters/CompilerFuel.agda,
  Correctness/ReductionSemantics/PipelineRed.agda): the two machines stop with
  the same constant, or both diverge.

  An alternative to FPC/proof/Adequacy/EndToEnd.agda, which observes the
  compiler through the clocked interpreters instead and is the graph
  model's end theorem (FPC/Theorems/GraphModelAdequateWrtClockedInterpreters.agda); this one is kept for
  the comparison of the two targets of adequacy, reported separately.

-}

module FPC.proof.Adequacy.AbstractMachines.EndToEnd where

open import Framework.Primitives using (base-rep; Int)
open import proof.Framework.GraphModel.SetsAsPredicates
open import FPC.Language.Type using (base)
open import FPC.Language.FPC using (Tm)
open import FPC.Compiler.Pipeline using (compile)
open import Semantics.Observation
open import proof.Semantics.CEK.Smallstep using (Terminates; Diverges)
import FPC.Semantics.AbstractMachines.FPC as I
import FPC.Semantics.AbstractMachines.X86 as X
import FPC.proof.Adequacy.AbstractMachines.FPC as AI
import FPC.proof.Adequacy.AbstractMachines.X86 as AX
open import FPC.proof.Correctness.GraphModel.CompilerCorrect using (compile-same)
open import FPC.proof.Semantics.AbstractMachines.NoError using () renaming (fpc-no-error to fpc-ok; x86-no-error to x86-ok)

open import Data.Integer using (ℤ)
open import Data.List using ([])
open import Data.Product using (proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)

end-to-end-x86-const : ∀ (M : Tm [] (base Int)) (k : ℤ)
  → Terminates (I.sem M) (o-const Int k) ⇔ Terminates (X.sem (compile M)) (o-const Int k)
end-to-end-x86-const M k =
  ⟨ (λ t → proj₁ (AX.x86-const-iff M) (proj₁ (proj₁ (compile-same M) k) (AI.sound-const M t)))
  , (λ t → AI.adequacy-const M (proj₂ (proj₁ (compile-same M) k) (proj₂ (AX.x86-const-iff M) t))) ⟩

end-to-end-x86-converges : ∀ {A} (M : Tm [] A)
  → Converges (Terminates (I.sem M)) ⇔ Converges (Terminates (X.sem (compile M)))
end-to-end-x86-converges M =
  ⟨ (λ t → proj₁ (AX.x86-nonempty-iff M) (proj₁ (proj₂ (compile-same M)) (AI.sound-nonempty M t)))
  , (λ t → AI.adequacy-converges M (proj₂ (proj₂ (compile-same M)) (proj₂ (AX.x86-nonempty-iff M) t))) ⟩

end-to-end-x86-diverges : ∀ (M : Tm [] (base Int))
  → Diverges (I.sem M) ⇔ Diverges (X.sem (compile M))
end-to-end-x86-diverges M =
  ⟨ (λ div → AI.no-error-diverges _ (x86-ok (compile M)) λ c → AI.diverges-not-converges div (proj₂ (end-to-end-x86-converges M) c))
  , (λ div → AI.no-error-diverges _ (fpc-ok M) λ c → AI.diverges-not-converges div (proj₁ (end-to-end-x86-converges M) c)) ⟩

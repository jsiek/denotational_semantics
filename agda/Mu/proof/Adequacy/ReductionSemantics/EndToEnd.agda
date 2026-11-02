{-

  The FPC compiler in the graph model, observed through the reduction
  semantics of FPC and the machine of X86μ, as
  Mu/proof/Adequacy/AbstractMachines/EndToEnd.agda is through the two
  machines: for a closed FPC program M,

    FPC reduction  ⇔  ⟦ M ⟧ ρ₀          (Adequacy/ReductionSemantics/FPC.agda)
                   ⇔  ⟦ compile M ⟧ₜ    (Correctness/GraphModel/CompilerCorrect.agda)
                   ⇔  X86μ machine      (Adequacy/AbstractMachines/X86.agda)

  for constants and for divergence. For a main of type Int, the graph
  model so states the theorem the reduction column states
  (Mu/Theorems/ReductionSemantics.agda): the two stop with the same
  constant, or both diverge.

-}

module Mu.proof.Adequacy.ReductionSemantics.EndToEnd where

open import Framework.Primitives using (Int)
open import Mu.Language.Type using (base)
open import Mu.Language.FPC using (Tm)
open import Mu.Compiler.Pipeline using (compile)
open import Semantics.Observation using (o-const; _⇔_)
import Semantics.Reduction.Smallstep as R
import Semantics.CEK.Smallstep as C
import Mu.Semantics.ReductionSemantics.FPC as FPCᵣ
import Mu.Semantics.AbstractMachines.X86 as X86μₘ
import Mu.proof.Adequacy.ReductionSemantics.FPC as AR
import Mu.proof.Adequacy.AbstractMachines.X86 as AX
open import Mu.proof.Correctness.GraphModel.CompilerCorrect using (compile-same)

open import Data.Integer using (ℤ)
open import Data.List using ([])
open import Data.Product using (proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)

end-to-end-x86-const : ∀ (M : Tm [] (base Int)) (n : ℤ)
  → R.Terminates (FPCᵣ.sem M) (o-const Int n) ⇔ C.Terminates (X86μₘ.sem (compile M)) (o-const Int n)
end-to-end-x86-const M n =
  ⟨ (λ t → proj₁ (AX.x86-const-iff M) (proj₁ (proj₁ (compile-same M) n) (proj₂ (AR.const-iff M) t)))
  , (λ t → proj₁ (AR.const-iff M) (proj₂ (proj₁ (compile-same M) n) (proj₂ (AX.x86-const-iff M) t))) ⟩

end-to-end-x86-diverges : ∀ (M : Tm [] (base Int))
  → R.Diverges (FPCᵣ.sem M) ⇔ C.Diverges (X86μₘ.sem (compile M))
end-to-end-x86-diverges M =
  ⟨ (λ div → proj₂ (AX.x86-diverges-iff M) λ ne → proj₁ (AR.diverges-iff M) div (proj₂ (proj₂ (compile-same M)) ne))
  , (λ div → proj₂ (AR.diverges-iff M) λ ne → proj₁ (AX.x86-diverges-iff M) div (proj₁ (proj₂ (compile-same M)) ne)) ⟩

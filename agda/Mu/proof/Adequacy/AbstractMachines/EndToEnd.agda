{-

  The ISWIMμ compiler in the graph model, observed through the
  machines, as proof/Adequacy/EndToEnd.agda for the typed pipeline: for
  a closed ISWIMμ program M,

    ISWIMμ machine  ⇔  ⟦ M ⟧ ρ₀                (Adequacy/AbstractMachines/ISWIM.agda)
                    ⇔  ⟦ compile M ⟧ₜ       (Correctness/GraphModel/CompilerCorrect.agda)
                    ⇔  X86μ machine             (Adequacy/AbstractMachines/X86.agda)

  for constants and for convergence. Since neither machine stops with
  an error (proof/Semantics/AbstractMachines/NoError.agda), a machine that does not
  converge diverges, and so the graph model states, for a main of type
  Int, the theorem the operational columns state
  (Correctness/AbstractMachines/PipelineSim.agda, Correctness/ClockedInterpreters/CompilerFuel.agda,
  Correctness/ReductionSemantics/PipelineRed.agda): the two machines stop with
  the same constant, or both diverge.

  An alternative to Mu/proof/Adequacy/EndToEnd.agda, which observes the
  compiler through the clocked interpreters instead and is the graph
  model's end theorem (Mu/Theorems/Adequacy.agda); this one is kept for
  the comparison of the two targets of adequacy, reported separately.

-}

module Mu.proof.Adequacy.AbstractMachines.EndToEnd where

open import Framework.Primitives using (base-rep; Int)
open import proof.Framework.GraphModel.SetsAsPredicates
open import Mu.Language.Type using (base)
open import Mu.Language.ISWIM using (Tm)
open import Mu.Compiler.Pipeline using (compile)
open import Semantics.Observation
open import proof.Semantics.CEK.Smallstep
  using (Machine; Terminates; Diverges; Star; Final; start; never-final-diverges; diverges-not-terminates)
import Mu.Semantics.AbstractMachines.ISWIM as I
import Mu.Semantics.AbstractMachines.X86 as X
import Mu.proof.Adequacy.AbstractMachines.ISWIM as AI
import Mu.proof.Adequacy.AbstractMachines.X86 as AX
open import Mu.proof.Correctness.GraphModel.CompilerCorrect using (compile-same)
open import Mu.proof.Semantics.AbstractMachines.NoError using () renaming (iswim-no-error to iswim-ok; x86-no-error to x86-ok)

open import Data.Empty using (⊥-elim)
open import Data.Integer using (ℤ)
open import Data.List using ([])
open import Data.Product using (proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Nullary using (¬_)

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

{- a machine that never stops with an error, and does not converge,
   diverges -}
private
  diverges : ∀ (L : Machine) → ¬ Terminates L o-error → ¬ Converges (Terminates L) → Diverges L
  diverges L ok nc = never-final-diverges λ {s} {o} σ fin →
    nc ⟨ o , ⟨ (λ { refl → ok ⟨ s , ⟨ σ , fin ⟩ ⟩ }) , ⟨ s , ⟨ σ , fin ⟩ ⟩ ⟩ ⟩

  not-converges : ∀ {L : Machine} → Diverges L → ¬ Converges (Terminates L)
  not-converges div ⟨ o , ⟨ _ , t ⟩ ⟩ = diverges-not-terminates div t

end-to-end-x86-diverges : ∀ (M : Tm [] (base Int))
  → Diverges (I.sem M) ⇔ Diverges (X.sem (compile M))
end-to-end-x86-diverges M =
  ⟨ (λ div → diverges _ (x86-ok (compile M)) λ c → not-converges div (proj₂ (end-to-end-x86-converges M) c))
  , (λ div → diverges _ (iswim-ok M) λ c → not-converges div (proj₁ (end-to-end-x86-converges M) c)) ⟩

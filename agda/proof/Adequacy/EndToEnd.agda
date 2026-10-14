{-

  The correctness of the compiler in the graph model, observed through the
  machines: for a closed ISWIM program M, the ISWIM machine and the Clos5
  machine running compile M terminate with the same constants, and one
  terminates with an answer exactly when the other does.

  The proof goes through the denotations only:

    ISWIM machine  ⇔  ⟦ M ⟧ ρ₀          (Adequacy/ISWIM.agda)
                   ⇔  ⟦ compile M ⟧ₚ     (CompilerCorrect.agda)
                   ⇔  Clos5 machine      (Adequacy/Clos5.agda)

  with the precondition of Clos5 adequacy discharged by compile-wf.
  Likewise for the whole compiler, compile-x86, into X86:

    ISWIM machine  ⇔  ⟦ M ⟧ ρ₀          (Adequacy/ISWIM.agda)
                   ⇔  ⟦ compile-x86 M ⟧ₚ (SelectCorrect.agda)
                   ⇔  X86 machine        (Adequacy/X86.agda)

  with the precondition of X86 adequacy discharged by compile-x86-wf.

  What this cannot say: an error (o-error) and diverging both denote
  the empty set, so the graph model cannot tell them apart, and neither
  can this theorem. It does not say that M errors exactly when
  compile M errors (or diverges exactly when compile M diverges), only
  that each of the two does one or the other exactly when the other does
  (the negation of Converges). Nor does it say anything about the shape
  of a function or of a tuple of functions beyond that it is an answer.
  The forward simulations (proof/Correctness/CEK/*Sim.agda) prove the
  stronger statement, observation by observation.

-}

module proof.Adequacy.EndToEnd where

open import Framework.Primitives using (Base; base-rep)
open import Language.ISWIM using (AST)
open import Compiler.Pipeline using (compile; compile-x86)
open import Semantics.Observation
open import proof.Semantics.CEK.Smallstep using (Terminates)
import Semantics.CEK.ISWIM as I
import Semantics.CEK.Clos5 as C5
open import proof.Compiler.EncloseScope using (Closed)
import proof.Adequacy.ISWIM as AI
import proof.Adequacy.ISWIMCompile as AIC
import proof.Adequacy.Clos5 as A5
import Semantics.CEK.X86 as X
import proof.Adequacy.X86 as AX
open import proof.Adequacy.X86CompileWF using (compile-x86-wf)
open import proof.Correctness.Graph.SelectCorrect using (compile-x86-correct-const; compile-x86-correct-nonempty)

open import Data.Product using (proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)

end-to-end-const : ∀ M → Closed M → ∀ {B} (k : base-rep B)
  → Terminates (I.sem M) (o-const B k) ⇔ Terminates (C5.sem (compile M)) (o-const B k)
end-to-end-const M c k =
  ⟨ (λ t → A5.adequacy-const (compile M) wf (proj₁ (AIC.compile-correct-machine-const M c k) t))
  , (λ t → proj₂ (AIC.compile-correct-machine-const M c k) (A5.sound-const (compile M) wf t)) ⟩
  where wf = A5.compile-wf M c

end-to-end-converges : ∀ M → Closed M
  → Converges (Terminates (I.sem M)) ⇔ Converges (Terminates (C5.sem (compile M)))
end-to-end-converges M c =
  ⟨ (λ t → A5.adequacy-converges (compile M) wf (proj₁ (AIC.compile-correct-machine-converges M c) t))
  , (λ t → proj₂ (AIC.compile-correct-machine-converges M c) (A5.sound-nonempty (compile M) wf t)) ⟩
  where wf = A5.compile-wf M c

{- The whole compiler, into X86 -------------------------------------------------}

end-to-end-x86-const : ∀ M → Closed M → ∀ {B} (k : base-rep B)
  → Terminates (I.sem M) (o-const B k) ⇔ Terminates (X.sem (compile-x86 M)) (o-const B k)
end-to-end-x86-const M c k =
  ⟨ (λ t → AX.adequacy-const (compile-x86 M) wf (proj₁ (compile-x86-correct-const M k) (AI.sound-const M t)))
  , (λ t → AI.adequacy-const M c (proj₂ (compile-x86-correct-const M k) (AX.sound-const (compile-x86 M) wf t))) ⟩
  where wf = compile-x86-wf M c

end-to-end-x86-converges : ∀ M → Closed M
  → Converges (Terminates (I.sem M)) ⇔ Converges (Terminates (X.sem (compile-x86 M)))
end-to-end-x86-converges M c =
  ⟨ (λ t → AX.adequacy-converges (compile-x86 M) wf (proj₁ (compile-x86-correct-nonempty M) (AI.sound-nonempty M t)))
  , (λ t → AI.adequacy-converges M c (proj₂ (compile-x86-correct-nonempty M) (AX.sound-nonempty (compile-x86 M) wf t))) ⟩
  where wf = compile-x86-wf M c

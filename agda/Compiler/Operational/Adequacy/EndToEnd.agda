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

  What this cannot say: going wrong (o-wrong) and diverging both denote
  the empty set, so the graph model cannot tell them apart, and neither
  can this theorem. It does not say that M goes wrong exactly when
  compile M goes wrong (or diverges exactly when compile M diverges), only
  that each of the two does one or the other exactly when the other does
  (the negation of Converges). Nor does it say anything about the shape
  of a function or of a tuple of functions beyond that it is an answer.
  The forward simulations (Operational/Correctness/*Sim.agda) prove the
  stronger statement, observation by observation.

-}

module Compiler.Operational.Adequacy.EndToEnd where

open import Primitives using (Base; base-rep)
open import Compiler.Lang.ISWIM using (AST)
open import Compiler.Compile.Pipeline using (compile)
open import Compiler.Observation
open import Compiler.Operational.Smallstep using (Terminates)
import Compiler.Operational.Machine.ISWIM as I
import Compiler.Operational.Machine.Clos5 as C5
open import Compiler.Compile.EncloseScope using (Closed)
import Compiler.Operational.Adequacy.ISWIM as AI
import Compiler.Operational.Adequacy.Clos5 as A5

open import Data.Product using (proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)

end-to-end-const : ∀ M → Closed M → ∀ {B} (k : base-rep B)
  → Terminates (I.sem M) (o-const B k) ⇔ Terminates (C5.sem (compile M)) (o-const B k)
end-to-end-const M c k =
  ⟨ (λ t → A5.adequacy-const (compile M) wf (proj₁ (AI.compile-correct-machine-const M c k) t))
  , (λ t → proj₂ (AI.compile-correct-machine-const M c k) (A5.sound-const (compile M) wf t)) ⟩
  where wf = A5.compile-wf M c

end-to-end-converges : ∀ M → Closed M
  → Converges (Terminates (I.sem M)) ⇔ Converges (Terminates (C5.sem (compile M)))
end-to-end-converges M c =
  ⟨ (λ t → A5.adequacy-converges (compile M) wf (proj₁ (AI.compile-correct-machine-converges M c) t))
  , (λ t → proj₂ (AI.compile-correct-machine-converges M c) (A5.sound-nonempty (compile M) wf t)) ⟩
  where wf = A5.compile-wf M c

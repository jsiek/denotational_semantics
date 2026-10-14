{-

  The typed compiler in the graph model, observed through the machines,
  as proof/Adequacy/EndToEnd.agda: for a closed ISWIM program M,

    ISWIM machine  ⇔  ⟦ M ⟧ ρ₀              (Adequacy/ISWIM.agda, unchanged)
                   ⇔  ⟦ compile M ⟧₅         (Correctness/Typed/Graph/CompilerCorrect.agda)
                   ⇔  Clos5ᵀ machine         (Adequacy/Typed/Clos5.agda)

  with Clos5ᵀ adequacy's precondition discharged by globalize-older, and
  likewise into X86 through the X86 machine (Adequacy/X86.agda), with its
  precondition discharged by compile-x86-wf (Adequacy/Typed/X86.agda).

-}

module proof.Adequacy.Typed.EndToEnd where

open import Framework.Primitives using (base-rep)
open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.Domain using () renaming (const to dconst)
open import Language.ISWIM using (AST)
open import Compiler.EncloseScope using (Closed)
open import Compiler.Typed.Pipeline using (compile; compile₄; compile-x86)
open import Semantics.Observation
open import proof.Semantics.CEK.Smallstep using (Terminates)
open import Semantics.Graph.Typed.Clos5 using () renaming (⟦_⟧ₚ to ⟦_⟧₅)
import Semantics.CEK.ISWIM as I
import Semantics.CEK.Typed.Clos5 as C5
import Semantics.CEK.X86 as X
import proof.Adequacy.ISWIM as AI
import proof.Adequacy.Typed.Clos5 as A5
import proof.Adequacy.X86 as AX
open import proof.Adequacy.Typed.X86 using (compile-x86-wf)
open import proof.Compiler.Typed.GlobalizeOlder using (globalize-older)
open import proof.Correctness.Typed.Graph.CompilerCorrect using (compile-same; compile-x86-same)

open import Data.Product using (proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)

compile-correct-machine-const : ∀ M → Closed M → ∀ {B} (k : base-rep B)
  → Terminates (I.sem M) (o-const B k) ⇔ (dconst k ∈ ⟦ compile M ⟧₅)
compile-correct-machine-const M c k =
  ⟨ (λ t → proj₁ (proj₁ (compile-same M c) k) (AI.sound-const M t))
  , (λ k∈ → AI.adequacy-const M c (proj₂ (proj₁ (compile-same M c) k) k∈)) ⟩

compile-correct-machine-converges : ∀ M → Closed M
  → Converges (Terminates (I.sem M)) ⇔ nonempty ⟦ compile M ⟧₅
compile-correct-machine-converges M c =
  ⟨ (λ t → proj₁ (proj₂ (compile-same M c)) (AI.sound-nonempty M t))
  , (λ ne → AI.adequacy-converges M c (proj₂ (proj₂ (compile-same M c)) ne)) ⟩

end-to-end-const : ∀ M → Closed M → ∀ {B} (k : base-rep B)
  → Terminates (I.sem M) (o-const B k) ⇔ Terminates (C5.sem (compile M)) (o-const B k)
end-to-end-const M c k =
  ⟨ (λ t → proj₁ (A5.const-iff (compile M) od) (proj₁ (compile-correct-machine-const M c k) t))
  , (λ t → proj₂ (compile-correct-machine-const M c k) (proj₂ (A5.const-iff (compile M) od) t)) ⟩
  where od = globalize-older (compile₄ M)

end-to-end-converges : ∀ M → Closed M
  → Converges (Terminates (I.sem M)) ⇔ Converges (Terminates (C5.sem (compile M)))
end-to-end-converges M c =
  ⟨ (λ t → proj₁ (A5.nonempty-iff (compile M) od) (proj₁ (compile-correct-machine-converges M c) t))
  , (λ t → proj₂ (compile-correct-machine-converges M c) (proj₂ (A5.nonempty-iff (compile M) od) t)) ⟩
  where od = globalize-older (compile₄ M)

end-to-end-x86-const : ∀ M → Closed M → ∀ {B} (k : base-rep B)
  → Terminates (I.sem M) (o-const B k) ⇔ Terminates (X.sem (compile-x86 M)) (o-const B k)
end-to-end-x86-const M c k =
  ⟨ (λ t → AX.adequacy-const (compile-x86 M) wf (proj₁ (proj₁ (compile-x86-same M c) k) (AI.sound-const M t)))
  , (λ t → AI.adequacy-const M c (proj₂ (proj₁ (compile-x86-same M c) k) (AX.sound-const (compile-x86 M) wf t))) ⟩
  where wf = compile-x86-wf M c

end-to-end-x86-converges : ∀ M → Closed M
  → Converges (Terminates (I.sem M)) ⇔ Converges (Terminates (X.sem (compile-x86 M)))
end-to-end-x86-converges M c =
  ⟨ (λ t → AX.adequacy-converges (compile-x86 M) wf (proj₁ (proj₂ (compile-x86-same M c)) (AI.sound-nonempty M t)))
  , (λ t → AI.adequacy-converges M c (proj₂ (proj₂ (compile-x86-same M c)) (AX.sound-nonempty (compile-x86 M) wf t))) ⟩
  where wf = compile-x86-wf M c

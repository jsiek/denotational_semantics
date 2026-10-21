{-

  The typed compiler in the graph model, observed through the machines,
  as Untyped/proof/Adequacy/EndToEnd.agda: for a closed ISWIM program M,

    ISWIM machine  ⇔  ⟦ M ⟧ ρ₀              (Adequacy/ISWIM.agda, unchanged)
                   ⇔  ⟦ compile M ⟧₅         (Correctness/Graph/CompilerCorrect.agda)
                   ⇔  Clos5ᵀ machine         (Adequacy/Clos5.agda)

  with Clos5ᵀ adequacy's precondition discharged by globalize-older, and
  likewise into X86ᵀ through the X86ᵀ machine (Adequacy/X86.agda, whose
  precondition the compiled programs meet, X86Compiled.agda), from
  compile-x86-same.

-}

module proof.Adequacy.EndToEnd where

open import Framework.Primitives using (base-rep)
open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.Domain using () renaming (const to dconst)
open import Language.ISWIM using (AST)
open import Compiler.EncloseScope using (Closed)
open import Compiler.Pipeline using (compile; compile₄; compile-x86)
open import Semantics.Observation
open import proof.Semantics.CEK.Smallstep using (Terminates)
open import Semantics.Graph.Typed.Clos5 using () renaming (⟦_⟧ₚ to ⟦_⟧₅)
import Semantics.CEK.ISWIM as I
import Semantics.CEK.Typed.Clos5 as C5
import Semantics.CEK.Typed.X86 as X
import proof.Adequacy.ISWIM as AI
import proof.Adequacy.Clos5 as A5
import proof.Adequacy.X86 as AX
open import proof.Compiler.GlobalizeOlder using (globalize-older)
open import proof.Correctness.Graph.CompilerCorrect using (compile-same; compile-x86-same)

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
  ⟨ (λ t → proj₁ (AX.x86-const-iff M c) (proj₁ (proj₁ (compile-x86-same M c) k) (AI.sound-const M t)))
  , (λ t → AI.adequacy-const M c (proj₂ (proj₁ (compile-x86-same M c) k) (proj₂ (AX.x86-const-iff M c) t))) ⟩

end-to-end-x86-converges : ∀ M → Closed M
  → Converges (Terminates (I.sem M)) ⇔ Converges (Terminates (X.sem (compile-x86 M)))
end-to-end-x86-converges M c =
  ⟨ (λ t → proj₁ (AX.x86-nonempty-iff M c) (proj₁ (proj₂ (compile-x86-same M c)) (AI.sound-nonempty M t)))
  , (λ t → AI.adequacy-converges M c (proj₂ (proj₂ (compile-x86-same M c)) (proj₂ (AX.x86-nonempty-iff M c) t))) ⟩

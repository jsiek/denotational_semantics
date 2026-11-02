{-

  Soundness and adequacy of the graph model with respect to the
  small-step machines, and the compiler's correctness observed through
  the machines: the public statements. The proofs are in proof/Adequacy/
  (for the ISWIM machine, the same as for the preserved untyped
  pipeline, Untyped/Theorems/Adequacy.agda).

  To read them: those of Theorems/Denotational.agda, the ISWIM machine
  (Semantics/CEK/ISWIM.agda), the Clos5ᵀ machine
  (Semantics/CEK/Typed/Clos5.agda), the X86ᵀ machine
  (Semantics/CEK/Typed/X86.agda), and the observations
  (Semantics/Observation.agda). The Clos5ᵀ and X86ᵀ statements are for
  the programs the compiler produces, so that their preconditions (in
  proof/) need not be audited.

-}

module Theorems.Adequacy where

open import Framework.Primitives using (base-rep)
open import Framework.GraphModel.SetsAsPredicates using (_∈_; nonempty)
open import Framework.GraphModel.Domain using (Value; const)
open import Semantics.Observation using (o-const; o-error; Converges; _⇔_)
open import Semantics.CEK.Smallstep using (Terminates; Diverges)
import Language.ISWIM as ISWIM
open import Compiler.Pipeline using (compile; compile₄; compile-x86)
open import Compiler.CaptureScope using (Closed)
open import Theorems.Denotational using (ρ₀)
open import Semantics.Graph.ISWIM using (⟦_⟧)
open import Semantics.Graph.Typed.Clos5 using () renaming (⟦_⟧ₚ to ⟦_⟧₅)
open import Semantics.Graph.Typed.X86 using (⟦_⟧ₜ)
import Semantics.CEK.ISWIM as ISWIMₘ
import Semantics.CEK.Typed.Clos5 as Clos5ᵀₘ
import Semantics.CEK.Typed.X86 as X86ᵀₘ

import proof.Adequacy.ISWIM as AdequacyISWIM
import proof.Adequacy.Clos5 as AdequacyClos5
import proof.Adequacy.X86 as AdequacyX86
open import proof.Compiler.HoistOlder using (hoist-older)
import proof.Adequacy.EndToEnd as EndToEnd

open import Data.Product using (_,_)
open import Relation.Nullary using (¬_)

{- The ISWIM machine, for closed programs ------------------------------------}

iswim-const-iff : ∀ (M : ISWIM.AST) → Closed M → ∀ {B} {k : base-rep B}
  → (const k ∈ ⟦ M ⟧ ρ₀) ⇔ Terminates (ISWIMₘ.sem M) (o-const B k)
iswim-const-iff = AdequacyISWIM.const-iff

iswim-nonempty-iff : ∀ (M : ISWIM.AST) → Closed M
  → nonempty (⟦ M ⟧ ρ₀) ⇔ Converges (Terminates (ISWIMₘ.sem M))
iswim-nonempty-iff = AdequacyISWIM.nonempty-iff

iswim-error-empty : ∀ (M : ISWIM.AST) → Closed M → Terminates (ISWIMₘ.sem M) o-error
  → ∀ (d : Value) → ¬ (d ∈ ⟦ M ⟧ ρ₀)
iswim-error-empty = AdequacyISWIM.error-empty

iswim-diverges-empty : ∀ (M : ISWIM.AST) → Closed M → Diverges (ISWIMₘ.sem M)
  → ∀ (d : Value) → ¬ (d ∈ ⟦ M ⟧ ρ₀)
iswim-diverges-empty = AdequacyISWIM.diverges-empty

{- the constants of the compiled program are those the ISWIM machine
   computes, and it produces something exactly when the machine
   terminates with an answer -}
compile-correct-machine-const : ∀ (M : ISWIM.AST) → Closed M → ∀ {B} (k : base-rep B)
  → Terminates (ISWIMₘ.sem M) (o-const B k) ⇔ (const k ∈ ⟦ compile M ⟧₅)
compile-correct-machine-const = EndToEnd.compile-correct-machine-const

compile-correct-machine-converges : ∀ (M : ISWIM.AST) → Closed M
  → Converges (Terminates (ISWIMₘ.sem M)) ⇔ nonempty ⟦ compile M ⟧₅
compile-correct-machine-converges = EndToEnd.compile-correct-machine-converges

{- The Clos5ᵀ machine, for the programs compile produces ---------------------}

clos5-const-iff : ∀ (M : ISWIM.AST) → Closed M → ∀ {B} {k : base-rep B}
  → (const k ∈ ⟦ compile M ⟧₅) ⇔ Terminates (Clos5ᵀₘ.sem (compile M)) (o-const B k)
clos5-const-iff M c = AdequacyClos5.const-iff (compile M) (hoist-older (compile₄ M))

clos5-nonempty-iff : ∀ (M : ISWIM.AST) → Closed M
  → nonempty ⟦ compile M ⟧₅ ⇔ Converges (Terminates (Clos5ᵀₘ.sem (compile M)))
clos5-nonempty-iff M c = AdequacyClos5.nonempty-iff (compile M) (hoist-older (compile₄ M))

clos5-error-empty : ∀ (M : ISWIM.AST) → Closed M → Terminates (Clos5ᵀₘ.sem (compile M)) o-error
  → ∀ (d : Value) → ¬ (d ∈ ⟦ compile M ⟧₅)
clos5-error-empty M c = AdequacyClos5.error-empty (compile M) (hoist-older (compile₄ M))

clos5-diverges-empty : ∀ (M : ISWIM.AST) → Closed M → Diverges (Clos5ᵀₘ.sem (compile M))
  → ∀ (d : Value) → ¬ (d ∈ ⟦ compile M ⟧₅)
clos5-diverges-empty M c = AdequacyClos5.diverges-empty (compile M) (hoist-older (compile₄ M))

{- The X86ᵀ machine, for the programs compile-x86 produces -------------------}

x86-const-iff : ∀ (M : ISWIM.AST) → Closed M → ∀ {B} {k : base-rep B}
  → (const k ∈ ⟦ compile-x86 M ⟧ₜ) ⇔ Terminates (X86ᵀₘ.sem (compile-x86 M)) (o-const B k)
x86-const-iff = AdequacyX86.x86-const-iff

x86-nonempty-iff : ∀ (M : ISWIM.AST) → Closed M
  → nonempty ⟦ compile-x86 M ⟧ₜ ⇔ Converges (Terminates (X86ᵀₘ.sem (compile-x86 M)))
x86-nonempty-iff = AdequacyX86.x86-nonempty-iff

{- End to end: the compiler, observed through the machines only -------------}

end-to-end-const : ∀ (M : ISWIM.AST) → Closed M → ∀ {B} (k : base-rep B)
  → Terminates (ISWIMₘ.sem M) (o-const B k) ⇔ Terminates (Clos5ᵀₘ.sem (compile M)) (o-const B k)
end-to-end-const = EndToEnd.end-to-end-const

end-to-end-converges : ∀ (M : ISWIM.AST) → Closed M
  → Converges (Terminates (ISWIMₘ.sem M)) ⇔ Converges (Terminates (Clos5ᵀₘ.sem (compile M)))
end-to-end-converges = EndToEnd.end-to-end-converges

end-to-end-x86-const : ∀ (M : ISWIM.AST) → Closed M → ∀ {B} (k : base-rep B)
  → Terminates (ISWIMₘ.sem M) (o-const B k) ⇔ Terminates (X86ᵀₘ.sem (compile-x86 M)) (o-const B k)
end-to-end-x86-const = EndToEnd.end-to-end-x86-const

end-to-end-x86-converges : ∀ (M : ISWIM.AST) → Closed M
  → Converges (Terminates (ISWIMₘ.sem M)) ⇔ Converges (Terminates (X86ᵀₘ.sem (compile-x86 M)))
end-to-end-x86-converges = EndToEnd.end-to-end-x86-converges

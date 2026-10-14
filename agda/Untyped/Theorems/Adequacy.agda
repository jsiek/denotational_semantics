{-

  Soundness and adequacy of the graph model with respect to the
  small-step machines, and the correctness of the compiler in the graph
  model observed through the machines: the public statements. The proofs
  are in proof/Adequacy/; each theorem here is one of
  them (or a one-line instance of one), with its type written out, so
  that it can be read without opening proof/.

  To read them: those of Theorems/Denotational.agda (the graph-model
  semantics, and ρ₀) and of Theorems/Simulation.agda (the machines, the
  observations, Closed). Converges T is terminating with some answer
  (an observation other than o-error), and A ⇔ B is (A → B) × (B → A)
  (Semantics/Observation.agda).

  The adequacy theorems for the Clos5 and X86 machines are proved for
  any well-formed program (a precondition, in
  proof/Adequacy/{Clos5WF,X86WF}.agda, that the
  compiler establishes); they are stated here for the programs the
  compiler produces, so that the well-formedness conditions need not be
  audited.

-}

module Untyped.Theorems.Adequacy where

open import Framework.Primitives using (base-rep)
open import Framework.GraphModel.SetsAsPredicates using (_∈_; nonempty)
open import Framework.GraphModel.Domain using (Value; const)
open import Semantics.Observation using (o-const; o-error; Converges; _⇔_)
open import Semantics.CEK.Smallstep using (Terminates; Diverges)

import Language.ISWIM as ISWIM
open import Untyped.Compiler.Pipeline using (compile; compile-x86)
open import Compiler.EncloseScope using (Closed)

open import Untyped.Theorems.Denotational using (ρ₀)
open import Semantics.Graph.ISWIM using (⟦_⟧)
open import Untyped.Semantics.Graph.Clos5Iswim using () renaming (⟦_⟧ₚ to ⟦_⟧₅)
open import Semantics.Graph.X86 using () renaming (⟦_⟧ₚ to ⟦_⟧ₓ)

import Semantics.CEK.ISWIM as ISWIMₘ
import Untyped.Semantics.CEK.Clos5 as Clos5ₘ
import Semantics.CEK.X86 as X86ₘ

import proof.Adequacy.ISWIM as AdequacyISWIM
import Untyped.proof.Adequacy.ISWIMCompile as ISWIMCompile
import Untyped.proof.Adequacy.Clos5 as AdequacyClos5
import proof.Adequacy.X86 as AdequacyX86
open import Untyped.proof.Adequacy.X86CompileWF using (compile-x86-wf)
import Untyped.proof.Adequacy.EndToEnd as EndToEnd

open import Data.Product using (_,_)
open import Relation.Nullary using (¬_)

{- The ISWIM machine, for closed programs ------------------------------------}

{- ⟦ M ⟧ ρ₀ contains the constant k exactly when the machine terminates
   with it -}
iswim-const-iff : ∀ (M : ISWIM.AST) → Closed M → ∀ {B} {k : base-rep B}
  → (const k ∈ ⟦ M ⟧ ρ₀) ⇔ Terminates (ISWIMₘ.sem M) (o-const B k)
iswim-const-iff = AdequacyISWIM.const-iff

{- ⟦ M ⟧ ρ₀ is nonempty exactly when the machine terminates with an
   answer -}
iswim-nonempty-iff : ∀ (M : ISWIM.AST) → Closed M
  → nonempty (⟦ M ⟧ ρ₀) ⇔ Converges (Terminates (ISWIMₘ.sem M))
iswim-nonempty-iff = AdequacyISWIM.nonempty-iff

{- a program that errors, or diverges, denotes the empty set -}
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
compile-correct-machine-const = ISWIMCompile.compile-correct-machine-const

compile-correct-machine-converges : ∀ (M : ISWIM.AST) → Closed M
  → Converges (Terminates (ISWIMₘ.sem M)) ⇔ nonempty ⟦ compile M ⟧₅
compile-correct-machine-converges = ISWIMCompile.compile-correct-machine-converges

{- The Clos5 machine, for the programs compile produces ----------------------}

clos5-const-iff : ∀ (M : ISWIM.AST) → Closed M → ∀ {B} {k : base-rep B}
  → (const k ∈ ⟦ compile M ⟧₅) ⇔ Terminates (Clos5ₘ.sem (compile M)) (o-const B k)
clos5-const-iff M c = AdequacyClos5.const-iff (compile M) (AdequacyClos5.compile-wf M c)

clos5-nonempty-iff : ∀ (M : ISWIM.AST) → Closed M
  → nonempty ⟦ compile M ⟧₅ ⇔ Converges (Terminates (Clos5ₘ.sem (compile M)))
clos5-nonempty-iff M c = AdequacyClos5.nonempty-iff (compile M) (AdequacyClos5.compile-wf M c)

clos5-error-empty : ∀ (M : ISWIM.AST) → Closed M → Terminates (Clos5ₘ.sem (compile M)) o-error
  → ∀ (d : Value) → ¬ (d ∈ ⟦ compile M ⟧₅)
clos5-error-empty M c = AdequacyClos5.error-empty (compile M) (AdequacyClos5.compile-wf M c)

clos5-diverges-empty : ∀ (M : ISWIM.AST) → Closed M → Diverges (Clos5ₘ.sem (compile M))
  → ∀ (d : Value) → ¬ (d ∈ ⟦ compile M ⟧₅)
clos5-diverges-empty M c = AdequacyClos5.diverges-empty (compile M) (AdequacyClos5.compile-wf M c)

{- The X86 machine, for the programs compile-x86 produces --------------------}

x86-const-iff : ∀ (M : ISWIM.AST) → Closed M → ∀ {B} {k : base-rep B}
  → (const k ∈ ⟦ compile-x86 M ⟧ₓ) ⇔ Terminates (X86ₘ.sem (compile-x86 M)) (o-const B k)
x86-const-iff M c = AdequacyX86.adequacy-const _ wf , AdequacyX86.sound-const _ wf
  where wf = compile-x86-wf M c

x86-nonempty-iff : ∀ (M : ISWIM.AST) → Closed M
  → nonempty ⟦ compile-x86 M ⟧ₓ ⇔ Converges (Terminates (X86ₘ.sem (compile-x86 M)))
x86-nonempty-iff M c = AdequacyX86.adequacy-converges _ wf , AdequacyX86.sound-nonempty _ wf
  where wf = compile-x86-wf M c

{- End to end: the compiler, observed through the machines only -------------}

{- for a closed ISWIM program M, the ISWIM machine and the machine
   running the compiled program terminate with the same constants, and
   one terminates with an answer exactly when the other does. (An
   error and divergence both denote the empty set, so this cannot tell
   them apart; Theorems/Simulation.agda can.) -}

end-to-end-const : ∀ (M : ISWIM.AST) → Closed M → ∀ {B} (k : base-rep B)
  → Terminates (ISWIMₘ.sem M) (o-const B k) ⇔ Terminates (Clos5ₘ.sem (compile M)) (o-const B k)
end-to-end-const = EndToEnd.end-to-end-const

end-to-end-converges : ∀ (M : ISWIM.AST) → Closed M
  → Converges (Terminates (ISWIMₘ.sem M)) ⇔ Converges (Terminates (Clos5ₘ.sem (compile M)))
end-to-end-converges = EndToEnd.end-to-end-converges

end-to-end-x86-const : ∀ (M : ISWIM.AST) → Closed M → ∀ {B} (k : base-rep B)
  → Terminates (ISWIMₘ.sem M) (o-const B k) ⇔ Terminates (X86ₘ.sem (compile-x86 M)) (o-const B k)
end-to-end-x86-const = EndToEnd.end-to-end-x86-const

end-to-end-x86-converges : ∀ (M : ISWIM.AST) → Closed M
  → Converges (Terminates (ISWIMₘ.sem M)) ⇔ Converges (Terminates (X86ₘ.sem (compile-x86 M)))
end-to-end-x86-converges = EndToEnd.end-to-end-x86-converges

{-

  Soundness and adequacy of the graph model (Sem/X86.agda, ⟦_⟧ₚ) with
  respect to the X86 machine (Operational/Machine/X86.agda), for
  well-formed programs (WF, Adequacy/X86WF.agda), which the compiler
  produces from closed ISWIM programs (compile-x86-wf,
  Adequacy/X86CompileWF.agda). As for Clos5 (Adequacy/Clos5.agda):

    soundness : if the machine terminates with an answer o, then
      ⟦ P ⟧ₚ has an element of the shape of o (Adequacy/X86Soundness.agda);
    adequacy : if d ∈ ⟦ P ⟧ₚ, then the machine terminates with an
      answer o, and d has the shape of o (Adequacy/X86LogRel.agda);

  so that ⟦ P ⟧ₚ contains const k exactly when the machine terminates
  with o-const B k, and is nonempty exactly when the machine terminates
  with an answer.

  What is new is the semantics in continuation-passing style, with a
  frame of slots, registers and a flag, and the call stack of the
  machine. The machine and the semantics agree on what a call does:
  the callee starts with %rdi and %rsi set and %rax and the flag unset,
  and a call or a return goes wrong on an unset argument or result.

-}

module proof.Compiler.Operational.Adequacy.X86 where

open import Framework.Primitives using (base-rep)
open import Framework.GraphModel.SetsAsPredicates
open import Framework.GraphModel.Domain using () renaming (const to dconst)
open import Compiler.Lang.X86 using (program; body)
open import Compiler.Model.Graph.Sem.X86 using (⟦_⟧ₚ)
open import Compiler.Observation
open import Compiler.Operational.Smallstep using (Terminates)
open import Compiler.Operational.Machine.X86 using (sem; obs; halt?; halt)
open import proof.Compiler.Operational.Adequacy.Common using (ShapeOf; shape-answer; shape-const)
open import proof.Compiler.Operational.Adequacy.X86WF using (WF) public
open import proof.Compiler.Operational.Adequacy.X86Soundness using (soundness) public
open import proof.Compiler.Operational.Adequacy.X86CompileWF using (compile-x86-wf) public
import proof.Compiler.Operational.Adequacy.X86Common as C
import proof.Compiler.Operational.Adequacy.X86LogRel as LR

open import Data.Product using (Σ-syntax; _×_) renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality using (refl; cong; subst)

sound-const : ∀ P → WF P → ∀ {B} {k : base-rep B} → Terminates (sem P) (o-const B k) → dconst k ∈ ⟦ P ⟧ₚ
sound-const P wf t with soundness P wf t (λ ())
... | ⟨ d , ⟨ d∈ , refl ⟩ ⟩ = d∈

sound-nonempty : ∀ P → WF P → Converges (Terminates (sem P)) → nonempty ⟦ P ⟧ₚ
sound-nonempty P wf ⟨ o , ⟨ ans , t ⟩ ⟩ with soundness P wf t ans
... | ⟨ d , ⟨ d∈ , _ ⟩ ⟩ = ⟨ d , d∈ ⟩

adequacy : ∀ P → WF P → ∀ {d} → d ∈ ⟦ P ⟧ₚ → Σ[ o ∈ Obs ] Terminates (sem P) o × ShapeOf o d
adequacy (program ds (body n bs b)) ⟨ wfd , ⟨ ok , _ ⟩ ⟩ {d} d∈ with LR.adequate-main ds wfd ok d∈
... | ⟨ v , ⟨ r , rv ⟩ ⟩ with r halt
... | ⟨ _ , ⟨ _ , ⟨ _ , ⟨ _ , ⟨ τ , e ⟩ ⟩ ⟩ ⟩ ⟩ =
  ⟨ obs v , ⟨ ⟨ _ , ⟨ C.↠→star ds τ , cong halt? e ⟩ ⟩ , LR.𝕍-shape ds d v rv ⟩ ⟩

adequacy-const : ∀ P → WF P → ∀ {B} {k : base-rep B} → dconst k ∈ ⟦ P ⟧ₚ → Terminates (sem P) (o-const B k)
adequacy-const P wf k∈ with adequacy P wf k∈
... | ⟨ o , ⟨ t , sh ⟩ ⟩ = subst (Terminates (sem P)) (shape-const sh) t

adequacy-converges : ∀ P → WF P → nonempty ⟦ P ⟧ₚ → Converges (Terminates (sem P))
adequacy-converges P wf ⟨ d , d∈ ⟩ with adequacy P wf d∈
... | ⟨ o , ⟨ t , sh ⟩ ⟩ = ⟨ o , ⟨ shape-answer sh , t ⟩ ⟩

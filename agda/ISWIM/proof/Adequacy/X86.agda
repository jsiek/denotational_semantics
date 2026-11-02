{-

  Soundness and adequacy of the graph model of X86ᵀ
  (Semantics/Graph/Typed/X86.agda, ⟦_⟧ₜ) with respect to the X86ᵀ
  machine (Semantics/CEK/Typed/X86.agda), as for Clos5ᵀ
  (proof/Adequacy/Clos5.agda):

    adequacy (X86LogRel.agda), for every program: every d ∈ ⟦ P ⟧ₜ is
      related to the value that the machine returns;
    soundness (X86Soundness.agda), for a program whose table is
      consistent and contains the code of each definition interpreted
      with the whole table: if the machine stops with an answer, the
      value it returns denotes a part of ⟦ P ⟧ₜ.

  So ⟦ P ⟧ₜ holds const k exactly when the machine terminates with
  o-const B k, and it is nonempty exactly when the machine terminates
  with an answer; the programs that the compiler produces have such a
  table (X86Compiled.agda), so this holds of them with no other
  precondition.

-}

module proof.Adequacy.X86 where

open import Framework.Primitives using (base-rep)
open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.Domain using () renaming (const to dconst)
open import proof.Semantics.Graph.Typed.Ops using (ConT; tables)
open import Language.Typed.Type using (Any)
open import Language.Typed.X86 using (Program; program)
open import Language.ISWIM using (AST)
open import Compiler.CaptureScope using (Closed)
open import Compiler.Pipeline using (compile-x86)
open import Semantics.Graph.Typed.X86 using (⟦_⟧ₜ; codeₜ)
open import Semantics.Observation
open import proof.Semantics.CEK.Smallstep using (Terminates)
open import Semantics.CEK.Typed.X86 using (sem; obs; Val)
open import proof.Adequacy.X86Compiled using (Contains; compiled)
import proof.Adequacy.X86LogRel as LR
import proof.Adequacy.X86Soundness as S

open import Data.Product using (_×_; Σ-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality using (sym; subst)

adequacy : ∀ P {d} → d ∈ ⟦ P ⟧ₜ → Σ[ v ∈ Val (Program.table P) Any ] Terminates (sem P) (obs v) × LR.𝕍 (Program.defs P) d v
adequacy (program ds b) = LR.adequacy ds b

module _ (P : Program) (cT : ConT (tables codeₜ (Program.defs P))) (cl : Contains codeₜ (Program.defs P)) where

  const-iff : ∀ {B} {k : base-rep B} → (dconst k ∈ ⟦ P ⟧ₜ) ⇔ Terminates (sem P) (o-const B k)
  const-iff = ⟨ (λ k∈ → let ⟨ v , ⟨ t , r ⟩ ⟩ = adequacy P k∈ in subst (Terminates (sem P)) (LR.𝕍-const (Program.defs P) v r) t)
              , (λ t → let ⟨ v , ⟨ e , v⊆ ⟩ ⟩ = S.soundness (Program.defs P) cT cl (Program.main P) t (λ ()) in
                       v⊆ _ (S.𝒱-const (Program.defs P) cT cl v (sym e))) ⟩

  nonempty-iff : nonempty ⟦ P ⟧ₜ ⇔ Converges (Terminates (sem P))
  nonempty-iff = ⟨ (λ { ⟨ d , d∈ ⟩ → let ⟨ v , ⟨ t , _ ⟩ ⟩ = adequacy P d∈ in ⟨ obs v , ⟨ LR.obs-answer (Program.defs P) v , t ⟩ ⟩ })
                 , (λ { ⟨ o , ⟨ ans , t ⟩ ⟩ → let ⟨ v , ⟨ _ , v⊆ ⟩ ⟩ = S.soundness (Program.defs P) cT cl (Program.main P) t ans in
                                         let ⟨ d , d∈ ⟩ = S.𝒱-ne (Program.defs P) cT cl v in ⟨ d , v⊆ d d∈ ⟩ }) ⟩

{- the programs that the compiler produces -}
x86-const-iff : ∀ M → Closed M → ∀ {B} {k : base-rep B} → (dconst k ∈ ⟦ compile-x86 M ⟧ₜ) ⇔ Terminates (sem (compile-x86 M)) (o-const B k)
x86-const-iff M _ = const-iff (compile-x86 M) (proj₁ (compiled M)) (proj₂ (compiled M))

x86-nonempty-iff : ∀ M → Closed M → nonempty ⟦ compile-x86 M ⟧ₜ ⇔ Converges (Terminates (sem (compile-x86 M)))
x86-nonempty-iff M _ = nonempty-iff (compile-x86 M) (proj₁ (compiled M)) (proj₂ (compiled M))

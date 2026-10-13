{-

  Soundness and adequacy of the graph model (Semantics/Graph/Clos5Iswim.agda, ⟦_⟧ₚ)
  with respect to the Clos5 machine (Semantics/CEK/Clos5.agda), for
  well-formed programs (WF, Adequacy/Clos5WF.agda), which the compiler
  produces from closed ISWIM programs (compile-wf, Adequacy/CompileWF.agda).

    soundness : if the machine terminates with an answer o (anything but
      o-wrong), then ⟦ P ⟧ₚ has an element of the shape of o (ShapeOf,
      in Adequacy/Common.agda); for o-const B k, the constant itself.
    adequacy : if d ∈ ⟦ P ⟧ₚ, then the machine terminates with an
      answer o, and d has the shape of o.

  so that ⟦ P ⟧ₚ contains const k exactly when the machine terminates
  with o-const B k (const-iff), and is nonempty exactly when the machine
  terminates with an answer (nonempty-iff). The machine observes code
  pointers and pairs (closures) as functions, o-fun; a pair denotes
  entries ⦅ u , v ⦆, which ShapeOf o-fun allows.

  The approach is as for ISWIM (Adequacy/ISWIM.agda): soundness by a
  denotation of machine states that shrinks under steps
  (Adequacy/Clos5Soundness.agda), adequacy by a logical relation on
  denotational values (Adequacy/Clos5LogRel.agda). What is new is the
  table of global definitions: the machine looks references up in the
  whole table, while the semantics interprets each definition with the
  table of the older ones, and code runs with exactly two variables. The
  well-formedness condition is what makes these agree.

-}

module proof.Adequacy.Clos5 where

open import Framework.Primitives using (base-rep)
open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.Domain using (Value) renaming (const to dconst)
open import Language.Clos5 using (program)
open import Semantics.Graph.Clos5Iswim using (⟦_⟧ₚ)
open import Semantics.Observation
open import proof.Semantics.CEK.Smallstep
  using (Terminates; Diverges; diverges-not-terminates; terminates-det)
open import Semantics.CEK.Clos5
open import proof.Compiler.GlobalizeTable using (⊑-refl)
open import proof.Adequacy.Common using (ShapeOf; shape-answer; shape-const)
open import proof.Adequacy.Clos5WF using (WF) public
open import proof.Adequacy.Clos5Soundness using (soundness) public
open import proof.Adequacy.CompileWF using (compile-wf) public
import proof.Adequacy.Clos5Common as C
import proof.Adequacy.Clos5LogRel as LR

open import Data.Product using (_×_; Σ-syntax) renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)
open import Relation.Nullary using (¬_)

{- Soundness -------------------------------------------------------------------}

sound-const : ∀ P → WF P → ∀ {B} {k : base-rep B}
  → Terminates (sem P) (o-const B k) → dconst k ∈ ⟦ P ⟧ₚ
sound-const P wf t with soundness P wf t (λ ())
... | ⟨ d , ⟨ d∈ , refl ⟩ ⟩ = d∈

sound-nonempty : ∀ P → WF P → Converges (Terminates (sem P)) → nonempty ⟦ P ⟧ₚ
sound-nonempty P wf ⟨ o , ⟨ ans , t ⟩ ⟩ with soundness P wf t ans
... | ⟨ d , ⟨ d∈ , _ ⟩ ⟩ = ⟨ d , d∈ ⟩

{- Adequacy --------------------------------------------------------------------}

adequacy : ∀ P → WF P → ∀ {d} → d ∈ ⟦ P ⟧ₚ
  → Σ[ o ∈ Obs ] Terminates (sem P) o × ShapeOf o d
adequacy (program ds M) ⟨ wfd , ⟨ _ , ws ⟩ ⟩ {d} d∈
    with LR.adequate ds M (LR.tab ds ds ⊑-refl wfd) ws (λ x ()) d∈
... | ⟨ v , ⟨ e , r ⟩ ⟩ =
  ⟨ obs v , ⟨ ⟨ ret v halt , ⟨ C.↠→star ds (e halt) , refl ⟩ ⟩
            , LR.𝕍-shape ds d v r ⟩ ⟩

adequacy-const : ∀ P → WF P → ∀ {B} {k : base-rep B}
  → dconst k ∈ ⟦ P ⟧ₚ → Terminates (sem P) (o-const B k)
adequacy-const P wf k∈ with adequacy P wf k∈
... | ⟨ o , ⟨ t , sh ⟩ ⟩ = subst (Terminates (sem P)) (shape-const sh) t

adequacy-converges : ∀ P → WF P → nonempty ⟦ P ⟧ₚ → Converges (Terminates (sem P))
adequacy-converges P wf ⟨ d , d∈ ⟩ with adequacy P wf d∈
... | ⟨ o , ⟨ t , sh ⟩ ⟩ = ⟨ o , ⟨ shape-answer sh , t ⟩ ⟩

{- Characterizations ------------------------------------------------------------}

const-iff : ∀ P → WF P → ∀ {B} {k : base-rep B}
  → (dconst k ∈ ⟦ P ⟧ₚ) ⇔ Terminates (sem P) (o-const B k)
const-iff P wf = ⟨ adequacy-const P wf , sound-const P wf ⟩

nonempty-iff : ∀ P → WF P → nonempty ⟦ P ⟧ₚ ⇔ Converges (Terminates (sem P))
nonempty-iff P wf = ⟨ adequacy-converges P wf , sound-nonempty P wf ⟩

{- a program that goes wrong, or diverges, denotes the empty set -}
wrong-empty : ∀ P → WF P → Terminates (sem P) o-wrong → ∀ d → ¬ (d ∈ ⟦ P ⟧ₚ)
wrong-empty P wf w d d∈ with adequacy P wf d∈
... | ⟨ o , ⟨ t , sh ⟩ ⟩ = shape-answer sh (terminates-det t w)

diverges-empty : ∀ P → WF P → Diverges (sem P) → ∀ d → ¬ (d ∈ ⟦ P ⟧ₚ)
diverges-empty P wf div d d∈ with adequacy P wf d∈
... | ⟨ o , ⟨ t , _ ⟩ ⟩ = diverges-not-terminates div t

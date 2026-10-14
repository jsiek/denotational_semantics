{-

  Soundness and adequacy of the graph model of Clos5ᵀ
  (Semantics/Graph/Typed/Clos5.agda, ⟦_⟧ₚ) with respect to the Clos5ᵀ
  machine (Semantics/CEK/Typed/Clos5.agda), for programs whose
  definitions refer only to older ones (OlderDefs), which globalize
  produces (proof/Compiler/Typed/GlobalizeOlder.agda):

    soundness (Clos5Soundness): if the machine stops with an answer,
      the value it returns denotes a part of ⟦ P ⟧ₚ;
    adequacy (Clos5LogRel): every d ∈ ⟦ P ⟧ₚ is related to the value the
      machine returns.

  So ⟦ P ⟧ₚ holds const k exactly when the machine terminates with
  o-const B k, it is nonempty exactly when the machine terminates with an
  answer, and it is empty when the machine errs or diverges.

-}

module proof.Adequacy.Typed.Clos5 where

open import Framework.Primitives using (base-rep)
open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.Domain using (Value) renaming (const to dconst)
open import Language.Typed.Clos5 using (Program; program)
open import Semantics.Graph.Typed.Clos5 using (⟦_⟧ₚ)
open import Semantics.Observation
open import proof.Semantics.CEK.Smallstep using (Terminates; Diverges; diverges-not-terminates; terminates-det)
open import Semantics.CEK.Typed.Clos5 using (sem; ret; halt; obs)
open import proof.Compiler.Typed.GlobalizeOlder using (OlderDefs)
import proof.Adequacy.Typed.Clos5Common as C
import proof.Adequacy.Typed.Clos5LogRel as LR
import proof.Adequacy.Typed.Clos5Soundness as S

open import Data.Product using (_×_; Σ-syntax) renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import Relation.Nullary using (¬_)

adequacy : ∀ P → ∀ {d} → d ∈ ⟦ P ⟧ₚ → Σ[ v ∈ _ ] Terminates (sem P) (obs v) × LR.𝕍 (Program.defs P) d v
adequacy (program ds M) d∈ with LR.adequate ds M (LR.tab-ds ds) (λ ()) d∈
... | ⟨ v , ⟨ e , r ⟩ ⟩ = ⟨ v , ⟨ ⟨ ret v halt , ⟨ C.↠→star ds (e halt) , refl ⟩ ⟩ , r ⟩ ⟩

const-iff : ∀ P → OlderDefs (Program.defs P) → ∀ {B} {k : base-rep B}
  → (dconst k ∈ ⟦ P ⟧ₚ) ⇔ Terminates (sem P) (o-const B k)
const-iff P@(program ds M) od = ⟨ adequate-const , sound-const ⟩
  where
  adequate-const : ∀ {B} {k : base-rep B} → dconst k ∈ ⟦ P ⟧ₚ → Terminates (sem P) (o-const B k)
  adequate-const k∈ with adequacy P k∈
  ... | ⟨ v , ⟨ t , r ⟩ ⟩ = subst (Terminates (sem P)) (LR.𝕍-const ds v r) t
  sound-const : ∀ {B} {k : base-rep B} → Terminates (sem P) (o-const B k) → dconst k ∈ ⟦ P ⟧ₚ
  sound-const {k = k} ⟨ s , ⟨ σ , fin ⟩ ⟩ with S.final ds od σ fin (λ ())
  ... | ⟨ v , ⟨ o≡ , v⊆ ⟩ ⟩ = v⊆ (dconst k) (S.𝒱-const ds od v (sym o≡))

nonempty-iff : ∀ P → OlderDefs (Program.defs P) → nonempty ⟦ P ⟧ₚ ⇔ Converges (Terminates (sem P))
nonempty-iff P@(program ds M) od = ⟨ adequate-conv , sound-ne ⟩
  where
  adequate-conv : nonempty ⟦ P ⟧ₚ → Converges (Terminates (sem P))
  adequate-conv ⟨ d , d∈ ⟩ with adequacy P d∈
  ... | ⟨ v , ⟨ t , _ ⟩ ⟩ = ⟨ obs v , ⟨ LR.obs-answer ds v , t ⟩ ⟩
  sound-ne : Converges (Terminates (sem P)) → nonempty ⟦ P ⟧ₚ
  sound-ne ⟨ o , ⟨ ans , ⟨ s , ⟨ σ , fin ⟩ ⟩ ⟩ ⟩ with S.final ds od σ fin ans
  ... | ⟨ v , ⟨ _ , v⊆ ⟩ ⟩ = let ⟨ d , d∈ ⟩ = S.𝒱-ne ds od v in ⟨ d , v⊆ d d∈ ⟩

{- a program that errs, or diverges, denotes the empty set -}
error-empty : ∀ P → OlderDefs (Program.defs P) → Terminates (sem P) o-error → ∀ d → ¬ (d ∈ ⟦ P ⟧ₚ)
error-empty P od w d d∈ with adequacy P d∈
... | ⟨ v , ⟨ t , _ ⟩ ⟩ = LR.obs-answer (Program.defs P) v (terminates-det t w)

diverges-empty : ∀ P → OlderDefs (Program.defs P) → Diverges (sem P) → ∀ d → ¬ (d ∈ ⟦ P ⟧ₚ)
diverges-empty P od div d d∈ with adequacy P d∈
... | ⟨ v , ⟨ t , _ ⟩ ⟩ = diverges-not-terminates div t

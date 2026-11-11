{-

  Soundness and adequacy of the graph model of FPC
  (FPC/Semantics/GraphModel/FPC.agda) with respect to the FPC machine
  (FPC/Semantics/AbstractMachines/FPC.agda), for closed programs of any type,
  started in ρ₀ on the denotational side and in the empty environment
  on the machine side, as for ISWIM (ISWIM/proof/Adequacy/ISWIM.agda):

    soundness (FPC/proof/Adequacy/AbstractMachines/Soundness.agda): if the machine
      terminates with o, it returns a value v observed as o, and the
      denotation of v is part of ⟦ M ⟧ ρ₀;
    adequacy (FPC/proof/Adequacy/AbstractMachines/LogRel.agda): every d ∈ ⟦ M ⟧ ρ₀ is
      related to the value the machine returns.

  So ⟦ M ⟧ ρ₀ contains const k exactly when the machine terminates with
  o-const B k, it is nonempty exactly when the machine terminates with
  an answer, and it is empty exactly when the machine diverges. Since the
  machine is typed it never stops with o-error
  (FPC/proof/Semantics/AbstractMachines/NoError.agda), a run that does
  not stop with an answer diverges, and so, unlike for ISWIM, there is
  no statement about errors; as for Clos5ᵀ
  (ISWIM/proof/Adequacy/Clos5.agda), the shape of an observation is read off
  the related value (𝕍-const, obs-answer) rather than off d.

-}

module FPC.proof.Adequacy.AbstractMachines.FPC where

open import Framework.Primitives using (base-rep)
open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.Domain using (Value) renaming (const to dconst)
open import FPC.Semantics.GraphModel.Closed using (ρ₀)
open import FPC.Language.FPC using (Tm)
open import FPC.Semantics.GraphModel.FPC using (⟦_⟧)
open import FPC.Semantics.AbstractMachines.FPC using (sem; Val; ret; halt; obs)
open import Semantics.Observation
open import proof.Semantics.CEK.Smallstep
  using (Machine; Terminates; Diverges; never-final-diverges; diverges-not-terminates)
open import FPC.proof.Semantics.AbstractMachines.NoError using (fpc-no-error)
import FPC.proof.Adequacy.AbstractMachines.Soundness as S
open import FPC.proof.Adequacy.AbstractMachines.LogRel using (𝕍; adequate; 𝕍-const; obs-answer; ↠→star)

open import Data.List using ([])
open import Data.Product using (_×_; Σ-syntax) renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality using (refl; sym; subst)
open import Relation.Nullary using (¬_)

{- Soundness -------------------------------------------------------------------}

sound-const : ∀ {A} (M : Tm [] A) {B} {k : base-rep B}
  → Terminates (sem M) (o-const B k)
  → dconst k ∈ ⟦ M ⟧ ρ₀
sound-const M t with S.soundness M t
... | ⟨ _ , ⟨ v , ⟨ o≡ , v⊆ ⟩ ⟩ ⟩ = v⊆ _ (S.𝒱-const v (sym o≡))

sound-nonempty : ∀ {A} (M : Tm [] A)
  → Converges (Terminates (sem M))
  → nonempty (⟦ M ⟧ ρ₀)
sound-nonempty M ⟨ o , ⟨ _ , t ⟩ ⟩ with S.soundness M t
... | ⟨ _ , ⟨ v , ⟨ _ , v⊆ ⟩ ⟩ ⟩ = let ⟨ d , d∈ ⟩ = S.𝒱-ne v in ⟨ d , v⊆ d d∈ ⟩

{- Adequacy --------------------------------------------------------------------}

adequacy : ∀ {A} (M : Tm [] A) {d}
  → d ∈ ⟦ M ⟧ ρ₀
  → Σ[ v ∈ Val A ] Terminates (sem M) (obs v) × 𝕍 d v
adequacy M d∈ with adequate M (λ ()) d∈
... | ⟨ v , ⟨ e , r ⟩ ⟩ = ⟨ v , ⟨ ⟨ ret v halt , ⟨ ↠→star (e halt) , refl ⟩ ⟩ , r ⟩ ⟩

adequacy-const : ∀ {A} (M : Tm [] A) {B} {k : base-rep B}
  → dconst k ∈ ⟦ M ⟧ ρ₀
  → Terminates (sem M) (o-const B k)
adequacy-const M k∈ with adequacy M k∈
... | ⟨ v , ⟨ t , r ⟩ ⟩ = subst (Terminates (sem M)) (𝕍-const v r) t

adequacy-converges : ∀ {A} (M : Tm [] A)
  → nonempty (⟦ M ⟧ ρ₀)
  → Converges (Terminates (sem M))
adequacy-converges M ⟨ d , d∈ ⟩ with adequacy M d∈
... | ⟨ v , ⟨ t , _ ⟩ ⟩ = ⟨ obs v , ⟨ obs-answer v , t ⟩ ⟩

{- Characterizations ------------------------------------------------------------}

const-iff : ∀ {A} (M : Tm [] A) {B} {k : base-rep B} → (dconst k ∈ ⟦ M ⟧ ρ₀) ⇔ Terminates (sem M) (o-const B k)
const-iff M = ⟨ adequacy-const M , sound-const M ⟩

nonempty-iff : ∀ {A} (M : Tm [] A) → nonempty (⟦ M ⟧ ρ₀) ⇔ Converges (Terminates (sem M))
nonempty-iff M = ⟨ adequacy-converges M , sound-nonempty M ⟩

{- a program that diverges denotes the empty set -}
diverges-empty : ∀ {A} (M : Tm [] A)
  → Diverges (sem M)
  → ∀ (d : Value)
  → ¬ (d ∈ ⟦ M ⟧ ρ₀)
diverges-empty M div d d∈ with adequacy M d∈
... | ⟨ v , ⟨ t , _ ⟩ ⟩ = diverges-not-terminates div t

{- a machine that never stops with an error, and does not converge,
   diverges; and one that diverges does not converge -}
no-error-diverges : ∀ (L : Machine)
  → ¬ Terminates L o-error
  → ¬ Converges (Terminates L)
  → Diverges L
no-error-diverges L ok nc = never-final-diverges λ {s} {o} σ fin →
  nc ⟨ o , ⟨ (λ { refl → ok ⟨ s , ⟨ σ , fin ⟩ ⟩ }) , ⟨ s , ⟨ σ , fin ⟩ ⟩ ⟩ ⟩

diverges-not-converges : ∀ {L : Machine}
  → Diverges L
  → ¬ Converges (Terminates L)
diverges-not-converges div ⟨ o , ⟨ _ , t ⟩ ⟩ = diverges-not-terminates div t

{- ⟦ M ⟧ ρ₀ is empty exactly when the machine diverges -}
diverges-iff : ∀ {A} (M : Tm [] A) → Diverges (sem M) ⇔ (¬ nonempty (⟦ M ⟧ ρ₀))
diverges-iff M =
  ⟨ (λ { div ⟨ d , d∈ ⟩ → diverges-empty M div d d∈ })
  , (λ ne → no-error-diverges (sem M) (fpc-no-error M) (λ c → ne (sound-nonempty M c))) ⟩

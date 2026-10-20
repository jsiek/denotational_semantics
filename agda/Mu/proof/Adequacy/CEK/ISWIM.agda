{-

  Soundness and adequacy of the graph model of ISWIMμ
  (Mu/Semantics/Graph/ISWIM.agda) with respect to the ISWIMμ machine
  (Mu/Semantics/CEK/ISWIM.agda), for closed programs of any type,
  started in ρ₀ on the denotational side and in the empty environment
  on the machine side, as for ISWIM (proof/Adequacy/ISWIM.agda):

    soundness (Mu/proof/Adequacy/CEK/Soundness.agda): if the machine
      terminates with o, it returns a value v observed as o, and the
      denotation of v is part of ⟦ M ⟧ ρ₀;
    adequacy (Mu/proof/Adequacy/CEK/LogRel.agda): every d ∈ ⟦ M ⟧ ρ₀ is
      related to the value the machine returns.

  So ⟦ M ⟧ ρ₀ contains const k exactly when the machine terminates with
  o-const B k, it is nonempty exactly when the machine terminates with
  an answer, and it is empty when the machine diverges. Since the
  machine is typed it never stops with o-error, so, unlike for ISWIM,
  there is no statement about errors; as for Clos5ᵀ
  (proof/Adequacy/Clos5.agda), the shape of an observation is read off
  the related value (𝕍-const, obs-answer) rather than off d.

-}

module Mu.proof.Adequacy.CEK.ISWIM where

open import Framework.Primitives using (base-rep)
open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.Domain using (Value) renaming (const to dconst)
open import Mu.Semantics.Graph.Closed using (ρ₀)
open import Mu.Language.ISWIM using (Tm)
open import Mu.Semantics.Graph.ISWIM using (⟦_⟧)
open import Mu.Semantics.CEK.ISWIM using (sem; Val; ret; halt; obs)
open import Semantics.Observation
open import proof.Semantics.CEK.Smallstep using (Terminates; Diverges; diverges-not-terminates)
import Mu.proof.Adequacy.CEK.Soundness as S
open import Mu.proof.Adequacy.CEK.LogRel using (𝕍; adequate; 𝕍-const; obs-answer; ↠→star)

open import Data.List using ([])
open import Data.Product using (_×_; Σ-syntax) renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality using (refl; sym; subst)
open import Relation.Nullary using (¬_)

{- Soundness -------------------------------------------------------------------}

sound-const : ∀ {A} (M : Tm [] A) {B} {k : base-rep B} → Terminates (sem M) (o-const B k) → dconst k ∈ ⟦ M ⟧ ρ₀
sound-const M t with S.soundness M t
... | ⟨ _ , ⟨ v , ⟨ o≡ , v⊆ ⟩ ⟩ ⟩ = v⊆ _ (S.𝒱-const v (sym o≡))

sound-nonempty : ∀ {A} (M : Tm [] A) → Converges (Terminates (sem M)) → nonempty (⟦ M ⟧ ρ₀)
sound-nonempty M ⟨ o , ⟨ _ , t ⟩ ⟩ with S.soundness M t
... | ⟨ _ , ⟨ v , ⟨ _ , v⊆ ⟩ ⟩ ⟩ = let ⟨ d , d∈ ⟩ = S.𝒱-ne v in ⟨ d , v⊆ d d∈ ⟩

{- Adequacy --------------------------------------------------------------------}

adequacy : ∀ {A} (M : Tm [] A) {d} → d ∈ ⟦ M ⟧ ρ₀ → Σ[ v ∈ Val A ] Terminates (sem M) (obs v) × 𝕍 d v
adequacy M d∈ with adequate M (λ ()) d∈
... | ⟨ v , ⟨ e , r ⟩ ⟩ = ⟨ v , ⟨ ⟨ ret v halt , ⟨ ↠→star (e halt) , refl ⟩ ⟩ , r ⟩ ⟩

adequacy-const : ∀ {A} (M : Tm [] A) {B} {k : base-rep B} → dconst k ∈ ⟦ M ⟧ ρ₀ → Terminates (sem M) (o-const B k)
adequacy-const M k∈ with adequacy M k∈
... | ⟨ v , ⟨ t , r ⟩ ⟩ = subst (Terminates (sem M)) (𝕍-const v r) t

adequacy-converges : ∀ {A} (M : Tm [] A) → nonempty (⟦ M ⟧ ρ₀) → Converges (Terminates (sem M))
adequacy-converges M ⟨ d , d∈ ⟩ with adequacy M d∈
... | ⟨ v , ⟨ t , _ ⟩ ⟩ = ⟨ obs v , ⟨ obs-answer v , t ⟩ ⟩

{- Characterizations ------------------------------------------------------------}

const-iff : ∀ {A} (M : Tm [] A) {B} {k : base-rep B} → (dconst k ∈ ⟦ M ⟧ ρ₀) ⇔ Terminates (sem M) (o-const B k)
const-iff M = ⟨ adequacy-const M , sound-const M ⟩

nonempty-iff : ∀ {A} (M : Tm [] A) → nonempty (⟦ M ⟧ ρ₀) ⇔ Converges (Terminates (sem M))
nonempty-iff M = ⟨ adequacy-converges M , sound-nonempty M ⟩

{- a program that diverges denotes the empty set -}
diverges-empty : ∀ {A} (M : Tm [] A) → Diverges (sem M) → ∀ (d : Value) → ¬ (d ∈ ⟦ M ⟧ ρ₀)
diverges-empty M div d d∈ with adequacy M d∈
... | ⟨ v , ⟨ t , _ ⟩ ⟩ = diverges-not-terminates div t

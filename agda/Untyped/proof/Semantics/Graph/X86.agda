{-

  Lemmas about the semantics of X86 in the graph model
  (Untyped/Semantics/Graph/X86.agda), used by the proofs of select instructions
  of both pipelines (Correctness/Graph/SelectCorrect.agda, and that of
  the preserved untyped pipeline): no slot holds both an inl and an inr
  (Tagged, Inv), and X86's case, which tests the operand (isinl), binds
  its payload and branches on the flag, means the case of the graph
  model (case-core).

-}

module Untyped.proof.Semantics.Graph.X86 where

open import Untyped.Semantics.Graph.X86 public

open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.Domain
open import proof.Framework.GraphModel.Ops

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Nat using (_≟_)
open import Data.Product using (Σ; _×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (yes; no)

{- No slot holds both an inl and an inr -}
Tagged : 𝒫 Value → Set
Tagged D = ∀ {u v} → left u ∈ D → right v ∈ D → ⊥

Inv : Store → Set
Inv σ = ∀ y → Tagged (σ y)

tagged-≈ : ∀ {V} → V ≈ V → Tagged (mem V)
tagged-≈ {V} c l r = ≈⇒Every V V c _ _ l r

inv-↦ : ∀ {σ x X} → Inv σ → Tagged X → Inv (σ [ x ↦ X ])
inv-↦ {x = x} i t y with y ≟ x
... | yes _ = t
... | no _ = i y

{- case: test, bind the payload, and branch on the flag -}
case-core : ∀ {A A' : 𝒫 Value} {F₁ F₂ G₁ G₂ : 𝒫 Value → 𝒫 Value} → A ≃ A' → Tagged A
  → (∀ V → V ≈ V → F₁ (mem V) ≃ G₁ (mem V)) → (∀ V → V ≈ V → F₂ (mem V) ≃ G₂ (mem V))
  → ⋆ ⟨ Λ ⟨ (λ X → 𝒞 ⟨ isinl A , ⟨ (λ _ → F₁ X) , ⟨ (λ _ → F₂ X) , ptt ⟩ ⟩ ⟩) , ptt ⟩ , ⟨ payloadD A , ptt ⟩ ⟩
    ≃ 𝒞 ⟨ A' , ⟨ G₁ , ⟨ G₂ , ptt ⟩ ⟩ ⟩
case-core {A} {A'} ⟨ A⊆ , A⊇ ⟩ tg F₁≃ F₂≃ = ⟨ G , H ⟩
  where
  G : _
  G w ⟨ [] , ⟨ ⟨ _ , ⟨ ne , _ ⟩ ⟩ , _ ⟩ ⟩ = ⊥-elim (ne refl)
  G w ⟨ v ∷ V , ⟨ ⟨ inj₁ ⟨ f , ⟨ _ , ⟨ fl , ⟨ w∈ , _ ⟩ ⟩ ⟩ ⟩ , ⟨ _ , c ⟩ ⟩ , ⟨ V⊆ , _ ⟩ ⟩ ⟩
    with fl f (here refl)
  ... | inj₁ ⟨ u , ⟨ l∈ , _ ⟩ ⟩ =
    inj₁ ⟨ v , ⟨ V , ⟨ (λ d d∈ → A⊆ _ (lefts (V⊆ d d∈))) , ⟨ proj₁ (F₁≃ (v ∷ V) c) w w∈ , c ⟩ ⟩ ⟩ ⟩
    where
    lefts : ∀ {d} → payloadD A d → left d ∈ A
    lefts (inj₁ l) = l
    lefts (inj₂ r) = ⊥-elim (tg l∈ r)
  ... | inj₂ ⟨ _ , ⟨ _ , () ⟩ ⟩
  G w ⟨ v ∷ V , ⟨ ⟨ inj₂ ⟨ f , ⟨ _ , ⟨ fr , ⟨ w∈ , _ ⟩ ⟩ ⟩ ⟩ , ⟨ _ , c ⟩ ⟩ , ⟨ V⊆ , _ ⟩ ⟩ ⟩
    with fr f (here refl)
  ... | inj₂ ⟨ u , ⟨ r∈ , _ ⟩ ⟩ =
    inj₂ ⟨ v , ⟨ V , ⟨ (λ d d∈ → A⊆ _ (rights (V⊆ d d∈))) , ⟨ proj₁ (F₂≃ (v ∷ V) c) w w∈ , c ⟩ ⟩ ⟩ ⟩
    where
    rights : ∀ {d} → payloadD A d → right d ∈ A
    rights (inj₁ l) = ⊥-elim (tg l r∈)
    rights (inj₂ r) = r
  ... | inj₁ ⟨ _ , ⟨ _ , () ⟩ ⟩
  H : _
  H w (inj₁ ⟨ v , ⟨ V , ⟨ l∈ , ⟨ w∈ , c ⟩ ⟩ ⟩ ⟩) =
    ⟨ v ∷ V , ⟨ ⟨ inj₁ ⟨ ⟨⟩ , ⟨ [] , ⟨ (λ { _ (here refl) → inj₁ ⟨ v , ⟨ A⊇ _ (l∈ v (here refl)) , refl ⟩ ⟩ })
                                      , ⟨ proj₂ (F₁≃ (v ∷ V) c) w w∈ , ⟨ tt ∷ [] , tt ⟩ ⟩ ⟩ ⟩ ⟩
                , ⟨ (λ ()) , c ⟩ ⟩
              , ⟨ (λ d d∈ → inj₁ (A⊇ _ (l∈ d d∈))) , (λ ()) ⟩ ⟩ ⟩
  H w (inj₂ ⟨ v , ⟨ V , ⟨ r∈ , ⟨ w∈ , c ⟩ ⟩ ⟩ ⟩) =
    ⟨ v ∷ V , ⟨ ⟨ inj₂ ⟨ ⟨⟩ , ⟨ [] , ⟨ (λ { _ (here refl) → inj₂ ⟨ v , ⟨ A⊇ _ (r∈ v (here refl)) , refl ⟩ ⟩ })
                                      , ⟨ proj₂ (F₂≃ (v ∷ V) c) w w∈ , ⟨ tt ∷ [] , tt ⟩ ⟩ ⟩ ⟩ ⟩
                , ⟨ (λ ()) , c ⟩ ⟩
              , ⟨ (λ d d∈ → inj₂ (A⊇ _ (r∈ d d∈))) , (λ ()) ⟩ ⟩ ⟩

{-

  Lemmas about the semantics of CFGμ in the graph model
  (Mu/Semantics/GraphModel/CFG.agda), and about the simple expressions it
  shares with Impμ, as for CFGᵀ: a simple expression is monotone in its
  atoms (𝒮-⊆, hence a congruence in the table, 𝒮-≃), and a tail and the
  blocks are monotone in the frame (tail-mono, blocks-mono).

-}

module Mu.proof.Semantics.GraphModel.CFG where

open import Mu.Semantics.GraphModel.CFG public
open import Mu.Semantics.GraphModel.Imp using (𝒜s)
open import Mu.Semantics.GraphModel.Ops using (Table)

open import proof.Framework.GraphModel.Prelude
open import proof.Framework.GraphModel.DOpSig using (results-rel-pres)
open import proof.Framework.GraphModel.Ops
open import proof.Framework.GraphModel.Env using (_⊆ₑ_; •-~)
open import proof.Semantics.Graph.Prim using (primD-mono)
open import Framework.Membership using (_⊑_; here⊑; there⊑)
open import Mu.Language.Type
open import Mu.Language.CFG
open import Mu.Language.Imp using (var; lit; ref; atm; pack; callc; tuple; get; inl; inr; prim; fold; unfold)
open import Mu.Framework.AllUtil using (All; []; _∷_; pos)

open import Data.List using (List; []; _∷_; length; replicate)
open import Data.Nat using (suc)
open import Data.Product using (proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Level using (lift; lower)

module _ {Σ Δ} {T T' : Table Σ} {σ σ'} (h : ∀ {A} (a : Atm Σ Δ A) → 𝒜 a T σ ⊆ 𝒜 a T' σ') where

  𝒜s-⊆ : ∀ {Δs} (as : All (Atm Σ Δ) Δs) → results-rel-pres _⊆_ (replicate (length Δs) ■) (𝒜s as T σ) (𝒜s as T' σ')
  𝒜s-⊆ [] = ptt
  𝒜s-⊆ (a ∷ as) = ⟨ lift (h a) , 𝒜s-⊆ as ⟩

  𝒮-⊆ : ∀ {A} (s : Simple Σ Δ A) → 𝒮 s T σ ⊆ 𝒮 s T' σ'
  𝒮-⊆ (atm a) = h a
  𝒮-⊆ (pack a b) = lower (pair-mono _ _ ⟨ lift (h a) , ⟨ lift (h b) , ptt ⟩ ⟩)
  𝒮-⊆ (callc f a) = lower (⋆-mono _ _
    ⟨ ⋆-mono _ _ ⟨ car-mono _ _ ⟨ lift (h f) , ptt ⟩ , ⟨ cdr-mono _ _ ⟨ lift (h f) , ptt ⟩ , ptt ⟩ ⟩ , ⟨ lift (h a) , ptt ⟩ ⟩)
  𝒮-⊆ (tuple as) = lower (𝒯-mono _ _ _ (𝒜s-⊆ as))
  𝒮-⊆ (get i a) = lower (proj-mono (pos i) _ _ ⟨ lift (h a) , ptt ⟩)
  𝒮-⊆ (inl a) = lower (inl-mono _ _ ⟨ lift (h a) , ptt ⟩)
  𝒮-⊆ (inr a) = lower (inr-mono _ _ ⟨ lift (h a) , ptt ⟩)
  𝒮-⊆ (prim p a b) = lower (primD-mono p _ _ ⟨ lift (h a) , ⟨ lift (h b) , ptt ⟩ ⟩)
  𝒮-⊆ (fold a) = h a
  𝒮-⊆ (unfold a) = h a

{- an atom, in the table and the frame -}
𝒜-⊆ : ∀ {Σ Δ A} {T T' : Table Σ} {σ σ'} → (∀ {s} (f : Σ ∋ s) → T f ⊆ T' f) → σ ⊆ₑ σ' → ∀ (a : Atm Σ Δ A) → 𝒜 a T σ ⊆ 𝒜 a T' σ'
𝒜-⊆ h s (var x) = s (idx x)
𝒜-⊆ h s (lit B c) = λ _ z → z
𝒜-⊆ h s (ref f) = h f

𝒮-≃ : ∀ {Σ Δ A} {T T' : Table Σ} → (∀ {s} (f : Σ ∋ s) → T f ≃ T' f) → ∀ (s : Simple Σ Δ A) σ → 𝒮 s T σ ≃ 𝒮 s T' σ
𝒮-≃ TT s σ = ⟨ 𝒮-⊆ (𝒜-⊆ (λ f → proj₁ (TT f)) (λ _ _ z → z)) s , 𝒮-⊆ (𝒜-⊆ (λ f → proj₂ (TT f)) (λ _ _ z → z)) s ⟩

𝒜-mono : ∀ {Σ Δ A} {T : Table Σ} {σ σ'} → σ ⊆ₑ σ' → ∀ (a : Atm Σ Δ A) → 𝒜 a T σ ⊆ 𝒜 a T σ'
𝒜-mono = 𝒜-⊆ (λ _ _ z → z)

drop-mono : ∀ {Δ' Δ : Ctx} (p : Δ' ⊑ Δ) {σ σ'} → σ ⊆ₑ σ' → drop p σ ⊆ₑ drop p σ'
drop-mono here⊑ s = s
drop-mono (there⊑ p) s = drop-mono p (λ i → s (suc i))

module _ {Σ} {T : Table Σ} where

  MonoB : ∀ {Bs} → Meanings Bs → Set₁
  MonoB B = ∀ {Δ} (l : _ ∋ Δ) {σ σ'} → σ ⊆ₑ σ' → B l σ ⊆ B l σ'

  tail-mono : ∀ {R Bs Δ} (t : Tail Σ R Bs Δ) {B : Meanings Bs} → MonoB B → ∀ {σ σ'} → σ ⊆ₑ σ'
    → ⟦ t ⟧ᵗ T B σ ⊆ ⟦ t ⟧ᵗ T B σ'
  tail-mono (return s) mB σ⊆ = 𝒮-⊆ (𝒜-mono σ⊆) s
  tail-mono (seq p s t) mB σ⊆ = lower (⋆-mono _ _
    ⟨ Λ-mono _ _ ⟨ (λ X Y X⊆ → lift (tail-mono t mB (•-~ _⊆_ (drop-mono p σ⊆) X⊆))) , ptt ⟩
    , ⟨ lift (𝒮-⊆ (𝒜-mono σ⊆) s) , ptt ⟩ ⟩)
  tail-mono (goto l) mB σ⊆ = mB l σ⊆
  tail-mono (case a p l₁ l₂) mB σ⊆ = lower (𝒞-mono _ _
    ⟨ lift (𝒜-mono σ⊆ a) , ⟨ (λ X Y X⊆ → lift (mB l₁ (•-~ _⊆_ (drop-mono p σ⊆) X⊆)))
    , ⟨ (λ X Y X⊆ → lift (mB l₂ (•-~ _⊆_ (drop-mono p σ⊆) X⊆))) , ptt ⟩ ⟩ ⟩)

  blocks-mono : ∀ {R Bs} (bs : Blocks Σ R Bs) → MonoB (blocks bs T)
  blocks-mono (bs ▷ t) Z = tail-mono t (blocks-mono bs)
  blocks-mono (bs ▷ t) (S l) = blocks-mono bs l

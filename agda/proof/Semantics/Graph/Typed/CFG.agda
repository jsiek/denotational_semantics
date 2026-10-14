{-

  Lemmas about the semantics of CFGᵀ in the graph model
  (Semantics/Graph/Typed/CFG.agda), and about the simple expressions it
  shares with Impᵀ: a simple expression is monotone in its atoms (𝒮-⊆,
  hence a congruence in the table, 𝒮-≃), and a tail and the blocks are
  monotone in the frame (tail-mono, blocks-mono).

-}

module proof.Semantics.Graph.Typed.CFG where

open import Semantics.Graph.Typed.CFG public
open import Semantics.Graph.Typed.Imp using (𝒜s)
open import proof.Semantics.Graph.Typed.Ops using (Table; project-good; fun₄)

open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.DOpSig using (results-rel-pres)
open import proof.Framework.GraphModel.Domain
open import proof.Framework.GraphModel.Ops
open import proof.Framework.GraphModel.ContinuityBase using (mono)
open import proof.Framework.GraphModel.Env using (_⊆ₑ_; •-~)
open import proof.Semantics.Graph.Prim using (primD-mono)
open import Framework.Membership using (_⊑_; here⊑; there⊑)
open import Language.Typed.Type
open import Language.Typed.CFG
open import Language.Typed.Imp using (var; lit; ref; atm; pack; callc; tuple; get; inl; inr; prim; inject; project)

open import Data.List using (List; []; _∷_; replicate)
open import Data.Nat using (ℕ; suc)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Product using (proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Level using (lift; lower)

module _ {Σ Δ} {T T' : Table Σ} {σ σ'} (h : ∀ {A} (a : Atm Σ Δ A) → 𝒜 a T σ ⊆ 𝒜 a T' σ') where

  𝒜s-⊆ : ∀ {n} (as : Vec (Atm Σ Δ Any) n) → results-rel-pres _⊆_ (replicate n ■) (𝒜s as T σ) (𝒜s as T' σ')
  𝒜s-⊆ [] = ptt
  𝒜s-⊆ (a ∷ as) = ⟨ lift (h a) , 𝒜s-⊆ as ⟩

  𝒮-⊆ : ∀ {A} (s : Simple Σ Δ A) → 𝒮 s T σ ⊆ 𝒮 s T' σ'
  𝒮-⊆ (atm a) = h a
  𝒮-⊆ (pack a b) = lower (pair-mono _ _ ⟨ lift (h a) , ⟨ lift (h b) , ptt ⟩ ⟩)
  𝒮-⊆ (callc f a) = lower (⋆-mono _ _
    ⟨ ⋆-mono _ _ ⟨ car-mono _ _ ⟨ lift (h f) , ptt ⟩ , ⟨ cdr-mono _ _ ⟨ lift (h f) , ptt ⟩ , ptt ⟩ ⟩ , ⟨ lift (h a) , ptt ⟩ ⟩)
  𝒮-⊆ (tuple as) = lower (𝒯-mono _ _ _ (𝒜s-⊆ as))
  𝒮-⊆ (get i a) = lower (proj-mono i _ _ ⟨ lift (h a) , ptt ⟩)
  𝒮-⊆ (inl a) = lower (inl-mono _ _ ⟨ lift (h a) , ptt ⟩)
  𝒮-⊆ (inr a) = lower (inr-mono _ _ ⟨ lift (h a) , ptt ⟩)
  𝒮-⊆ (prim p a b) = lower (primD-mono p _ _ ⟨ lift (h a) , ⟨ lift (h b) , ptt ⟩ ⟩)
  𝒮-⊆ (inject G a) = h a
  𝒮-⊆ (project t a) = lower (mono (project-good fun₄ t) _ _ ⟨ lift (h a) , ptt ⟩)

{- in the table -}
𝒜-T⊆ : ∀ {Σ Δ A} {T T' : Table Σ} → (∀ {n} (f : Σ ∋ n) → T f ⊆ T' f) → ∀ (a : Atm Σ Δ A) {σ} → 𝒜 a T σ ⊆ 𝒜 a T' σ
𝒜-T⊆ h (var x) = λ _ z → z
𝒜-T⊆ h (lit B c) = λ _ z → z
𝒜-T⊆ h (ref f) = h f

𝒮-≃ : ∀ {Σ Δ A} {T T' : Table Σ} → (∀ {n} (f : Σ ∋ n) → T f ≃ T' f) → ∀ (s : Simple Σ Δ A) σ → 𝒮 s T σ ≃ 𝒮 s T' σ
𝒮-≃ TT s σ = ⟨ 𝒮-⊆ (λ a → 𝒜-T⊆ (λ f → proj₁ (TT f)) a) s , 𝒮-⊆ (λ a → 𝒜-T⊆ (λ f → proj₂ (TT f)) a) s ⟩

{- in the frame -}
𝒜-mono : ∀ {Σ Δ A} {T : Table Σ} {σ σ'} → σ ⊆ₑ σ' → ∀ (a : Atm Σ Δ A) → 𝒜 a T σ ⊆ 𝒜 a T σ'
𝒜-mono s (var x) = s (idx x)
𝒜-mono s (lit B c) = λ _ z → z
𝒜-mono s (ref f) = λ _ z → z

drop-mono : ∀ {Δ' Δ : Ctx} (p : Δ' ⊑ Δ) {σ σ'} → σ ⊆ₑ σ' → drop p σ ⊆ₑ drop p σ'
drop-mono here⊑ s = s
drop-mono (there⊑ p) s = drop-mono p (λ i → s (suc i))

module _ {Σ} {T : Table Σ} where

  MonoB : ∀ {Bs} → Meanings Bs → Set₁
  MonoB B = ∀ {Δ} (l : _ ∋ Δ) {σ σ'} → σ ⊆ₑ σ' → B l σ ⊆ B l σ'

  tail-mono : ∀ {Bs Δ} (t : Tail Σ Bs Δ) {B : Meanings Bs} → MonoB B → ∀ {σ σ'} → σ ⊆ₑ σ'
    → ⟦ t ⟧ᵗ T B σ ⊆ ⟦ t ⟧ᵗ T B σ'
  tail-mono (return s) mB σ⊆ = 𝒮-⊆ (𝒜-mono σ⊆) s
  tail-mono (seq p s t) mB σ⊆ = lower (⋆-mono _ _
    ⟨ Λ-mono _ _ ⟨ (λ X Y X⊆ → lift (tail-mono t mB (•-~ _⊆_ (drop-mono p σ⊆) X⊆))) , ptt ⟩
    , ⟨ lift (𝒮-⊆ (𝒜-mono σ⊆) s) , ptt ⟩ ⟩)
  tail-mono (goto l) mB σ⊆ = mB l σ⊆
  tail-mono (case a p l₁ l₂) mB σ⊆ = lower (𝒞-mono _ _
    ⟨ lift (𝒜-mono σ⊆ a) , ⟨ (λ X Y X⊆ → lift (mB l₁ (•-~ _⊆_ (drop-mono p σ⊆) X⊆)))
    , ⟨ (λ X Y X⊆ → lift (mB l₂ (•-~ _⊆_ (drop-mono p σ⊆) X⊆))) , ptt ⟩ ⟩ ⟩)

  blocks-mono : ∀ {Bs} (bs : Blocks Σ Bs) → MonoB (blocks bs T)
  blocks-mono (bs ▷ t) Z = tail-mono t (blocks-mono bs)
  blocks-mono (bs ▷ t) (S l) = blocks-mono bs l

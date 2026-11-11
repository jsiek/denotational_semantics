{-

  The semantics of Impμ (FPC/Language/Imp.agda) in the graph model, in
  continuation-passing style, as that of Impᵀ
  (ISWIM/Semantics/Graph/Typed/Imp.agda), in a fixed frame. The frame σ
  gives each slot (a typed index, at position idx) a meaning; a
  continuation κ takes the value of the expression. Atoms and simple
  expressions (𝒜, 𝒮, shared with CFGμ) are the operators of GlobalFunμ
  on atoms; fold and unfold are the identity.

  x := e₁; e₂ runs e₁ with the continuation that is strict in its value
  D like let in GlobalFunμ: ⋆ ⟨ Λ F , D ⟩, where F X runs e₂ in the frame
  with X written to slot x, and then κ. A case is 𝒞, and each branch
  writes the payload to the slot of its variable and runs with κ. The
  code of a definition runs its body in the frame that holds its
  environment and its argument in their slots (start), with the
  continuation that returns the value.

-}

module FPC.Semantics.GraphModel.Imp where

open import Framework.GraphModel.Prelude
open import Framework.GraphModel.Ops renaming (inl to inlD; inr to inrD; pair to
  pairD)
open import Semantics.Graph.Prim using (primD)
open import FPC.Semantics.GraphModel.Ops
open import FPC.Language.Type
open import FPC.Language.Imp
open import FPC.Framework.AllUtil using (All; []; _∷_; pos)

open import Data.List using (List; []; _∷_; length; replicate)
open import Data.Product using () renaming (_,_ to ⟨_,_⟩)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)

𝒜 : ∀ {Σ Δ I A} → Atm Σ Δ I A → Table Σ → Env Value → 𝒫 Value
𝒜 (var x _) T σ = σ (idx x)
𝒜 (lit B c) T σ = ℬ B c ptt
𝒜 (ref f) T σ = T f

𝒜s : ∀ {Σ Δ I Δs} → All (Atm Σ Δ I) Δs → Table Σ → Env Value
  → Results (𝒫 Value) (replicate (length Δs) ■)
𝒜s [] T σ = ptt
𝒜s (a ∷ as) T σ = ⟨ 𝒜 a T σ , 𝒜s as T σ ⟩

𝒮 : ∀ {Σ Δ I A} → Simple Σ Δ I A → Table Σ → Env Value → 𝒫 Value
𝒮 (atm a) T σ = 𝒜 a T σ
𝒮 (pair a b) T σ = pairD ⟨ 𝒜 a T σ , ⟨ 𝒜 b T σ , ptt ⟩ ⟩
𝒮 (callc f a) T σ =
  ⋆
  ⟨ ⋆ ⟨ car ⟨ 𝒜 f T σ , ptt ⟩ , ⟨ cdr ⟨ 𝒜 f T σ , ptt ⟩ , ptt ⟩ ⟩
    , ⟨ 𝒜 a T σ , ptt ⟩ ⟩
𝒮 (tuple {Δs} as) T σ = 𝒯 (length Δs) (𝒜s as T σ)
𝒮 (get i a) T σ = proj (pos i) ⟨ 𝒜 a T σ , ptt ⟩
𝒮 (inl a) T σ = inlD ⟨ 𝒜 a T σ , ptt ⟩
𝒮 (inr a) T σ = inrD ⟨ 𝒜 a T σ , ptt ⟩
𝒮 (prim p a b) T σ = primD p ⟨ 𝒜 a T σ , ⟨ 𝒜 b T σ , ptt ⟩ ⟩
𝒮 (fold a) T σ = 𝒜 a T σ
𝒮 (unfold a) T σ = 𝒜 a T σ

⟦_⟧ᴷ : ∀ {Σ Δ I A} → Exp Σ Δ I A → Table Σ → Env Value
  → (𝒫 Value → 𝒫 Value) → 𝒫 Value
⟦ simple s ⟧ᴷ T σ κ = κ (𝒮 s T σ)
⟦ assign x _ e₁ e₂ ⟧ᴷ T σ κ =
  ⟦ e₁ ⟧ᴷ T σ λ D →
  ⋆ ⟨ Λ ⟨ (λ X → ⟦ e₂ ⟧ᴷ T (σ [ idx x ≔ X ]) κ) , ptt ⟩ , ⟨ D , ptt ⟩ ⟩
⟦ case a x _ y _ e₁ e₂ ⟧ᴷ T σ κ =
  𝒞
    ⟨ 𝒜 a T σ
      ,
      ⟨ (λ X → ⟦ e₁ ⟧ᴷ T (σ [ idx x ≔ X ]) κ)
        , ⟨ (λ X → ⟦ e₂ ⟧ᴷ T (σ [ idx y ≔ X ]) κ) , ptt ⟩ ⟩ ⟩

{- the function whose body is b, given the table T -}
code′ : ∀ {Σ} → Table Σ → ∀ {s} → Body Σ (Args s) (DSig.cod s) → 𝒫 Value
code′ T (body Δ p e) =
  Λ ⟨ (λ X → Λ ⟨ (λ Y → ⟦ e ⟧ᴷ T (start p X Y) (λ D → D)) , ptt ⟩) , ptt ⟩

table : ∀ {Σ} → All (λ s → Body Σ (Args s) (DSig.cod s)) Σ → Table Σ
table = tables code′

{- the meaning of a whole program: the value of main -}
⟦_⟧ₚ : ∀ {A} → Program A → 𝒫 Value
⟦ program ds (body Δ p e) ⟧ₚ = ⟦ e ⟧ᴷ (table ds) (λ _ → init) (λ D → D)

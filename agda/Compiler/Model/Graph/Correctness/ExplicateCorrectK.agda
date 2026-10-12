{-

  Correctness of explicate control (Imp → CFG, Compile/Explicate.agda)
  against the continuation-passing semantics of Imp (Sem/ImpK.agda), the
  main proof (ExplicateCorrect.agda is an alternative, against the
  direct semantics): the meaning of the CFG program (Sem/CFG.agda) is
  that of the Imp program.

    explicate-correct : ⟦ explicate P ⟧ₚ ≃ ⟦ P ⟧ᴷₚ

  explicate-assign e x k is e in continuation-passing style, and so is
  the semantics: the tail it makes means e run with the continuation
  that assigns x and runs k (cps),

    ⟪ explicate-assign e x k ⟫ ≃ ⟦ e ⟧ᴷ (assignK x ⟪ k ⟫)

  and explicate-tail e means e run with halt (tail). Each case is a
  congruence: a nested assignment y := e₁; e₂ is e₁ with the
  continuation that assigns y and runs e₂, on both sides, and a case
  passes the continuation to its branches, which in CFG reach it through
  the join point, the block that holds k.

  A tail made at the blocks bs runs with any newer blocks
  (ExplicateCommon.agda), so the meaning of a continuation does not
  depend on the blocks added after it (Stable).

-}

open import SetsAsPredicates
open import Compiler.Model.Graph.Domain.ISWIM.Domain
open import Compiler.Model.Graph.Domain.ISWIM.Ops
open import Compiler.Lang.Imp as I
  using (simple; case; assign; body; program)
import Compiler.Lang.CFG as C
open import Compiler.Compile.Explicate
open import Compiler.Model.Graph.Sem.ImpK
  using (Store; _[_↦_]; checked; Table; zeros; frame; Kont; halt; ⟦_⟧ᴷ[_]; ⟦_⟧ᴷₚ)
  renaming (table to tableᴷ)
open import Compiler.Model.Graph.Sem.CFG
  using (⟦_⟧ₚ)
  renaming (⟦_⟧[_] to ⟪_⟫[_]; table to tableₜ)
open import Compiler.Model.Graph.Correctness.GlobalizeCorrect
  using (ΛΛ-≃)
open import Compiler.Model.Graph.Correctness.ConcretizeCorrect
  using (⋆-≃; 𝒞-≃)
open import Compiler.Model.Graph.Correctness.RCOCorrect using (Λ-≃)
open import Compiler.Model.Graph.Correctness.LiftLocalsCorrectK using (compile-imp-same)
open import Compiler.Model.Graph.Correctness.ExplicateCommon

open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_; length; map)
open import Data.List.Properties using (length-map)
open import Data.Nat using (ℕ; _≟_)
open import Data.Product using (proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Relation.Binary.PropositionalEquality using (refl; sym; trans; cong)
open import Relation.Nullary using (yes; no)

module Compiler.Model.Graph.Correctness.ExplicateCorrectK where

{- The continuations ------------------------------------------------------------------}

module _ (n : ℕ) where

  {- assign x the value, then K, as x := s; K does in CFG -}
  assignK : ℕ → (Store → 𝒫 Value) → Kont
  assignK x K D σ = checked n x (⋆ ⟨ Λ ⟨ (λ X → K (σ [ x ↦ X ])) , ptt ⟩ , ⟨ D , ptt ⟩ ⟩)

  assignK-≃ : ∀ {x} {K K' : Store → 𝒫 Value} {D D' σ} → (∀ σ' → K σ' ≃ K' σ') → D ≃ D' → assignK x K D σ ≃ assignK x K' D' σ
  assignK-≃ {x} {K} {K'} {σ = σ} K≃ D≃ =
    checked-≃ n {x} (⋆-≃ (Λ-≃ {λ X → K (σ [ x ↦ X ])} {λ X → K' (σ [ x ↦ X ])} λ V _ _ → K≃ _) D≃)

{- The pass preserves meanings ----------------------------------------------------------}

{- for tables T (of CFG) and T' (of Imp) that agree -}
module _ {T T' : Table} (TT : ∀ k → T k ≃ T' k) (n : ℕ) where

  open Agreeing TT n

  {- k means the same with newer blocks -}
  Stable : List C.Tail → C.Tail → Set₁
  Stable bs k = ∀ bs'' → bs ≼ bs'' → ∀ σ → ⟪ k ⟫[ T ] n (B bs'') σ ≃ ⟪ k ⟫[ T ] n (B bs) σ

  {- a jump to the block that holds k -}
  goto-stable : ∀ {k bs bs₁} → k ∷ bs ≼ bs₁ → Stable bs₁ (C.goto (length bs))
  goto-stable e₁ bs'' e = goto-≃ e₁ e

  {- explicate-assign e x k: e, then assign x and run k -}
  cps : ∀ e x k bs → Stable bs k → ∀ bs'' → proj₂ (explicate-assign e x k bs) ≼ bs'' → ∀ σ {κ : Kont}
    → (∀ D σ' → κ D σ' ≃ assignK n x (⟪ k ⟫[ T ] n (B bs)) D σ')
    → ⟪ proj₁ (explicate-assign e x k bs) ⟫[ T ] n (B bs'') σ ≃ ⟦ e ⟧ᴷ[ T' ] n σ κ
  cps (simple s) x k bs st bs'' ext σ κ≃ =
    ≃-trans (assignK-≃ n {x} (st bs'' ext) (𝒮-≃ s σ)) (≃-sym (κ≃ _ σ))
  cps (assign y e₁ e₂) x k bs st bs'' ext σ {κ} κ≃ =
    cps e₁ y t' bs₁ st' bs'' ext σ λ D σ' → ≃-sym (assignK-≃ n {y} (λ σ'' → cps e₂ x k bs st bs₁ ≼-refl σ'' κ≃) ≃-refl)
    where
    t' = proj₁ (explicate-assign e₂ x k bs)
    bs₁ = proj₂ (explicate-assign e₂ x k bs)
    st' : Stable bs₁ t'
    st' bs₂ e σ' = ≃-trans (cps e₂ x k bs st bs₂ e σ' κ≃) (≃-sym (cps e₂ x k bs st bs₁ ≼-refl σ' κ≃))
  cps (case a y e₁ e₂) x k bs st bs'' ext σ {κ} κ≃ =
    checked-≃ n {y} (𝒞-≃ {F = λ Y → B bs'' (length bs₂) (σ [ y ↦ Y ])} {λ Y → ⟦ e₁ ⟧ᴷ[ T' ] n (σ [ y ↦ Y ]) κ}
                         {λ Y → B bs'' (length bs₄) (σ [ y ↦ Y ])} {λ Y → ⟦ e₂ ⟧ᴷ[ T' ] n (σ [ y ↦ Y ]) κ}
      (𝒜-≃ a σ)
      (λ v V _ → ≃-trans (at-σ (blocks-at T n (≼-trans (grows-assign e₂ x (C.goto l) bs₃) (≼-trans ≼-∷ ext))) _)
                         (cps e₁ x (C.goto l) bs₁ (goto-stable ≼-refl) bs₂ ≼-refl _ (κ≃' ≼-refl)))
      (λ v V _ → ≃-trans (at-σ (blocks-at T n ext) _)
                         (cps e₂ x (C.goto l) bs₃ (goto-stable e₁₃) bs₄ ≼-refl _ (κ≃' e₁₃))))
    where
    l = length bs
    bs₁ = k ∷ bs
    t₁ = proj₁ (explicate-assign e₁ x (C.goto l) bs₁)
    bs₂ = proj₂ (explicate-assign e₁ x (C.goto l) bs₁)
    bs₃ = t₁ ∷ bs₂
    bs₄ = proj₂ (explicate-assign e₂ x (C.goto l) bs₃)
    e₁₃ : bs₁ ≼ bs₃
    e₁₃ = ≼-trans (grows-assign e₁ x (C.goto l) bs₁) ≼-∷
    {- the join point: a jump to the block that holds k -}
    κ≃' : ∀ {bs'} → bs₁ ≼ bs' → ∀ D σ' → κ D σ' ≃ assignK n x (⟪ C.goto l ⟫[ T ] n (B bs')) D σ'
    κ≃' e D σ' = ≃-trans (κ≃ D σ') (≃-reflexive (cong (λ K → assignK n x K D σ') (sym (blocks-at T n e))))

  {- explicate-tail e: e, then halt -}
  tail : ∀ e bs bs'' → proj₂ (explicate-tail e bs) ≼ bs'' → ∀ σ
    → ⟪ proj₁ (explicate-tail e bs) ⟫[ T ] n (B bs'') σ ≃ ⟦ e ⟧ᴷ[ T' ] n σ halt
  tail (simple s) bs bs'' ext σ = 𝒮-≃ s σ
  tail (assign x e₁ e₂) bs bs'' ext σ =
    cps e₁ x t₂ bs₁ st bs'' ext σ λ D σ' → ≃-sym (assignK-≃ n {x} (λ σ'' → tail e₂ bs bs₁ ≼-refl σ'') ≃-refl)
    where
    t₂ = proj₁ (explicate-tail e₂ bs)
    bs₁ = proj₂ (explicate-tail e₂ bs)
    st : Stable bs₁ t₂
    st bs₂ e σ' = ≃-trans (tail e₂ bs bs₂ e σ') (≃-sym (tail e₂ bs bs₁ ≼-refl σ'))
  tail (case a x e₁ e₂) bs bs'' ext σ =
    checked-≃ n {x} (𝒞-≃ {F = λ Y → B bs'' (length bs₁) (σ [ x ↦ Y ])} {λ Y → ⟦ e₁ ⟧ᴷ[ T' ] n (σ [ x ↦ Y ]) halt}
                         {λ Y → B bs'' (length bs₃) (σ [ x ↦ Y ])} {λ Y → ⟦ e₂ ⟧ᴷ[ T' ] n (σ [ x ↦ Y ]) halt}
      (𝒜-≃ a σ)
      (λ v V _ → ≃-trans (at-σ (blocks-at T n (≼-trans (grows-tail e₂ bs₂) (≼-trans ≼-∷ ext))) _)
                         (tail e₁ bs bs₁ ≼-refl _))
      (λ v V _ → ≃-trans (at-σ (blocks-at T n ext) _) (tail e₂ bs₂ bs₃ ≼-refl _)))
    where
    t₁ = proj₁ (explicate-tail e₁ bs)
    bs₁ = proj₂ (explicate-tail e₁ bs)
    bs₂ = t₁ ∷ bs₁
    bs₃ = proj₂ (explicate-tail e₂ bs₂)

{- Programs -----------------------------------------------------------------------------}

table-≃ : ∀ ds k → tableₜ (map explicate-body ds) k ≃ tableᴷ ds k
table-≃ [] k = ≃-refl
table-≃ (body n e ∷ bs) k with k ≟ length (map explicate-body bs) | k ≟ length bs
... | yes _ | yes _ = ΛΛ-≃ λ X Y → tail (table-≃ bs) n e [] _ ≼-refl (frame X Y)
... | no _ | no _ = table-≃ bs k
... | yes k≡ | no k≢ = ⊥-elim (k≢ (trans k≡ (length-map explicate-body bs)))
... | no k≢ | yes k≡ = ⊥-elim (k≢ (trans k≡ (sym (length-map explicate-body bs))))

explicate-correct : ∀ P → ⟦ explicate P ⟧ₚ ≃ ⟦ P ⟧ᴷₚ
explicate-correct (program ds (body n e)) = tail (table-≃ ds) n e [] _ ≼-refl zeros

{- the whole compiler, into CFG -}
open Into ⟦_⟧ᴷₚ compile-imp-same explicate-correct public

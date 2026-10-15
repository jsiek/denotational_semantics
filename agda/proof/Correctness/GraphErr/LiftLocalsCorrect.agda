{-

  Correctness of typed lift locals (Monᵀ → Impᵀ, Compiler/LiftLocals.agda)
  in the graph model with errors, against the continuation-passing
  semantics of Impᵀ (Semantics/GraphErr/Typed/Imp.agda):

    lift-locals-correct : ⟦ ⌜ P ⌝ₚ ⟧₅ ≃ ⟦ lift-program P ⟧ᵢ

  As in Untyped/proof/Correctness/GraphErr/LiftLocalsCorrect.agda: lift e run
  with a continuation that means K means K of the meaning of e
  (lift-sem). K is a bind (K⟨_⟩): it commutes with a let, a bind
  (let-law), and with a case (case-lawᵗ), and a slot binding is the bind
  of its body (letᵗ-≫=), since the bodies of Clos5ᵀ are monotone and
  finitary (Ok). The frame is the environment, as in Clos5ᵀ, so there
  are no slots to relate and no frame checks.

-}

module proof.Correctness.GraphErr.LiftLocalsCorrect where

open import proof.Framework.GraphModel.ErrorPrelude
open import proof.Framework.GraphModel.OpsBase using (Mono₁)
open import proof.Framework.GraphModel.Env using (Env; nonempty-env; extend-nonempty-env; •-~)
open import proof.Framework.GraphModel.TypedOk using (fin₁)
open import proof.Semantics.GraphErr.Typed.Clos2 using (caseᵗ-≃)
open import proof.Semantics.GraphErr.Typed.Clos5 renaming (ok to ok₅)
open import proof.Semantics.GraphErr.Typed.Imp
open import Semantics.GraphErr.Typed.Imp using (⟦_⟧ᴷ; codeᵢ; ⟦_⟧ᵢ; letᵗ)
open import Language.Typed.Type hiding (_≟_)
import Language.Typed.Mon as M
open M using (⌜_⌝; ⌜_⌝ᵃ; ⌜_⌝ₚ)

open import Compiler.LiftLocals

open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_) renaming (map to All-map)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Unit using (tt)
open import Level using () renaming (lift to up)
open import Relation.Binary.PropositionalEquality using (refl)

module _ {T T' : Table} (TT : ∀ k → T k ≃ T' k) (TC : ∀ k → Con (T k)) where

  ⟦_⟧ₘ : ∀ {Σ Δ A} → M.Exp Σ Δ A → Env Value → 𝒫 Value
  ⟦ e ⟧ₘ = ⟦ ⌜ e ⌝ ⟧[ T ]

  body-mono : ∀ {Σ Δ A B} (e : M.Exp Σ (B ∷ Δ) A) ρ → Mono₁ (λ X → ⟦ e ⟧ₘ (X • ρ))
  body-mono e ρ X⊆ = proj₁ (ok₅ TC ⌜ e ⌝) (•-~ _⊆_ (λ _ _ z → z) X⊆)

  {- κ, given a consistent value, means K of it -}
  Ret : Maybe (𝒫 Value → 𝒫 Value) → (𝒫 Value → 𝒫 Value) → Set₁
  Ret k κ = ∀ D → Con D → K⟨ k ⟩ D ≃ κ D

  {- a simple expression -}
  ret : ∀ {Σ Δ A} (e : M.Exp Σ Δ A) {ρ} k {κ} → KOK k → Con-env ρ → Ret k κ → K⟨ k ⟩ (⟦ e ⟧ₘ ρ) ≃ κ (⟦ ⌜ e ⌝ ⟧[ T' ] ρ)
  ret e k ok cρ r = ≃-trans (K-≃ k ok eq) (r _ (Con-⊆ (con TC ⌜ e ⌝ cρ) (proj₂ eq)))
    where eq = tm-≃ TT ⌜ e ⌝ (λ _ → ≃-refl)

  lift-sem : ∀ {Σ Δ A} (e : M.Exp Σ Δ A) {ρ} k {κ} → KOK k → nonempty-env ρ → Con-env ρ → Ret k κ
    → K⟨ k ⟩ (⟦ e ⟧ₘ ρ) ≃ ⟦ lift e ⟧ᴷ T' ρ κ
  lift-sem e@(M.atm _) k ok NE cρ r = ret e k ok cρ r
  lift-sem e@(M.pack _ _) k ok NE cρ r = ret e k ok cρ r
  lift-sem e@(M.callc _ _) k ok NE cρ r = ret e k ok cρ r
  lift-sem e@(M.tuple _) k ok NE cρ r = ret e k ok cρ r
  lift-sem e@(M.get _ _) k ok NE cρ r = ret e k ok cρ r
  lift-sem e@(M.inl _) k ok NE cρ r = ret e k ok cρ r
  lift-sem e@(M.inr _) k ok NE cρ r = ret e k ok cρ r
  lift-sem e@(M.prim _ _ _) k ok NE cρ r = ret e k ok cρ r
  lift-sem e@(M.inject _ _) k ok NE cρ r = ret e k ok cρ r
  lift-sem e@(M.project _ _) k ok NE cρ r = ret e k ok cρ r
  lift-sem (M.case a e₁ e₂) {ρ} k {κ} ok NE cρ r =
    ≃-trans (case-lawᵗ k ok (con TC ⌜ a ⌝ᵃ cρ) (body-mono e₁ ρ) (body-mono e₂ ρ))
      (caseᵗ-≃ {F = λ X → K⟨ k ⟩ (⟦ e₁ ⟧ₘ (X • ρ))} {λ X → ⟦ lift e₁ ⟧ᴷ T' (X • ρ) κ}
               {λ X → K⟨ k ⟩ (⟦ e₂ ⟧ₘ (X • ρ))} {λ X → ⟦ lift e₂ ⟧ᴷ T' (X • ρ) κ}
         (tm-≃ TT ⌜ a ⌝ᵃ (λ _ → ≃-refl))
         (λ V ne c _ → lift-sem e₁ k ok (extend-nonempty-env NE (E≢[]⇒nonempty-mem ne)) (Con-• (≈⇒Con c) cρ) r)
         (λ V ne c _ → lift-sem e₂ k ok (extend-nonempty-env NE (E≢[]⇒nonempty-mem ne)) (Con-• (≈⇒Con c) cρ) r))
  lift-sem (M.let′ e₁ e₂) {ρ} k {κ} ok NE cρ r =
    ≃-trans (let-law k ok {⟦ e₁ ⟧ₘ ρ} {λ X → ⟦ e₂ ⟧ₘ (X • ρ)}) (lift-sem e₁ (just G) okG NE cρ r₁)
    where
    G = λ X → K⟨ k ⟩ (⟦ e₂ ⟧ₘ (X • ρ))
    okG = K-ok k ok (body-mono e₂ ρ) (λ Y neY → fin₁ (ok₅ TC ⌜ e₂ ⌝) NE neY)
    r₁ : Ret (just G) (λ D → letᵗ D λ X → ⟦ lift e₂ ⟧ᴷ T' (X • ρ) κ)
    r₁ D cD = ≃-trans (≃-sym (letᵗ-≫= (proj₁ okG) cD (λ c → proj₂ okG _ c)))
                      (letᵗ-≃ {F = G} {λ X → ⟦ lift e₂ ⟧ᴷ T' (X • ρ) κ} ≃-refl
                         (λ V ne c _ → lift-sem e₂ k ok (extend-nonempty-env NE (E≢[]⇒nonempty-mem ne)) (Con-• (≈⇒Con c) cρ) r))

lift-locals-correct : ∀ (P : M.Program) → ⟦ ⌜ P ⌝ₚ ⟧₅ ≃ ⟦ lift-program P ⟧ᵢ
lift-locals-correct (M.program ds e) =
  lift-sem (TT ds) (tbl-con (λ TC d → code₅-con TC d) (All-map ⌜_⌝ ds)) e nothing (up tt) (λ _ → ⟨ ω , refl ⟩) (λ _ → Con-⌈⌉ ω) (λ _ _ → ≃-refl)
  where
  TT : ∀ {Σ ns} (ds : All (λ n → M.Exp Σ (Any ∷ ⟪ tup n ⟫ ∷ []) Any) ns) k → tbl (code₅ {Σ}) (All-map ⌜_⌝ ds) k ≃ tbl (codeᵢ {Σ}) (All-map lift ds) k
  TT {Σ} ds = tbl-map {c = code₅ {Σ}} {codeᵢ {Σ}} (λ T → ∀ k → Con (T k)) ⌜_⌝ lift (λ es → tbl-con (λ TC d → code₅-con TC d) (All-map ⌜_⌝ es))
    (λ TT' TC' d → ΛΛᵐ-≃′ λ V U neV cV _ neU cU _ →
       lift-sem TT' TC' d nothing (up tt)
         (extend-nonempty-env (extend-nonempty-env (λ _ → ⟨ ω , refl ⟩) (E≢[]⇒nonempty-mem neV)) (E≢[]⇒nonempty-mem neU))
         (Con-• (≈⇒Con cU) (Con-• (≈⇒Con cV) (λ _ → Con-⌈⌉ ω))) (λ _ _ → ≃-refl)) ds

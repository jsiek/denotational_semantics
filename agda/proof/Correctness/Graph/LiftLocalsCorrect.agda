{-

  Correctness of typed lift locals (Monᵀ → Impᵀ) in the graph model: the
  continuation-passing meaning of the output (Semantics/Graph/Typed/Imp.agda)
  is the meaning of the input (its embedding into Clos5ᵀ) given to the
  continuation.

    lift-sem : ⟦ lift e ⟧ᴷ T σ K⟨ k ⟩ ≃ K⟨ k ⟩ (⟦ ⌜ e ⌝ ⟧[ T' ] σ)

  for tables that agree and a consistent frame. Every continuation of
  the Impᵀ semantics is K⟨ k ⟩: the end of a body (nothing) or the rest
  of an assignment, a let (just G). A simple expression is the same
  operator on the same atoms; an assignment and a case commute with the
  continuation (let-law, case-law, proof/Framework/GraphModel/Laws.agda).

-}

module proof.Correctness.Graph.LiftLocalsCorrect where

open import proof.Framework.GraphModel.Prelude
open import proof.Framework.GraphModel.Ops renaming (inl to inlD; inr to inrD)
open import proof.Framework.GraphModel.ContinuityBase using (mono)
open import proof.Framework.GraphModel.Env using (Env; •-~)
open import proof.Framework.GraphModel.Laws using (K⟨_⟩; K-≃; let-law; case-law)
open import proof.Semantics.Graph.Prim using (primD-≃)
open import proof.Semantics.Graph.Typed.Ops
open import proof.Semantics.Graph.Typed.Clos5 using (ok; con; code-con; table-con)
open import Semantics.Graph.Typed.Clos5
import Semantics.Graph.Typed.Imp as I
open I using (⟦_⟧ᴷ; 𝒜; 𝒜s; 𝒮)
open import Language.Typed.Type hiding (_≟_)
import Language.Typed.Mon as M
open M using (Atm; var; lit; ref; ⌜_⌝; ⌜_⌝ᵃ; ⌜_⌝ᵛ; ⌜_⌝ₚ)
open import Compiler.LiftLocals

open import Data.Fin using (zero; suc)
open import Data.List using (List; []; _∷_; length)
open import Data.List.Relation.Unary.All using (All; []; _∷_) renaming (map to All-map)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Nat using (ℕ; _≟_)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Unit using (⊤)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Data.Vec using (Vec; []; _∷_)
open import Level using () renaming (lift to up)
open import Relation.Nullary using (yes; no)

module _ {Σ} {T T' : Table Σ} (cT : ConT T') (TT : ∀ {n} (f : Σ ∋ n) → T f ≃ T' f) where

  atm-≃ : ∀ {Δ A} (a : Atm Σ Δ A) σ → 𝒜 a T σ ≃ ⟦ ⌜ a ⌝ᵃ ⟧[ T' ] σ
  atm-≃ (var x) σ = ≃-refl
  atm-≃ (lit B c) σ = ≃-refl
  atm-≃ (ref f) σ = TT f

  atms-≃ : ∀ {Δ n} (as : Vec (Atm Σ Δ Any) n) σ i → nthD (𝒜s as T σ) i ≃ nthD (⟦ ⌜ as ⌝ᵛ ⟧s[ T' ] σ) i
  atms-≃ (a ∷ as) σ zero = atm-≃ a σ
  atms-≃ (a ∷ as) σ (suc i) = atms-≃ as σ i

  lift-sem : ∀ {Δ A} (e : M.Exp Σ Δ A) σ k → Con-env σ → ⟦ lift e ⟧ᴷ T σ K⟨ k ⟩ ≃ K⟨ k ⟩ (⟦ ⌜ e ⌝ ⟧[ T' ] σ)
  lift-sem (M.atm a) σ k C = K-≃ k (atm-≃ a σ)
  lift-sem (M.pack a b) σ k C = K-≃ k (mono-≃ pair-mono ⟨ up (atm-≃ a σ) , ⟨ up (atm-≃ b σ) , ptt ⟩ ⟩)
  lift-sem (M.callc a b) σ k C = K-≃ k (mono-≃ (mono (callc-good {⊤})) ⟨ up (atm-≃ a σ) , ⟨ up (atm-≃ b σ) , ptt ⟩ ⟩)
  lift-sem (M.tuple as) σ k C = K-≃ k (𝒯-≃ _ (atms-≃ as σ))
  lift-sem (M.get i a) σ k C = K-≃ k (proj-≃ i (atm-≃ a σ))
  lift-sem (M.inl a) σ k C = K-≃ k (inl-≃ (atm-≃ a σ))
  lift-sem (M.inr a) σ k C = K-≃ k (inr-≃ (atm-≃ a σ))
  lift-sem (M.prim p a b) σ k C = K-≃ k (primD-≃ p (atm-≃ a σ) (atm-≃ b σ))
  lift-sem (M.inject G a) σ k C = K-≃ k (atm-≃ a σ)
  lift-sem (M.project t a) σ k C = K-≃ k (project-≃ fun₄ t (atm-≃ a σ))
  lift-sem (M.let′ e₁ e₂) σ k C =
    ≃-trans (lift-sem e₁ σ (just λ X → ⟦ lift e₂ ⟧ᴷ T (X • σ) K⟨ k ⟩) C)
    (≃-trans (⋆-≃ (Λ-≃ {λ X → ⟦ lift e₂ ⟧ᴷ T (X • σ) K⟨ k ⟩} {λ X → K⟨ k ⟩ (⟦ ⌜ e₂ ⌝ ⟧[ T' ] (X • σ))}
                     λ V _ c → lift-sem e₂ (mem V • σ) k (Con-• (≈⇒Con c) C)) ≃-refl)
             (≃-sym (let-law k (con cT ⌜ e₁ ⌝ C) λ X⊆ → proj₁ (ok cT ⌜ e₂ ⌝) (•-~ _⊆_ (λ _ _ z → z) X⊆))))
  lift-sem (M.case a e₁ e₂) σ k C =
    ≃-trans (𝒞-≃ {F = λ X → ⟦ lift e₁ ⟧ᴷ T (X • σ) K⟨ k ⟩} {λ X → K⟨ k ⟩ (⟦ ⌜ e₁ ⌝ ⟧[ T' ] (X • σ))}
                  {λ X → ⟦ lift e₂ ⟧ᴷ T (X • σ) K⟨ k ⟩} {λ X → K⟨ k ⟩ (⟦ ⌜ e₂ ⌝ ⟧[ T' ] (X • σ))}
                  (atm-≃ a σ) (λ v V c → lift-sem e₁ _ k (Con-• (≈⇒Con c) C)) (λ v V c → lift-sem e₂ _ k (Con-• (≈⇒Con c) C)))
            (≃-sym (case-law k (con cT ⌜ M.atm a ⌝ C) (mono′ e₁) (mono′ e₂)))
    where mono′ = λ (e : M.Exp Σ (Any ∷ _) Any) {X} {X'} X⊆ → proj₁ (ok cT ⌜ e ⌝) {X • σ} {X' • σ} (•-~ _⊆_ (λ _ _ z → z) X⊆)

{- Programs ---------------------------------------------------------------------------}

{- the table of the output means what the table of the input does -}
table-lift : ∀ {Σ ns} (ds : All (λ n → M.Exp Σ (Any ∷ ⟪ tup n ⟫ ∷ []) Any) ns) {n} (f : Σ ∋ n)
  → tables I.code′ (All-map lift ds) f ≃ tables code′ (All-map ⌜_⌝ ds) f
table-lift [] f = ≃-refl
table-lift {ns = _ ∷ ns} (d ∷ ds) f with lvl f ≟ length ns
... | yes _ = Λ-≃ λ V _ cV → Λ-≃ λ U _ cU →
  lift-sem (tables-con code-con (All-map ⌜_⌝ ds)) (table-lift ds) d _ nothing
    (Con-• (≈⇒Con cU) (Con-• (≈⇒Con cV) (λ _ → Con-⌈⌉ ω)))
... | no _ = table-lift ds f

lift-locals-correct : ∀ (P : M.Program) → I.⟦ lift-program P ⟧ₚ ≃ ⟦ ⌜ P ⌝ₚ ⟧ₚ
lift-locals-correct (M.program ds e) =
  lift-sem (table-con (All-map ⌜_⌝ ds)) (table-lift ds) e _ nothing (λ _ → Con-⌈⌉ ω)

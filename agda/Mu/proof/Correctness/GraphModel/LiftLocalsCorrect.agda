{-

  Correctness of lift locals (Monμ → Impμ) in the graph model, as for
  the typed pass (proof/Correctness/Graph/LiftLocalsCorrect.agda): the
  continuation-passing meaning of the output (Mu/Semantics/GraphModel/Imp.agda)
  is the meaning of the input (its embedding into GlobalFunμ) given to the
  continuation.

    lift-sem : K⟨ k ⟩ (⟦ ⌜ e ⌝ ⟧[ T ] σ) ≃ ⟦ lift e ⟧ᴷ T' σ K⟨ k ⟩

  for tables that agree and a consistent frame. Every continuation of
  the Impμ semantics is K⟨ k ⟩: the end of a body (nothing) or the rest
  of an assignment, a let (just G). A simple expression is the same
  operator on the same atoms; an assignment and a case commute with the
  continuation (let-law, case-law, proof/Framework/GraphModel/Laws.agda).

-}

module Mu.proof.Correctness.GraphModel.LiftLocalsCorrect where

open import proof.Framework.GraphModel.Prelude
open import proof.Framework.GraphModel.Ops renaming (inl to inlD; inr to inrD)
open import proof.Framework.GraphModel.ContinuityBase using (mono)
open import proof.Framework.GraphModel.Env using (Env; •-~)
open import proof.Framework.GraphModel.Laws using (K⟨_⟩; K-≃; let-law; case-law)
open import proof.Semantics.Graph.Prim using (primD-≃)
open import Mu.proof.Semantics.GraphModel.Ops
open import Mu.proof.Semantics.GraphModel.GlobalFun using (ok; con; code-con; table-con)
open import Mu.Semantics.GraphModel.GlobalFun
import Mu.Semantics.GraphModel.Imp as I
open I using (⟦_⟧ᴷ; 𝒜; 𝒜s; 𝒮)
open import Mu.Language.Type
import Mu.Language.Mon as M
open M using (DSig; Args; Atm; var; lit; ref; ⌜_⌝; ⌜_⌝ᵃ; ⌜_⌝ᵛ; ⌜_⌝ₚ)
open import Mu.Compiler.LiftLocals
open import Mu.proof.Semantics.GraphModel.Binders using (lam-≃; let-≃; case-≃; body-mono)
open import Mu.Framework.AllUtil using (All; []; _∷_; pos) renaming (map to All-map)

open import Data.Fin using (zero; suc)
open import Data.List using (List; []; _∷_; length)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Nat using (ℕ; _≟_)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Unit using (⊤)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Level using () renaming (lift to up)
open import Relation.Nullary using (yes; no)

module _ {Σ} {T T' : Table Σ} (cT : ConT T) (TT : ∀ {s} (f : Σ ∋ s) → T f ≃ T' f) where

  atm-≃ : ∀ {Δ A} (a : Atm Σ Δ A) σ → ⟦ ⌜ a ⌝ᵃ ⟧[ T ] σ ≃ 𝒜 a T' σ
  atm-≃ (var x) σ = ≃-refl
  atm-≃ (lit B c) σ = ≃-refl
  atm-≃ (ref f) σ = TT f

  atms-≃ : ∀ {Δ Δs} (as : All (Atm Σ Δ) Δs) σ i → nthD (⟦ ⌜ as ⌝ᵛ ⟧s[ T ] σ) i ≃ nthD (𝒜s as T' σ) i
  atms-≃ (a ∷ as) σ zero = atm-≃ a σ
  atms-≃ (a ∷ as) σ (suc i) = atms-≃ as σ i

  lift-sem : ∀ {Δ A} (e : M.Exp Σ Δ A) σ k → Con-env σ → K⟨ k ⟩ (⟦ ⌜ e ⌝ ⟧[ T ] σ) ≃ ⟦ lift e ⟧ᴷ T' σ K⟨ k ⟩
  lift-sem (M.atm a) σ k C = K-≃ k (atm-≃ a σ)
  lift-sem (M.pack a b) σ k C = K-≃ k (mono-≃ pair-mono ⟨ up (atm-≃ a σ) , ⟨ up (atm-≃ b σ) , ptt ⟩ ⟩)
  lift-sem (M.callc a b) σ k C = K-≃ k (mono-≃ (mono (callc-good {⊤})) ⟨ up (atm-≃ a σ) , ⟨ up (atm-≃ b σ) , ptt ⟩ ⟩)
  lift-sem (M.tuple as) σ k C = K-≃ k (𝒯-≃ _ (atms-≃ as σ))
  lift-sem (M.get i a) σ k C = K-≃ k (proj-≃ (pos i) (atm-≃ a σ))
  lift-sem (M.inl a) σ k C = K-≃ k (inl-≃ (atm-≃ a σ))
  lift-sem (M.inr a) σ k C = K-≃ k (inr-≃ (atm-≃ a σ))
  lift-sem (M.prim p a b) σ k C = K-≃ k (primD-≃ p (atm-≃ a σ) (atm-≃ b σ))
  lift-sem (M.fold a) σ k C = K-≃ k (atm-≃ a σ)
  lift-sem (M.unfold a) σ k C = K-≃ k (atm-≃ a σ)
  lift-sem (M.let′ e₁ e₂) σ k C =
    ≃-trans (let-law k (con cT ⌜ e₁ ⌝ C) (body-mono (ok cT ⌜ e₂ ⌝) σ))
      (≃-trans (let-≃ ≃-refl λ X _ cX → lift-sem e₂ (X • σ) k (Con-• cX C)) (lift-sem e₁ σ (just λ X → ⟦ lift e₂ ⟧ᴷ T' (X • σ) K⟨ k ⟩) C))
  lift-sem (M.case a e₁ e₂) σ k C =
    ≃-trans (case-law k (con cT ⌜ M.atm a ⌝ C) (body-mono (ok cT ⌜ e₁ ⌝) σ) (body-mono (ok cT ⌜ e₂ ⌝) σ))
      (case-≃ (atm-≃ a σ) (λ X _ cX → lift-sem e₁ (X • σ) k (Con-• cX C)) (λ X _ cX → lift-sem e₂ (X • σ) k (Con-• cX C)))

  {- the code of a definition means the code of its output -}
  code-lift : ∀ {s} (d : M.Exp Σ (Args s) (DSig.cod s)) → code′ T ⌜ d ⌝ ≃ I.code′ T' (lift d)
  code-lift d = lam-≃ λ X _ cX → lam-≃ λ Y _ cY → lift-sem d _ nothing (Con-• cY (Con-• cX (λ _ → Con-⌈⌉ ⟨⟩)))

{- Programs ---------------------------------------------------------------------------}

{- the table of the output means what the table of the input does -}
table-lift : ∀ {Σ ss} (ds : All (λ s → M.Exp Σ (Args s) (DSig.cod s)) ss) {s} (f : Σ ∋ s)
  → tables code′ (All-map ⌜_⌝ ds) f ≃ tables I.code′ (All-map lift ds) f
table-lift [] f = ≃-refl
table-lift {ss = _ ∷ ss} (d ∷ ds) f with lvl f ≟ length ss
... | yes _ = code-lift (tables-con code-con (All-map ⌜_⌝ ds)) (table-lift ds) d
... | no _ = table-lift ds f

lift-locals-correct : ∀ {A} (P : M.Program A) → ⟦ ⌜ P ⌝ₚ ⟧ₚ ≃ I.⟦ lift-program P ⟧ₚ
lift-locals-correct (M.program ds e) =
  lift-sem (table-con (All-map ⌜_⌝ ds)) (table-lift ds) e _ nothing (λ _ → Con-⌈⌉ ⟨⟩)

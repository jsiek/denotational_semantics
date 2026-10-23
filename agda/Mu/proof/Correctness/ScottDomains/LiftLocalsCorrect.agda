{-

  Correctness of lift locals (Monμ → Impμ) in Scott domains
  (Mu/Semantics/ScottDomains/{GlobalFun,Imp}.agda), as in the graph model
  (Mu/proof/Correctness/GraphModel/LiftLocalsCorrect.agda), with equality of
  values in place of equality of sets: the continuation-passing meaning
  of the output is the meaning of the input (its embedding into GlobalFunμ)
  given to the continuation,

    lift-sem : κ (⟦ ⌜ e ⌝ ⟧[ T ] σ) ＝ ⟦ lift e ⟧ᴷ T' σ κ

  for tables that agree and every strict continuation κ (the graph
  model's K⟨ k ⟩; there is no consistency to track). A simple
  expression is the same operator on the same atoms; an assignment and
  a case commute with the continuation, as κ is strict (seq-strict,
  cases-strict-natural in Mu/proof/Semantics/ScottDomains/BackEndLemmas.agda,
  in place of the let-law and case-law). The continuation that an
  assignment gives its right-hand side, app (Λ F), is strict too.

-}

open import MLTT.Spartan hiding (inl; inr; cases)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons
open import UF.Base using (ap₂; happly)

open import Mu.Language.Type
import Mu.Language.Mon as M
open M using (DSig; Args; Atm; var; lit; ref; ⌜_⌝; ⌜_⌝ᵃ; ⌜_⌝ᵛ; ⌜_⌝ₚ)
open import Mu.Compiler.LiftLocals
open import Mu.Framework.AllUtil using (All; []; _∷_; pos) renaming (map to All-map)
open import Framework.abt.GSubst using (_•_)
open import Data.List using (List; []; _∷_; length)
open import Data.Fin using (Fin; zero; suc)

module Mu.proof.Correctness.ScottDomains.LiftLocalsCorrect
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : propext 𝓤₀)
       where

open import Framework.Scott.Base pt fe
open import proof.Framework.Scott.Ops pt fe pe renaming (app to appᵈ; inl to inlᵈ; inr to inrᵈ; tuple to tupleᵈ)
open import proof.Framework.Scott.Semantics pt fe pe
open import Semantics.Scott.Prim pt fe pe using (primD)
open import Mu.Semantics.ScottDomains.Ops pt fe pe
open import Mu.Semantics.ScottDomains.GlobalFun pt fe pe
import Mu.Semantics.ScottDomains.Imp pt fe pe as I
open I using (⟦_⟧ᴷ; 𝒜; 𝒜s; K; idK; underK)
open import Mu.proof.Semantics.ScottDomains.BackEndLemmas pt fe pe using (seq-⊥; cases-strict-natural; codeᶜ-cong; tables-cons)

module _ {Σ} {T T' : Table Σ} (TT : ∀ {s} (f : Σ ∋ s) → T f ＝ T' f) where

  atm-＝ : ∀ {Δ A} (a : Atm Σ Δ A) σ → ⟦ ⌜ a ⌝ᵃ ⟧[ T ] · σ ＝ 𝒜 a T' · σ
  atm-＝ (var x) σ = refl
  atm-＝ (lit B c) σ = refl
  atm-＝ (ref f) σ = TT f

  atms-＝ : ∀ {Δ Δs} (as : All (Atm Σ Δ) Δs) σ → ⟦ ⌜ as ⌝ᵛ ⟧s[ T ] · σ ＝ 𝒜s as T' · σ
  atms-＝ [] σ = refl
  atms-＝ (a ∷ as) σ = dfunext fe λ { zero → atm-＝ a σ ; (suc i) → happly (atms-＝ as σ) i }

  lift-sem : ∀ {Δ A} (e : M.Exp Σ Δ A) σ (κ : ⟨ K ⟩) → κ · ⊥𝔻 ＝ ⊥𝔻
    → κ · (⟦ ⌜ e ⌝ ⟧[ T ] · σ) ＝ ⟦ lift e ⟧ᴷ T' · σ · κ
  lift-sem (M.atm a) σ κ s = ap (κ ·_) (atm-＝ a σ)
  lift-sem (M.pack a b) σ κ s = ap₂ (λ x y → κ · (pair · x · y)) (atm-＝ a σ) (atm-＝ b σ)
  lift-sem (M.callc a b) σ κ s =
    ap₂ (λ x y → κ · (appᵈ · (appᵈ · (car · x) · (cdr · x)) · y)) (atm-＝ a σ) (atm-＝ b σ)
  lift-sem (M.tuple {Δs} as) σ κ s = ap (λ x → κ · (tupleᵈ (length Δs) · x)) (atms-＝ as σ)
  lift-sem (M.get i a) σ κ s = ap (λ x → κ · (proj (pos i) · x)) (atm-＝ a σ)
  lift-sem (M.inl a) σ κ s = ap (λ x → κ · (inlᵈ · x)) (atm-＝ a σ)
  lift-sem (M.inr a) σ κ s = ap (λ x → κ · (inrᵈ · x)) (atm-＝ a σ)
  lift-sem (M.prim p a b) σ κ s = ap₂ (λ x y → κ · (primD p · x · y)) (atm-＝ a σ) (atm-＝ b σ)
  lift-sem (M.fold a) σ κ s = ap (κ ·_) (atm-＝ a σ)
  lift-sem (M.unfold a) σ κ s = ap (κ ·_) (atm-＝ a σ)
  lift-sem (M.let′ e₁ e₂) σ κ s =
    ap (κ ·_) (letᶜ-β Mᵈ Nᵈ σ)
    ∙ seq-strict κ s D (Nᵈ · (D • σ))
    ∙ ap (seq · D ·_) (lift-sem e₂ (D • σ) κ s)
    ∙ (app-Λ F D) ⁻¹
    ∙ lift-sem e₁ σ (appᵈ · (Λ · F)) (app-Λ F ⊥𝔻 ∙ seq-⊥ (F · ⊥𝔻))
   where
    Mᵈ = ⟦ ⌜ e₁ ⌝ ⟧[ T ]
    Nᵈ = ⟦ ⌜ e₂ ⌝ ⟧[ T ]
    D = Mᵈ · σ
    F = underK (⟦ lift e₂ ⟧ᴷ T') · (σ , κ)
  lift-sem (M.case a e₁ e₂) σ κ s =
    cases-strict-natural κ s (abs ⟦ ⌜ e₁ ⌝ ⟧[ T ] · σ) (abs ⟦ ⌜ e₂ ⌝ ⟧[ T ] · σ) F₁ F₂
      (λ X → lift-sem e₁ (X • σ) κ s) (λ X → lift-sem e₂ (X • σ) κ s) (⟦ ⌜ a ⌝ᵃ ⟧[ T ] · σ)
    ∙ ap (λ x → cases · x · (strict · F₁ , strict · F₂)) (atm-＝ a σ)
   where
    F₁ = underK (⟦ lift e₁ ⟧ᴷ T') · (σ , κ)
    F₂ = underK (⟦ lift e₂ ⟧ᴷ T') · (σ , κ)

  {- the code of a definition means the code of its output -}
  code-lift : ∀ {s} (d : M.Exp Σ (Args s) (DSig.cod s)) → code′ T ⌜ d ⌝ ＝ I.code′ T' (lift d)
  code-lift d = codeᶜ-cong ⟦ ⌜ d ⌝ ⟧[ T ] (∘₁ Env (K ⟹₁ 𝔻) 𝔻 (⟦ lift d ⟧ᴷ T') (at-point₁ K 𝔻 idK))
                  (λ X Y _ _ → lift-sem d (env₂ X Y) idK refl)

{- Programs ---------------------------------------------------------------------------}

{- the table of the output means what the table of the input does -}
table-lift : ∀ {Σ ss} (ds : All (λ s → M.Exp Σ (Args s) (DSig.cod s)) ss) {s} (f : Σ ∋ s)
  → tables code′ (All-map ⌜_⌝ ds) f ＝ tables I.code′ (All-map lift ds) f
table-lift [] f = refl
table-lift (d ∷ ds) f =
  tables-cons code′ I.code′ ⌜ d ⌝ (All-map ⌜_⌝ ds) (lift d) (All-map lift ds) f
    (code-lift (table-lift ds) d)
    (table-lift ds f)

lift-locals-correct : ∀ {A} (P : M.Program A) → ⟦ ⌜ P ⌝ₚ ⟧ₚ ＝ I.⟦ lift-program P ⟧ₚ
lift-locals-correct (M.program ds e) =
  lift-sem (table-lift ds) e ρ₀ idK refl

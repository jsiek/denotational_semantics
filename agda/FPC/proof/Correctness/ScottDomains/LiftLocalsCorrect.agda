{-

  Correctness of lift locals (Monμ → Impμ) in Scott domains
  (FPC/Semantics/ScottDomains/{GlobalFun,Imp}.agda), as in the graph model
  (FPC/proof/Correctness/GraphModel/LiftLocalsCorrect.agda), with equality of
  values in place of equality of sets: the continuation-passing meaning
  of the output is the meaning of the input (its embedding into GlobalFunμ)
  given to the continuation,

    lift-sem : κ (⟦ ⌜ e ⌝ ⟧[ T ] γ) ＝ ⟦ lift e q ρ ok o ⟧ᴷ T' σ κ

  for tables that agree, every strict continuation κ (the graph model's
  K⟨ k ⟩; there is no consistency to track), and a Monμ environment γ
  and an Impμ frame σ that agree through the slots ρ (Ag: variable x
  means in γ what slot ρ x holds in σ). A simple expression is the same
  operator on the same atoms; an assignment and a case commute with the
  continuation, as κ is strict (seq-strict, cases-strict-natural in
  FPC/proof/Semantics/ScottDomains/BackEndLemmas.agda, in place of the
  let-law and case-law). The continuation that an assignment gives its
  right-hand side, app (Λ F), is strict too. A let or a case writes a
  slot that is not initialized, while the variables in scope are in
  initialized slots, so the write keeps the agreement (ag-ext, by
  ∈∉-idx). A definition starts with its environment and argument at the
  slots of its parameters (frame₂), which agrees with env₂ through
  those slots.

-}

open import MLTT.Spartan hiding (inl; inr; cases; Type)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons
open import UF.Base using (ap₂; happly)

open import FPC.Language.Type
import FPC.Language.Mon as M
open M using (DSig; Args; Atm; var; lit; ref; ⌜_⌝; ⌜_⌝ᵃ; ⌜_⌝ᵛ; ⌜_⌝ₚ)
open import FPC.Language.Imp using (Inits; _∉_; Only; ∈∉-idx; fill-∈;
  only-initial)
open import Framework.Membership using (_⊑_; here⊑; ⊑-∋; ⊑-trans)
open import FPC.Compiler.LiftLocals
open import FPC.Framework.AllUtil using (All; []; _∷_; pos) renaming (map to
  All-map)
open import Framework.abt.GSubst using (_•_)
open import Data.List using (List; []; _∷_; length)
open import Data.Fin using (Fin; zero; suc)
open import Data.Empty using (⊥-elim-irr)
import Relation.Binary.PropositionalEquality as Eq

module FPC.proof.Correctness.ScottDomains.LiftLocalsCorrect
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : propext 𝓤₀)
       where

open import Framework.Scott.Base pt fe
open import proof.Framework.Scott.Ops pt fe pe renaming (app to appᵈ; inl to
  inlᵈ; inr to inrᵈ; tuple to tupleᵈ; ext to extᵈ)
open import proof.Framework.Scott.Semantics pt fe pe
open import Semantics.Scott.Prim pt fe pe using (primD)
open import FPC.Semantics.ScottDomains.Ops pt fe pe
open import FPC.Semantics.ScottDomains.GlobalFun pt fe pe
import FPC.Semantics.ScottDomains.Imp pt fe pe as I
open I using (⟦_⟧ᴷ; 𝒜; 𝒜s; K; idK; underK)
open import FPC.proof.Semantics.ScottDomains.BackEndLemmas pt fe pe using
  (seq-⊥; cases-strict-natural; codeᶜ-codeᶠ; tables-cons; params-≢;
  frame₂-arg; frame₂-env)

{- the Monμ environment γ and the Impμ frame σ agree through the slots ρ -}
Ag : ∀ {Γ Δ} → Slots Γ Δ → ⟨ Env ⟩ → ⟨ Env ⟩ → 𝓤₁ ̇
Ag {Γ} ρ γ σ = ∀ {A} (x : Γ ∋ A) → γ (idx x) ＝ σ (idx (ρ x))

{- a write to a slot that is not initialized keeps the agreement on the
   variables in scope, whose slots are initialized -}
ag-ext : ∀ {Γ Δ A} {I : Inits Δ} (s : Δ ∋ A) (ρ : Slots Γ Δ) {γ σ X}
  → .(Inited ρ I)
  → .(s ∉ I)
  → Ag ρ γ σ
  → Ag (ext s ρ) (X • γ) (write (idx s) σ X)
ag-ext s ρ {σ = σ} {X} ok n ag Z = write-same (idx s) σ X ⁻¹
ag-ext {I = I} s ρ {σ = σ} {X} ok n ag (S y) =
  ag y
  ∙ write-other (idx s) (idx (ρ y)) σ X
      (λ e → ⊥-elim-irr (∈∉-idx {I = I} (ρ y) s (ok y) n (Eq.sym e))) ⁻¹

module _ {Σ} {T T' : Table Σ} (TT : ∀ {s} (f : Σ ∋ s) → T f ＝ T' f) where

  atm-＝ : ∀ {Γ Δ A} {I : Inits Δ} {ρ : Slots Γ Δ} .(ok : Inited ρ I)
    (a : Atm Σ Γ A) {γ σ}
    → Ag ρ γ σ
    → ⟦ ⌜ a ⌝ᵃ ⟧[ T ] · γ ＝ 𝒜 (atom {I = I} ρ ok a) T' · σ
  atm-＝ ok (var x) ag = ag x
  atm-＝ ok (lit B c) ag = refl
  atm-＝ ok (ref f) ag = TT f

  atms-＝ : ∀ {Γ Δ Δs} {I : Inits Δ} {ρ : Slots Γ Δ} .(ok : Inited ρ I)
    (as : All (Atm Σ Γ) Δs) {γ σ}
    → Ag ρ γ σ
    → ⟦ ⌜ as ⌝ᵛ ⟧s[ T ] · γ ＝ 𝒜s (atoms {I = I} ρ ok as) T' · σ
  atms-＝ ok [] ag = refl
  atms-＝ {I = I} ok (a ∷ as) ag =
    dfunext fe λ
      { zero → atm-＝ {I = I} ok a ag
      ; (suc i) → happly (atms-＝ {I = I} ok as ag) i }

  lift-sem : ∀ {Γ Δ D A} {I : Inits Δ} (e : M.Exp Σ Γ A)
    (q : binds e D ⊑ Δ) (ρ : Slots Γ Δ) .(ok : Inited ρ I)
    .(o : Only (⊑-trans (binds-⊒ e D) q) I) {γ σ} (κ : ⟨ K ⟩)
    → Ag ρ γ σ
    → κ · ⊥𝔻 ＝ ⊥𝔻
    → κ · (⟦ ⌜ e ⌝ ⟧[ T ] · γ) ＝ ⟦ lift e q ρ ok o ⟧ᴷ T' · σ · κ
  lift-sem {I = I} (M.atm a) q ρ ok o κ ag s = ap (κ ·_) (atm-＝ {I = I} ok a ag)
  lift-sem {I = I} (M.pair a b) q ρ ok o κ ag s =
    ap₂ (λ x y → κ · (pair · x · y)) (atm-＝ {I = I} ok a ag) (atm-＝ {I = I} ok b ag)
  lift-sem {I = I} (M.callc a b) q ρ ok o κ ag s =
    ap₂ (λ x y → κ · (appᵈ · (appᵈ · (car · x) · (cdr · x)) · y))
      (atm-＝ {I = I} ok a ag) (atm-＝ {I = I} ok b ag)
  lift-sem {I = I} (M.tuple {Δs} as) q ρ ok o κ ag s =
    ap (λ x → κ · (tupleᵈ (length Δs) · x)) (atms-＝ {I = I} ok as ag)
  lift-sem {I = I} (M.get i a) q ρ ok o κ ag s =
    ap (λ x → κ · (proj (pos i) · x)) (atm-＝ {I = I} ok a ag)
  lift-sem {I = I} (M.inl a) q ρ ok o κ ag s =
    ap (λ x → κ · (inlᵈ · x)) (atm-＝ {I = I} ok a ag)
  lift-sem {I = I} (M.inr a) q ρ ok o κ ag s =
    ap (λ x → κ · (inrᵈ · x)) (atm-＝ {I = I} ok a ag)
  lift-sem {I = I} (M.prim p a b) q ρ ok o κ ag s =
    ap₂ (λ x y → κ · (primD p · x · y)) (atm-＝ {I = I} ok a ag) (atm-＝ {I = I} ok b ag)
  lift-sem {I = I} (M.fold a) q ρ ok o κ ag s = ap (κ ·_) (atm-＝ {I = I} ok a ag)
  lift-sem {I = I} (M.unfold a) q ρ ok o κ ag s = ap (κ ·_) (atm-＝ {I = I} ok a ag)
  lift-sem {I = I} (M.let′ e₁ e₂) q ρ ok o {γ} {σ} κ ag s =
    ap (κ ·_) (letᶜ-β Mᵈ Nᵈ γ)
    ∙ seq-strict κ s D (Nᵈ · (D • γ))
    ∙ ap (seq · D ·_)
        (lift-sem e₂ q (ext x ρ) (inited-ext {I = I} x ρ ok) (only₂ o) κ
           (ag-ext {I = I} x ρ {σ = σ} ok (fresh o) ag) s)
    ∙ (app-Λ F D) ⁻¹
    ∙ lift-sem e₁ q₁ ρ ok (only₁ o) (appᵈ · (Λ · F)) ag
        (app-Λ F ⊥𝔻 ∙ seq-⊥ (F · ⊥𝔻))
   where
    open Let {I = I} e₁ e₂ q
    Mᵈ = ⟦ ⌜ e₁ ⌝ ⟧[ T ]
    Nᵈ = ⟦ ⌜ e₂ ⌝ ⟧[ T ]
    D = Mᵈ · γ
    F =
      underK (idx x)
        (⟦ lift e₂ q (ext x ρ) (inited-ext {I = I} x ρ ok) (only₂ o) ⟧ᴷ T')
      · (σ , κ)
  lift-sem {I = I} (M.case a e₁ e₂) q ρ ok o {γ} {σ} κ ag s =
    cases-strict-natural κ s (abs ⟦ ⌜ e₁ ⌝ ⟧[ T ] · γ)
      (abs ⟦ ⌜ e₂ ⌝ ⟧[ T ] · γ) F₁ F₂
      (λ X →
        lift-sem e₁ q₁ (ext x ρ) (inited-ext {I = I} x ρ ok) (only₁ o) κ
          (ag-ext {I = I} x ρ {σ = σ} ok (fresh₁ o) ag) s)
      (λ X →
        lift-sem e₂ q (ext y ρ) (inited-ext {I = I} y ρ ok) (only₂ o) κ
          (ag-ext {I = I} y ρ {σ = σ} ok (fresh₂ o) ag) s)
      (⟦ ⌜ a ⌝ᵃ ⟧[ T ] · γ)
    ∙ ap (λ v → cases · v · (strict · F₁ , strict · F₂)) (atm-＝ {I = I} ok a ag)
   where
    open Case {I = I} a e₁ e₂ q
    F₁ =
      underK (idx x)
        (⟦ lift e₁ q₁ (ext x ρ) (inited-ext {I = I} x ρ ok) (only₁ o) ⟧ᴷ T')
      · (σ , κ)
    F₂ =
      underK (idx y)
        (⟦ lift e₂ q (ext y ρ) (inited-ext {I = I} y ρ ok) (only₂ o) ⟧ᴷ T')
      · (σ , κ)

  {- the code of a definition means the code of its output: its frame
     holds the environment X and the argument Y at the slots of its
     parameters, as env₂ X Y does at positions 1 and 0 -}
  code-lift : ∀ {s} (d : M.Exp Σ (Args s) (DSig.cod s))
    → code′ T ⌜ d ⌝ ＝ I.code′ T' (lift-body d)
  code-lift {s} d =
    codeᶜ-codeᶠ p ⟦ ⌜ d ⌝ ⟧[ T ]
      (∘₁ Env (K ⟹₁ 𝔻) 𝔻
         (⟦ lift d here⊑ (⊑-∋ p) (fill-∈ (⊑-∋ p)) (only-initial p) ⟧ᴷ T')
         (at-point₁ K 𝔻 idK))
      (λ X Y _ _ →
         lift-sem d here⊑ (⊑-∋ p) (fill-∈ (⊑-∋ p)) (only-initial p) idK
           (ag₂ X Y) refl)
   where
    p = binds-⊒ d (Args s)
    e = idx (⊑-∋ p (S Z))
    a = idx (⊑-∋ p Z)
    ag₂ : (X Y : ⟨ 𝔻 ⟩) → Ag (⊑-∋ p) (env₂ X Y) (frame₂ e a X Y)
    ag₂ X Y Z = frame₂-arg e a X Y ⁻¹
    ag₂ X Y (S Z) = frame₂-env e a X Y (params-≢ p) ⁻¹

{- Programs -------------------------------------------------------------------}

{- the table of the output means what the table of the input does -}
table-lift : ∀ {Σ ss} (ds : All (λ s → M.Exp Σ (Args s) (DSig.cod s)) ss)
  {s} (f : Σ ∋ s)
  → tables code′ (All-map ⌜_⌝ ds) f ＝ tables I.code′ (All-map lift-body ds) f
table-lift [] f = refl
table-lift (d ∷ ds) f =
  tables-cons code′ I.code′ ⌜ d ⌝ (All-map ⌜_⌝ ds) (lift-body d)
    (All-map lift-body ds) f
    (code-lift (table-lift ds) d)
    (table-lift ds f)

lift-locals-correct : ∀ {A} (P : M.Program A)
  → ⟦ ⌜ P ⌝ₚ ⟧ₚ ＝ I.⟦ lift-program P ⟧ₚ
lift-locals-correct (M.program ds e) =
  lift-sem (table-lift ds) e here⊑ (⊑-∋ p) (fill-∈ (⊑-∋ p)) (only-initial p)
    idK (λ ()) refl
 where p = binds-⊒ e []

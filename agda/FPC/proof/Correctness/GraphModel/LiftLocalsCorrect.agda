{-

  Correctness of lift locals (Monμ → Impμ) in the graph model, as for
  the typed pass (ISWIM/proof/Correctness/Graph/LiftLocalsCorrect.agda): the
  continuation-passing meaning of the output (FPC/Semantics/GraphModel/Imp.agda)
  is the meaning of the input (its embedding into GlobalFunμ) given to the
  continuation.

    lift-sem : K⟨ k ⟩ (⟦ ⌜ e ⌝ ⟧[ T ] σ) ≃ ⟦ lift e q ρ ok o ⟧ᴷ T' φ K⟨ k ⟩

  for tables that agree, a consistent environment σ of Monμ and a frame
  φ of Impμ that holds the meaning of each variable x in its slot ρ x
  (Rel ρ σ φ). Every continuation of the Impμ semantics is K⟨ k ⟩: the
  end of a body (nothing) or the rest of an assignment, a let (just G).
  A simple expression is the same operator on atoms of the same
  meanings; an assignment and a case commute with the continuation
  (let-law, case-law, proof/Framework/GraphModel/Laws.agda). A let or a
  case writes the slot of its variable, which is not initialized, so
  the write changes no slot of a variable in scope (rel-ext, by
  ∈∉-idx).

-}

module FPC.proof.Correctness.GraphModel.LiftLocalsCorrect where

open import proof.Framework.GraphModel.Prelude
open import proof.Framework.GraphModel.Ops renaming (inl to inlD; inr to inrD)
open import proof.Framework.GraphModel.ContinuityBase using (mono)
open import proof.Framework.GraphModel.Laws using (K⟨_⟩; K-≃; let-law; case-law)
open import proof.Semantics.Graph.Prim using (primD-≃)
open import FPC.proof.Semantics.GraphModel.Ops
open import FPC.proof.Semantics.GraphModel.GlobalFun using (ok; con; code-con;
  table-con)
open import FPC.Semantics.GraphModel.GlobalFun
import FPC.Semantics.GraphModel.Imp as I
open I using (⟦_⟧ᴷ; 𝒜; 𝒜s; 𝒮)
open import FPC.Language.Type
import FPC.Language.Mon as M
open M using (DSig; Args; Atm; var; lit; ref; ⌜_⌝; ⌜_⌝ᵃ; ⌜_⌝ᵛ; ⌜_⌝ₚ)
import FPC.Language.Imp as Imp
open Imp using (Inits; _∉_; ∈∉-idx; ∈-⊕; params-fresh; none; _⊕_)
open import FPC.Compiler.LiftLocals
open import FPC.proof.Semantics.GraphModel.Binders using (lam-≃; let-≃; case-≃;
  body-mono)
open import FPC.Framework.AllUtil using (All; []; _∷_; pos) renaming (map to
  All-map)
open import Framework.Membership using (_⊑_; ⊑-∋; here⊑; ⊑-trans)

open import Data.Empty.Irrelevant using (⊥-elim)
open import Data.Fin using (zero; suc)
open import Data.List using (List; []; _∷_; length)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Nat using (ℕ; _≟_)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Unit using (⊤)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Level using () renaming (lift to up)
open import Relation.Binary.PropositionalEquality using (sym)
open import Relation.Nullary using (yes; no)

{- the frame φ holds the meaning in σ of each variable x in its slot ρ x -}
Rel : ∀ {Γ Δ} → Slots Γ Δ → Env Value → Env Value → Set
Rel {Γ} ρ σ φ = ∀ {B} (x : Γ ∋ B) → σ (idx x) ≃ φ (idx (ρ x))

{- a let or a case binds X to its variable and writes X to the slot s,
   which is not initialized -}
rel-ext : ∀ {Γ Δ A} {I : Inits Δ} {ρ : Slots Γ Δ} {σ φ X} (s : Δ ∋ A)
  → .(Inited ρ I)
  → .(s ∉ I)
  → Rel ρ σ φ
  → Rel (ext s ρ) (X • σ) (φ [ idx s ≔ X ])
rel-ext s ik n r Z = ≃-reflexive (sym (≔-same (idx s)))
rel-ext {I = I} {ρ} s ik n r (S y) =
  ≃-trans (r y)
    (≃-reflexive
      (sym (≔-other λ e → ⊥-elim (∈∉-idx {I = I} (ρ y) s (ik y) n (sym e)))))

{- the start frame of a body holds its argument and its environment in
   the slots of its parameters -}
rel-start : ∀ {Δ A B} (p : (A ∷ B ∷ []) ⊑ Δ) {X Y}
  → Rel (⊑-∋ p) (Y • X • λ _ → init) (start p X Y)
rel-start p Z = ≃-reflexive (sym (≔-same (idx (⊑-∋ p Z))))
rel-start {Δ} p (S Z) =
  ≃-trans (≃-reflexive (sym (≔-same (idx (⊑-∋ p (S Z))))))
    (≃-reflexive
      (sym (≔-other λ e →
        ∈∉-idx {I = none Δ ⊕ ⊑-∋ p (S Z)} (⊑-∋ p (S Z)) (⊑-∋ p Z)
          (∈-⊕ {I = none Δ} (⊑-∋ p (S Z))) (params-fresh p) (sym e))))

module _ {Σ} {T T' : Table Σ} (cT : ConT T)
  (TT : ∀ {s} (f : Σ ∋ s) → T f ≃ T' f) where

  atm-≃ : ∀ {Γ Δ A} (I : Inits Δ) (ρ : Slots Γ Δ) (ik : Inited ρ I) σ φ
    → Rel ρ σ φ
    → (a : Atm Σ Γ A)
    → ⟦ ⌜ a ⌝ᵃ ⟧[ T ] σ ≃ 𝒜 (atom {I = I} ρ ik a) T' φ
  atm-≃ I ρ ik σ φ r (var x) = r x
  atm-≃ I ρ ik σ φ r (lit B c) = ≃-refl
  atm-≃ I ρ ik σ φ r (ref f) = TT f

  atms-≃ : ∀ {Γ Δ Δs} (I : Inits Δ) (ρ : Slots Γ Δ) (ik : Inited ρ I) σ φ
    → Rel ρ σ φ
    → (as : All (Atm Σ Γ) Δs)
    → ∀ i
    → nthD (⟦ ⌜ as ⌝ᵛ ⟧s[ T ] σ) i ≃ nthD (𝒜s (atoms {I = I} ρ ik as) T' φ) i
  atms-≃ I ρ ik σ φ r (a ∷ as) zero = atm-≃ I ρ ik σ φ r a
  atms-≃ I ρ ik σ φ r (a ∷ as) (suc i) = atms-≃ I ρ ik σ φ r as i

  lift-sem : ∀ {Γ Δ D A} {I : Inits Δ} (e : M.Exp Σ Γ A)
    (q : binds e D ⊑ Δ) (ρ : Slots Γ Δ) (ik : Inited ρ I)
    .(o : Imp.Only (⊑-trans (binds-⊒ e D) q) I) σ φ k
    → Con-env σ
    → Rel ρ σ φ
    → K⟨ k ⟩ (⟦ ⌜ e ⌝ ⟧[ T ] σ) ≃ ⟦ lift e q ρ ik o ⟧ᴷ T' φ K⟨ k ⟩
  lift-sem {I = I} (M.atm a) q ρ ik o σ φ k C r =
    K-≃ k (atm-≃ I ρ ik σ φ r a)
  lift-sem {I = I} (M.pair a b) q ρ ik o σ φ k C r =
    K-≃ k
    (mono-≃ pair-mono
      ⟨ up (atm-≃ I ρ ik σ φ r a) , ⟨ up (atm-≃ I ρ ik σ φ r b) , ptt ⟩ ⟩)
  lift-sem {I = I} (M.callc a b) q ρ ik o σ φ k C r =
    K-≃ k
    (mono-≃ (mono (callc-good {⊤}))
      ⟨ up (atm-≃ I ρ ik σ φ r a) , ⟨ up (atm-≃ I ρ ik σ φ r b) , ptt ⟩ ⟩)
  lift-sem {I = I} (M.tuple as) q ρ ik o σ φ k C r =
    K-≃ k (𝒯-≃ _ (atms-≃ I ρ ik σ φ r as))
  lift-sem {I = I} (M.get i a) q ρ ik o σ φ k C r =
    K-≃ k (proj-≃ (pos i) (atm-≃ I ρ ik σ φ r a))
  lift-sem {I = I} (M.inl a) q ρ ik o σ φ k C r =
    K-≃ k (inl-≃ (atm-≃ I ρ ik σ φ r a))
  lift-sem {I = I} (M.inr a) q ρ ik o σ φ k C r =
    K-≃ k (inr-≃ (atm-≃ I ρ ik σ φ r a))
  lift-sem {I = I} (M.prim p a b) q ρ ik o σ φ k C r =
    K-≃ k (primD-≃ p (atm-≃ I ρ ik σ φ r a) (atm-≃ I ρ ik σ φ r b))
  lift-sem {I = I} (M.fold a) q ρ ik o σ φ k C r =
    K-≃ k (atm-≃ I ρ ik σ φ r a)
  lift-sem {I = I} (M.unfold a) q ρ ik o σ φ k C r =
    K-≃ k (atm-≃ I ρ ik σ φ r a)
  lift-sem {I = I} (M.let′ e₁ e₂) q ρ ik o σ φ k C r =
    ≃-trans (let-law k (con cT ⌜ e₁ ⌝ C) (body-mono (ok cT ⌜ e₂ ⌝) σ))
      (≃-trans
        (let-≃ ≃-refl λ X _ cX →
          lift-sem e₂ q (ext x ρ) (inited-ext {I = I} x ρ ik) (only₂ o)
            (X • σ) (φ [ idx x ≔ X ]) k (Con-• cX C)
            (rel-ext {I = I} x ik (fresh o) r))
        (lift-sem e₁ q₁ ρ ik (only₁ o) σ φ (just G) C r))
    where
    open Let {I = I} e₁ e₂ q
    G : 𝒫 Value → 𝒫 Value
    G X =
      ⟦ lift e₂ q (ext x ρ) (inited-ext {I = I} x ρ ik) (only₂ o) ⟧ᴷ T'
        (φ [ idx x ≔ X ]) K⟨ k ⟩
  lift-sem {I = I} (M.case a e₁ e₂) q ρ ik o σ φ k C r =
    ≃-trans
      (case-law k (con cT ⌜ M.atm a ⌝ C) (body-mono (ok cT ⌜ e₁ ⌝) σ)
        (body-mono (ok cT ⌜ e₂ ⌝) σ))
      (case-≃ (atm-≃ I ρ ik σ φ r a)
        (λ X _ cX →
          lift-sem e₁ q₁ (ext x ρ) (inited-ext {I = I} x ρ ik) (only₁ o)
            (X • σ) (φ [ idx x ≔ X ]) k (Con-• cX C)
            (rel-ext {I = I} x ik (fresh₁ o) r))
        (λ X _ cX →
          lift-sem e₂ q (ext y ρ) (inited-ext {I = I} y ρ ik) (only₂ o)
            (X • σ) (φ [ idx y ≔ X ]) k (Con-• cX C)
            (rel-ext {I = I} y ik (fresh₂ o) r)))
    where open Case {I = I} a e₁ e₂ q

  {- the code of a definition means the code of its output -}
  code-lift : ∀ {s} (d : M.Exp Σ (Args s) (DSig.cod s))
    → code′ T ⌜ d ⌝ ≃ I.code′ T' (lift-body d)
  code-lift {s} d =
    lam-≃ λ X _ cX → lam-≃ λ Y _ cY →
    lift-sem {I = Imp.initial p} d here⊑ (⊑-∋ p) (Imp.fill-∈ (⊑-∋ p))
      (Imp.only-initial p)
      _ (start p X Y) nothing (Con-• cY (Con-• cX (λ _ → Con-⌈⌉ ⟨⟩)))
      (rel-start p)
    where p = binds-⊒ d (Args s)

{- Programs -------------------------------------------------------------------}

{- the table of the output means what the table of the input does -}
table-lift : ∀ {Σ ss} (ds : All (λ s → M.Exp Σ (Args s) (DSig.cod s)) ss)
  {s} (f : Σ ∋ s)
  → tables code′ (All-map ⌜_⌝ ds) f ≃ tables I.code′ (All-map lift-body ds) f
table-lift [] f = ≃-refl
table-lift {ss = _ ∷ ss} (d ∷ ds) f with lvl f ≟ length ss
... | yes _ = code-lift (tables-con code-con (All-map ⌜_⌝ ds)) (table-lift ds) d
... | no _ = table-lift ds f

lift-locals-correct : ∀ {A} (P : M.Program A)
  → ⟦ ⌜ P ⌝ₚ ⟧ₚ ≃ I.⟦ lift-program P ⟧ₚ
lift-locals-correct (M.program ds e) =
  lift-sem (table-con (All-map ⌜_⌝ ds)) (table-lift ds) {I = Imp.initial p} e
    here⊑ (⊑-∋ p)
    (Imp.fill-∈ (⊑-∋ p)) (Imp.only-initial p) _ _ nothing
    (λ _ → Con-⌈⌉ ⟨⟩) (λ ())
  where p = binds-⊒ e []

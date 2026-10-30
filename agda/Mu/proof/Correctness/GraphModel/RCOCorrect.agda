{-

  Correctness of remove complex operands (GlobalFunμ → Monμ) in the graph
  model, as for the typed pass (proof/Correctness/Graph/RCOCorrect.agda):
  the embedding of the output means what the input means.

    rco-sem : ⟦ M ⟧[ T ] γ ≃ ⟦ ⌜ rco M ρ ⌝ ⟧[ T' ] σ

  for environments that agree through the renaming ρ (Ag), σ nonempty
  and consistent (the three together: Ext), and tables that agree (T' consistent). Every operator
  rco names the operands of is strict in them (Strict,
  proof/Framework/GraphModel/Strict.agda), so binding an operand first
  by a let changes nothing: the let is the β law of its body (Λ-β, the
  body finitary by its continuity), and the continuation of atomize
  means the operator on the atom under any extension of the frame
  (atomize-sem, atomizes-sem, atomize₂-sem).

-}

module Mu.proof.Correctness.GraphModel.RCOCorrect where

open import proof.Framework.GraphModel.Prelude
open import proof.Framework.GraphModel.Ops renaming (inl to inlD; inr to inrD)
open import proof.Framework.GraphModel.ContinuityBase using (mono)
open import proof.Framework.GraphModel.Env using (Env; nonempty-env; extend-nonempty-env; •-~)
open import proof.Framework.GraphModel.Strict
open import proof.Semantics.Graph.Prim using (primD; primD-mono)
open import Mu.proof.Semantics.GraphModel.Ops
open import Mu.proof.Semantics.GraphModel.GlobalFun using (ok; con; table-con; code-con)
open import Mu.Semantics.GraphModel.GlobalFun
open import Mu.Language.Type
open import Mu.Language.GlobalFun
import Mu.Language.Mon as M
open M using (Atm; Exp; var; lit; ref; ren; ⌜_⌝; ⌜_⌝ᵃ; ⌜_⌝ᵛ; ⌜_⌝ₚ)
open import Mu.Compiler.RCO
open import Mu.proof.Semantics.GraphModel.Binders using (lam-≃; let-≃; case-≃; ne-≃; body-mono)
open import Mu.Framework.AllUtil using (All; []; _∷_; pos) renaming (map to All-map)

open import Data.List using (List; []; _∷_; length)
open import Data.Nat using (ℕ; suc; _≟_)
open import Data.Product using (_×_; proj₁) renaming (_,_ to ⟨_,_⟩)
open import Data.Unit using (⊤; tt)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Level using (lift; lower)
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Nullary using (yes; no)

{- the operators that rco names the operands of, besides Strict.agda's -}
callc-op : Strict 2
callc-op = record { op = callcᵈ ; cong = mono-≃ (mono (callc-good {⊤}))
  ; ne-of = λ { _ w ⟨ V , ⟨ ⟨ U , ⟨ ⟨ _ , p∈ ⟩ , _ ⟩ ⟩ , ⟨ V⊆ , V≢[] ⟩ ⟩ ⟩ → ⟨ ⟨ _ , p∈ ⟩ , ⟨ ne-mem V≢[] V⊆ , tt ⟩ ⟩ } }

prim-op : ∀ p → Strict 2
prim-op p = record { op = primD p ; cong = mono-≃ (primD-mono p)
  ; ne-of = λ { _ w ⟨ n , ⟨ m , ⟨ n∈ , ⟨ m∈ , _ ⟩ ⟩ ⟩ ⟩ → ⟨ ⟨ _ , n∈ ⟩ , ⟨ ⟨ _ , m∈ ⟩ , tt ⟩ ⟩ } }

id-op : Strict 1
id-op = record { op = proj₁ ; cong = λ eq → lower (proj₁ eq) ; ne-of = λ _ w w∈ → ⟨ ⟨ w , w∈ ⟩ , tt ⟩ }

{- the operator O with its operands after the first fixed to Es -}
first : ∀ {n} → Strict (suc n) → Results (𝒫 Value) (Data.List.replicate n ■) → Strict 1
first O Es = record { op = λ Ds → op O ⟨ proj₁ Ds , Es ⟩ ; cong = λ eq → cong O ⟨ proj₁ eq , RRs-refl Es ⟩
  ; ne-of = λ Ds w w∈ → ⟨ proj₁ (ne-of O _ w w∈) , tt ⟩ }

module _ {Σ} {T T' : Table Σ} (cT : ConT T') (TT : ∀ {s} (f : Σ ∋ s) → T f ≃ T' f) where

  {- the frames agree through the renaming ρ -}
  Ag : ∀ {Γ Δ} → Ren Γ Δ → Env Value → Env Value → Set
  Ag ρ γ σ = ∀ {A} x → γ (idx x) ≃ σ (idx (ρ {A} x))

  ren-atm : ∀ {Δ Δ' A σ σ'} (r : Ren Δ Δ') (a : Atm Σ Δ A) → Ag r σ σ' → ⟦ ⌜ a ⌝ᵃ ⟧[ T' ] σ ≃ ⟦ ⌜ ren r a ⌝ᵃ ⟧[ T' ] σ'
  ren-atm r (var x) ag = ag x
  ren-atm r (lit B c) ag = ≃-refl
  ren-atm r (ref f) ag = ≃-refl

  {- frames that agree through r, the second nonempty and consistent -}
  record Ext {Δ Δ'} (r : Ren Δ Δ') (σ σ' : Env Value) : Set where
    constructor ext′
    field ne : nonempty-env σ'
          cn : Con-env σ'
          agr : Ag r σ σ'
  open Ext

  {- the identity, the composition, and under a binder -}
  id-ext : ∀ {Δ Δ'} {r : Ren Δ Δ'} {σ σ'} → Ext r σ σ' → Ext {Δ'} (λ y → y) σ' σ'
  id-ext e = ext′ (ne e) (cn e) λ _ → ≃-refl

  _⨾_ : ∀ {Γ Δ Δ'} {ρ : Ren Γ Δ} {r : Ren Δ Δ'} {γ σ σ'} → Ext ρ γ σ → Ext r σ σ' → Ext (λ x → r (ρ x)) γ σ'
  _⨾_ {ρ = ρ} e e' = ext′ (ne e') (cn e') λ x → ≃-trans (agr e x) (agr e' (ρ x))

  ext-ext : ∀ {Γ Δ B} {ρ : Ren Γ Δ} {γ σ X} → Ext ρ γ σ → nonempty X → Con X → Ext (ext {B = B} ρ) (X • γ) (X • σ)
  ext-ext e neX cX = ext′ (extend-nonempty-env (ne e) neX) (Con-• cX (cn e)) λ { Z → ≃-refl ; (S x) → agr e x }

  rco-sem : ∀ {Γ Δ A} (N : Tm Σ Γ A) {ρ : Ren Γ Δ} {γ σ} → Ext ρ γ σ → ⟦ N ⟧[ T ] γ ≃ ⟦ ⌜ rco N ρ ⌝ ⟧[ T' ] σ

  atomize-sem : ∀ {Γ Δ A B} (N : Tm Σ Γ A) {ρ : Ren Γ Δ} (k : K Σ Δ A B) {γ σ} → Ext ρ γ σ → (O : Strict 1)
    → (∀ {Δ'} (r : Ren Δ Δ') σ' a → Ext r σ σ' → op O ⟨ ⟦ ⌜ a ⌝ᵃ ⟧[ T' ] σ' , ptt ⟩ ≃ ⟦ ⌜ k r a ⌝ ⟧[ T' ] σ')
    → op O ⟨ ⟦ N ⟧[ T ] γ , ptt ⟩ ≃ ⟦ ⌜ atomize N ρ k ⌝ ⟧[ T' ] σ
  {- a complex operand, bound by a let -}
  let-sem : ∀ {Γ Δ A B} (N : Tm Σ Γ A) {ρ : Ren Γ Δ} (k : K Σ Δ A B) {γ σ} → Ext ρ γ σ → (O : Strict 1)
    → (∀ {Δ'} (r : Ren Δ Δ') σ' a → Ext r σ σ' → op O ⟨ ⟦ ⌜ a ⌝ᵃ ⟧[ T' ] σ' , ptt ⟩ ≃ ⟦ ⌜ k r a ⌝ ⟧[ T' ] σ')
    → op O ⟨ ⟦ N ⟧[ T ] γ , ptt ⟩ ≃ ⟦ ⌜ M.let′ (rco N ρ) (k S (var Z)) ⌝ ⟧[ T' ] σ
  atomize-sem (` x) k e O ks = ≃-trans (cong O ⟨ lift (agr e x) , ptt ⟩) (ks (λ y → y) _ _ (id-ext e))
  atomize-sem (fun-ref f) k e O ks = ≃-trans (cong O ⟨ lift (TT f) , ptt ⟩) (ks (λ y → y) _ _ (id-ext e))
  atomize-sem (lit B c) k e O ks = ks (λ y → y) _ _ (id-ext e)
  atomize-sem N@(pair _ _) = let-sem N
  atomize-sem N@(callc _ _) = let-sem N
  atomize-sem N@(tuple _) = let-sem N
  atomize-sem N@(get _ _) = let-sem N
  atomize-sem N@(inl _) = let-sem N
  atomize-sem N@(inr _) = let-sem N
  atomize-sem N@(case _ _ _) = let-sem N
  atomize-sem N@(prim _ _ _) = let-sem N
  atomize-sem N@(let′ _ _) = let-sem N
  atomize-sem N@(fold _) = let-sem N
  atomize-sem N@(unfold _) = let-sem N
  let-sem N {ρ} k {σ = σ} e O ks =
    ≃-when (λ w w∈ → ne-≃ IH (proj₁ (ne-of O _ w w∈))) (λ { w ⟨ V , ⟨ _ , ⟨ V⊆ , neV ⟩ ⟩ ⟩ → ne-mem neV V⊆ }) λ neD →
    ≃-trans (cong O ⟨ lift IH , ptt ⟩)
      (≃-trans (ks S _ (var Z) (ext′ (extend-nonempty-env (ne e) neD) (Con-• cD (cn e)) (λ y → ≃-refl)))
               (≃-sym (Λ-β (body-mono okt σ) (fin₁ okt (ne e) neD) cD)))
    where IH = rco-sem N e
          cD = con cT ⌜ rco N ρ ⌝ (cn e)
          okt = ok cT ⌜ k S (var Z) ⌝

  atomizes-sem : ∀ {Γ Δ Δs B} (Ns : All (Tm Σ Γ) Δs) {ρ : Ren Γ Δ}
    (k : ∀ {Δ'} → Ren Δ Δ' → All (Atm Σ Δ') Δs → Exp Σ Δ' B) {γ σ} → Ext ρ γ σ → (O : Strict (length Δs))
    → (∀ {Δ'} (r : Ren Δ Δ') σ' as → Ext r σ σ' → op O (⟦ ⌜ as ⌝ᵛ ⟧s[ T' ] σ') ≃ ⟦ ⌜ k r as ⌝ ⟧[ T' ] σ')
    → op O (⟦ Ns ⟧s[ T ] γ) ≃ ⟦ ⌜ atomizes Ns ρ k ⌝ ⟧[ T' ] σ
  atomizes-sem [] k e O ks = ks (λ y → y) _ [] (id-ext e)
  atomizes-sem (N ∷ Ns) k {γ} e O ks =
    atomize-sem N _ e (first O (⟦ Ns ⟧s[ T ] γ)) λ r σ' a e₁ →
      atomizes-sem Ns _ (e ⨾ e₁) (⟦ ⌜ a ⌝ᵃ ⟧[ T' ] σ' ▷ O) λ r' σ'' xs e₂ →
        ≃-trans (cong O ⟨ lift (ren-atm r' a (agr e₂)) , RRs-refl _ ⟩) (ks _ σ'' (ren r' a ∷ xs) (e₁ ⨾ e₂))

  atomize₂-sem : ∀ {Γ Δ A₁ A₂ B} (L : Tm Σ Γ A₁) (N : Tm Σ Γ A₂) {ρ : Ren Γ Δ}
    (k : ∀ {Δ'} → Atm Σ Δ' A₁ → Atm Σ Δ' A₂ → Exp Σ Δ' B) {γ σ} → Ext ρ γ σ → (O : Strict 2)
    → (∀ {Δ'} σ' (a : Atm Σ Δ' A₁) b → op O ⟨ ⟦ ⌜ a ⌝ᵃ ⟧[ T' ] σ' , ⟨ ⟦ ⌜ b ⌝ᵃ ⟧[ T' ] σ' , ptt ⟩ ⟩ ≃ ⟦ ⌜ k a b ⌝ ⟧[ T' ] σ')
    → op O ⟨ ⟦ L ⟧[ T ] γ , ⟨ ⟦ N ⟧[ T ] γ , ptt ⟩ ⟩ ≃ ⟦ ⌜ atomize₂ L N ρ k ⌝ ⟧[ T' ] σ
  atomize₂-sem L N k {γ} e O ks =
    atomize-sem L _ e (first O ⟨ ⟦ N ⟧[ T ] γ , ptt ⟩) λ r σ' a e₁ →
      atomize-sem N _ (e ⨾ e₁) (⟦ ⌜ a ⌝ᵃ ⟧[ T' ] σ' ▷ O) λ r' σ'' b e₂ →
        ≃-trans (cong O ⟨ lift (ren-atm r' a (agr e₂)) , ⟨ lift ≃-refl , ptt ⟩ ⟩) (ks σ'' (ren r' a) b)

  rco-sem (` x) e = agr e x
  rco-sem (fun-ref f) e = TT f
  rco-sem (pair L N) e = atomize₂-sem L N M.pair e pair-op′ λ _ _ _ → ≃-refl
  rco-sem (callc L N) e = atomize₂-sem L N M.callc e callc-op λ _ _ _ → ≃-refl
  rco-sem (lit B c) e = ≃-refl
  rco-sem (tuple Ns) e = atomizes-sem Ns _ e (tuple-op _) λ _ _ _ _ → ≃-refl
  rco-sem (get i N) e = atomize-sem N _ e (get-op (pos i)) λ _ _ _ _ → ≃-refl
  rco-sem (inl N) e = atomize-sem N _ e inl-op′ λ _ _ _ _ → ≃-refl
  rco-sem (inr N) e = atomize-sem N _ e inr-op′ λ _ _ _ _ → ≃-refl
  rco-sem (case L N₁ N₂) {γ = γ} e =
    atomize-sem L _ e (case-op′ (λ X → ⟦ N₁ ⟧[ T ] (X • γ)) (λ X → ⟦ N₂ ⟧[ T ] (X • γ))) λ r σ' a e₁ →
      case-≃ (≃-refl {D = ⟦ ⌜ a ⌝ᵃ ⟧[ T' ] σ'}) (λ X neX cX → rco-sem N₁ (ext-ext (e ⨾ e₁) neX cX))
        (λ X neX cX → rco-sem N₂ (ext-ext (e ⨾ e₁) neX cX))
  rco-sem (prim p L N) e = atomize₂-sem L N (M.prim p) e (prim-op p) λ _ _ _ → ≃-refl
  rco-sem (let′ N₁ N₂) e = let-≃ (rco-sem N₁ e) λ X neX cX → rco-sem N₂ (ext-ext e neX cX)
  rco-sem (fold N) e = atomize-sem N _ e id-op λ _ _ _ _ → ≃-refl
  rco-sem (unfold N) e = atomize-sem N _ e id-op λ _ _ _ _ → ≃-refl

  {- the code of a definition means the code of its output -}
  code-rco : ∀ {s} (d : Code Σ s) → code′ T d ≃ code′ T' ⌜ rco d (λ x → x) ⌝
  code-rco d = lam-≃ λ X neX cX → lam-≃ λ Y neY cY →
    rco-sem d (ext′ (extend-nonempty-env (extend-nonempty-env (λ _ → ⟨ ⟨⟩ , refl ⟩) neX) neY)
                    (Con-• cY (Con-• cX (λ _ → Con-⌈⌉ ⟨⟩))) (λ x → ≃-refl))

{- Programs ---------------------------------------------------------------------------}

{- the table of the output means what the table of the input does -}
table-rco : ∀ {Σ ss} (ds : All (Code Σ) ss) {s} (f : Σ ∋ s)
  → tables code′ ds f ≃ tables code′ (All-map ⌜_⌝ (All-map (λ D → rco D (λ x → x)) ds)) f
table-rco [] f = ≃-refl
table-rco {ss = _ ∷ ss} (d ∷ ds) f with lvl f ≟ length ss
... | yes _ = code-rco (tables-con code-con (All-map ⌜_⌝ (All-map (λ D → rco D (λ x → x)) ds))) (table-rco ds) d
... | no _ = table-rco ds f

rco-correct : ∀ {A} (P : Program A) → ⟦ P ⟧ₚ ≃ ⟦ ⌜ rco-program P ⌝ₚ ⟧ₚ
rco-correct (program ds N) =
  rco-sem (table-con (All-map ⌜_⌝ (All-map (λ D → rco D (λ x → x)) ds))) (table-rco ds) N
    (ext′ (λ _ → ⟨ ⟨⟩ , refl ⟩) (λ _ → Con-⌈⌉ ⟨⟩) (λ x → ≃-refl))

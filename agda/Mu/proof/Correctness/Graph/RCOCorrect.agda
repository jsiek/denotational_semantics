{-

  Correctness of remove complex operands (Clos5μ → Monμ) in the graph
  model, as for the typed pass (proof/Correctness/Graph/RCOCorrect.agda):
  the embedding of the output means what the input means.

    rco-sem : ⟦ M ⟧[ T ] γ ≃ ⟦ ⌜ rco M ρ ⌝ ⟧[ T' ] σ

  for environments that agree through the renaming ρ (Ag), σ nonempty
  and consistent, and tables that agree (T' consistent). Every operator
  rco names the operands of is strict in them (Strict,
  proof/Framework/GraphModel/Strict.agda), so binding an operand first
  by a let changes nothing: the let is the β law of its body (Λ-β, the
  body finitary by its continuity), and the continuation of atomize
  means the operator on the atom under any extension of the frame
  (atomize-sem, atomizes-sem, atomize₂-sem).

-}

module Mu.proof.Correctness.Graph.RCOCorrect where

open import proof.Framework.GraphModel.Prelude
open import proof.Framework.GraphModel.Ops renaming (inl to inlD; inr to inrD)
open import proof.Framework.GraphModel.ContinuityBase using (mono)
open import proof.Framework.GraphModel.Env using (Env; nonempty-env; extend-nonempty-env; •-~)
open import proof.Framework.GraphModel.Strict
open import proof.Semantics.Graph.Prim using (primD; primD-mono)
open import Mu.proof.Semantics.Graph.Ops
open import Mu.proof.Semantics.Graph.Clos5 using (ok; con; table-con; code-con)
open import Mu.Semantics.Graph.Clos5
open import Mu.Language.Type
open import Mu.Language.Clos5
import Mu.Language.Mon as M
open M using (Atm; Exp; var; lit; ref; ren; ⌜_⌝; ⌜_⌝ᵃ; ⌜_⌝ᵛ; ⌜_⌝ₚ)
open import Mu.Compiler.RCO
open import Mu.Framework.AllUtil using (All; []; _∷_; pos) renaming (map to All-map)

open import Data.List using (List; []; _∷_; length)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Nat using (ℕ; suc; _≟_)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
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

  {- frames extended through r, nonempty and consistent -}
  record Ext {Δ Δ'} (r : Ren Δ Δ') (σ σ' : Env Value) : Set where
    constructor ext′
    field ne : nonempty-env σ'
          cn : Con-env σ'
          agr : Ag r σ σ'
  open Ext

  rco-sem : ∀ {Γ Δ A} (N : Tm Σ Γ A) (ρ : Ren Γ Δ) γ σ → nonempty-env σ → Con-env σ → Ag ρ γ σ
    → ⟦ N ⟧[ T ] γ ≃ ⟦ ⌜ rco N ρ ⌝ ⟧[ T' ] σ

  atomize-sem : ∀ {Γ Δ A B} (N : Tm Σ Γ A) (ρ : Ren Γ Δ) (k : K Σ Δ A B) γ σ → nonempty-env σ → Con-env σ
    → Ag ρ γ σ → (O : Strict 1)
    → (∀ {Δ'} (r : Ren Δ Δ') σ' a → Ext r σ σ' → op O ⟨ ⟦ ⌜ a ⌝ᵃ ⟧[ T' ] σ' , ptt ⟩ ≃ ⟦ ⌜ k r a ⌝ ⟧[ T' ] σ')
    → op O ⟨ ⟦ N ⟧[ T ] γ , ptt ⟩ ≃ ⟦ ⌜ atomize N ρ k ⌝ ⟧[ T' ] σ
  {- a complex operand, bound by a let -}
  let-sem : ∀ {Γ Δ A B} (N : Tm Σ Γ A) (ρ : Ren Γ Δ) (k : K Σ Δ A B) γ σ → nonempty-env σ → Con-env σ
    → Ag ρ γ σ → (O : Strict 1)
    → (∀ {Δ'} (r : Ren Δ Δ') σ' a → Ext r σ σ' → op O ⟨ ⟦ ⌜ a ⌝ᵃ ⟧[ T' ] σ' , ptt ⟩ ≃ ⟦ ⌜ k r a ⌝ ⟧[ T' ] σ')
    → op O ⟨ ⟦ N ⟧[ T ] γ , ptt ⟩ ≃ ⟦ ⌜ M.let′ (rco N ρ) (k S (var Z)) ⌝ ⟧[ T' ] σ
  atomize-sem (` x) ρ k γ σ NE C ag O ks =
    ≃-trans (cong O ⟨ lift (ag x) , ptt ⟩) (ks (λ y → y) σ _ (ext′ NE C (λ y → ≃-refl)))
  atomize-sem (fun-ref f) ρ k γ σ NE C ag O ks =
    ≃-trans (cong O ⟨ lift (TT f) , ptt ⟩) (ks (λ y → y) σ _ (ext′ NE C (λ y → ≃-refl)))
  atomize-sem (lit B c) ρ k γ σ NE C ag O ks = ks (λ y → y) σ _ (ext′ NE C (λ y → ≃-refl))
  atomize-sem N@(pack _ _) = let-sem N
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
  let-sem N ρ k γ σ NE C ag O ks =
    ≃-when (λ w w∈ → let ⟨ v , v∈ ⟩ = proj₁ (ne-of O _ w w∈) in ⟨ v , proj₁ IH v v∈ ⟩)
      (λ { w ⟨ V , ⟨ _ , ⟨ V⊆ , ne ⟩ ⟩ ⟩ → ne-mem ne V⊆ }) λ neD →
    ≃-trans (cong O ⟨ lift IH , ptt ⟩)
      (≃-trans (ks S _ (var Z) (ext′ (extend-nonempty-env NE neD) (Con-• (con cT ⌜ rco N ρ ⌝ C) C) (λ y → ≃-refl)))
               (≃-sym (Λ-β (λ X⊆ → proj₁ okt (•-~ _⊆_ (λ _ _ z → z) X⊆)) (fin₁ okt NE neD) (con cT ⌜ rco N ρ ⌝ C))))
    where IH = rco-sem N ρ γ σ NE C ag
          okt = ok cT ⌜ k S (var Z) ⌝

  atomizes-sem : ∀ {Γ Δ Δs B} (Ns : All (Tm Σ Γ) Δs) (ρ : Ren Γ Δ)
    (k : ∀ {Δ'} → Ren Δ Δ' → All (Atm Σ Δ') Δs → Exp Σ Δ' B) γ σ → nonempty-env σ → Con-env σ
    → Ag ρ γ σ → (O : Strict (length Δs))
    → (∀ {Δ'} (r : Ren Δ Δ') σ' as → Ext r σ σ' → op O (⟦ ⌜ as ⌝ᵛ ⟧s[ T' ] σ') ≃ ⟦ ⌜ k r as ⌝ ⟧[ T' ] σ')
    → op O (⟦ Ns ⟧s[ T ] γ) ≃ ⟦ ⌜ atomizes Ns ρ k ⌝ ⟧[ T' ] σ
  atomizes-sem [] ρ k γ σ NE C ag O ks = ks (λ y → y) σ [] (ext′ NE C (λ y → ≃-refl))
  atomizes-sem (N ∷ Ns) ρ k γ σ NE C ag O ks =
    atomize-sem N ρ _ γ σ NE C ag (first O (⟦ Ns ⟧s[ T ] γ)) λ r σ' a e →
      atomizes-sem Ns _ _ γ σ' (ne e) (cn e) (λ x → ≃-trans (ag x) (agr e (ρ x))) (⟦ ⌜ a ⌝ᵃ ⟧[ T' ] σ' ▷ O)
        λ r' σ'' xs e' →
          ≃-trans (cong O ⟨ lift (ren-atm r' a (agr e')) , RRs-refl _ ⟩)
                  (ks _ σ'' (ren r' a ∷ xs) (ext′ (ne e') (cn e') (λ y → ≃-trans (agr e y) (agr e' (r y)))))

  atomize₂-sem : ∀ {Γ Δ A₁ A₂ B} (L : Tm Σ Γ A₁) (N : Tm Σ Γ A₂) (ρ : Ren Γ Δ)
    (k : ∀ {Δ'} → Atm Σ Δ' A₁ → Atm Σ Δ' A₂ → Exp Σ Δ' B) γ σ → nonempty-env σ → Con-env σ
    → Ag ρ γ σ → (O : Strict 2)
    → (∀ {Δ'} σ' (a : Atm Σ Δ' A₁) b → op O ⟨ ⟦ ⌜ a ⌝ᵃ ⟧[ T' ] σ' , ⟨ ⟦ ⌜ b ⌝ᵃ ⟧[ T' ] σ' , ptt ⟩ ⟩ ≃ ⟦ ⌜ k a b ⌝ ⟧[ T' ] σ')
    → op O ⟨ ⟦ L ⟧[ T ] γ , ⟨ ⟦ N ⟧[ T ] γ , ptt ⟩ ⟩ ≃ ⟦ ⌜ atomize₂ L N ρ k ⌝ ⟧[ T' ] σ
  atomize₂-sem L N ρ k γ σ NE C ag O ks =
    atomize-sem L ρ _ γ σ NE C ag (first O ⟨ ⟦ N ⟧[ T ] γ , ptt ⟩) λ r σ' a e →
      atomize-sem N _ _ γ σ' (ne e) (cn e) (λ x → ≃-trans (ag x) (agr e (ρ x))) (⟦ ⌜ a ⌝ᵃ ⟧[ T' ] σ' ▷ O)
        λ r' σ'' b e' →
          ≃-trans (cong O ⟨ lift (ren-atm r' a (agr e')) , ⟨ lift ≃-refl , ptt ⟩ ⟩) (ks σ'' (ren r' a) b)

  {- under a binder -}
  ag-ext : ∀ {Γ Δ B} {ρ : Ren Γ Δ} {γ σ X} → Ag ρ γ σ → Ag (ext {B = B} ρ) (X • γ) (X • σ)
  ag-ext ag Z = ≃-refl
  ag-ext ag (S x) = ag x

  rco-sem (` x) ρ γ σ NE C ag = ag x
  rco-sem (fun-ref f) ρ γ σ NE C ag = TT f
  rco-sem (pack L N) ρ γ σ NE C ag = atomize₂-sem L N ρ M.pack γ σ NE C ag pair-op′ λ _ _ _ → ≃-refl
  rco-sem (callc L N) ρ γ σ NE C ag = atomize₂-sem L N ρ M.callc γ σ NE C ag callc-op λ _ _ _ → ≃-refl
  rco-sem (lit B c) ρ γ σ NE C ag = ≃-refl
  rco-sem (tuple Ns) ρ γ σ NE C ag = atomizes-sem Ns ρ _ γ σ NE C ag (tuple-op _) λ _ _ _ _ → ≃-refl
  rco-sem (get i N) ρ γ σ NE C ag = atomize-sem N ρ _ γ σ NE C ag (get-op (pos i)) λ _ _ _ _ → ≃-refl
  rco-sem (inl N) ρ γ σ NE C ag = atomize-sem N ρ _ γ σ NE C ag inl-op′ λ _ _ _ _ → ≃-refl
  rco-sem (inr N) ρ γ σ NE C ag = atomize-sem N ρ _ γ σ NE C ag inr-op′ λ _ _ _ _ → ≃-refl
  rco-sem (case L N₁ N₂) ρ γ σ NE C ag =
    atomize-sem L ρ _ γ σ NE C ag (case-op′ (λ X → ⟦ N₁ ⟧[ T ] (X • γ)) (λ X → ⟦ N₂ ⟧[ T ] (X • γ)))
      λ r σ' a e →
        let ag₁ = λ {A} (x : _ ∋ A) → ≃-trans (ag x) (agr e (ρ x))
            br : ∀ {A} (N' : Tm Σ (A ∷ _) _) v V → (v ∷ V) ≈ (v ∷ V) → _
            br N' v V c = rco-sem N' _ (mem (v ∷ V) • γ) (mem (v ∷ V) • σ')
                            (extend-nonempty-env (ne e) ⟨ v , here refl ⟩) (Con-• (≈⇒Con c) (cn e)) (ag-ext ag₁)
        in 𝒞-≃ {D = ⟦ ⌜ a ⌝ᵃ ⟧[ T' ] σ'} {⟦ ⌜ a ⌝ᵃ ⟧[ T' ] σ'} {λ X → ⟦ N₁ ⟧[ T ] (X • γ)} {λ X → ⟦ ⌜ rco N₁ (ext λ x → r (ρ x)) ⌝ ⟧[ T' ] (X • σ')}
               {λ X → ⟦ N₂ ⟧[ T ] (X • γ)} {λ X → ⟦ ⌜ rco N₂ (ext λ x → r (ρ x)) ⌝ ⟧[ T' ] (X • σ')}
               ≃-refl (br N₁) (br N₂)
  rco-sem (prim p L N) ρ γ σ NE C ag = atomize₂-sem L N ρ (M.prim p) γ σ NE C ag (prim-op p) λ _ _ _ → ≃-refl
  rco-sem (let′ N₁ N₂) ρ γ σ NE C ag =
    ⋆-≃ (Λ-≃ {λ X → ⟦ N₂ ⟧[ T ] (X • γ)} {λ X → ⟦ ⌜ rco N₂ (ext ρ) ⌝ ⟧[ T' ] (X • σ)} λ V ne c →
           rco-sem N₂ (ext ρ) (mem V • γ) (mem V • σ) (extend-nonempty-env NE (E≢[]⇒nonempty-mem ne))
             (Con-• (≈⇒Con c) C) (ag-ext ag))
        (rco-sem N₁ ρ γ σ NE C ag)
  rco-sem (fold N) ρ γ σ NE C ag = atomize-sem N ρ _ γ σ NE C ag id-op λ _ _ _ _ → ≃-refl
  rco-sem (unfold N) ρ γ σ NE C ag = atomize-sem N ρ _ γ σ NE C ag id-op λ _ _ _ _ → ≃-refl

{- Programs ---------------------------------------------------------------------------}

{- the table of the output means what the table of the input does -}
table-rco : ∀ {Σ ss} (ds : All (Code Σ) ss) {s} (f : Σ ∋ s)
  → tables code′ ds f ≃ tables code′ (All-map ⌜_⌝ (All-map (λ D → rco D (λ x → x)) ds)) f
table-rco [] f = ≃-refl
table-rco {ss = _ ∷ ss} (d ∷ ds) f with lvl f ≟ length ss
... | yes _ = Λ-≃ λ V neV cV → Λ-≃ λ U neU cU →
  rco-sem (tables-con code-con (All-map ⌜_⌝ (All-map (λ D → rco D (λ x → x)) ds))) (table-rco ds) d (λ x → x) _ _
    (extend-nonempty-env (extend-nonempty-env (λ _ → ⟨ ω , refl ⟩) (E≢[]⇒nonempty-mem neV)) (E≢[]⇒nonempty-mem neU))
    (Con-• (≈⇒Con cU) (Con-• (≈⇒Con cV) (λ _ → Con-⌈⌉ ω))) (λ x → ≃-refl)
... | no _ = table-rco ds f

rco-correct : ∀ {A} (P : Program A) → ⟦ P ⟧ₚ ≃ ⟦ ⌜ rco-program P ⌝ₚ ⟧ₚ
rco-correct (program ds N) =
  rco-sem (table-con (All-map ⌜_⌝ (All-map (λ D → rco D (λ x → x)) ds))) (table-rco ds) N (λ x → x) _ _
    (λ _ → ⟨ ω , refl ⟩) (λ _ → Con-⌈⌉ ω) (λ x → ≃-refl)

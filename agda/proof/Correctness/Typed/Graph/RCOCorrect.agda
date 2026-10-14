{-

  Correctness of typed remove complex operands (Clos5ᵀ → Monᵀ) in the
  graph model: the embedding of the output means what the input means.

    rco-sem : ⟦ ⌜ rco M ρ ⌝ ⟧[ T ] σ ≃ ⟦ M ⟧[ T' ] γ

  for environments that agree through the renaming ρ (Ag), σ nonempty
  and consistent, and tables that agree (T consistent). Every operator
  rco names the operands of is strict in them (Strict,
  proof/Framework/GraphModel/Strict.agda), so binding an operand first
  by a let changes nothing: the let is the β law of its body (Λ-β, the
  body finitary by its continuity), and the continuation of atomize
  means the operator on the atom under any extension of the frame
  (atomize-sem, atomizes-sem, atomize₂-sem).

-}

module proof.Correctness.Typed.Graph.RCOCorrect where

open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.DOpSig
open import proof.Framework.GraphModel.Domain
open import proof.Framework.GraphModel.Ops renaming (inl to inlD; inr to inrD)
open import proof.Framework.GraphModel.ContinuityBase using (mono)
open import proof.Framework.GraphModel.Env using (Env; nonempty-env; extend-nonempty-env; •-~)
open import proof.Framework.GraphModel.Strict
open import proof.Semantics.Graph.Prim using (primD; primD-mono)
open import proof.Semantics.Graph.Typed.Ops
open import proof.Semantics.Graph.Typed.Clos5 using (ok; con; table-con; code-con)
open import Semantics.Graph.Typed.Clos5
open import Language.Typed.Type hiding (_≟_)
open import Language.Typed.Clos5
import Language.Typed.Mon as M
open M using (Atm; Exp; var; lit; ref; ren; ⌜_⌝; ⌜_⌝ᵃ; ⌜_⌝ᵛ; ⌜_⌝ₚ)
open import Compiler.Typed.RCO

open import Data.List using (List; []; _∷_; length)
open import Data.List.Relation.Unary.All using (All; []; _∷_) renaming (map to All-map)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Nat using (ℕ; suc; _≟_)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Unit using (⊤; tt)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Data.Vec using (Vec; []; _∷_)
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

project-op : Tag → Strict 1
project-op t = record { op = λ Ds → projectᵍ fun₄ t (proj₁ Ds) ; cong = λ eq → project-≃ fun₄ t (lower (proj₁ eq))
  ; ne-of = λ _ w w∈ → ⟨ ⟨ w , proj₂ w∈ ⟩ , tt ⟩ }

{- the operator O with its operands after the first fixed to Es -}
first : ∀ {n} → Strict (suc n) → Results (𝒫 Value) (Data.List.replicate n ■) → Strict 1
first O Es = record { op = λ Ds → op O ⟨ proj₁ Ds , Es ⟩ ; cong = λ eq → cong O ⟨ proj₁ eq , RRs-refl Es ⟩
  ; ne-of = λ Ds w w∈ → ⟨ proj₁ (ne-of O _ w w∈) , tt ⟩ }

module _ {Σ} {T T' : Table Σ} (cT : ConT T) (TT : ∀ {n} (f : Σ ∋ n) → T f ≃ T' f) where

  {- the frames agree through the renaming ρ -}
  Ag : ∀ {Γ Δ} → Ren Γ Δ → Env Value → Env Value → Set
  Ag ρ σ γ = ∀ {A} x → σ (idx (ρ {A} x)) ≃ γ (idx x)

  ren-atm : ∀ {Δ Δ' A σ' σ} (r : Ren Δ Δ') (a : Atm Σ Δ A) → Ag r σ' σ → ⟦ ⌜ ren r a ⌝ᵃ ⟧[ T ] σ' ≃ ⟦ ⌜ a ⌝ᵃ ⟧[ T ] σ
  ren-atm r (var x) ag = ag x
  ren-atm r (lit B c) ag = ≃-refl
  ren-atm r (ref f) ag = ≃-refl

  {- frames extended through r, nonempty and consistent -}
  record Ext {Δ Δ'} (r : Ren Δ Δ') (σ' σ : Env Value) : Set where
    constructor ext′
    field ne : nonempty-env σ'
          cn : Con-env σ'
          agr : Ag r σ' σ
  open Ext

  rco-sem : ∀ {Γ Δ A} (N : Tm Σ Γ A) (ρ : Ren Γ Δ) σ γ → nonempty-env σ → Con-env σ → Ag ρ σ γ
    → ⟦ ⌜ rco N ρ ⌝ ⟧[ T ] σ ≃ ⟦ N ⟧[ T' ] γ

  atomize-sem : ∀ {Γ Δ A B} (N : Tm Σ Γ A) (ρ : Ren Γ Δ) (k : K Σ Δ A B) σ γ → nonempty-env σ → Con-env σ
    → Ag ρ σ γ → (O : Strict 1)
    → (∀ {Δ'} (r : Ren Δ Δ') σ' a → Ext r σ' σ → ⟦ ⌜ k r a ⌝ ⟧[ T ] σ' ≃ op O ⟨ ⟦ ⌜ a ⌝ᵃ ⟧[ T ] σ' , ptt ⟩)
    → ⟦ ⌜ atomize N ρ k ⌝ ⟧[ T ] σ ≃ op O ⟨ ⟦ N ⟧[ T' ] γ , ptt ⟩
  {- a complex operand, bound by a let -}
  let-sem : ∀ {Γ Δ A B} (N : Tm Σ Γ A) (ρ : Ren Γ Δ) (k : K Σ Δ A B) σ γ → nonempty-env σ → Con-env σ
    → Ag ρ σ γ → (O : Strict 1)
    → (∀ {Δ'} (r : Ren Δ Δ') σ' a → Ext r σ' σ → ⟦ ⌜ k r a ⌝ ⟧[ T ] σ' ≃ op O ⟨ ⟦ ⌜ a ⌝ᵃ ⟧[ T ] σ' , ptt ⟩)
    → ⟦ ⌜ M.let′ (rco N ρ) (k S (var Z)) ⌝ ⟧[ T ] σ ≃ op O ⟨ ⟦ N ⟧[ T' ] γ , ptt ⟩
  atomize-sem (` x) ρ k σ γ NE C ag O ks =
    ≃-trans (ks (λ y → y) σ _ (ext′ NE C (λ y → ≃-refl))) (cong O ⟨ lift (ag x) , ptt ⟩)
  atomize-sem (fun-ref f) ρ k σ γ NE C ag O ks =
    ≃-trans (ks (λ y → y) σ _ (ext′ NE C (λ y → ≃-refl))) (cong O ⟨ lift (TT f) , ptt ⟩)
  atomize-sem (lit B c) ρ k σ γ NE C ag O ks = ks (λ y → y) σ _ (ext′ NE C (λ y → ≃-refl))
  atomize-sem N@(pack _ _) = let-sem N
  atomize-sem N@(callc _ _) = let-sem N
  atomize-sem N@(tuple _) = let-sem N
  atomize-sem N@(get _ _) = let-sem N
  atomize-sem N@(inl _) = let-sem N
  atomize-sem N@(inr _) = let-sem N
  atomize-sem N@(case _ _ _) = let-sem N
  atomize-sem N@(prim _ _ _) = let-sem N
  atomize-sem N@(let′ _ _) = let-sem N
  atomize-sem N@(inject _ _) = let-sem N
  atomize-sem N@(project _ _) = let-sem N
  let-sem N ρ k σ γ NE C ag O ks =
    ≃-when (λ { w ⟨ V , ⟨ _ , ⟨ V⊆ , ne ⟩ ⟩ ⟩ → ne-mem ne V⊆ })
      (λ w w∈ → let ⟨ v , v∈ ⟩ = proj₁ (ne-of O _ w w∈) in ⟨ v , proj₂ IH v v∈ ⟩) λ neD →
    ≃-trans (Λ-β (λ X⊆ → proj₁ okt (•-~ _⊆_ (λ _ _ z → z) X⊆)) (fin₁ okt NE neD) (con cT ⌜ rco N ρ ⌝ C))
    (≃-trans (ks S _ (var Z) (ext′ (extend-nonempty-env NE neD) (Con-• (con cT ⌜ rco N ρ ⌝ C) C) (λ y → ≃-refl)))
             (cong O ⟨ lift IH , ptt ⟩))
    where IH = rco-sem N ρ σ γ NE C ag
          okt = ok cT ⌜ k S (var Z) ⌝

  atomizes-sem : ∀ {Γ Δ n B} (Ns : Vec (Tm Σ Γ Any) n) (ρ : Ren Γ Δ)
    (k : ∀ {Δ'} → Ren Δ Δ' → Vec (Atm Σ Δ' Any) n → Exp Σ Δ' B) σ γ → nonempty-env σ → Con-env σ
    → Ag ρ σ γ → (O : Strict n)
    → (∀ {Δ'} (r : Ren Δ Δ') σ' as → Ext r σ' σ → ⟦ ⌜ k r as ⌝ ⟧[ T ] σ' ≃ op O (⟦ ⌜ as ⌝ᵛ ⟧s[ T ] σ'))
    → ⟦ ⌜ atomizes Ns ρ k ⌝ ⟧[ T ] σ ≃ op O (⟦ Ns ⟧s[ T' ] γ)
  atomizes-sem [] ρ k σ γ NE C ag O ks = ks (λ y → y) σ [] (ext′ NE C (λ y → ≃-refl))
  atomizes-sem (N ∷ Ns) ρ k σ γ NE C ag O ks =
    atomize-sem N ρ _ σ γ NE C ag (first O (⟦ Ns ⟧s[ T' ] γ)) λ r σ' a e →
      atomizes-sem Ns _ _ σ' γ (ne e) (cn e) (λ x → ≃-trans (agr e (ρ x)) (ag x)) (⟦ ⌜ a ⌝ᵃ ⟧[ T ] σ' ▷ O)
        λ r' σ'' xs e' →
          ≃-trans (ks _ σ'' (ren r' a ∷ xs) (ext′ (ne e') (cn e') (λ y → ≃-trans (agr e' (r y)) (agr e y))))
                  (cong O ⟨ lift (ren-atm r' a (agr e')) , RRs-refl _ ⟩)

  atomize₂-sem : ∀ {Γ Δ A₁ A₂ B} (L : Tm Σ Γ A₁) (N : Tm Σ Γ A₂) (ρ : Ren Γ Δ)
    (k : ∀ {Δ'} → Atm Σ Δ' A₁ → Atm Σ Δ' A₂ → Exp Σ Δ' B) σ γ → nonempty-env σ → Con-env σ
    → Ag ρ σ γ → (O : Strict 2)
    → (∀ {Δ'} σ' (a : Atm Σ Δ' A₁) b → ⟦ ⌜ k a b ⌝ ⟧[ T ] σ' ≃ op O ⟨ ⟦ ⌜ a ⌝ᵃ ⟧[ T ] σ' , ⟨ ⟦ ⌜ b ⌝ᵃ ⟧[ T ] σ' , ptt ⟩ ⟩)
    → ⟦ ⌜ atomize₂ L N ρ k ⌝ ⟧[ T ] σ ≃ op O ⟨ ⟦ L ⟧[ T' ] γ , ⟨ ⟦ N ⟧[ T' ] γ , ptt ⟩ ⟩
  atomize₂-sem L N ρ k σ γ NE C ag O ks =
    atomize-sem L ρ _ σ γ NE C ag (first O ⟨ ⟦ N ⟧[ T' ] γ , ptt ⟩) λ r σ' a e →
      atomize-sem N _ _ σ' γ (ne e) (cn e) (λ x → ≃-trans (agr e (ρ x)) (ag x)) (⟦ ⌜ a ⌝ᵃ ⟧[ T ] σ' ▷ O)
        λ r' σ'' b e' →
          ≃-trans (ks σ'' (ren r' a) b) (cong O ⟨ lift (ren-atm r' a (agr e')) , ⟨ lift ≃-refl , ptt ⟩ ⟩)

  {- under a binder -}
  ag-ext : ∀ {Γ Δ B} {ρ : Ren Γ Δ} {σ γ X} → Ag ρ σ γ → Ag (ext {B = B} ρ) (X • σ) (X • γ)
  ag-ext ag Z = ≃-refl
  ag-ext ag (S x) = ag x

  rco-sem (` x) ρ σ γ NE C ag = ag x
  rco-sem (fun-ref f) ρ σ γ NE C ag = TT f
  rco-sem (pack L N) ρ σ γ NE C ag = atomize₂-sem L N ρ M.pack σ γ NE C ag pair-op′ λ _ _ _ → ≃-refl
  rco-sem (callc L N) ρ σ γ NE C ag = atomize₂-sem L N ρ M.callc σ γ NE C ag callc-op λ _ _ _ → ≃-refl
  rco-sem (lit B c) ρ σ γ NE C ag = ≃-refl
  rco-sem (tuple Ns) ρ σ γ NE C ag = atomizes-sem Ns ρ _ σ γ NE C ag (tuple-op _) λ _ _ _ _ → ≃-refl
  rco-sem (get i N) ρ σ γ NE C ag = atomize-sem N ρ _ σ γ NE C ag (get-op i) λ _ _ _ _ → ≃-refl
  rco-sem (inl N) ρ σ γ NE C ag = atomize-sem N ρ _ σ γ NE C ag inl-op′ λ _ _ _ _ → ≃-refl
  rco-sem (inr N) ρ σ γ NE C ag = atomize-sem N ρ _ σ γ NE C ag inr-op′ λ _ _ _ _ → ≃-refl
  rco-sem (case L N₁ N₂) ρ σ γ NE C ag =
    atomize-sem L ρ _ σ γ NE C ag (case-op′ (λ X → ⟦ N₁ ⟧[ T' ] (X • γ)) (λ X → ⟦ N₂ ⟧[ T' ] (X • γ)))
      λ r σ' a e →
        let ag₁ = λ {A} (x : _ ∋ A) → ≃-trans (agr e (ρ x)) (ag x)
            br : ∀ (N' : Tm Σ _ Any) v V → (v ∷ V) ≈ (v ∷ V) → _
            br N' v V c = rco-sem N' _ (mem (v ∷ V) • σ') (mem (v ∷ V) • γ)
                            (extend-nonempty-env (ne e) ⟨ v , here refl ⟩) (Con-• (≈⇒Con c) (cn e)) (ag-ext ag₁)
        in 𝒞-≃ {D = ⟦ ⌜ a ⌝ᵃ ⟧[ T ] σ'} {⟦ ⌜ a ⌝ᵃ ⟧[ T ] σ'} {λ X → ⟦ ⌜ rco N₁ (ext λ x → r (ρ x)) ⌝ ⟧[ T ] (X • σ')} {λ X → ⟦ N₁ ⟧[ T' ] (X • γ)}
               {λ X → ⟦ ⌜ rco N₂ (ext λ x → r (ρ x)) ⌝ ⟧[ T ] (X • σ')} {λ X → ⟦ N₂ ⟧[ T' ] (X • γ)}
               ≃-refl (br N₁) (br N₂)
  rco-sem (prim p L N) ρ σ γ NE C ag = atomize₂-sem L N ρ (M.prim p) σ γ NE C ag (prim-op p) λ _ _ _ → ≃-refl
  rco-sem (let′ N₁ N₂) ρ σ γ NE C ag =
    ⋆-≃ (Λ-≃ {λ X → ⟦ ⌜ rco N₂ (ext ρ) ⌝ ⟧[ T ] (X • σ)} {λ X → ⟦ N₂ ⟧[ T' ] (X • γ)} λ V ne c →
           rco-sem N₂ (ext ρ) (mem V • σ) (mem V • γ) (extend-nonempty-env NE (E≢[]⇒nonempty-mem ne))
             (Con-• (≈⇒Con c) C) (ag-ext ag))
        (rco-sem N₁ ρ σ γ NE C ag)
  rco-sem (inject G N) ρ σ γ NE C ag = atomize-sem N ρ _ σ γ NE C ag id-op λ _ _ _ _ → ≃-refl
  rco-sem (project t N) ρ σ γ NE C ag = atomize-sem N ρ _ σ γ NE C ag (project-op t) λ _ _ _ _ → ≃-refl

{- Programs ---------------------------------------------------------------------------}

{- the table of the output means what the table of the input does -}
table-rco : ∀ {Σ ns} (ds : All (Code Σ) ns) {n} (f : Σ ∋ n)
  → tables code′ (All-map ⌜_⌝ (All-map (λ D → rco D (λ x → x)) ds)) f ≃ tables code′ ds f
table-rco [] f = ≃-refl
table-rco {ns = _ ∷ ns} (d ∷ ds) f with lvl f ≟ length ns
... | yes _ = Λ-≃ λ V neV cV → Λ-≃ λ U neU cU →
  rco-sem (tables-con code-con (All-map ⌜_⌝ (All-map (λ D → rco D (λ x → x)) ds))) (table-rco ds) d (λ x → x) _ _
    (extend-nonempty-env (extend-nonempty-env (λ _ → ⟨ ω , refl ⟩) (E≢[]⇒nonempty-mem neV)) (E≢[]⇒nonempty-mem neU))
    (Con-• (≈⇒Con cU) (Con-• (≈⇒Con cV) (λ _ → Con-⌈⌉ ω))) (λ x → ≃-refl)
... | no _ = table-rco ds f

rco-correct : ∀ (P : Program) → ⟦ ⌜ rco-program P ⌝ₚ ⟧ₚ ≃ ⟦ P ⟧ₚ
rco-correct (program ds N) =
  rco-sem (table-con (All-map ⌜_⌝ (All-map (λ D → rco D (λ x → x)) ds))) (table-rco ds) N (λ x → x) _ _
    (λ _ → ⟨ ω , refl ⟩) (λ _ → Con-⌈⌉ ω) (λ x → ≃-refl)

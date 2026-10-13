{-

  Correctness of the concretize pass (Clos2 → Clos3) in the graph model
  with errors (Semantics/GraphErr/{Clos2,Clos3}.agda).

  As in the graph model (proof/Correctness/Graph/ConcretizeCorrect.agda),
  the pass preserves denotations exactly, ⟦ M ⟧ ρ₂ ≃ ⟦ concretize φ M ⟧' ρ₃,
  for every term. What changes is the closure: a Clos2 closure is an error
  exactly when one of its free variables is (left to right), and so is the
  Clos3 closure, whose tuple of free variables is then an error, which
  the application of its code passes on. Otherwise, by consistency, the
  tuple holds no ω, so the code's binders can bind any finite part of it,
  and projecting from it gives back each free variable.

-}

module proof.Correctness.GraphErr.ConcretizeCorrect where

open import Framework.Syntax.SigUtil
open import Framework.Syntax.SyntaxUtil
open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.DOpSig
open import proof.Framework.GraphModel.Domain
open import proof.Framework.GraphModel.OpsBase
open import proof.Framework.GraphModel.ErrorOps
open import proof.Semantics.GraphErr.Prim
open import Language.Clos2 as L2
open import Language.Clos3 as L3
  renaming (AST to AST'; Arg to Arg'; Args to Args'; `_ to #_;
            _⦅_⦆ to _⦅_⦆'; ast to ast'; bind to bind'; clear to clear')
open import proof.Semantics.GraphErr.Clos2 as S2 using (apply-n; push; apply-push; push-plus; ⟦_⟧; ⟦_⟧ₐ; ⟦_⟧₊)
open import proof.Semantics.GraphErr.Clos3 as S3 using (Clos3ᵉ-con) renaming
  (⟦_⟧ to ⟦_⟧'; ⟦_⟧ₐ to ⟦_⟧ₐ'; ⟦_⟧₊ to ⟦_⟧₊')
open import Compiler.Concretize
open import proof.Framework.GraphModel.Env using (Env; •-~)

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _<_; _<?_)
open import Data.Nat.Properties using (+-identityʳ; ≤-antisym; ≤-pred; ≮⇒≥; m+[n∸m]≡n)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_; replicate)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax)
  renaming (_,_ to ⟨_,_⟩ )
open import Data.Sum using (inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Data.Unit using (tt)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong)
open import Relation.Nullary using (¬_; yes; no)
open import Level using (lift; lower)

{- Variables in Clos3 -----------------------------------------------------------}

⟦_⟧ᵣ : Ref → Env Value → 𝒫 Value
⟦ var x ⟧ᵣ ρ = ρ x
⟦ prj i x ⟧ᵣ ρ = projᵉ i ⟨ ρ x , ptt ⟩

ref-ok : ∀ r ρ → ⟦ ref-ast r ⟧' ρ ≡ ⟦ r ⟧ᵣ ρ
ref-ok (var x) ρ = refl
ref-ok (prj i x) ρ = refl

shift-ok : ∀ r X ρ → ⟦ shift-ref r ⟧ᵣ (X • ρ) ≡ ⟦ r ⟧ᵣ ρ
shift-ok (var x) X ρ = refl
shift-ok (prj i x) X ρ = refl

EnvRel : (Var → Ref) → Env Value → Env Value → Set
EnvRel φ ρ₂ ρ₃ = ∀ x → ρ₂ x ≃ ⟦ φ x ⟧ᵣ ρ₃

rel-ext : ∀ {φ ρ₂ ρ₃} → EnvRel φ ρ₂ ρ₃ → ∀ X → EnvRel (ext-ref φ) (X • ρ₂) (X • ρ₃)
rel-ext rel X zero = ≃-refl
rel-ext {φ} {ρ₃ = ρ₃} rel X (suc x) = ≃-trans (rel x) (≃-reflexive (sym (shift-ok (φ x) X ρ₃)))

{- The environment of a Clos2 closure's body ----------------------------------}

init₀ : Env Value
init₀ = λ _ → ⌈ ω ⌉

push-yes : ∀ n (Ds : Results (𝒫 Value) (replicate n ■)) ρ k (p : k < n)
  → push Ds ρ k ≡ nthD Ds (fv-index n k p)
push-yes (suc n) ⟨ D , Ds ⟩ ρ k p with k <? n
... | yes k<n = push-yes n Ds (D • ρ) k k<n
... | no ¬k<n =
  trans (cong (push Ds (D • ρ)) (trans (≤-antisym (≤-pred p) (≮⇒≥ ¬k<n)) (sym (+-identityʳ n))))
        (push-plus n Ds (D • ρ) 0)

push-no : ∀ n (Ds : Results (𝒫 Value) (replicate n ■)) ρ k → ¬ (k < n)
  → push Ds ρ k ≡ ρ (k ∸ n)
push-no n Ds ρ k ¬k<n =
  trans (cong (push Ds ρ) (sym (m+[n∸m]≡n (≮⇒≥ ¬k<n)))) (push-plus n Ds ρ (k ∸ n))

{- a consistent tuple whose components have values holds no ω, nor do its
   components -}
T-val : ∀ n (Ds : Results (𝒫 Value) (replicate n ■)) → vals n Ds → val∈ (𝒯ᵉ n Ds)
T-val zero _ _ = ⟨ ⟨⟩ , ⟨ tt , (λ ()) ⟩ ⟩
T-val (suc n) Ds vs = ⟨ tup[ zero ] (proj₁ (vs zero)) , ⟨ ⟨ refl , ⟨ proj₁ (proj₂ (vs zero)) , vs ⟩ ⟩ , (λ ()) ⟩ ⟩

T-clean : ∀ n (Ds : Results (𝒫 Value) (replicate n ■)) → Con (𝒯ᵉ n Ds) → vals n Ds → Clean (𝒯ᵉ n Ds)
T-clean n Ds cT vs .ω ω∈ refl with T-val n Ds vs
... | ⟨ t , ⟨ t∈ , t≢ ⟩ ⟩ = t≢ (~ω t (cT t ω t∈ ω∈))

comp-clean : ∀ n (Ds : Results (𝒫 Value) (replicate n ■)) → Con (𝒯ᵉ n Ds) → vals n Ds
  → ∀ j → Clean (nthD Ds j)
comp-clean (suc n) Ds cT vs j .ω ω∈ refl with vs j
... | ⟨ d , ⟨ d∈ , d≢ ⟩ ⟩ with cT (tup[ j ] ω) (tup[ j ] d) ⟨ refl , ⟨ ω∈ , vs ⟩ ⟩ ⟨ refl , ⟨ d∈ , vs ⟩ ⟩
... | ⟨ refl , inj₁ neq ⟩ = neq refl
... | ⟨ refl , inj₂ ⟨ _ , ω~d ⟩ ⟩ = d≢ (ω~ d ω~d)

T-vals : ∀ n (Ds : Results (𝒫 Value) (replicate n ■)) v → v ∈ 𝒯ᵉ n Ds → v ≢ ω → vals n Ds
T-vals n Ds v v∈ v≢ with 𝒯ᵉ-inv n v v∈
... | inj₁ ⟨ refl , _ ⟩ = ⊥-elim (v≢ refl)
... | inj₂ (inj₁ ⟨ _ , ⟨ _ , ⟨ _ , ⟨ _ , vs ⟩ ⟩ ⟩ ⟩) = vs
... | inj₂ (inj₂ ⟨ refl , _ ⟩) = λ ()

val-ne : ∀ {D} → val∈ D → nonempty D
val-ne ⟨ d , ⟨ d∈ , _ ⟩ ⟩ = ⟨ d , d∈ ⟩

{- the body of a Clos2 closure and the body of its Clos3 code see the
   same free variables -}
fv-env-rel : ∀ n (Ds₂ Ds₃ : Results (𝒫 Value) (replicate n ■)) (Y : 𝒫 Value)
  → (∀ i → nthD Ds₂ i ≃ nthD Ds₃ i) → vals n Ds₃ → (∀ j → Clean (nthD Ds₃ j))
  → EnvRel (fv-ref n) (Y • push Ds₂ init₀) (Y • 𝒯ᵉ n Ds₃ • init₀)
fv-env-rel n Ds₂ Ds₃ Y Ds≃ vs cl zero = ≃-refl
fv-env-rel n Ds₂ Ds₃ Y Ds≃ vs cl (suc k) with k <? n
... | yes k<n =
  ≃-trans (≃-reflexive (push-yes n Ds₂ init₀ k k<n))
          (≃-trans (Ds≃ (fv-index n k k<n)) (≃-sym (projᵉ-𝒯ᵉ n Ds₃ vs cl (fv-index n k k<n))))
... | no ¬k<n = ≃-reflexive (push-no n Ds₂ init₀ k ¬k<n)

{- Closures -------------------------------------------------------------------}

clos-correct : ∀ n (a : Arg (ν-n n (ν ■))) (Ds₂ Ds₃ : Results (𝒫 Value) (replicate n ■))
  (N' : AST')
  → (∀ i → nthD Ds₂ i ≃ nthD Ds₃ i) → Con (𝒯ᵉ n Ds₃)
  → (∀ ρ₂ ρ₃ → Con-env ρ₃ → EnvRel (fv-ref n) ρ₂ ρ₃ → ⟦ unbind-n n a ⟧ ρ₂ ≃ ⟦ N' ⟧' ρ₃)
  → guardᵉ-n n Ds₂ (Λᵉ ⟨ apply-n n (⟦ a ⟧ₐ init₀) Ds₂ , ptt ⟩)
    ≃ closᵉ n ⟨ (λ X Y → ⟦ N' ⟧' (Y • X • init₀)) , Ds₃ ⟩
clos-correct n a Ds₂ Ds₃ N' Ds≃ cT body = ⟨ G , H ⟩
  where
  T = 𝒯ᵉ n Ds₃
  F' = λ X Y → ⟦ N' ⟧' (Y • X • init₀)
  Ds⊆ = λ i → proj₁ (Ds≃ i)
  Ds⊇ = λ i → proj₂ (Ds≃ i)
  errs→ : errs n Ds₂ → errs n Ds₃
  errs→ = errs-mono n Ds₂ Ds₃ (proj₁ (RRs⇒⊆ (nthD⇒RRs Ds₂ Ds₃ Ds≃)))
  errs← : errs n Ds₃ → errs n Ds₂
  errs← = errs-mono n Ds₃ Ds₂ (proj₂ (RRs⇒⊆ (nthD⇒RRs Ds₂ Ds₃ Ds≃)))
  vals→ : vals n Ds₂ → vals n Ds₃
  vals→ vs i = val∈-mono (Ds⊆ i) (vs i)
  vals← : vals n Ds₃ → vals n Ds₂
  vals← vs i = val∈-mono (Ds⊇ i) (vs i)

  {- applying the closure to U runs the body on the same free variables -}
  body≃ : ∀ U → U ≈ U → vals n Ds₃
    → apply-n n (⟦ a ⟧ₐ init₀) Ds₂ (mem U) ≃ ⟦ N' ⟧' (mem U • T • init₀)
  body≃ U cU vs rewrite apply-push n a init₀ Ds₂ (mem U) =
    body (mem U • push Ds₂ init₀) (mem U • T • init₀)
      (Con-• (≈⇒Con cU) (Con-• cT (λ _ → Con-⌈⌉ ω)))
      (fv-env-rel n Ds₂ Ds₃ (mem U) Ds≃ vs (comp-clean n Ds₃ cT vs))

  G : guardᵉ-n n Ds₂ (Λᵉ ⟨ apply-n n (⟦ a ⟧ₐ init₀) Ds₂ , ptt ⟩) ⊆ closᵉ n ⟨ F' , Ds₃ ⟩
  G w (inj₁ ⟨ refl , e ⟩) = inj₂ ⟨ refl , inj₂ (inj₂ ⟨ ⟨ ν , ⟨ tt , tt ⟩ ⟩ , errs→ e ⟩) ⟩
  G ν (inj₂ ⟨ vs , tt ⟩) with T-val n Ds₃ (vals→ vs)
  ... | ⟨ t , ⟨ t∈ , t≢ ⟩ ⟩ =
    inj₁ ⟨ t ∷ [] , ⟨ ⟨ tt , ⟨ (λ ()) , ⟨ ≈-single , nt ⟩ ⟩ ⟩ , ⟨ (λ { _ (here refl) → t∈ }) , ⟨ (λ ()) , nt ⟩ ⟩ ⟩ ⟩
    where nt = λ { (here eq) → t≢ (sym eq) }
  G (U ↦ x) (inj₂ ⟨ vs , ⟨ x∈ , r ⟩ ⟩)
      with S3.body2-continuous N' init₀ (λ _ → ⟨ ω , refl ⟩) (val-ne (T-val n Ds₃ (vals→ vs)))
             (E≢[]⇒nonempty-mem (proj₁ r)) x (proj₁ (body≃ U (proj₁ (proj₂ r)) (vals→ vs)) x x∈)
  ... | ⟨ V , ⟨ U' , ⟨ neV , ⟨ _ , ⟨ V⊆ , ⟨ U'⊆ , x∈′ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ =
    inj₁ ⟨ V , ⟨ ⟨ ⟨ S3.⟦⟧-monotone N' (•-~ _⊆_ (λ _ _ d∈ → d∈) U'⊆) x x∈′ , r ⟩
                 , ⟨ neV , ⟨ Con⇒≈ V cT V⊆ , nV ⟩ ⟩ ⟩
             , ⟨ V⊆ , ⟨ neV , nV ⟩ ⟩ ⟩ ⟩
    where
    nV = Clean-NoErr V (T-clean n Ds₃ cT (vals→ vs)) V⊆

  H : closᵉ n ⟨ F' , Ds₃ ⟩ ⊆ guardᵉ-n n Ds₂ (Λᵉ ⟨ apply-n n (⟦ a ⟧ₐ init₀) Ds₂ , ptt ⟩)
  H w (inj₁ ⟨ [] , ⟨ _ , ⟨ _ , ⟨ ne , _ ⟩ ⟩ ⟩ ⟩) = ⊥-elim (ne refl)
  H ν (inj₁ ⟨ v ∷ V , ⟨ _ , ⟨ V⊆T , ⟨ _ , nV ⟩ ⟩ ⟩ ⟩) =
    inj₂ ⟨ vals← (T-vals n Ds₃ v (V⊆T v (here refl)) (λ { refl → nV (here refl) })) , tt ⟩
  H (U ↦ x) (inj₁ ⟨ v ∷ V , ⟨ ⟨ ⟨ x∈ , r ⟩ , _ ⟩ , ⟨ V⊆T , ⟨ _ , nV ⟩ ⟩ ⟩ ⟩) =
    inj₂ ⟨ vals← vs , ⟨ proj₂ (body≃ U (proj₁ (proj₂ r)) vs) x
                         (S3.⟦⟧-monotone N' (•-~ _⊆_ (•-~ _⊆_ (λ _ _ d∈ → d∈) V⊆T) (λ _ d∈ → d∈)) x x∈)
                       , r ⟩ ⟩
    where vs = T-vals n Ds₃ v (V⊆T v (here refl)) (λ { refl → nV (here refl) })
  H w (inj₂ ⟨ refl , inj₁ () ⟩)
  H w (inj₂ ⟨ refl , inj₂ (inj₁ ⟨ d , ⟨ d∈ , ⟨ _ , nf ⟩ ⟩ ⟩) ⟩) = ⊥-elim (nf (Λᵉ-fun d d∈))
  H w (inj₂ ⟨ refl , inj₂ (inj₂ ⟨ _ , e ⟩) ⟩) = inj₁ ⟨ refl , errs← e ⟩

{- The main lemma -------------------------------------------------------------}

concretize-correct : ∀ (M : AST) φ ρ₂ ρ₃ → Con-env ρ₃ → EnvRel φ ρ₂ ρ₃
  → ⟦ M ⟧ ρ₂ ≃ ⟦ concretize φ M ⟧' ρ₃

body-correct : ∀ n k (a : Arg (ν-n k (ν ■)))
  → ∀ ρ₂ ρ₃ → Con-env ρ₃ → EnvRel (fv-ref n) ρ₂ ρ₃
  → ⟦ unbind-n k a ⟧ ρ₂ ≃ ⟦ conc-body n k a ⟧' ρ₃

args-correct : ∀ {n} (args : Args (replicate n ■)) φ ρ₂ ρ₃ → Con-env ρ₃ → EnvRel φ ρ₂ ρ₃
  → RRs (replicate n ■) (⟦ args ⟧₊ ρ₂) (⟦ conc-args φ args ⟧₊' ρ₃)

concretize-correct (` x) φ ρ₂ ρ₃ c rel =
  ≃-trans (rel x) (≃-reflexive (sym (ref-ok (φ x) ρ₃)))
concretize-correct (clos-op n ⦅ ! clear a ,, fvs ⦆) φ ρ₂ ρ₃ c rel =
  clos-correct n a (⟦ fvs ⟧₊ ρ₂) (⟦ conc-args φ fvs ⟧₊' ρ₃) (conc-body n n a)
    (nthD-≃ _ _ (args-correct fvs φ ρ₂ ρ₃ c rel)) (Clos3ᵉ-con (tuple n ⦅ conc-args φ fvs ⦆') c)
    (body-correct n n a)
concretize-correct (app ⦅ L ,, M ,, Nil ⦆) φ ρ₂ ρ₃ c rel =
  ⋆ᵉ-≃ (concretize-correct L φ ρ₂ ρ₃ c rel) (concretize-correct M φ ρ₂ ρ₃ c rel)
concretize-correct (lit B k ⦅ Nil ⦆) φ ρ₂ ρ₃ c rel = ≃-refl
concretize-correct (tuple n ⦅ args ⦆) φ ρ₂ ρ₃ c rel =
  mono-≃ (𝒯ᵉ-mono n) (args-correct args φ ρ₂ ρ₃ c rel)
concretize-correct (get i ⦅ M ,, Nil ⦆) φ ρ₂ ρ₃ c rel =
  projᵉ-≃ i (concretize-correct M φ ρ₂ ρ₃ c rel)
concretize-correct (inl-op ⦅ M ,, Nil ⦆) φ ρ₂ ρ₃ c rel =
  inlᵉ-≃ (concretize-correct M φ ρ₂ ρ₃ c rel)
concretize-correct (inr-op ⦅ M ,, Nil ⦆) φ ρ₂ ρ₃ c rel =
  inrᵉ-≃ (concretize-correct M φ ρ₂ ρ₃ c rel)
concretize-correct (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) φ ρ₂ ρ₃ c rel =
  𝒞ᵉ-≃ {F = λ X → ⟦ M ⟧ (X • ρ₂)} {λ X → ⟦ concretize (ext-ref φ) M ⟧' (X • ρ₃)}
       {λ X → ⟦ N ⟧ (X • ρ₂)} {λ X → ⟦ concretize (ext-ref φ) N ⟧' (X • ρ₃)}
       (concretize-correct L φ ρ₂ ρ₃ c rel)
       (λ v V cV _ → concretize-correct M (ext-ref φ) _ _ (Con-• (≈⇒Con cV) c) (rel-ext rel (mem (v ∷ V))))
       (λ v V cV _ → concretize-correct N (ext-ref φ) _ _ (Con-• (≈⇒Con cV) c) (rel-ext rel (mem (v ∷ V))))
concretize-correct (prim p ⦅ L ,, M ,, Nil ⦆) φ ρ₂ ρ₃ c rel =
  primᵉ-≃ p (concretize-correct L φ ρ₂ ρ₃ c rel) (concretize-correct M φ ρ₂ ρ₃ c rel)
concretize-correct (let-op ⦅ M ,, ⟩ N ,, Nil ⦆) φ ρ₂ ρ₃ c rel =
  letᵉ-≃ (concretize-correct M φ ρ₂ ρ₃ c rel)
    (λ V _ cV _ → concretize-correct N (ext-ref φ) _ _ (Con-• (≈⇒Con cV) c) (rel-ext rel (mem V)))

body-correct n zero (bind (ast N)) ρ₂ ρ₃ rel = concretize-correct N (fv-ref n) ρ₂ ρ₃ rel
body-correct n (suc k) (bind a) = body-correct n k a

args-correct {zero} Nil φ ρ₂ ρ₃ c rel = ptt
args-correct {suc n} (M ,, args) φ ρ₂ ρ₃ c rel =
  ⟨ lift (concretize-correct M φ ρ₂ ρ₃ c rel) , args-correct args φ ρ₂ ρ₃ c rel ⟩

{- The end theorem: every program ------------------------------------------------}

concretize-correct-closed : ∀ (M : AST) → ⟦ M ⟧ ρ₀ ≃ ⟦ concretize-program M ⟧' ρ₀
concretize-correct-closed M = concretize-correct M var ρ₀ ρ₀ (λ _ → Con-⌈⌉ ω) (λ x → ≃-refl)

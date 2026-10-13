{-

  Correctness of the concretize pass (Clos2 → Clos3) in the monadic graph
  model with errors (Semantics/GraphErrM/{Clos2,Clos3}.agda, a pilot).

  As in the graph model (proof/Correctness/Graph/ConcretizeCorrect.agda),
  the pass preserves denotations exactly, for every term. The closures
  of both languages bind their free variables left to right (binds), so
  they err together; on the values of the free variables, the Clos3
  closure is its code applied to their tuple (⋆ᵐ-val, binds-assoc), and
  projecting from that tuple gives back each free variable.

-}

module proof.Correctness.GraphErrM.ConcretizeCorrect where

open import Framework.Syntax.SigUtil
open import Framework.Syntax.SyntaxUtil
open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.DOpSig
open import proof.Framework.GraphModel.Domain
open import proof.Framework.GraphModel.OpsBase
open import proof.Framework.GraphModel.ErrorMonad
open import proof.Framework.GraphModel.Ops using (𝒯; ⋆; 𝒯-mono; 𝒯-consis)
open import proof.Framework.GraphModel.ContinuityBase using (mono)
open import proof.Framework.GraphModel.DenotProperties using (Every)
open import proof.Semantics.GraphErrM.Prim
open import Language.Clos2 as L2
open import Language.Clos3 as L3
  renaming (AST to AST'; Arg to Arg'; Args to Args'; `_ to #_;
            _⦅_⦆ to _⦅_⦆'; ast to ast'; bind to bind'; clear to clear')
open import proof.Semantics.GraphErrM.Clos2 as S2 using (apply-n; apply-n-pres; push; apply-push; push-plus; ⟦_⟧; ⟦_⟧ₐ; ⟦_⟧₊; ⟦⟧-monotone-arg)
open import proof.Semantics.GraphErrM.Clos3 as S3 using (Clos3ᵐ-con) renaming
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
open import Data.Unit using (tt; ⊤)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong)
open import Relation.Nullary using (¬_; yes; no)
open import Level using (lift; lower)

{- Variables in Clos3 -----------------------------------------------------------}

⟦_⟧ᵣ : Ref → Env Value → 𝒫 Value
⟦ var x ⟧ᵣ ρ = ρ x
⟦ prj i x ⟧ᵣ ρ = projᵐ i ⟨ ρ x , ptt ⟩

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

𝒯-ne : ∀ n (Xs : Results (𝒫 Value) (replicate n ■)) → (∀ j → nonempty (nthD Xs j)) → nonempty (𝒯 n Xs)
𝒯-ne zero _ _ = ⟨ ⟨⟩ , tt ⟩
𝒯-ne (suc n) Xs ne = ⟨ tup[ zero ] _ , ⟨ refl , ⟨ proj₂ (ne zero) , ne ⟩ ⟩ ⟩

{- the body of a Clos2 closure and the body of its Clos3 code see the
   same free variables -}
fv-env-rel : ∀ n (Xs : Results (𝒫 Value) (replicate n ■)) (Y : 𝒫 Value) → (∀ j → nonempty (nthD Xs j))
  → EnvRel (fv-ref n) (Y • push Xs init₀) (Y • 𝒯 n Xs • init₀)
fv-env-rel n Xs Y ne zero = ≃-refl
fv-env-rel n Xs Y ne (suc k) with k <? n
... | yes k<n = ≃-trans (≃-reflexive (push-yes n Xs init₀ k k<n)) (≃-sym (projᵐ-𝒯 n Xs ne (fv-index n k k<n)))
... | no ¬k<n = ≃-reflexive (push-no n Xs init₀ k ¬k<n)

{- Closures -------------------------------------------------------------------}

clos-correct : ∀ n (a : Arg (ν-n n (ν ■))) (Ds₂ Ds₃ : Results (𝒫 Value) (replicate n ■)) (N' : AST')
  → (∀ i → nthD Ds₂ i ≃ nthD Ds₃ i) → (∀ i → Con (nthD Ds₃ i))
  → (∀ ρ₂ ρ₃ → Con-env ρ₃ → EnvRel (fv-ref n) ρ₂ ρ₃ → ⟦ unbind-n n a ⟧ ρ₂ ≃ ⟦ N' ⟧' ρ₃)
  → binds n Ds₂ (λ Xs → Λᵐ ⟨ apply-n n (⟦ a ⟧ₐ init₀) Xs , ptt ⟩)
    ≃ closᵐ n ⟨ (λ X Y → ⟦ N' ⟧' (Y • X • init₀)) , Ds₃ ⟩
clos-correct n a Ds₂ Ds₃ N' Ds≃ cDs body =
  ≃-trans (mono⇒≃ (λ _ _ r → lift (binds-mono n r mK)) (proj₁ (RRs⇒⊆ (nthD⇒RRs Ds₂ Ds₃ Ds≃)))
                                                       (proj₂ (RRs⇒⊆ (nthD⇒RRs Ds₂ Ds₃ Ds≃))))
  (≃-trans (binds-cong n core)
  (≃-sym (≃-trans (⋆ᵐ-val {ΛΛᵐ ⟨ F' , ptt ⟩} {𝒯ᵐ n Ds₃} (λ { .ω ⟨ () , _ ⟩ refl }) ⟨ ν , ⟨ tt , tt ⟩ ⟩
                            (λ { (V ↦ w) _ → refl ; ν _ → refl }))
          (≃-trans (binds-assoc n (⋆-r {ΛΛᵐ ⟨ F' , ptt ⟩}))
                   (binds-cong n (λ b → ≫=-β (⋆-r {ΛΛᵐ ⟨ F' , ptt ⟩}) (𝒯-clean n)
                                            (𝒯-ne n _ (λ j → proj₂ (proj₂ (b j))))))))))
  where
  F = ⟦ a ⟧ₐ init₀
  F' = λ X Y → ⟦ N' ⟧' (Y • X • init₀)
  mK : Rel⊆ n (λ Xs → Λᵐ ⟨ apply-n n F Xs , ptt ⟩) (λ Xs → Λᵐ ⟨ apply-n n F Xs , ptt ⟩)
  mK {Xs} {Ys} Xs⊆ = lower (mono (Λᵐ-good {⊤}) ⟨ apply-n n F Xs , ptt ⟩ ⟨ apply-n n F Ys , ptt ⟩
    ⟨ apply-n-pres _⊆_ n F F Xs Ys (⟦⟧-monotone-arg a (λ _ _ z → z)) Xs⊆ , ptt ⟩)
  core : ∀ {Xs} → Bound n Xs Ds₃ → Λᵐ ⟨ apply-n n F Xs , ptt ⟩ ≃ ⋆ ⟨ ΛΛᵐ ⟨ F' , ptt ⟩ , ⟨ 𝒯 n Xs , ptt ⟩ ⟩
  core {Xs} b = ⟨ G , H ⟩
    where
    ne = λ j → proj₂ (proj₂ (b j))
    T = 𝒯 n Xs
    cT : Con T
    cT = lower (𝒯-consis n Xs Xs (cs n Xs (λ j → Con-⊆ (cDs j) (proj₁ (b j)))))
      where
      cs : ∀ m (Ys : Results (𝒫 Value) (replicate m ■)) → (∀ j → Con (nthD Ys j))
        → results-rel-pres (Every _~_) (replicate m ■) Ys Ys
      cs zero _ _ = ptt
      cs (suc m) ⟨ Y , Ys ⟩ c = ⟨ lift (c zero) , cs m Ys (λ j → c (suc j)) ⟩
    t = proj₁ (𝒯-ne n Xs ne)
    t∈ = proj₂ (𝒯-ne n Xs ne)
    body≃ : ∀ U → U ≈ U → apply-n n F Xs (mem U) ≃ ⟦ N' ⟧' (mem U • T • init₀)
    body≃ U cU rewrite apply-push n a init₀ Xs (mem U) =
      body (mem U • push Xs init₀) (mem U • T • init₀) (Con-• (≈⇒Con cU) (Con-• cT (λ _ → Con-⌈⌉ ω)))
        (fv-env-rel n Xs (mem U) ne)
    G : Λᵐ ⟨ apply-n n F Xs , ptt ⟩ ⊆ ⋆ ⟨ ΛΛᵐ ⟨ F' , ptt ⟩ , ⟨ T , ptt ⟩ ⟩
    G ν _ = ⟨ t ∷ [] , ⟨ ⟨ ⟨ tt , ⟨ (λ ()) , ≈-single ⟩ ⟩ , ⟨ nt , tt ⟩ ⟩ , ⟨ (λ { _ (here refl) → t∈ }) , (λ ()) ⟩ ⟩ ⟩
      where nt = λ { (here eq) → 𝒯-clean n t t∈ (sym eq) }
    G (U ↦ x) ⟨ ⟨ x∈ , ⟨ neU , cU ⟩ ⟩ , nU ⟩
        with S3.body2-continuous N' init₀ (λ _ → ⟨ ω , refl ⟩) ⟨ t , t∈ ⟩ (E≢[]⇒nonempty-mem neU) x
               (proj₁ (body≃ U cU) x x∈)
    ... | ⟨ V , ⟨ U' , ⟨ neV , ⟨ _ , ⟨ V⊆ , ⟨ U'⊆ , x∈′ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ =
      ⟨ V , ⟨ ⟨ ⟨ ⟨ S3.⟦⟧-monotone N' (•-~ _⊆_ (λ _ _ d∈ → d∈) U'⊆) x x∈′ , ⟨ neU , cU ⟩ ⟩ , ⟨ neV , Con⇒≈ V cT V⊆ ⟩ ⟩
              , ⟨ (λ ω∈ → 𝒯-clean n ω (V⊆ ω ω∈) refl) , nU ⟩ ⟩ , ⟨ V⊆ , neV ⟩ ⟩ ⟩
    H : ⋆ ⟨ ΛΛᵐ ⟨ F' , ptt ⟩ , ⟨ T , ptt ⟩ ⟩ ⊆ Λᵐ ⟨ apply-n n F Xs , ptt ⟩
    H ν _ = ⟨ tt , tt ⟩
    H (U ↦ x) ⟨ V , ⟨ ⟨ ⟨ ⟨ x∈ , r ⟩ , _ ⟩ , ⟨ _ , nU ⟩ ⟩ , ⟨ V⊆T , _ ⟩ ⟩ ⟩ =
      ⟨ ⟨ proj₂ (body≃ U (proj₂ r)) x
            (S3.⟦⟧-monotone N' (•-~ _⊆_ (•-~ _⊆_ (λ _ _ d∈ → d∈) V⊆T) (λ _ d∈ → d∈)) x x∈) , r ⟩ , nU ⟩

args-con : ∀ {n} (args : Args' (replicate n ■)) {ρ} → Con-env ρ → ∀ i → Con (nthD (⟦ args ⟧₊' ρ) i)
args-con {suc n} (M ,, args) c zero = Clos3ᵐ-con M c
args-con {suc n} (M ,, args) c (suc i) = args-con args c i

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
    (nthD-≃ _ _ (args-correct fvs φ ρ₂ ρ₃ c rel)) (args-con (conc-args φ fvs) c)
    (body-correct n n a)
concretize-correct (app ⦅ L ,, M ,, Nil ⦆) φ ρ₂ ρ₃ c rel =
  ⋆ᵐ-≃ (concretize-correct L φ ρ₂ ρ₃ c rel) (concretize-correct M φ ρ₂ ρ₃ c rel)
concretize-correct (lit B k ⦅ Nil ⦆) φ ρ₂ ρ₃ c rel = ≃-refl
concretize-correct (tuple n ⦅ args ⦆) φ ρ₂ ρ₃ c rel =
  mono-≃ (mono (𝒯ᵐ-good {⊤} n)) (args-correct args φ ρ₂ ρ₃ c rel)
concretize-correct (get i ⦅ M ,, Nil ⦆) φ ρ₂ ρ₃ c rel =
  projᵐ-≃ i (concretize-correct M φ ρ₂ ρ₃ c rel)
concretize-correct (inl-op ⦅ M ,, Nil ⦆) φ ρ₂ ρ₃ c rel =
  inlᵐ-≃ (concretize-correct M φ ρ₂ ρ₃ c rel)
concretize-correct (inr-op ⦅ M ,, Nil ⦆) φ ρ₂ ρ₃ c rel =
  inrᵐ-≃ (concretize-correct M φ ρ₂ ρ₃ c rel)
concretize-correct (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) φ ρ₂ ρ₃ c rel =
  𝒞ᵐ-≃ {F = λ X → ⟦ M ⟧ (X • ρ₂)} {λ X → ⟦ concretize (ext-ref φ) M ⟧' (X • ρ₃)}
       {λ X → ⟦ N ⟧ (X • ρ₂)} {λ X → ⟦ concretize (ext-ref φ) N ⟧' (X • ρ₃)}
       (concretize-correct L φ ρ₂ ρ₃ c rel)
       (λ V _ cV _ → concretize-correct M (ext-ref φ) _ _ (Con-• (≈⇒Con cV) c) (rel-ext rel (mem V)))
       (λ V _ cV _ → concretize-correct N (ext-ref φ) _ _ (Con-• (≈⇒Con cV) c) (rel-ext rel (mem V)))
concretize-correct (prim p ⦅ L ,, M ,, Nil ⦆) φ ρ₂ ρ₃ c rel =
  primᵐ-≃ p (concretize-correct L φ ρ₂ ρ₃ c rel) (concretize-correct M φ ρ₂ ρ₃ c rel)
concretize-correct (let-op ⦅ M ,, ⟩ N ,, Nil ⦆) φ ρ₂ ρ₃ c rel =
  letᵐ-≃ (concretize-correct M φ ρ₂ ρ₃ c rel)
    (λ V _ cV _ → concretize-correct N (ext-ref φ) _ _ (Con-• (≈⇒Con cV) c) (rel-ext rel (mem V)))

body-correct n zero (bind (ast N)) ρ₂ ρ₃ rel = concretize-correct N (fv-ref n) ρ₂ ρ₃ rel
body-correct n (suc k) (bind a) = body-correct n k a

args-correct {zero} Nil φ ρ₂ ρ₃ c rel = ptt
args-correct {suc n} (M ,, args) φ ρ₂ ρ₃ c rel =
  ⟨ lift (concretize-correct M φ ρ₂ ρ₃ c rel) , args-correct args φ ρ₂ ρ₃ c rel ⟩

{- The end theorem: every program ------------------------------------------------}

concretize-correct-closed : ∀ (M : AST) → ⟦ M ⟧ ρ₀ ≃ ⟦ concretize-program M ⟧' ρ₀
concretize-correct-closed M = concretize-correct M var ρ₀ ρ₀ (λ _ → Con-⌈⌉ ω) (λ x → ≃-refl)

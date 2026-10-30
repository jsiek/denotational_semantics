{-

  Correctness of the concretize pass (Clos2 → Clos3).

  Clos2 and Clos3 use the same values, and concretize only changes how
  the code of a closure reaches its free variables: one at a time in
  Clos2, as components of a tuple in Clos3. So the pass preserves
  denotations exactly: ⟦ M ⟧ ρ₂ ≃ ⟦ concretize φ M ⟧' ρ₃, which gives both
  the forward and the backward direction at once.

  Tuples and Clos2 closures are both strict, so a closure has values in
  Clos2 exactly when its tuple of free variables has values in Clos3, and
  then projecting from the tuple gives back each free variable.

  The direction from Clos2 to Clos3 uses the continuity of the Clos3
  semantics (body2-continuous), to pick a finite part of the
  tuple of free variables.

-}

open import Framework.Syntax.SigUtil
open import Framework.Syntax.SyntaxUtil
open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.DOpSig
open import Framework.Primitives
open import proof.Framework.GraphModel.Domain
open import proof.Framework.GraphModel.Ops
open import proof.Semantics.Graph.Prim
open import Untyped.Language.Clos2 as L2
open import Untyped.Language.Clos3 as L3
  renaming (AST to AST'; Arg to Arg'; Args to Args'; `_ to #_;
            _⦅_⦆ to _⦅_⦆'; ast to ast'; bind to bind'; clear to clear')
open import Untyped.proof.Semantics.Graph.Clos2Iswim as S2
open import Untyped.proof.Semantics.Graph.Clos3Iswim as S3 renaming
  (⟦_⟧ to ⟦_⟧'; ⟦_⟧ₐ to ⟦_⟧ₐ'; ⟦_⟧₊ to ⟦_⟧₊')
open import Untyped.Compiler.Concretize
open import Untyped.proof.Correctness.Graph.SplitFiniteCommon using (Env; Init; ρ₀; single⊆; ne-mem)
open import proof.Framework.GraphModel.Env using (nonempty-env; •-~)

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _<_; _<?_)
open import Data.Nat.Properties using (+-suc; +-identityʳ; ≤-antisym; ≤-pred; ≮⇒≥; m+[n∸m]≡n)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_; replicate)
open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax)
  renaming (_,_ to ⟨_,_⟩ )
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong)
open import Relation.Nullary using (¬_; yes; no)
open import Level using (lift; lower)

module Untyped.proof.Correctness.Graph.ConcretizeCorrect where

{- Variables in Clos3 -----------------------------------------------------------}

⟦_⟧ᵣ : Ref → Env → 𝒫 Value
⟦ var x ⟧ᵣ ρ = ρ x
⟦ prj i x ⟧ᵣ ρ = proj i ⟨ ρ x , ptt ⟩

ref-ok : ∀ r ρ → ⟦ ref-ast r ⟧' ρ ≡ ⟦ r ⟧ᵣ ρ
ref-ok (var x) ρ = refl
ref-ok (prj i x) ρ = refl

shift-ok : ∀ r X ρ → ⟦ shift-ref r ⟧ᵣ (X • ρ) ≡ ⟦ r ⟧ᵣ ρ
shift-ok (var x) X ρ = refl
shift-ok (prj i x) X ρ = refl

{- a Clos2 environment and a Clos3 environment that agree through φ -}
EnvRel : (Var → Ref) → Env → Env → Set
EnvRel φ ρ₂ ρ₃ = ∀ x → ρ₂ x ≃ ⟦ φ x ⟧ᵣ ρ₃

rel-ext : ∀ {φ ρ₂ ρ₃} → EnvRel φ ρ₂ ρ₃ → ∀ X → EnvRel (ext-ref φ) (X • ρ₂) (X • ρ₃)
rel-ext rel X zero = ≃-refl
rel-ext {φ} {ρ₃ = ρ₃} rel X (suc x) = ≃-trans (rel x) (≃-reflexive (sym (shift-ok (φ x) X ρ₃)))

{- The environment of a Clos2 closure's body ----------------------------------}

init₀ : Env
init₀ = λ _ → Init

{- bind the free variables one at a time, the last one ending up first -}
push : ∀ {n} → Results (𝒫 Value) (replicate n ■) → Env → Env
push {zero} _ ρ = ρ
push {suc n} ⟨ D , Ds ⟩ ρ = push Ds (D • ρ)

apply-push : ∀ k (a : Arg (ν-n k (ν ■))) (ρ : Env) Ds (Y : 𝒫 Value)
  → apply-n k (⟦ a ⟧ₐ ρ) Ds Y ≡ ⟦ unbind-n k a ⟧ (Y • push Ds ρ)
apply-push zero (bind (ast N)) ρ _ Y = refl
apply-push (suc k) (bind a) ρ ⟨ D , Ds ⟩ Y = apply-push k a (D • ρ) Ds Y

push-plus : ∀ n (Ds : Results (𝒫 Value) (replicate n ■)) ρ j → push Ds ρ (n + j) ≡ ρ j
push-plus zero _ ρ j = refl
push-plus (suc n) ⟨ D , Ds ⟩ ρ j rewrite sym (+-suc n j) = push-plus n Ds (D • ρ) (suc j)

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

proj-𝒯 : ∀ n (Ds : Results (𝒫 Value) (replicate n ■)) → (∀ j → nonempty (nthD Ds j))
  → (i : Fin n) → proj i ⟨ 𝒯 n Ds , ptt ⟩ ≃ nthD Ds i
proj-𝒯 (suc n) Ds ne i = ⟨ G , (λ d d∈ → ⟨ refl , ⟨ d∈ , ne ⟩ ⟩) ⟩
  where
  G : proj i ⟨ 𝒯 (suc n) Ds , ptt ⟩ ⊆ nthD Ds i
  G d ⟨ refl , ⟨ d∈ , _ ⟩ ⟩ = d∈

{- the body of a Clos2 closure and the body of its Clos3 code see the
   same free variables -}
fv-env-rel : ∀ n (Ds₂ Ds₃ : Results (𝒫 Value) (replicate n ■)) (Y : 𝒫 Value)
  → (∀ i → nthD Ds₂ i ≃ nthD Ds₃ i) → (∀ j → nonempty (nthD Ds₃ j))
  → EnvRel (fv-ref n) (Y • push Ds₂ init₀) (Y • 𝒯 n Ds₃ • init₀)
fv-env-rel n Ds₂ Ds₃ Y Ds≃ ne₃ zero = ≃-refl
fv-env-rel n Ds₂ Ds₃ Y Ds≃ ne₃ (suc k) with k <? n
... | yes k<n =
  ≃-trans (≃-reflexive (push-yes n Ds₂ init₀ k k<n))
          (≃-trans (Ds≃ (fv-index n k k<n)) (≃-sym (proj-𝒯 n Ds₃ ne₃ (fv-index n k k<n))))
... | no ¬k<n = ≃-reflexive (push-no n Ds₂ init₀ k ¬k<n)

ne-≃ : ∀ {n} {Ds Es : Results (𝒫 Value) (replicate n ■)} → (∀ i → nthD Ds i ⊆ nthD Es i)
  → (∀ i → nonempty (nthD Ds i)) → ∀ i → nonempty (nthD Es i)
ne-≃ Ds⊆ ne i = ⟨ proj₁ (ne i) , Ds⊆ i _ (proj₂ (ne i)) ⟩

{- a tuple has values exactly when all of its components do -}
T-ne : ∀ n (Ds : Results (𝒫 Value) (replicate n ■)) → (∀ i → nonempty (nthD Ds i))
  → nonempty (𝒯 n Ds)
T-ne zero _ _ = ⟨ ⟨⟩ , tt ⟩
T-ne (suc n) Ds ne = ⟨ tup[ zero ] (proj₁ (ne zero)) , ⟨ refl , ⟨ proj₂ (ne zero) , ne ⟩ ⟩ ⟩

T-ne⁻ : ∀ n (Ds : Results (𝒫 Value) (replicate n ■)) → nonempty (𝒯 n Ds)
  → ∀ i → nonempty (nthD Ds i)
T-ne⁻ (suc n) Ds ⟨ tup[ i ] d , ⟨ refl , ⟨ _ , ne ⟩ ⟩ ⟩ = ne

{- Closures -------------------------------------------------------------------}

clos-correct : ∀ n (a : Arg (ν-n n (ν ■))) (Ds₂ Ds₃ : Results (𝒫 Value) (replicate n ■))
  (N' : AST')
  → (∀ i → nthD Ds₂ i ≃ nthD Ds₃ i) → Con (𝒯 n Ds₃)
  → (∀ ρ₂ ρ₃ → Con-env ρ₃ → EnvRel (fv-ref n) ρ₂ ρ₃ → ⟦ unbind-n n a ⟧ ρ₂ ≃ ⟦ N' ⟧' ρ₃)
  → guard-n n Ds₂ (Λ ⟨ apply-n n (⟦ a ⟧ₐ init₀) Ds₂ , ptt ⟩)
    ≃ ⋆ ⟨ Λ ⟨ (λ X → Λ ⟨ (λ Y → ⟦ N' ⟧' (Y • X • init₀)) , ptt ⟩) , ptt ⟩
        , ⟨ 𝒯 n Ds₃ , ptt ⟩ ⟩
clos-correct n a Ds₂ Ds₃ N' Ds≃ cT body = ⟨ G , H ⟩
  where
  T = 𝒯 n Ds₃

  {- applying the closure to U runs the body on the same free variables -}
  body≃ : ∀ U → U ≈ U → (∀ i → nonempty (nthD Ds₂ i))
    → apply-n n (⟦ a ⟧ₐ init₀) Ds₂ (mem U) ≃ ⟦ N' ⟧' (mem U • T • init₀)
  body≃ U cU ne₂ rewrite apply-push n a init₀ Ds₂ (mem U) =
    body (mem U • push Ds₂ init₀) (mem U • T • init₀)
      (Con-• (≈⇒Con cU) (Con-• cT (λ _ → Con-⌈⌉ ω)))
      (fv-env-rel n Ds₂ Ds₃ (mem U) Ds≃ (ne-≃ (λ i → proj₁ (Ds≃ i)) ne₂))

  G : guard-n n Ds₂ (Λ ⟨ apply-n n (⟦ a ⟧ₐ init₀) Ds₂ , ptt ⟩)
      ⊆ ⋆ ⟨ Λ ⟨ (λ X → Λ ⟨ (λ Y → ⟦ N' ⟧' (Y • X • init₀)) , ptt ⟩) , ptt ⟩ , ⟨ T , ptt ⟩ ⟩
  G ν ⟨ ne₂ , tt ⟩ =
    ⟨ proj₁ neT ∷ [] , ⟨ ⟨ tt , ⟨ (λ ()) , ≈-single ⟩ ⟩ , ⟨ single⊆ (proj₂ neT) , (λ ()) ⟩ ⟩ ⟩
    where neT = T-ne n Ds₃ (ne-≃ (λ i → proj₁ (Ds≃ i)) ne₂)
  G (U ↦ x) ⟨ ne₂ , ⟨ x∈ , ⟨ neU , cU ⟩ ⟩ ⟩
      with S3.body2-continuous N' init₀ (λ _ → ⟨ ω , refl ⟩) (T-ne n Ds₃ (ne-≃ (λ i → proj₁ (Ds≃ i)) ne₂))
             (E≢[]⇒nonempty-mem neU) x (proj₁ (body≃ U cU ne₂) x x∈)
  ... | ⟨ V , ⟨ U' , ⟨ neV , ⟨ _ , ⟨ V⊆ , ⟨ U'⊆ , x∈′ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ =
    ⟨ V , ⟨ ⟨ ⟨ S3.⟦⟧-monotone N' (•-~ _⊆_ (λ _ _ d∈ → d∈) U'⊆) x x∈′ , ⟨ neU , cU ⟩ ⟩
            , ⟨ neV , Con⇒≈ V cT V⊆ ⟩ ⟩ , ⟨ V⊆ , neV ⟩ ⟩ ⟩

  H : ⋆ ⟨ Λ ⟨ (λ X → Λ ⟨ (λ Y → ⟦ N' ⟧' (Y • X • init₀)) , ptt ⟩) , ptt ⟩ , ⟨ T , ptt ⟩ ⟩
      ⊆ guard-n n Ds₂ (Λ ⟨ apply-n n (⟦ a ⟧ₐ init₀) Ds₂ , ptt ⟩)
  H ν ⟨ V , ⟨ _ , ⟨ V⊆T , neV ⟩ ⟩ ⟩ =
    ⟨ ne-≃ (λ i → proj₂ (Ds≃ i)) (T-ne⁻ n Ds₃ (ne-mem neV V⊆T)) , tt ⟩
  H (U ↦ x) ⟨ V , ⟨ ⟨ ⟨ x∈ , neU ⟩ , _ ⟩ , ⟨ V⊆T , neV ⟩ ⟩ ⟩ =
    ⟨ ne₂ , ⟨ proj₂ (body≃ U (proj₂ neU) ne₂) x
                (S3.⟦⟧-monotone N' (•-~ _⊆_ (•-~ _⊆_ (λ _ _ d∈ → d∈) V⊆T) (λ _ d∈ → d∈)) x x∈)
            , neU ⟩ ⟩
    where
    ne₂ = ne-≃ (λ i → proj₂ (Ds≃ i)) (T-ne⁻ n Ds₃ (ne-mem neV V⊆T))

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
    (nthD-≃ _ _ (args-correct fvs φ ρ₂ ρ₃ c rel)) (Clos3-con (tuple n ⦅ conc-args φ fvs ⦆') c)
    (body-correct n n a)
concretize-correct (app ⦅ L ,, M ,, Nil ⦆) φ ρ₂ ρ₃ c rel =
  ⋆-≃ (concretize-correct L φ ρ₂ ρ₃ c rel) (concretize-correct M φ ρ₂ ρ₃ c rel)
concretize-correct (lit B k ⦅ Nil ⦆) φ ρ₂ ρ₃ c rel = ≃-refl
concretize-correct (tuple n ⦅ args ⦆) φ ρ₂ ρ₃ c rel =
  mono-≃ (𝒯-mono n) (args-correct args φ ρ₂ ρ₃ c rel)
concretize-correct (get i ⦅ M ,, Nil ⦆) φ ρ₂ ρ₃ c rel =
  proj-≃ i (concretize-correct M φ ρ₂ ρ₃ c rel)
concretize-correct (inl-op ⦅ M ,, Nil ⦆) φ ρ₂ ρ₃ c rel =
  inl-≃ (concretize-correct M φ ρ₂ ρ₃ c rel)
concretize-correct (inr-op ⦅ M ,, Nil ⦆) φ ρ₂ ρ₃ c rel =
  inr-≃ (concretize-correct M φ ρ₂ ρ₃ c rel)
concretize-correct (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) φ ρ₂ ρ₃ c rel =
  𝒞-≃ {F = λ X → ⟦ M ⟧ (X • ρ₂)} {λ X → ⟦ concretize (ext-ref φ) M ⟧' (X • ρ₃)}
      {λ X → ⟦ N ⟧ (X • ρ₂)} {λ X → ⟦ concretize (ext-ref φ) N ⟧' (X • ρ₃)}
      (concretize-correct L φ ρ₂ ρ₃ c rel)
      (λ v V cV → concretize-correct M (ext-ref φ) _ _ (Con-• (≈⇒Con cV) c) (rel-ext rel (mem (v ∷ V))))
      (λ v V cV → concretize-correct N (ext-ref φ) _ _ (Con-• (≈⇒Con cV) c) (rel-ext rel (mem (v ∷ V))))
concretize-correct (prim p ⦅ L ,, M ,, Nil ⦆) φ ρ₂ ρ₃ c rel =
  primD-≃ p (concretize-correct L φ ρ₂ ρ₃ c rel) (concretize-correct M φ ρ₂ ρ₃ c rel)
concretize-correct (let-op ⦅ M ,, ⟩ N ,, Nil ⦆) φ ρ₂ ρ₃ c rel =
  ⋆-≃ (Λ-≃ {λ X → ⟦ N ⟧ (X • ρ₂)} {λ X → ⟦ concretize (ext-ref φ) N ⟧' (X • ρ₃)} (λ V _ cV → concretize-correct N (ext-ref φ) _ _ (Con-• (≈⇒Con cV) c) (rel-ext rel (mem V))))
      (concretize-correct M φ ρ₂ ρ₃ c rel)

body-correct n zero (bind (ast N)) ρ₂ ρ₃ rel = concretize-correct N (fv-ref n) ρ₂ ρ₃ rel
body-correct n (suc k) (bind a) = body-correct n k a

args-correct {zero} Nil φ ρ₂ ρ₃ c rel = ptt
args-correct {suc n} (M ,, args) φ ρ₂ ρ₃ c rel = ⟨ lift (concretize-correct M φ ρ₂ ρ₃ c rel) , args-correct args φ ρ₂ ρ₃ c rel ⟩

{- The end theorem ------------------------------------------------------------}

concretize-correct-closed : ∀ (M : AST) → ⟦ M ⟧ ρ₀ ≃ ⟦ concretize-program M ⟧' ρ₀
concretize-correct-closed M = concretize-correct M var ρ₀ ρ₀ (λ _ → Con-⌈⌉ ω) (λ x → ≃-refl)

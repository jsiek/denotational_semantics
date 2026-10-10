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
  semantics (Sem.Clos3IswimContinuous), to pick a finite part of the
  tuple of free variables.

-}

open import NewSigUtil
open import NewSyntaxUtil
open import SetsAsPredicates
open import NewDOpSig
open import Primitives
open import Compiler.Model.Graph.Domain.ISWIM.Domain
open import Compiler.Model.Graph.Domain.ISWIM.Ops
open import Compiler.Lang.Clos2 as L2
open import Compiler.Lang.Clos3 as L3
  renaming (AST to AST'; Arg to Arg'; Args to Args'; `_ to #_;
            _⦅_⦆ to _⦅_⦆'; ast to ast'; bind to bind'; clear to clear')
open import Compiler.Model.Graph.Sem.Clos2Iswim as S2
open import Compiler.Model.Graph.Sem.Clos3Iswim as S3 renaming
  (⟦_⟧ to ⟦_⟧'; ⟦_⟧ₐ to ⟦_⟧ₐ'; ⟦_⟧₊ to ⟦_⟧₊')
import Compiler.Model.Graph.Sem.Clos3IswimContinuous as C3
import Compiler.Model.Graph.Sem.Clos4Iswim as S4
open import Compiler.Compile.Concretize
open import Compiler.Compile.Delay using (delay)
open import Compiler.Model.Graph.Correctness.DelayFiniteCommon using (Env; Init; ρ₀; single⊆; ne-mem)
open import Compiler.Model.Graph.Correctness.DelayPreserveFinite
  using (delay-correct-const; delay-correct-nonempty)
open import NewEnv using (nonempty-env)

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _<_; _<?_)
open import Data.Nat.Properties using (+-suc; +-identityʳ; ≤-antisym; ≤-pred; ≮⇒≥; m+[n∸m]≡n)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_; replicate)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax)
  renaming (_,_ to ⟨_,_⟩ )
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong)
open import Relation.Nullary using (¬_; yes; no)

module Compiler.Model.Graph.Correctness.ConcretizeCorrect where

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
  → (∀ i → nthD Ds₂ i ≃ nthD Ds₃ i)
  → (∀ ρ₂ ρ₃ → EnvRel (fv-ref n) ρ₂ ρ₃ → ⟦ unbind-n n a ⟧ ρ₂ ≃ ⟦ N' ⟧' ρ₃)
  → guard-n n Ds₂ (Λ ⟨ apply-n n (⟦ a ⟧ₐ init₀) Ds₂ , ptt ⟩)
    ≃ ⋆ ⟨ Λ ⟨ (λ X → Λ ⟨ (λ Y → ⟦ N' ⟧' (Y • X • init₀)) , ptt ⟩) , ptt ⟩
        , ⟨ 𝒯 n Ds₃ , ptt ⟩ ⟩
clos-correct n a Ds₂ Ds₃ N' Ds≃ body = ⟨ G , H ⟩
  where
  T = 𝒯 n Ds₃

  NE₃ : ∀ U → U ≢ [] → nonempty T → nonempty-env (mem U • T • init₀)
  NE₃ U neU neT zero = E≢[]⇒nonempty-mem neU
  NE₃ U neU neT (suc zero) = neT
  NE₃ U neU neT (suc (suc y)) = ⟨ ω , refl ⟩

  {- applying the closure to U runs the body on the same free variables -}
  body≃ : ∀ U → (∀ i → nonempty (nthD Ds₂ i))
    → apply-n n (⟦ a ⟧ₐ init₀) Ds₂ (mem U) ≃ ⟦ N' ⟧' (mem U • T • init₀)
  body≃ U ne₂ rewrite apply-push n a init₀ Ds₂ (mem U) =
    body (mem U • push Ds₂ init₀) (mem U • T • init₀)
      (fv-env-rel n Ds₂ Ds₃ (mem U) Ds≃ (ne-≃ (λ i → proj₁ (Ds≃ i)) ne₂))

  G : guard-n n Ds₂ (Λ ⟨ apply-n n (⟦ a ⟧ₐ init₀) Ds₂ , ptt ⟩)
      ⊆ ⋆ ⟨ Λ ⟨ (λ X → Λ ⟨ (λ Y → ⟦ N' ⟧' (Y • X • init₀)) , ptt ⟩) , ptt ⟩ , ⟨ T , ptt ⟩ ⟩
  G ν ⟨ ne₂ , tt ⟩ =
    ⟨ proj₁ neT ∷ [] , ⟨ ⟨ tt , (λ ()) ⟩ , ⟨ single⊆ (proj₂ neT) , (λ ()) ⟩ ⟩ ⟩
    where neT = T-ne n Ds₃ (ne-≃ (λ i → proj₁ (Ds≃ i)) ne₂)
  G (U ↦ x) ⟨ ne₂ , ⟨ x∈ , neU ⟩ ⟩
      with C3.term-continuous N' (mem U • T • init₀)
             (NE₃ U neU (T-ne n Ds₃ (ne-≃ (λ i → proj₁ (Ds≃ i)) ne₂)))
             x (proj₁ (body≃ U ne₂) x x∈)
  ... | ⟨ Vs , ⟨ ok , x∈fin ⟩ ⟩ =
    ⟨ Vs 1 , ⟨ ⟨ ⟨ x∈′ , neU ⟩ , proj₁ (ok 1) ⟩ , ⟨ proj₂ (ok 1) , proj₁ (ok 1) ⟩ ⟩ ⟩
    where
    env⊆ : ∀ y → mem (Vs y) ⊆ (mem U • mem (Vs 1) • init₀) y
    env⊆ zero = proj₂ (ok 0)
    env⊆ (suc zero) = λ d d∈ → d∈
    env⊆ (suc (suc y)) = proj₂ (ok (suc (suc y)))
    x∈′ = S3.⟦⟧-monotone {ρ = λ y → mem (Vs y)} {ρ′ = mem U • mem (Vs 1) • init₀}
                         N' env⊆ x x∈fin

  H : ⋆ ⟨ Λ ⟨ (λ X → Λ ⟨ (λ Y → ⟦ N' ⟧' (Y • X • init₀)) , ptt ⟩) , ptt ⟩ , ⟨ T , ptt ⟩ ⟩
      ⊆ guard-n n Ds₂ (Λ ⟨ apply-n n (⟦ a ⟧ₐ init₀) Ds₂ , ptt ⟩)
  H ν ⟨ V , ⟨ _ , ⟨ V⊆T , neV ⟩ ⟩ ⟩ =
    ⟨ ne-≃ (λ i → proj₂ (Ds≃ i)) (T-ne⁻ n Ds₃ (ne-mem neV V⊆T)) , tt ⟩
  H (U ↦ x) ⟨ V , ⟨ ⟨ ⟨ x∈ , neU ⟩ , _ ⟩ , ⟨ V⊆T , neV ⟩ ⟩ ⟩ =
    ⟨ ne₂ , ⟨ proj₂ (body≃ U ne₂) x
                (S3.⟦⟧-monotone {ρ = mem U • mem V • init₀} {ρ′ = mem U • T • init₀}
                                N' env⊆ x x∈)
            , neU ⟩ ⟩
    where
    ne₂ = ne-≃ (λ i → proj₂ (Ds≃ i)) (T-ne⁻ n Ds₃ (ne-mem neV V⊆T))
    env⊆ : ∀ y → (mem U • mem V • init₀) y ⊆ (mem U • T • init₀) y
    env⊆ zero = λ d d∈ → d∈
    env⊆ (suc zero) = V⊆T
    env⊆ (suc (suc y)) = λ d d∈ → d∈

{- Congruences ---------------------------------------------------------------}

⋆-≃ : ∀ {D D' E E'} → D ≃ D' → E ≃ E' → ⋆ ⟨ D , ⟨ E , ptt ⟩ ⟩ ≃ ⋆ ⟨ D' , ⟨ E' , ptt ⟩ ⟩
⋆-≃ ⟨ D⊆ , D⊇ ⟩ ⟨ E⊆ , E⊇ ⟩ =
  ⟨ (λ w → λ { ⟨ V , ⟨ e∈ , ⟨ V⊆ , ne ⟩ ⟩ ⟩ →
               ⟨ V , ⟨ D⊆ _ e∈ , ⟨ (λ d d∈ → E⊆ d (V⊆ d d∈)) , ne ⟩ ⟩ ⟩ })
  , (λ w → λ { ⟨ V , ⟨ e∈ , ⟨ V⊆ , ne ⟩ ⟩ ⟩ →
               ⟨ V , ⟨ D⊇ _ e∈ , ⟨ (λ d d∈ → E⊇ d (V⊆ d d∈)) , ne ⟩ ⟩ ⟩ }) ⟩

𝒯-≃ : ∀ n {Ds Es : Results (𝒫 Value) (replicate n ■)}
  → (∀ i → nthD Ds i ≃ nthD Es i) → 𝒯 n Ds ≃ 𝒯 n Es
𝒯-≃ zero {Ds} {Es} _ = ⟨ G , H ⟩
  where
  G : 𝒯 zero Ds ⊆ 𝒯 zero Es
  G ⟨⟩ tt = tt
  H : 𝒯 zero Es ⊆ 𝒯 zero Ds
  H ⟨⟩ tt = tt
𝒯-≃ (suc n) {Ds} {Es} eq = ⟨ G , H ⟩
  where
  G : 𝒯 (suc n) Ds ⊆ 𝒯 (suc n) Es
  G (tup[ i ] d) ⟨ refl , ⟨ d∈ , ne ⟩ ⟩ =
    ⟨ refl , ⟨ proj₁ (eq i) d d∈ , ne-≃ (λ j → proj₁ (eq j)) ne ⟩ ⟩
  H : 𝒯 (suc n) Es ⊆ 𝒯 (suc n) Ds
  H (tup[ i ] d) ⟨ refl , ⟨ d∈ , ne ⟩ ⟩ =
    ⟨ refl , ⟨ proj₂ (eq i) d d∈ , ne-≃ (λ j → proj₂ (eq j)) ne ⟩ ⟩

proj-≃ : ∀ {n} (i : Fin n) {D E} → D ≃ E → proj i ⟨ D , ptt ⟩ ≃ proj i ⟨ E , ptt ⟩
proj-≃ i ⟨ D⊆ , D⊇ ⟩ = ⟨ (λ d → D⊆ (tup[ i ] d)) , (λ d → D⊇ (tup[ i ] d)) ⟩

ℒ-≃ : ∀ {D E} → D ≃ E → ℒ ⟨ D , ptt ⟩ ≃ ℒ ⟨ E , ptt ⟩
ℒ-≃ {D} {E} ⟨ D⊆ , D⊇ ⟩ = ⟨ G , H ⟩
  where
  G : ℒ ⟨ D , ptt ⟩ ⊆ ℒ ⟨ E , ptt ⟩
  G (left d) d∈ = D⊆ d d∈
  H : ℒ ⟨ E , ptt ⟩ ⊆ ℒ ⟨ D , ptt ⟩
  H (left d) d∈ = D⊇ d d∈

ℛ-≃ : ∀ {D E} → D ≃ E → ℛ ⟨ D , ptt ⟩ ≃ ℛ ⟨ E , ptt ⟩
ℛ-≃ {D} {E} ⟨ D⊆ , D⊇ ⟩ = ⟨ G , H ⟩
  where
  G : ℛ ⟨ D , ptt ⟩ ⊆ ℛ ⟨ E , ptt ⟩
  G (right d) d∈ = D⊆ d d∈
  H : ℛ ⟨ E , ptt ⟩ ⊆ ℛ ⟨ D , ptt ⟩
  H (right d) d∈ = D⊇ d d∈

{- The main lemma -------------------------------------------------------------}

concretize-correct : ∀ (M : AST) φ ρ₂ ρ₃ → EnvRel φ ρ₂ ρ₃
  → ⟦ M ⟧ ρ₂ ≃ ⟦ concretize φ M ⟧' ρ₃

body-correct : ∀ n k (a : Arg (ν-n k (ν ■)))
  → ∀ ρ₂ ρ₃ → EnvRel (fv-ref n) ρ₂ ρ₃
  → ⟦ unbind-n k a ⟧ ρ₂ ≃ ⟦ conc-body n k a ⟧' ρ₃

args-correct : ∀ {n} (args : Args (replicate n ■)) φ ρ₂ ρ₃ → EnvRel φ ρ₂ ρ₃
  → ∀ i → nthD (⟦ args ⟧₊ ρ₂) i ≃ nthD (⟦ conc-args φ args ⟧₊' ρ₃) i

concretize-correct (` x) φ ρ₂ ρ₃ rel =
  ≃-trans (rel x) (≃-reflexive (sym (ref-ok (φ x) ρ₃)))
concretize-correct (clos-op n ⦅ ! clear a ,, fvs ⦆) φ ρ₂ ρ₃ rel =
  clos-correct n a (⟦ fvs ⟧₊ ρ₂) (⟦ conc-args φ fvs ⟧₊' ρ₃) (conc-body n n a)
    (args-correct fvs φ ρ₂ ρ₃ rel) (body-correct n n a)
concretize-correct (app ⦅ L ,, M ,, Nil ⦆) φ ρ₂ ρ₃ rel =
  ⋆-≃ (concretize-correct L φ ρ₂ ρ₃ rel) (concretize-correct M φ ρ₂ ρ₃ rel)
concretize-correct (lit B k ⦅ Nil ⦆) φ ρ₂ ρ₃ rel = ≃-refl
concretize-correct (tuple n ⦅ args ⦆) φ ρ₂ ρ₃ rel =
  𝒯-≃ n (args-correct args φ ρ₂ ρ₃ rel)
concretize-correct (get i ⦅ M ,, Nil ⦆) φ ρ₂ ρ₃ rel =
  proj-≃ i (concretize-correct M φ ρ₂ ρ₃ rel)
concretize-correct (inl-op ⦅ M ,, Nil ⦆) φ ρ₂ ρ₃ rel =
  ℒ-≃ (concretize-correct M φ ρ₂ ρ₃ rel)
concretize-correct (inr-op ⦅ M ,, Nil ⦆) φ ρ₂ ρ₃ rel =
  ℛ-≃ (concretize-correct M φ ρ₂ ρ₃ rel)
concretize-correct (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) φ ρ₂ ρ₃ rel = ⟨ G , H ⟩
  where
  L≃ = concretize-correct L φ ρ₂ ρ₃ rel

  rel-ext : ∀ X → EnvRel (ext-ref φ) (X • ρ₂) (X • ρ₃)
  rel-ext X zero = ≃-refl
  rel-ext X (suc x) = ≃-trans (rel x) (≃-reflexive (sym (shift-ok (φ x) X ρ₃)))

  M≃ : ∀ X → ⟦ M ⟧ (X • ρ₂) ≃ ⟦ concretize (ext-ref φ) M ⟧' (X • ρ₃)
  M≃ X = concretize-correct M (ext-ref φ) (X • ρ₂) (X • ρ₃) (rel-ext X)

  N≃ : ∀ X → ⟦ N ⟧ (X • ρ₂) ≃ ⟦ concretize (ext-ref φ) N ⟧' (X • ρ₃)
  N≃ X = concretize-correct N (ext-ref φ) (X • ρ₂) (X • ρ₃) (rel-ext X)

  G : ⟦ case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆ ⟧ ρ₂
      ⊆ ⟦ concretize φ (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) ⟧' ρ₃
  G w (inj₁ ⟨ v , ⟨ V , ⟨ allL , w∈ ⟩ ⟩ ⟩) =
    inj₁ ⟨ v , ⟨ V , ⟨ (λ d d∈ → proj₁ L≃ (left d) (allL d d∈))
                     , proj₁ (M≃ (mem (v ∷ V))) w w∈ ⟩ ⟩ ⟩
  G w (inj₂ ⟨ v , ⟨ V , ⟨ allR , w∈ ⟩ ⟩ ⟩) =
    inj₂ ⟨ v , ⟨ V , ⟨ (λ d d∈ → proj₁ L≃ (right d) (allR d d∈))
                     , proj₁ (N≃ (mem (v ∷ V))) w w∈ ⟩ ⟩ ⟩

  H : ⟦ concretize φ (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) ⟧' ρ₃
      ⊆ ⟦ case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆ ⟧ ρ₂
  H w (inj₁ ⟨ v , ⟨ V , ⟨ allL , w∈ ⟩ ⟩ ⟩) =
    inj₁ ⟨ v , ⟨ V , ⟨ (λ d d∈ → proj₂ L≃ (left d) (allL d d∈))
                     , proj₂ (M≃ (mem (v ∷ V))) w w∈ ⟩ ⟩ ⟩
  H w (inj₂ ⟨ v , ⟨ V , ⟨ allR , w∈ ⟩ ⟩ ⟩) =
    inj₂ ⟨ v , ⟨ V , ⟨ (λ d d∈ → proj₂ L≃ (right d) (allR d d∈))
                     , proj₂ (N≃ (mem (v ∷ V))) w w∈ ⟩ ⟩ ⟩

body-correct n zero (bind (ast N)) ρ₂ ρ₃ rel = concretize-correct N (fv-ref n) ρ₂ ρ₃ rel
body-correct n (suc k) (bind a) = body-correct n k a

args-correct {suc n} (M ,, args) φ ρ₂ ρ₃ rel zero = concretize-correct M φ ρ₂ ρ₃ rel
args-correct {suc n} (M ,, args) φ ρ₂ ρ₃ rel (suc i) = args-correct args φ ρ₂ ρ₃ rel i

{- The end theorems -----------------------------------------------------------}

concretize-correct-closed : ∀ (M : AST) → ⟦ M ⟧ ρ₀ ≃ ⟦ concretize-program M ⟧' ρ₀
concretize-correct-closed M = concretize-correct M var ρ₀ ρ₀ (λ x → ≃-refl)

{- Composed with the delay pass: for a closed program, Clos2 → Clos3 → Clos4
   preserves and reflects the constants it produces and whether it produces
   anything at all. -}
compile-correct-const : ∀ (M : AST) → ∀ {B} (c : base-rep B)
  → (const c ∈ ⟦ M ⟧ ρ₀ → const c ∈ S4.⟦ delay (concretize-program M) ⟧ ρ₀)
  × (const c ∈ S4.⟦ delay (concretize-program M) ⟧ ρ₀ → const c ∈ ⟦ M ⟧ ρ₀)
compile-correct-const M c =
  ⟨ (λ c∈ → proj₁ (delay-correct-const M' c) (proj₁ M≃ _ c∈))
  , (λ c∈ → proj₂ M≃ _ (proj₂ (delay-correct-const M' c) c∈)) ⟩
  where
  M' = concretize-program M
  M≃ = concretize-correct-closed M

compile-correct-nonempty : ∀ (M : AST)
  → (nonempty (⟦ M ⟧ ρ₀) → nonempty (S4.⟦ delay (concretize-program M) ⟧ ρ₀))
  × (nonempty (S4.⟦ delay (concretize-program M) ⟧ ρ₀) → nonempty (⟦ M ⟧ ρ₀))
compile-correct-nonempty M =
  ⟨ (λ ne → proj₁ (delay-correct-nonempty M')
                ⟨ proj₁ ne , proj₁ M≃ _ (proj₂ ne) ⟩)
  , (λ ne → let ne' = proj₂ (delay-correct-nonempty M') ne in
            ⟨ proj₁ ne' , proj₂ M≃ _ (proj₂ ne') ⟩) ⟩
  where
  M' = concretize-program M
  M≃ = concretize-correct-closed M

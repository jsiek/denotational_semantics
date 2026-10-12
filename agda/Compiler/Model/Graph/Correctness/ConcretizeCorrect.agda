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
open import Compiler.Compile.Concretize
open import Compiler.Model.Graph.Correctness.DelayFiniteCommon using (Env; Init; ρ₀; single⊆; ne-mem)
open import NewEnv using (nonempty-env)

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
  → (∀ i → nthD Ds₂ i ≃ nthD Ds₃ i) → Con (𝒯 n Ds₃)
  → (∀ ρ₂ ρ₃ → Con-env ρ₃ → EnvRel (fv-ref n) ρ₂ ρ₃ → ⟦ unbind-n n a ⟧ ρ₂ ≃ ⟦ N' ⟧' ρ₃)
  → guard-n n Ds₂ (Λ ⟨ apply-n n (⟦ a ⟧ₐ init₀) Ds₂ , ptt ⟩)
    ≃ ⋆ ⟨ Λ ⟨ (λ X → Λ ⟨ (λ Y → ⟦ N' ⟧' (Y • X • init₀)) , ptt ⟩) , ptt ⟩
        , ⟨ 𝒯 n Ds₃ , ptt ⟩ ⟩
clos-correct n a Ds₂ Ds₃ N' Ds≃ cT body = ⟨ G , H ⟩
  where
  T = 𝒯 n Ds₃

  NE₃ : ∀ U → U ≢ [] → nonempty T → nonempty-env (mem U • T • init₀)
  NE₃ U neU neT zero = E≢[]⇒nonempty-mem neU
  NE₃ U neU neT (suc zero) = neT
  NE₃ U neU neT (suc (suc y)) = ⟨ ω , refl ⟩

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
      with C3.term-continuous N' (mem U • T • init₀)
             (NE₃ U neU (T-ne n Ds₃ (ne-≃ (λ i → proj₁ (Ds≃ i)) ne₂)))
             x (proj₁ (body≃ U cU ne₂) x x∈)
  ... | ⟨ Vs , ⟨ ok , x∈fin ⟩ ⟩ =
    ⟨ Vs 1 , ⟨ ⟨ ⟨ x∈′ , ⟨ neU , cU ⟩ ⟩ , ⟨ proj₁ (ok 1) , Con⇒≈ (Vs 1) cT (proj₂ (ok 1)) ⟩ ⟩
             , ⟨ proj₂ (ok 1) , proj₁ (ok 1) ⟩ ⟩ ⟩
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
    ⟨ ne₂ , ⟨ proj₂ (body≃ U (proj₂ neU) ne₂) x
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

primD-≃ : ∀ p {D D' E E'} → D ≃ D' → E ≃ E'
  → primD p ⟨ D , ⟨ E , ptt ⟩ ⟩ ≃ primD p ⟨ D' , ⟨ E' , ptt ⟩ ⟩
primD-≃ p ⟨ D⊆ , D⊇ ⟩ ⟨ E⊆ , E⊇ ⟩ =
  ⟨ lower (primD-mono p _ _ ⟨ lift D⊆ , ⟨ lift E⊆ , ptt ⟩ ⟩)
  , lower (primD-mono p _ _ ⟨ lift D⊇ , ⟨ lift E⊇ , ptt ⟩ ⟩) ⟩

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

inl-≃ : ∀ {D E} → D ≃ E → inl ⟨ D , ptt ⟩ ≃ inl ⟨ E , ptt ⟩
inl-≃ {D} {E} ⟨ D⊆ , D⊇ ⟩ = ⟨ G , H ⟩
  where
  G : inl ⟨ D , ptt ⟩ ⊆ inl ⟨ E , ptt ⟩
  G (left d) d∈ = D⊆ d d∈
  H : inl ⟨ E , ptt ⟩ ⊆ inl ⟨ D , ptt ⟩
  H (left d) d∈ = D⊇ d d∈

inr-≃ : ∀ {D E} → D ≃ E → inr ⟨ D , ptt ⟩ ≃ inr ⟨ E , ptt ⟩
inr-≃ {D} {E} ⟨ D⊆ , D⊇ ⟩ = ⟨ G , H ⟩
  where
  G : inr ⟨ D , ptt ⟩ ⊆ inr ⟨ E , ptt ⟩
  G (right d) d∈ = D⊆ d d∈
  H : inr ⟨ E , ptt ⟩ ⊆ inr ⟨ D , ptt ⟩
  H (right d) d∈ = D⊇ d d∈

{- case analysis, whose branches are compared on nonempty finite sets -}
𝒞-≃ : ∀ {D D' F F' G G'} → D ≃ D'
  → (∀ v V → (v ∷ V) ≈ (v ∷ V) → F (mem (v ∷ V)) ≃ F' (mem (v ∷ V)))
  → (∀ v V → (v ∷ V) ≈ (v ∷ V) → G (mem (v ∷ V)) ≃ G' (mem (v ∷ V)))
  → 𝒞 ⟨ D , ⟨ F , ⟨ G , ptt ⟩ ⟩ ⟩ ≃ 𝒞 ⟨ D' , ⟨ F' , ⟨ G' , ptt ⟩ ⟩ ⟩
𝒞-≃ {F = F} {F'} {G} {G'} D≃ F≃ G≃ =
  ⟨ H {B = F} {F'} {G} {G'} (proj₁ D≃) (λ v V c → proj₁ (F≃ v V c)) (λ v V c → proj₁ (G≃ v V c))
  , H {B = F'} {F} {G'} {G} (proj₂ D≃) (λ v V c → proj₂ (F≃ v V c)) (λ v V c → proj₂ (G≃ v V c)) ⟩
  where
  H : ∀ {A A' B B' C C'} → A ⊆ A' → (∀ v V → (v ∷ V) ≈ (v ∷ V) → B (mem (v ∷ V)) ⊆ B' (mem (v ∷ V)))
    → (∀ v V → (v ∷ V) ≈ (v ∷ V) → C (mem (v ∷ V)) ⊆ C' (mem (v ∷ V)))
    → 𝒞 ⟨ A , ⟨ B , ⟨ C , ptt ⟩ ⟩ ⟩ ⊆ 𝒞 ⟨ A' , ⟨ B' , ⟨ C' , ptt ⟩ ⟩ ⟩
  H A⊆ B⊆ C⊆ w (inj₁ ⟨ v , ⟨ V , ⟨ all , ⟨ w∈ , c ⟩ ⟩ ⟩ ⟩) =
    inj₁ ⟨ v , ⟨ V , ⟨ (λ d d∈ → A⊆ (left d) (all d d∈)) , ⟨ B⊆ v V c w w∈ , c ⟩ ⟩ ⟩ ⟩
  H A⊆ B⊆ C⊆ w (inj₂ ⟨ v , ⟨ V , ⟨ all , ⟨ w∈ , c ⟩ ⟩ ⟩ ⟩) =
    inj₂ ⟨ v , ⟨ V , ⟨ (λ d d∈ → A⊆ (right d) (all d d∈)) , ⟨ C⊆ v V c w w∈ , c ⟩ ⟩ ⟩ ⟩

{- The main lemma -------------------------------------------------------------}

concretize-correct : ∀ (M : AST) φ ρ₂ ρ₃ → Con-env ρ₃ → EnvRel φ ρ₂ ρ₃
  → ⟦ M ⟧ ρ₂ ≃ ⟦ concretize φ M ⟧' ρ₃

body-correct : ∀ n k (a : Arg (ν-n k (ν ■)))
  → ∀ ρ₂ ρ₃ → Con-env ρ₃ → EnvRel (fv-ref n) ρ₂ ρ₃
  → ⟦ unbind-n k a ⟧ ρ₂ ≃ ⟦ conc-body n k a ⟧' ρ₃

args-correct : ∀ {n} (args : Args (replicate n ■)) φ ρ₂ ρ₃ → Con-env ρ₃ → EnvRel φ ρ₂ ρ₃
  → ∀ i → nthD (⟦ args ⟧₊ ρ₂) i ≃ nthD (⟦ conc-args φ args ⟧₊' ρ₃) i

concretize-correct (` x) φ ρ₂ ρ₃ c rel =
  ≃-trans (rel x) (≃-reflexive (sym (ref-ok (φ x) ρ₃)))
concretize-correct (clos-op n ⦅ ! clear a ,, fvs ⦆) φ ρ₂ ρ₃ c rel =
  clos-correct n a (⟦ fvs ⟧₊ ρ₂) (⟦ conc-args φ fvs ⟧₊' ρ₃) (conc-body n n a)
    (args-correct fvs φ ρ₂ ρ₃ c rel) (Clos3-con (tuple n ⦅ conc-args φ fvs ⦆') c)
    (body-correct n n a)
concretize-correct (app ⦅ L ,, M ,, Nil ⦆) φ ρ₂ ρ₃ c rel =
  ⋆-≃ (concretize-correct L φ ρ₂ ρ₃ c rel) (concretize-correct M φ ρ₂ ρ₃ c rel)
concretize-correct (lit B k ⦅ Nil ⦆) φ ρ₂ ρ₃ c rel = ≃-refl
concretize-correct (tuple n ⦅ args ⦆) φ ρ₂ ρ₃ c rel =
  𝒯-≃ n (args-correct args φ ρ₂ ρ₃ c rel)
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
      (λ v V cV → concretize-correct M (ext-ref φ) _ _ (Con-• (≈⇒Con cV) c) (rel-ext (mem (v ∷ V))))
      (λ v V cV → concretize-correct N (ext-ref φ) _ _ (Con-• (≈⇒Con cV) c) (rel-ext (mem (v ∷ V))))
  where
  rel-ext : ∀ X → EnvRel (ext-ref φ) (X • ρ₂) (X • ρ₃)
  rel-ext X zero = ≃-refl
  rel-ext X (suc x) = ≃-trans (rel x) (≃-reflexive (sym (shift-ok (φ x) X ρ₃)))
concretize-correct (prim p ⦅ L ,, M ,, Nil ⦆) φ ρ₂ ρ₃ c rel =
  primD-≃ p (concretize-correct L φ ρ₂ ρ₃ c rel) (concretize-correct M φ ρ₂ ρ₃ c rel)

body-correct n zero (bind (ast N)) ρ₂ ρ₃ rel = concretize-correct N (fv-ref n) ρ₂ ρ₃ rel
body-correct n (suc k) (bind a) = body-correct n k a

args-correct {suc n} (M ,, args) φ ρ₂ ρ₃ c rel zero = concretize-correct M φ ρ₂ ρ₃ c rel
args-correct {suc n} (M ,, args) φ ρ₂ ρ₃ c rel (suc i) = args-correct args φ ρ₂ ρ₃ c rel i

{- The end theorem ------------------------------------------------------------}

concretize-correct-closed : ∀ (M : AST) → ⟦ M ⟧ ρ₀ ≃ ⟦ concretize-program M ⟧' ρ₀
concretize-correct-closed M = concretize-correct M var ρ₀ ρ₀ (λ _ → Con-⌈⌉ ω) (λ x → ≃-refl)

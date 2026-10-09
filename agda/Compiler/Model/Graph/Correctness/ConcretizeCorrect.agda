{-

  Correctness of the concretize pass (Clos2 → Clos3).

  Clos2 and Clos3 use the same values, and concretize only changes how
  the code of a closure reaches its free variables: one at a time in
  Clos2, as components of a tuple in Clos3. So the pass preserves
  denotations exactly: ⟦ M ⟧ ρ₂ ≃ ⟦ concretize φ M ⟧' ρ₃, which gives both
  the forward and the backward direction at once.

  The side condition (Good) is that the free-variable expressions of each
  closure are variables, as the earlier passes produce them. In a
  nonempty environment these denote nonempty sets. That matters because
  tuples are not strict in their components: a Clos3 closure needs at
  least one value in its tuple of free variables, while a Clos2 closure
  does not.

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
open import Compiler.Model.Graph.Correctness.DelayFiniteCommon using (Env; Init; ρ₀; single⊆)
open import Compiler.Model.Graph.Correctness.DelayPreserveFinite
  using (delay-correct-const; delay-correct-nonempty)
open import NewEnv using (nonempty-env; extend-nonempty-env)

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

{- Programs whose closures capture variables -------------------------------}

data FVars : ∀ {n} → Args (replicate n ■) → Set where
  fv-nil : FVars {zero} Nil
  fv-cons : ∀ {n x} {fvs : Args (replicate n ■)} → FVars fvs → FVars {suc n} ((` x) ,, fvs)

data Good : AST → Set
data GoodArgs : ∀ {n} → Args (replicate n ■) → Set

data Good where
  good-var : ∀ {x} → Good (` x)
  good-clos : ∀ {n} {a : Arg (ν-n n (ν ■))} {fvs : Args (replicate n ■)}
    → Good (unbind-n n a) → FVars fvs → Good (clos-op n ⦅ ! clear a ,, fvs ⦆)
  good-app : ∀ {L M} → Good L → Good M → Good (app ⦅ L ,, M ,, Nil ⦆)
  good-lit : ∀ {B k} → Good (lit B k ⦅ Nil ⦆)
  good-tuple : ∀ {n} {args : Args (replicate n ■)} → GoodArgs args → Good (tuple n ⦅ args ⦆)
  good-get : ∀ {n} {i : Fin n} {M} → Good M → Good (get i ⦅ M ,, Nil ⦆)
  good-inl : ∀ {M} → Good M → Good (inl-op ⦅ M ,, Nil ⦆)
  good-inr : ∀ {M} → Good M → Good (inr-op ⦅ M ,, Nil ⦆)
  good-case : ∀ {L M N} → Good L → Good M → Good N
    → Good (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆)

data GoodArgs where
  good-nil : GoodArgs {zero} Nil
  good-cons : ∀ {n M} {args : Args (replicate n ■)} → Good M → GoodArgs args
    → GoodArgs {suc n} (M ,, args)

fvars-good : ∀ {n} {fvs : Args (replicate n ■)} → FVars fvs → GoodArgs fvs
fvars-good fv-nil = good-nil
fvars-good (fv-cons fvs) = good-cons good-var (fvars-good fvs)

fvars-ne : ∀ {n} {fvs : Args (replicate n ■)} → FVars fvs → ∀ ρ → nonempty-env ρ
  → ∀ i → nonempty (nthD (⟦ fvs ⟧₊ ρ) i)
fvars-ne (fv-cons {x = x} fvs) ρ NE zero = NE x
fvars-ne (fv-cons fvs) ρ NE (suc i) = fvars-ne fvs ρ NE i

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

push-ne : ∀ n (Ds : Results (𝒫 Value) (replicate n ■)) ρ
  → (∀ i → nonempty (nthD Ds i)) → nonempty-env ρ → nonempty-env (push Ds ρ)
push-ne zero _ ρ _ NE = NE
push-ne (suc n) ⟨ D , Ds ⟩ ρ ne NE =
  push-ne n Ds (D • ρ) (λ i → ne (suc i)) (extend-nonempty-env NE (ne zero))

proj-𝒯 : ∀ n (Ds : Results (𝒫 Value) (replicate n ■)) (i : Fin n)
  → proj i ⟨ 𝒯 n Ds , ptt ⟩ ≃ nthD Ds i
proj-𝒯 (suc n) Ds i = ⟨ G , (λ d d∈ → ⟨ refl , d∈ ⟩) ⟩
  where
  G : proj i ⟨ 𝒯 (suc n) Ds , ptt ⟩ ⊆ nthD Ds i
  G d ⟨ refl , d∈ ⟩ = d∈

{- the body of a Clos2 closure and the body of its Clos3 code see the
   same free variables -}
fv-env-rel : ∀ n (Ds₂ Ds₃ : Results (𝒫 Value) (replicate n ■)) (Y : 𝒫 Value)
  → (∀ i → nthD Ds₂ i ≃ nthD Ds₃ i)
  → EnvRel (fv-ref n) (Y • push Ds₂ init₀) (Y • 𝒯 n Ds₃ • init₀)
fv-env-rel n Ds₂ Ds₃ Y Ds≃ zero = ≃-refl
fv-env-rel n Ds₂ Ds₃ Y Ds≃ (suc k) with k <? n
... | yes k<n =
  ≃-trans (≃-reflexive (push-yes n Ds₂ init₀ k k<n))
          (≃-trans (Ds≃ (fv-index n k k<n)) (≃-sym (proj-𝒯 n Ds₃ (fv-index n k k<n))))
... | no ¬k<n = ≃-reflexive (push-no n Ds₂ init₀ k ¬k<n)

{- the tuple of free variables is never empty -}
T-ne : ∀ n (Ds₂ Ds₃ : Results (𝒫 Value) (replicate n ■))
  → (∀ i → nthD Ds₂ i ≃ nthD Ds₃ i) → (∀ i → nonempty (nthD Ds₂ i))
  → nonempty (𝒯 n Ds₃)
T-ne zero _ _ _ _ = ⟨ ⟨⟩ , tt ⟩
T-ne (suc n) Ds₂ Ds₃ Ds≃ ne =
  ⟨ tup[ zero ] (proj₁ (ne zero)) , ⟨ refl , proj₁ (Ds≃ zero) _ (proj₂ (ne zero)) ⟩ ⟩

{- Closures -------------------------------------------------------------------}

clos-correct : ∀ n (a : Arg (ν-n n (ν ■))) (Ds₂ Ds₃ : Results (𝒫 Value) (replicate n ■))
  (N' : AST')
  → (∀ i → nthD Ds₂ i ≃ nthD Ds₃ i) → (∀ i → nonempty (nthD Ds₂ i))
  → (∀ ρ₂ ρ₃ → nonempty-env ρ₂ → EnvRel (fv-ref n) ρ₂ ρ₃
      → ⟦ unbind-n n a ⟧ ρ₂ ≃ ⟦ N' ⟧' ρ₃)
  → Λ ⟨ apply-n n (⟦ a ⟧ₐ init₀) Ds₂ , ptt ⟩
    ≃ ⋆ ⟨ Λ ⟨ (λ X → Λ ⟨ (λ Y → ⟦ N' ⟧' (Y • X • init₀)) , ptt ⟩) , ptt ⟩
        , ⟨ 𝒯 n Ds₃ , ptt ⟩ ⟩
clos-correct n a Ds₂ Ds₃ N' Ds≃ ne body = ⟨ G , H ⟩
  where
  T = 𝒯 n Ds₃
  NE-T = T-ne n Ds₂ Ds₃ Ds≃ ne

  NE₃ : ∀ U → U ≢ [] → nonempty-env (mem U • T • init₀)
  NE₃ U neU zero = E≢[]⇒nonempty-mem neU
  NE₃ U neU (suc zero) = NE-T
  NE₃ U neU (suc (suc y)) = ⟨ ω , refl ⟩

  {- applying the closure to U runs the body on the same free variables -}
  body≃ : ∀ U → U ≢ [] → apply-n n (⟦ a ⟧ₐ init₀) Ds₂ (mem U) ≃ ⟦ N' ⟧' (mem U • T • init₀)
  body≃ U neU rewrite apply-push n a init₀ Ds₂ (mem U) =
    body (mem U • push Ds₂ init₀) (mem U • T • init₀)
      (extend-nonempty-env (push-ne n Ds₂ init₀ ne (λ _ → ⟨ ω , refl ⟩)) (E≢[]⇒nonempty-mem neU))
      (fv-env-rel n Ds₂ Ds₃ (mem U) Ds≃)

  G : Λ ⟨ apply-n n (⟦ a ⟧ₐ init₀) Ds₂ , ptt ⟩
      ⊆ ⋆ ⟨ Λ ⟨ (λ X → Λ ⟨ (λ Y → ⟦ N' ⟧' (Y • X • init₀)) , ptt ⟩) , ptt ⟩ , ⟨ T , ptt ⟩ ⟩
  G ν tt = ⟨ proj₁ NE-T ∷ [] , ⟨ ⟨ tt , (λ ()) ⟩ , ⟨ single⊆ (proj₂ NE-T) , (λ ()) ⟩ ⟩ ⟩
  G (U ↦ x) ⟨ x∈ , neU ⟩
      with C3.term-continuous N' (mem U • T • init₀) (NE₃ U neU) x (proj₁ (body≃ U neU) x x∈)
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
      ⊆ Λ ⟨ apply-n n (⟦ a ⟧ₐ init₀) Ds₂ , ptt ⟩
  H ν _ = tt
  H (U ↦ x) ⟨ V , ⟨ ⟨ ⟨ x∈ , neU ⟩ , _ ⟩ , ⟨ V⊆T , _ ⟩ ⟩ ⟩ =
    ⟨ proj₂ (body≃ U neU) x
        (S3.⟦⟧-monotone {ρ = mem U • mem V • init₀} {ρ′ = mem U • T • init₀} N' env⊆ x x∈)
    , neU ⟩
    where
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
  G (tup[ i ] d) ⟨ refl , d∈ ⟩ = ⟨ refl , proj₁ (eq i) d d∈ ⟩
  H : 𝒯 (suc n) Es ⊆ 𝒯 (suc n) Ds
  H (tup[ i ] d) ⟨ refl , d∈ ⟩ = ⟨ refl , proj₂ (eq i) d d∈ ⟩

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

concretize-correct : ∀ (M : AST) φ ρ₂ ρ₃ → nonempty-env ρ₂ → Good M → EnvRel φ ρ₂ ρ₃
  → ⟦ M ⟧ ρ₂ ≃ ⟦ concretize φ M ⟧' ρ₃

body-correct : ∀ n k (a : Arg (ν-n k (ν ■))) → Good (unbind-n k a)
  → ∀ ρ₂ ρ₃ → nonempty-env ρ₂ → EnvRel (fv-ref n) ρ₂ ρ₃
  → ⟦ unbind-n k a ⟧ ρ₂ ≃ ⟦ conc-body n k a ⟧' ρ₃

args-correct : ∀ {n} (args : Args (replicate n ■)) φ ρ₂ ρ₃ → nonempty-env ρ₂
  → GoodArgs args → EnvRel φ ρ₂ ρ₃
  → ∀ i → nthD (⟦ args ⟧₊ ρ₂) i ≃ nthD (⟦ conc-args φ args ⟧₊' ρ₃) i

concretize-correct (` x) φ ρ₂ ρ₃ NE g rel =
  ≃-trans (rel x) (≃-reflexive (sym (ref-ok (φ x) ρ₃)))
concretize-correct (clos-op n ⦅ ! clear a ,, fvs ⦆) φ ρ₂ ρ₃ NE (good-clos gN fv) rel =
  clos-correct n a (⟦ fvs ⟧₊ ρ₂) (⟦ conc-args φ fvs ⟧₊' ρ₃) (conc-body n n a)
    (args-correct fvs φ ρ₂ ρ₃ NE (fvars-good fv) rel) (fvars-ne fv ρ₂ NE)
    (body-correct n n a gN)
concretize-correct (app ⦅ L ,, M ,, Nil ⦆) φ ρ₂ ρ₃ NE (good-app gL gM) rel =
  ⋆-≃ (concretize-correct L φ ρ₂ ρ₃ NE gL rel) (concretize-correct M φ ρ₂ ρ₃ NE gM rel)
concretize-correct (lit B k ⦅ Nil ⦆) φ ρ₂ ρ₃ NE g rel = ≃-refl
concretize-correct (tuple n ⦅ args ⦆) φ ρ₂ ρ₃ NE (good-tuple gs) rel =
  𝒯-≃ n (args-correct args φ ρ₂ ρ₃ NE gs rel)
concretize-correct (get i ⦅ M ,, Nil ⦆) φ ρ₂ ρ₃ NE (good-get gM) rel =
  proj-≃ i (concretize-correct M φ ρ₂ ρ₃ NE gM rel)
concretize-correct (inl-op ⦅ M ,, Nil ⦆) φ ρ₂ ρ₃ NE (good-inl gM) rel =
  ℒ-≃ (concretize-correct M φ ρ₂ ρ₃ NE gM rel)
concretize-correct (inr-op ⦅ M ,, Nil ⦆) φ ρ₂ ρ₃ NE (good-inr gM) rel =
  ℛ-≃ (concretize-correct M φ ρ₂ ρ₃ NE gM rel)
concretize-correct (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) φ ρ₂ ρ₃ NE (good-case gL gM gN) rel =
  ⟨ G , H ⟩
  where
  L≃ = concretize-correct L φ ρ₂ ρ₃ NE gL rel

  rel-ext : ∀ X → EnvRel (ext-ref φ) (X • ρ₂) (X • ρ₃)
  rel-ext X zero = ≃-refl
  rel-ext X (suc x) = ≃-trans (rel x) (≃-reflexive (sym (shift-ok (φ x) X ρ₃)))

  M≃ : ∀ v V → ⟦ M ⟧ (mem (v ∷ V) • ρ₂) ≃ ⟦ concretize (ext-ref φ) M ⟧' (mem (v ∷ V) • ρ₃)
  M≃ v V = concretize-correct M (ext-ref φ) (mem (v ∷ V) • ρ₂) (mem (v ∷ V) • ρ₃)
             (extend-nonempty-env NE ⟨ v , here refl ⟩) gM (rel-ext (mem (v ∷ V)))

  N≃ : ∀ v V → ⟦ N ⟧ (mem (v ∷ V) • ρ₂) ≃ ⟦ concretize (ext-ref φ) N ⟧' (mem (v ∷ V) • ρ₃)
  N≃ v V = concretize-correct N (ext-ref φ) (mem (v ∷ V) • ρ₂) (mem (v ∷ V) • ρ₃)
             (extend-nonempty-env NE ⟨ v , here refl ⟩) gN (rel-ext (mem (v ∷ V)))

  G : ⟦ case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆ ⟧ ρ₂
      ⊆ ⟦ concretize φ (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) ⟧' ρ₃
  G w (inj₁ ⟨ v , ⟨ V , ⟨ allL , w∈ ⟩ ⟩ ⟩) =
    inj₁ ⟨ v , ⟨ V , ⟨ (λ d d∈ → proj₁ L≃ (left d) (allL d d∈)) , proj₁ (M≃ v V) w w∈ ⟩ ⟩ ⟩
  G w (inj₂ ⟨ v , ⟨ V , ⟨ allR , w∈ ⟩ ⟩ ⟩) =
    inj₂ ⟨ v , ⟨ V , ⟨ (λ d d∈ → proj₁ L≃ (right d) (allR d d∈)) , proj₁ (N≃ v V) w w∈ ⟩ ⟩ ⟩

  H : ⟦ concretize φ (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) ⟧' ρ₃
      ⊆ ⟦ case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆ ⟧ ρ₂
  H w (inj₁ ⟨ v , ⟨ V , ⟨ allL , w∈ ⟩ ⟩ ⟩) =
    inj₁ ⟨ v , ⟨ V , ⟨ (λ d d∈ → proj₂ L≃ (left d) (allL d d∈)) , proj₂ (M≃ v V) w w∈ ⟩ ⟩ ⟩
  H w (inj₂ ⟨ v , ⟨ V , ⟨ allR , w∈ ⟩ ⟩ ⟩) =
    inj₂ ⟨ v , ⟨ V , ⟨ (λ d d∈ → proj₂ L≃ (right d) (allR d d∈)) , proj₂ (N≃ v V) w w∈ ⟩ ⟩ ⟩

body-correct n zero (bind (ast N)) g ρ₂ ρ₃ NE rel = concretize-correct N (fv-ref n) ρ₂ ρ₃ NE g rel
body-correct n (suc k) (bind a) g = body-correct n k a g

args-correct {suc n} (M ,, args) φ ρ₂ ρ₃ NE (good-cons gM gs) rel zero =
  concretize-correct M φ ρ₂ ρ₃ NE gM rel
args-correct {suc n} (M ,, args) φ ρ₂ ρ₃ NE (good-cons gM gs) rel (suc i) =
  args-correct args φ ρ₂ ρ₃ NE gs rel i

{- The end theorems -----------------------------------------------------------}

concretize-correct-closed : ∀ (M : AST) → Good M → ⟦ M ⟧ ρ₀ ≃ ⟦ concretize-program M ⟧' ρ₀
concretize-correct-closed M g =
  concretize-correct M var ρ₀ ρ₀ (λ _ → ⟨ ω , refl ⟩) g (λ x → ≃-refl)

{- Composed with the delay pass: for a closed program, Clos2 → Clos3 → Clos4
   preserves and reflects the constants it produces and whether it produces
   anything at all. -}
compile-correct-const : ∀ (M : AST) → Good M → ∀ {B} (c : base-rep B)
  → (const c ∈ ⟦ M ⟧ ρ₀ → const c ∈ S4.⟦ delay (concretize-program M) ⟧ ρ₀)
  × (const c ∈ S4.⟦ delay (concretize-program M) ⟧ ρ₀ → const c ∈ ⟦ M ⟧ ρ₀)
compile-correct-const M g c =
  ⟨ (λ c∈ → proj₁ (delay-correct-const M' c) (proj₁ M≃ _ c∈))
  , (λ c∈ → proj₂ M≃ _ (proj₂ (delay-correct-const M' c) c∈)) ⟩
  where
  M' = concretize-program M
  M≃ = concretize-correct-closed M g

compile-correct-nonempty : ∀ (M : AST) → Good M
  → (nonempty (⟦ M ⟧ ρ₀) → nonempty (S4.⟦ delay (concretize-program M) ⟧ ρ₀))
  × (nonempty (S4.⟦ delay (concretize-program M) ⟧ ρ₀) → nonempty (⟦ M ⟧ ρ₀))
compile-correct-nonempty M g =
  ⟨ (λ ne → proj₁ (delay-correct-nonempty M')
                ⟨ proj₁ ne , proj₁ M≃ _ (proj₂ ne) ⟩)
  , (λ ne → let ne' = proj₂ (delay-correct-nonempty M') ne in
            ⟨ proj₁ ne' , proj₂ M≃ _ (proj₂ ne') ⟩) ⟩
  where
  M' = concretize-program M
  M≃ = concretize-correct-closed M g

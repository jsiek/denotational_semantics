{-# OPTIONS --safe #-}
{-

  Correctness of the optimize pass (Clos2 → Clos2).

  Optimize renames variables (by r) and drops free variables that a
  closure's code does not use. The denotation is unchanged:
  ⟦ M ⟧ ρ ≃ ⟦ optimize r M ⟧ ρ', when ρ and ρ' agree through r on the
  variables M uses, and ρ is nonempty. Since this is an equality, it
  gives both the forward and the backward direction.

  The environment must be nonempty because closures are strict: a dropped
  free variable is a variable, so it is nonempty, and dropping it does not
  change whether the closure has values.

-}

open import NewSigUtil
open import NewSyntaxUtil
open import SetsAsPredicates
open import NewDOpSig
open import Primitives
open import Compiler.Model.Graph.Domain.ISWIM.Domain
open import Compiler.Model.Graph.Domain.ISWIM.Ops
open import Compiler.Lang.Clos2
open import Compiler.Model.Graph.Sem.Clos2Iswim
open import Compiler.Compile.Concretize using (unbind-n)
open import Compiler.Compile.Optimize
open import Compiler.Model.Graph.Correctness.DelayFiniteCommon using (Env; Init; ρ₀)
open import Compiler.Model.Graph.Correctness.ConcretizeCorrect
  using (init₀; push; apply-push; ⋆-≃; 𝒯-≃; proj-≃; ℒ-≃; ℛ-≃)
open import NewEnv using (nonempty-env; extend-nonempty-env)

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-suc; +-identityʳ)
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
  using (_≡_; _≢_; refl; subst)
open import Relation.Nullary using (Dec; yes; no)

module Compiler.Model.Graph.Correctness.OptimizeCorrect where

{- Helpers --------------------------------------------------------------------}

unbind-bind : ∀ m (N : AST) → unbind-n m (bind-n-ast m N) ≡ N
unbind-bind zero N = refl
unbind-bind (suc m) N = unbind-bind m N

push-ne : ∀ n (Ds : Results (𝒫 Value) (replicate n ■)) ρ
  → (∀ i → nonempty (nthD Ds i)) → nonempty-env ρ → nonempty-env (push Ds ρ)
push-ne zero _ ρ _ NE = NE
push-ne (suc n) ⟨ D , Ds ⟩ ρ ne NE =
  push-ne n Ds (D • ρ) (λ i → ne (suc i)) (extend-nonempty-env NE (ne zero))

{- What pruning a closure's free variables preserves --------------------------}

record PruneOK n (U : ℕ → Set) (fvs : Args (replicate n ■)) (P : Pruned) (b : ℕ → ℕ)
    (ρ ρ' : Env) : Set₁ where
  field
    {- the kept free variables are nonempty exactly when all of them were -}
    ne→ : (∀ i → nonempty (nthD (⟦ fvs ⟧₊ ρ) i)) → ∀ i → nonempty (nthD (⟦ kept P ⟧₊ ρ') i)
    ne← : (∀ i → nonempty (nthD (⟦ kept P ⟧₊ ρ') i)) → ∀ i → nonempty (nthD (⟦ fvs ⟧₊ ρ) i)
    {- every position that the code uses is renumbered to the same set -}
    push≃ : ∀ ρ₁ ρ₂ → (∀ k → U (n + k) → ρ₁ k ≃ ρ₂ (b k))
      → ∀ j → U j → push (⟦ fvs ⟧₊ ρ) ρ₁ j ≃ push (⟦ kept P ⟧₊ ρ') ρ₂ (index P j)

keep-ok : ∀ {n U} {M M' : AST} {fvs : Args (replicate n ■)} {P b ρ ρ'}
  → ⟦ M ⟧ ρ ≃ ⟦ M' ⟧ ρ'
  → PruneOK n U fvs P (keep-base b) ρ ρ'
  → PruneOK (suc n) U (M ,, fvs) (keep M' P) b ρ ρ'
keep-ok {n} {U} {M} {M'} {fvs} {P} {b} {ρ} {ρ'} M≃ ok = record
  { ne→ = λ { ne zero → ⟨ proj₁ (ne zero) , proj₁ M≃ _ (proj₂ (ne zero)) ⟩
            ; ne (suc i) → PruneOK.ne→ ok (λ i → ne (suc i)) i }
  ; ne← = λ { ne zero → ⟨ proj₁ (ne zero) , proj₂ M≃ _ (proj₂ (ne zero)) ⟩
            ; ne (suc i) → PruneOK.ne← ok (λ i → ne (suc i)) i }
  ; push≃ = λ ρ₁ ρ₂ bse j u →
      PruneOK.push≃ ok (⟦ M ⟧ ρ • ρ₁) (⟦ M' ⟧ ρ' • ρ₂) (bse' ρ₁ ρ₂ bse) j u
  }
  where
  bse' : ∀ ρ₁ ρ₂ → (∀ k → U (suc n + k) → ρ₁ k ≃ ρ₂ (b k))
    → ∀ k → U (n + k) → (⟦ M ⟧ ρ • ρ₁) k ≃ (⟦ M' ⟧ ρ' • ρ₂) (keep-base b k)
  bse' ρ₁ ρ₂ bse zero _ = M≃
  bse' ρ₁ ρ₂ bse (suc k) uk = bse k (subst U (+-suc n k) uk)

{- The main lemma -------------------------------------------------------------}

opt-correct : ∀ (M : AST) r ρ ρ' → nonempty-env ρ → (∀ x → Uses x M → ρ x ≃ ρ' (r x))
  → ⟦ M ⟧ ρ ≃ ⟦ optimize r M ⟧ ρ'

opt-body-correct : ∀ r k (a : Arg (ν-n k (ν ■))) ρ ρ' → nonempty-env ρ
  → (∀ x → Uses x (unbind-n k a) → ρ x ≃ ρ' (r x))
  → ⟦ unbind-n k a ⟧ ρ ≃ ⟦ opt-body r k a ⟧ ρ'

opt-args-correct : ∀ {n} (args : Args (replicate n ■)) r ρ ρ' → nonempty-env ρ
  → (∀ x → UsesArgs x args → ρ x ≃ ρ' (r x))
  → ∀ i → nthD (⟦ args ⟧₊ ρ) i ≃ nthD (⟦ opt-args r args ⟧₊ ρ') i

prune-ok : ∀ n r {U : ℕ → Set} (dec : ∀ j → Dec (U j)) (fvs : Args (replicate n ■))
  (b : ℕ → ℕ) ρ ρ' → nonempty-env ρ → (∀ x → UsesArgs x fvs → ρ x ≃ ρ' (r x))
  → PruneOK n U fvs (prune n r dec fvs b) b ρ ρ'

opt-correct (` x) r ρ ρ' NE rel = rel x refl
opt-correct (clos-op n ⦅ ! clear a ,, fvs ⦆) r ρ ρ' NE rel = ⟨ G , H ⟩
  where
  N = unbind-n n a
  P = prune n r (λ j → uses? (suc j) N) fvs (λ k → k)
  ok = prune-ok n r (λ j → uses? (suc j) N) fvs (λ k → k) ρ ρ' NE (λ x u → rel x (inj₂ u))
  Ds = ⟦ fvs ⟧₊ ρ
  Ds' = ⟦ kept P ⟧₊ ρ'
  m = count P
  N' = opt-body (ext-var (index P)) n a

  {- applying the closure to U runs the same body on the same free variables -}
  body≃ : ∀ U → U ≢ [] → (∀ i → nonempty (nthD Ds i))
    → apply-n n (⟦ a ⟧ₐ init₀) Ds (mem U) ≃ apply-n m (⟦ bind-n-ast m N' ⟧ₐ init₀) Ds' (mem U)
  body≃ U neU ne
    rewrite apply-push n a init₀ Ds (mem U)
          | apply-push m (bind-n-ast m N') init₀ Ds' (mem U)
          | unbind-bind m N' =
    opt-body-correct (ext-var (index P)) n a (mem U • push Ds init₀) (mem U • push Ds' init₀)
      (extend-nonempty-env (push-ne n Ds init₀ ne (λ _ → ⟨ ω , refl ⟩)) (E≢[]⇒nonempty-mem neU))
      rel₁
    where
    rel₁ : ∀ x → Uses x N → (mem U • push Ds init₀) x ≃ (mem U • push Ds' init₀) (ext-var (index P) x)
    rel₁ zero _ = ≃-refl
    rel₁ (suc j) u = PruneOK.push≃ ok init₀ init₀ (λ k _ → ≃-refl) j u

  G : ⟦ clos-op n ⦅ ! clear a ,, fvs ⦆ ⟧ ρ ⊆ ⟦ optimize r (clos-op n ⦅ ! clear a ,, fvs ⦆) ⟧ ρ'
  G ν ⟨ ne , tt ⟩ = ⟨ PruneOK.ne→ ok ne , tt ⟩
  G (U ↦ x) ⟨ ne , ⟨ x∈ , neU ⟩ ⟩ = ⟨ PruneOK.ne→ ok ne , ⟨ proj₁ (body≃ U neU ne) x x∈ , neU ⟩ ⟩

  H : ⟦ optimize r (clos-op n ⦅ ! clear a ,, fvs ⦆) ⟧ ρ' ⊆ ⟦ clos-op n ⦅ ! clear a ,, fvs ⦆ ⟧ ρ
  H ν ⟨ ne' , tt ⟩ = ⟨ PruneOK.ne← ok ne' , tt ⟩
  H (U ↦ x) ⟨ ne' , ⟨ x∈ , neU ⟩ ⟩ =
    ⟨ PruneOK.ne← ok ne' , ⟨ proj₂ (body≃ U neU (PruneOK.ne← ok ne')) x x∈ , neU ⟩ ⟩
opt-correct (app ⦅ L ,, M ,, Nil ⦆) r ρ ρ' NE rel =
  ⋆-≃ (opt-correct L r ρ ρ' NE (λ x u → rel x (inj₁ u)))
      (opt-correct M r ρ ρ' NE (λ x u → rel x (inj₂ (inj₁ u))))
opt-correct (lit B k ⦅ Nil ⦆) r ρ ρ' NE rel = ≃-refl
opt-correct (tuple n ⦅ args ⦆) r ρ ρ' NE rel = 𝒯-≃ n (opt-args-correct args r ρ ρ' NE rel)
opt-correct (get i ⦅ M ,, Nil ⦆) r ρ ρ' NE rel =
  proj-≃ i (opt-correct M r ρ ρ' NE (λ x u → rel x (inj₁ u)))
opt-correct (inl-op ⦅ M ,, Nil ⦆) r ρ ρ' NE rel =
  ℒ-≃ (opt-correct M r ρ ρ' NE (λ x u → rel x (inj₁ u)))
opt-correct (inr-op ⦅ M ,, Nil ⦆) r ρ ρ' NE rel =
  ℛ-≃ (opt-correct M r ρ ρ' NE (λ x u → rel x (inj₁ u)))
opt-correct (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) r ρ ρ' NE rel = ⟨ G , H ⟩
  where
  L≃ = opt-correct L r ρ ρ' NE (λ x u → rel x (inj₁ u))

  NE-ext : ∀ v V → nonempty-env (mem (v ∷ V) • ρ)
  NE-ext v V = extend-nonempty-env NE ⟨ v , here refl ⟩

  M≃ : ∀ v V → ⟦ M ⟧ (mem (v ∷ V) • ρ) ≃ ⟦ optimize (ext-var r) M ⟧ (mem (v ∷ V) • ρ')
  M≃ v V = opt-correct M (ext-var r) _ _ (NE-ext v V) relM
    where
    relM : ∀ x → Uses x M → (mem (v ∷ V) • ρ) x ≃ (mem (v ∷ V) • ρ') (ext-var r x)
    relM zero _ = ≃-refl
    relM (suc x) u = rel x (inj₂ (inj₁ u))

  N≃ : ∀ v V → ⟦ N ⟧ (mem (v ∷ V) • ρ) ≃ ⟦ optimize (ext-var r) N ⟧ (mem (v ∷ V) • ρ')
  N≃ v V = opt-correct N (ext-var r) _ _ (NE-ext v V) relN
    where
    relN : ∀ x → Uses x N → (mem (v ∷ V) • ρ) x ≃ (mem (v ∷ V) • ρ') (ext-var r x)
    relN zero _ = ≃-refl
    relN (suc x) u = rel x (inj₂ (inj₂ (inj₁ u)))

  G : ⟦ case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆ ⟧ ρ
      ⊆ ⟦ optimize r (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) ⟧ ρ'
  G w (inj₁ ⟨ v , ⟨ V , ⟨ allL , w∈ ⟩ ⟩ ⟩) =
    inj₁ ⟨ v , ⟨ V , ⟨ (λ d d∈ → proj₁ L≃ (left d) (allL d d∈)) , proj₁ (M≃ v V) w w∈ ⟩ ⟩ ⟩
  G w (inj₂ ⟨ v , ⟨ V , ⟨ allR , w∈ ⟩ ⟩ ⟩) =
    inj₂ ⟨ v , ⟨ V , ⟨ (λ d d∈ → proj₁ L≃ (right d) (allR d d∈)) , proj₁ (N≃ v V) w w∈ ⟩ ⟩ ⟩

  H : ⟦ optimize r (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) ⟧ ρ'
      ⊆ ⟦ case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆ ⟧ ρ
  H w (inj₁ ⟨ v , ⟨ V , ⟨ allL , w∈ ⟩ ⟩ ⟩) =
    inj₁ ⟨ v , ⟨ V , ⟨ (λ d d∈ → proj₂ L≃ (left d) (allL d d∈)) , proj₂ (M≃ v V) w w∈ ⟩ ⟩ ⟩
  H w (inj₂ ⟨ v , ⟨ V , ⟨ allR , w∈ ⟩ ⟩ ⟩) =
    inj₂ ⟨ v , ⟨ V , ⟨ (λ d d∈ → proj₂ L≃ (right d) (allR d d∈)) , proj₂ (N≃ v V) w w∈ ⟩ ⟩ ⟩

opt-body-correct r zero (bind (ast N)) ρ ρ' NE rel = opt-correct N r ρ ρ' NE rel
opt-body-correct r (suc k) (bind a) = opt-body-correct r k a

opt-args-correct {suc n} (M ,, args) r ρ ρ' NE rel zero =
  opt-correct M r ρ ρ' NE (λ x u → rel x (inj₁ u))
opt-args-correct {suc n} (M ,, args) r ρ ρ' NE rel (suc i) =
  opt-args-correct args r ρ ρ' NE (λ x u → rel x (inj₂ u)) i

prune-ok zero r dec Nil b ρ ρ' NE rel = record
  { ne→ = λ _ () ; ne← = λ _ () ; push≃ = λ ρ₁ ρ₂ bse j u → bse j u }
prune-ok (suc n) r {U} dec ((` y) ,, fvs) b ρ ρ' NE rel with dec n
... | yes _ =
  keep-ok (rel y (inj₁ refl))
          (prune-ok n r dec fvs (keep-base b) ρ ρ' NE (λ x u → rel x (inj₂ u)))
... | no ¬u = record
  { ne→ = λ ne → PruneOK.ne→ ok (λ i → ne (suc i))
  ; ne← = λ { ne' zero → NE y ; ne' (suc i) → PruneOK.ne← ok ne' i }
  ; push≃ = λ ρ₁ ρ₂ bse j u → PruneOK.push≃ ok (ρ y • ρ₁) ρ₂ (bse' ρ₁ ρ₂ bse) j u
  }
  where
  ok = prune-ok n r dec fvs (drop-base b) ρ ρ' NE (λ x u → rel x (inj₂ u))
  bse' : ∀ ρ₁ ρ₂ → (∀ k → U (suc n + k) → ρ₁ k ≃ ρ₂ (b k))
    → ∀ k → U (n + k) → (ρ y • ρ₁) k ≃ ρ₂ (drop-base b k)
  bse' ρ₁ ρ₂ bse zero uk = ⊥-elim (¬u (subst U (+-identityʳ n) uk))
  bse' ρ₁ ρ₂ bse (suc k) uk = bse k (subst U (+-suc n k) uk)
prune-ok (suc n) r dec ((op ⦅ args ⦆) ,, fvs) b ρ ρ' NE rel =
  keep-ok (opt-correct (op ⦅ args ⦆) r ρ ρ' NE (λ x u → rel x (inj₁ u)))
          (prune-ok n r dec fvs (keep-base b) ρ ρ' NE (λ x u → rel x (inj₂ u)))

{- The end theorem ------------------------------------------------------------}

optimize-correct-closed : ∀ (M : AST) → ⟦ M ⟧ ρ₀ ≃ ⟦ optimize-program M ⟧ ρ₀
optimize-correct-closed M = opt-correct M (λ x → x) ρ₀ ρ₀ (λ _ → ⟨ ω , refl ⟩) (λ x _ → ≃-refl)

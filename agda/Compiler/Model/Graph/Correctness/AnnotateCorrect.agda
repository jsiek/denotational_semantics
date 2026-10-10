{-# OPTIONS --safe #-}
{-

  Correctness of the annotate pass (ISWIM → Clos1), and of the whole
  pipeline from ISWIM to Clos4.

  ISWIM and Clos1 use the same values, and annotate only adds to each
  function the list of surrounding variables it may use. So the pass
  preserves denotations exactly, ⟦ M ⟧ ρ₁ ≃ ⟦ annotate M ⟧₁ ρ₂, when the
  environments agree on the variables M uses; this gives both the forward
  and the backward direction. The environment must be nonempty because
  Clos1 closures are strict in their listed free variables.

  Annotate also produces the shape that enclose needs (Enclosed): each
  closure lists ` (m - 1) , ... , ` 0, and its body uses no other
  surrounding variable.

-}

open import NewSigUtil
open import NewSyntaxUtil
open import SetsAsPredicates
open import NewDOpSig
open import Primitives
open import Compiler.Model.Graph.Domain.ISWIM.Domain
open import Compiler.Model.Graph.Domain.ISWIM.Ops
open import Compiler.Lang.ISWIM
open import Compiler.Lang.Uses Op sig
import Compiler.Lang.Clos1 as L1
import Compiler.Lang.Clos4 as L4
import Compiler.Lang.Uses as UsesM
module U1 = UsesM L1.Op L1.sig
open import Compiler.Model.Graph.Sem.ISWIM
open import Compiler.Model.Graph.Sem.Clos1Iswim as S1 renaming
  (⟦_⟧ to ⟦_⟧₁; ⟦_⟧ₐ to ⟦_⟧ₐ₁; ⟦_⟧₊ to ⟦_⟧₊₁)
import Compiler.Model.Graph.Sem.Clos4Iswim as S4
open import Compiler.Compile.Enclose using (fv-vars)
open import Compiler.Compile.Annotate
open import Compiler.Model.Graph.Correctness.DelayFiniteCommon using (Env; ρ₀)
open import Compiler.Model.Graph.Correctness.ConcretizeCorrect
  using (⋆-≃; 𝒯-≃; proj-≃; ℒ-≃; ℛ-≃)
open import Compiler.Model.Graph.Correctness.EncloseCorrect
open import Compiler.Model.Graph.Correctness.PipelineCorrect
  using (compile; pipeline-correct-const; pipeline-correct-nonempty)
open import NewEnv using (nonempty-env; extend-nonempty-env)

open import Data.Nat using (ℕ; zero; suc; _<_; _∸_; _⊔_)
open import Data.Nat.Properties using (n<1+n; ≤-pred; <-≤-trans; m≤m⊔n; m≤n⊔m)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_; replicate)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩ )
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≢_; refl)

module Compiler.Model.Graph.Correctness.AnnotateCorrect where

{- Every variable a term uses is below its bound -------------------------------}

<-∸1 : ∀ {x b} → suc x < b → x < b ∸ 1
<-∸1 {x} {suc b} sx<sb = ≤-pred sx<sb

uses-bound : ∀ x (M : L1.AST) → U1.Uses x M → x < bound M
uses-bound-arg : ∀ {b} x (a : L1.Arg b) → U1.UsesArg x a → x < bound-arg a
uses-bound-args : ∀ {bs} x (args : L1.Args bs) → U1.UsesArgs x args → x < bound-args args

uses-bound x (L1.` .x) refl = n<1+n x
uses-bound x (op L1.⦅ args ⦆) u = uses-bound-args x args u

uses-bound-arg x (L1.ast M) u = uses-bound x M u
uses-bound-arg x (L1.bind a) u = <-∸1 (uses-bound-arg (suc x) a u)

uses-bound-args x (L1.cons a args) (inj₁ u) = <-≤-trans (uses-bound-arg x a u) (m≤m⊔n _ _)
uses-bound-args x (L1.cons a args) (inj₂ u) =
  <-≤-trans (uses-bound-args x args u) (m≤n⊔m (bound-arg a) _)

{- Annotate produces the shape that enclose needs ------------------------------}

ann-enclosed : ∀ (M : AST) → Enclosed (annotate M)
ann-enclosed-args : ∀ {n} (args : Args (replicate n ■)) → EnclosedArgs (ann-args args)

ann-enclosed (` x) = enc-var
ann-enclosed (lam ⦅ ⟩ N ,, Nil ⦆) =
  enc-clos (ann-enclosed N) (λ k u → <-∸1 (uses-bound (suc k) (annotate N) u))
ann-enclosed (app ⦅ L ,, M ,, Nil ⦆) = enc-app (ann-enclosed L) (ann-enclosed M)
ann-enclosed (lit B k ⦅ Nil ⦆) = enc-lit
ann-enclosed (tuple n ⦅ args ⦆) = enc-tuple (ann-enclosed-args args)
ann-enclosed (get i ⦅ M ,, Nil ⦆) = enc-get (ann-enclosed M)
ann-enclosed (inl-op ⦅ M ,, Nil ⦆) = enc-inl (ann-enclosed M)
ann-enclosed (inr-op ⦅ M ,, Nil ⦆) = enc-inr (ann-enclosed M)
ann-enclosed (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) =
  enc-case (ann-enclosed L) (ann-enclosed M) (ann-enclosed N)

ann-enclosed-args {zero} Nil = enc-nil
ann-enclosed-args {suc n} (M ,, args) = enc-cons (ann-enclosed M) (ann-enclosed-args args)

{- The listed free variables are nonempty -------------------------------------}

fv-vars-ne : ∀ m (ρ : Env) → nonempty-env ρ → ∀ i → nonempty (nthD (⟦ fv-vars m ⟧₊₁ ρ) i)
fv-vars-ne (suc m) ρ NE zero = NE m
fv-vars-ne (suc m) ρ NE (suc i) = fv-vars-ne m ρ NE i

{- The main lemma -------------------------------------------------------------}

ann-correct : ∀ (M : AST) ρ₁ ρ₂ → nonempty-env ρ₂ → (∀ x → Uses x M → ρ₁ x ≃ ρ₂ x)
  → ⟦ M ⟧ ρ₁ ≃ ⟦ annotate M ⟧₁ ρ₂

ann-args-correct : ∀ {n} (args : Args (replicate n ■)) ρ₁ ρ₂ → nonempty-env ρ₂
  → (∀ x → UsesArgs x args → ρ₁ x ≃ ρ₂ x)
  → ∀ i → nthD (⟦ args ⟧₊ ρ₁) i ≃ nthD (⟦ ann-args args ⟧₊₁ ρ₂) i

ann-correct (` x) ρ₁ ρ₂ NE rel = rel x refl
ann-correct (lam ⦅ ⟩ N ,, Nil ⦆) ρ₁ ρ₂ NE rel = ⟨ G , H ⟩
  where
  m = bound (annotate N) ∸ 1
  ne = fv-vars-ne m ρ₂ NE

  body≃ : ∀ U → U ≢ [] → ⟦ N ⟧ (mem U • ρ₁) ≃ ⟦ annotate N ⟧₁ (mem U • ρ₂)
  body≃ U neU =
    ann-correct N (mem U • ρ₁) (mem U • ρ₂) (extend-nonempty-env NE (E≢[]⇒nonempty-mem neU)) rel'
    where
    rel' : ∀ x → Uses x N → (mem U • ρ₁) x ≃ (mem U • ρ₂) x
    rel' zero _ = ≃-refl
    rel' (suc k) u = rel k (inj₁ u)

  G : ⟦ lam ⦅ ⟩ N ,, Nil ⦆ ⟧ ρ₁ ⊆ ⟦ annotate (lam ⦅ ⟩ N ,, Nil ⦆) ⟧₁ ρ₂
  G ν tt = ⟨ ne , tt ⟩
  G (U ↦ x) ⟨ x∈ , neU ⟩ = ⟨ ne , ⟨ proj₁ (body≃ U neU) x x∈ , neU ⟩ ⟩

  H : ⟦ annotate (lam ⦅ ⟩ N ,, Nil ⦆) ⟧₁ ρ₂ ⊆ ⟦ lam ⦅ ⟩ N ,, Nil ⦆ ⟧ ρ₁
  H ν ⟨ _ , tt ⟩ = tt
  H (U ↦ x) ⟨ _ , ⟨ x∈ , neU ⟩ ⟩ = ⟨ proj₂ (body≃ U neU) x x∈ , neU ⟩
ann-correct (app ⦅ L ,, M ,, Nil ⦆) ρ₁ ρ₂ NE rel =
  ⋆-≃ (ann-correct L ρ₁ ρ₂ NE (λ x u → rel x (inj₁ u)))
      (ann-correct M ρ₁ ρ₂ NE (λ x u → rel x (inj₂ (inj₁ u))))
ann-correct (lit B k ⦅ Nil ⦆) ρ₁ ρ₂ NE rel = ≃-refl
ann-correct (tuple n ⦅ args ⦆) ρ₁ ρ₂ NE rel = 𝒯-≃ n (ann-args-correct args ρ₁ ρ₂ NE rel)
ann-correct (get i ⦅ M ,, Nil ⦆) ρ₁ ρ₂ NE rel =
  proj-≃ i (ann-correct M ρ₁ ρ₂ NE (λ x u → rel x (inj₁ u)))
ann-correct (inl-op ⦅ M ,, Nil ⦆) ρ₁ ρ₂ NE rel =
  ℒ-≃ (ann-correct M ρ₁ ρ₂ NE (λ x u → rel x (inj₁ u)))
ann-correct (inr-op ⦅ M ,, Nil ⦆) ρ₁ ρ₂ NE rel =
  ℛ-≃ (ann-correct M ρ₁ ρ₂ NE (λ x u → rel x (inj₁ u)))
ann-correct (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) ρ₁ ρ₂ NE rel = ⟨ G , H ⟩
  where
  L≃ = ann-correct L ρ₁ ρ₂ NE (λ x u → rel x (inj₁ u))

  NE-ext : ∀ v V → nonempty-env (mem (v ∷ V) • ρ₂)
  NE-ext v V = extend-nonempty-env NE ⟨ v , here refl ⟩

  M≃ : ∀ v V → ⟦ M ⟧ (mem (v ∷ V) • ρ₁) ≃ ⟦ annotate M ⟧₁ (mem (v ∷ V) • ρ₂)
  M≃ v V = ann-correct M _ _ (NE-ext v V) relM
    where
    relM : ∀ x → Uses x M → (mem (v ∷ V) • ρ₁) x ≃ (mem (v ∷ V) • ρ₂) x
    relM zero _ = ≃-refl
    relM (suc x) u = rel x (inj₂ (inj₁ u))

  N≃ : ∀ v V → ⟦ N ⟧ (mem (v ∷ V) • ρ₁) ≃ ⟦ annotate N ⟧₁ (mem (v ∷ V) • ρ₂)
  N≃ v V = ann-correct N _ _ (NE-ext v V) relN
    where
    relN : ∀ x → Uses x N → (mem (v ∷ V) • ρ₁) x ≃ (mem (v ∷ V) • ρ₂) x
    relN zero _ = ≃-refl
    relN (suc x) u = rel x (inj₂ (inj₂ (inj₁ u)))

  G : ⟦ case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆ ⟧ ρ₁
      ⊆ ⟦ annotate (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) ⟧₁ ρ₂
  G w (inj₁ ⟨ v , ⟨ V , ⟨ allL , w∈ ⟩ ⟩ ⟩) =
    inj₁ ⟨ v , ⟨ V , ⟨ (λ d d∈ → proj₁ L≃ (left d) (allL d d∈)) , proj₁ (M≃ v V) w w∈ ⟩ ⟩ ⟩
  G w (inj₂ ⟨ v , ⟨ V , ⟨ allR , w∈ ⟩ ⟩ ⟩) =
    inj₂ ⟨ v , ⟨ V , ⟨ (λ d d∈ → proj₁ L≃ (right d) (allR d d∈)) , proj₁ (N≃ v V) w w∈ ⟩ ⟩ ⟩

  H : ⟦ annotate (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) ⟧₁ ρ₂
      ⊆ ⟦ case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆ ⟧ ρ₁
  H w (inj₁ ⟨ v , ⟨ V , ⟨ allL , w∈ ⟩ ⟩ ⟩) =
    inj₁ ⟨ v , ⟨ V , ⟨ (λ d d∈ → proj₂ L≃ (left d) (allL d d∈)) , proj₂ (M≃ v V) w w∈ ⟩ ⟩ ⟩
  H w (inj₂ ⟨ v , ⟨ V , ⟨ allR , w∈ ⟩ ⟩ ⟩) =
    inj₂ ⟨ v , ⟨ V , ⟨ (λ d d∈ → proj₂ L≃ (right d) (allR d d∈)) , proj₂ (N≃ v V) w w∈ ⟩ ⟩ ⟩

ann-args-correct {suc n} (M ,, args) ρ₁ ρ₂ NE rel zero =
  ann-correct M ρ₁ ρ₂ NE (λ x u → rel x (inj₁ u))
ann-args-correct {suc n} (M ,, args) ρ₁ ρ₂ NE rel (suc i) =
  ann-args-correct args ρ₁ ρ₂ NE (λ x u → rel x (inj₂ u)) i

{- The end theorems -----------------------------------------------------------}

annotate-correct-closed : ∀ (M : AST) → ⟦ M ⟧ ρ₀ ≃ ⟦ annotate M ⟧₁ ρ₀
annotate-correct-closed M = ann-correct M ρ₀ ρ₀ (λ _ → ⟨ ω , refl ⟩) (λ x _ → ≃-refl)

{- the whole pipeline, from ISWIM to Clos4 -}
compile-iswim : AST → L4.AST
compile-iswim M = compile (annotate M)

compile-iswim-correct-const : ∀ (M : AST) → ∀ {B} (c : base-rep B)
  → (const c ∈ ⟦ M ⟧ ρ₀ → const c ∈ S4.⟦ compile-iswim M ⟧ ρ₀)
  × (const c ∈ S4.⟦ compile-iswim M ⟧ ρ₀ → const c ∈ ⟦ M ⟧ ρ₀)
compile-iswim-correct-const M c =
  ⟨ (λ c∈ → proj₁ rest (proj₁ M≃ _ c∈))
  , (λ c∈ → proj₂ M≃ _ (proj₂ rest c∈)) ⟩
  where
  M≃ = annotate-correct-closed M
  rest = pipeline-correct-const (annotate M) (ann-enclosed M) c

compile-iswim-correct-nonempty : ∀ (M : AST)
  → (nonempty (⟦ M ⟧ ρ₀) → nonempty (S4.⟦ compile-iswim M ⟧ ρ₀))
  × (nonempty (S4.⟦ compile-iswim M ⟧ ρ₀) → nonempty (⟦ M ⟧ ρ₀))
compile-iswim-correct-nonempty M =
  ⟨ (λ ne → proj₁ rest ⟨ proj₁ ne , proj₁ M≃ _ (proj₂ ne) ⟩)
  , (λ ne → let ne' = proj₂ rest ne in ⟨ proj₁ ne' , proj₂ M≃ _ (proj₂ ne') ⟩) ⟩
  where
  M≃ = annotate-correct-closed M
  rest = pipeline-correct-nonempty (annotate M) (ann-enclosed M)

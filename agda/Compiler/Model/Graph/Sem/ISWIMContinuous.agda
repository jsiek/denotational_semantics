{-

  The ISWIM semantics is continuous: a ContinuousSemantics instance built
  from the per-operator lemmas in GraphModel.Continuity (as for Clos3 in
  Clos3IswimContinuous), and its consequence for a function body: an
  element of ⟦ N ⟧ (X • ρ) needs only finitely many elements of X.

-}

open import SetsAsPredicates
open import GraphModel.Domain
open import GraphModel.Continuity
open import Compiler.Model.Graph.Prim
open import Compiler.Lang.ISWIM
open import GraphModel.SemanticsUtil Op sig using (args-nth-mono; args-nth-cont)
open import Compiler.Model.Graph.Sem.ISWIM
open import NewEnv using (Env; nonempty-env; finiteNE-env; _⊆ₑ_; extend-nonempty-env)

open import Data.Nat using (zero; suc)
open import Data.List using (List; []; _∷_; replicate)
open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax)
  renaming (_,_ to ⟨_,_⟩ )
open import Relation.Binary.PropositionalEquality using (_≢_)

module Compiler.Model.Graph.Sem.ISWIMContinuous where

ISWIM-continuous-op : ∀ {op} {ρ : Env Value} {NE : nonempty-env ρ} {v} {args}
  → v ∈ ⟦ op ⦅ args ⦆ ⟧ ρ → continuous-args ρ NE (sig op) args
  → Σ[ ρ′ ∈ Env Value ] finiteNE-env ρ′ × ρ′ ⊆ₑ ρ × v ∈ ⟦ op ⦅ args ⦆ ⟧ ρ′
ISWIM-continuous-op {lam} {ρ} {NE} {v} {cons (bind (ast N)) nil} v∈ ⟨ cN , _ ⟩ =
  Λ-cont {B = λ ρ → ⟦ N ⟧ ρ} NE (⟦⟧-monotone N) cN v v∈
ISWIM-continuous-op {app} {ρ} {NE} {v} {cons (ast L) (cons (ast N) nil)} v∈
    ⟨ cL , ⟨ cN , _ ⟩ ⟩ =
  ⋆-cont {E₁ = λ ρ → ⟦ L ⟧ ρ} {E₂ = λ ρ → ⟦ N ⟧ ρ} NE (⟦⟧-monotone L) (⟦⟧-monotone N) cL cN v v∈
ISWIM-continuous-op {lit B k} {ρ} {NE} {v} {nil} v∈ _ =
  const-cont {D = ⟦ lit B k ⦅ nil ⦆ ⟧ ρ} NE v v∈
ISWIM-continuous-op {tuple n} {ρ} {NE} {v} {args} v∈ cs =
  𝒯-cont {Ds = λ ρ → ⟦ args ⟧₊ ρ} NE (args-nth-mono args) (args-nth-cont args {ρ} {NE} cs) v v∈
ISWIM-continuous-op {get i} {ρ} {NE} {v} {cons (ast M) nil} v∈ ⟨ cM , _ ⟩ =
  proj-cont i {E = λ ρ → ⟦ M ⟧ ρ} cM v v∈
ISWIM-continuous-op {inl-op} {ρ} {NE} {v} {cons (ast M) nil} v∈ ⟨ cM , _ ⟩ =
  inl-cont {E = λ ρ → ⟦ M ⟧ ρ} cM v v∈
ISWIM-continuous-op {inr-op} {ρ} {NE} {v} {cons (ast M) nil} v∈ ⟨ cM , _ ⟩ =
  inr-cont {E = λ ρ → ⟦ M ⟧ ρ} cM v v∈
ISWIM-continuous-op {case-op} {ρ} {NE} {v}
    {cons (ast L) (cons (bind (ast M)) (cons (bind (ast N)) nil))} v∈
    ⟨ cL , ⟨ cM , ⟨ cN , _ ⟩ ⟩ ⟩ =
  𝒞-cont {L = λ ρ → ⟦ L ⟧ ρ} {B₁ = λ ρ → ⟦ M ⟧ ρ} {B₂ = λ ρ → ⟦ N ⟧ ρ} NE
    (⟦⟧-monotone L) cL (⟦⟧-monotone M) cM (⟦⟧-monotone N) cN v v∈
ISWIM-continuous-op {prim p} {ρ} {NE} {v}
    {cons (ast L) (cons (ast M) nil)} v∈ ⟨ cL , ⟨ cM , _ ⟩ ⟩ =
  primD-cont p {E₁ = λ ρ → ⟦ L ⟧ ρ} {E₂ = λ ρ → ⟦ M ⟧ ρ} (⟦⟧-monotone L) (⟦⟧-monotone M) cL cM v v∈

ISWIM-Continuous : ContinuousSemantics
ISWIM-Continuous = record
  { Sem = ISWIM-Semantics
  ; continuous-op = λ {op} {ρ} {NE} {v} {args} → ISWIM-continuous-op {op} {ρ} {NE} {v} {args}
  }

{- a function body uses only a finite, nonempty part of its argument -}
body-continuous : ∀ (N : AST) (ρ : Env Value) → nonempty-env ρ → ∀ (X : 𝒫 Value) → nonempty X
  → ∀ d → d ∈ ⟦ N ⟧ (X • ρ)
  → Σ[ V ∈ List Value ] V ≢ [] × mem V ⊆ X × d ∈ ⟦ N ⟧ (mem V • ρ)
body-continuous N ρ NE X neX d d∈
    with ⟦⟧-continuous {{ISWIM-Continuous}} {X • ρ} {extend-nonempty-env NE neX} N d d∈
... | ⟨ ρ′ , ⟨ fin , ⟨ ρ′⊆ , d∈′ ⟩ ⟩ ⟩ with fin 0
... | ⟨ V , ⟨ ρ′0≃V , V≢[] ⟩ ⟩ =
  ⟨ V , ⟨ V≢[] , ⟨ (λ u u∈ → ρ′⊆ 0 u (proj₂ ρ′0≃V u u∈)) , ⟦⟧-monotone N G d d∈′ ⟩ ⟩ ⟩
  where
  G : ∀ x → ρ′ x ⊆ (mem V • ρ) x
  G zero = proj₁ ρ′0≃V
  G (suc x) = ρ′⊆ (suc x)

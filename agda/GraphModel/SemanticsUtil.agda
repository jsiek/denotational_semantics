{-

  Consequences of NewSemantics' monotonicity and continuity theorems that
  every graph-model semantics of the compiler's languages uses: the
  components of a tuple of terms, and the finite parts of the environment
  that an element of a term's denotation needs.

-}

open import SetsAsPredicates
open import GraphModel.Domain
open import GraphModel.Ops using (nthD)
open import GraphModel.Continuity using (Mono; Cont)
open import NewEnv using (Env; nonempty-env)

open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; replicate)
open import Data.Product using (_×_; proj₁; proj₂; Σ-syntax) renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality using (_≢_)

module GraphModel.SemanticsUtil (Op : Set) (sig : Op → List Sig) where

open import abt.AbstractBindingTree Op sig
open import NewSemantics Op sig

module _ {{S : Semantics {Value}}} where
  open Semantics S

  args-nth-mono : ∀ {n} (args : Args (replicate n ■)) (i : Fin n)
    → Mono (λ ρ → nthD (⟦ args ⟧₊ ρ) i)
  args-nth-mono (cons (ast M) args) zero ρ⊆ = ⟦⟧-monotone M ρ⊆
  args-nth-mono (cons (ast M) args) (suc i) ρ⊆ = args-nth-mono args i ρ⊆

  args-nth-cont : ∀ {n} (args : Args (replicate n ■)) {ρ : Env Value} {NE : nonempty-env ρ}
    → continuous-args ρ NE (replicate n ■) args
    → (i : Fin n) → Cont (λ ρ → nthD (⟦ args ⟧₊ ρ) i) ρ
  args-nth-cont (cons (ast M) args) ⟨ cM , cs ⟩ zero = cM
  args-nth-cont (cons (ast M) args) {ρ} {NE} ⟨ cM , cs ⟩ (suc i) = args-nth-cont args {ρ} {NE} cs i

{- every element of a term's denotation is produced by finite, nonempty
   parts of the environment -}
term-continuous : {{C : ContinuousSemantics {Value}}} (M : ABT) (ρ : Env Value) → nonempty-env ρ
  → ∀ v → v ∈ Semantics.⟦ ContinuousSemantics.Sem C ⟧ M ρ
  → Σ[ Vs ∈ (Var → List Value) ] (∀ x → Vs x ≢ [] × mem (Vs x) ⊆ ρ x)
                                 × v ∈ Semantics.⟦ ContinuousSemantics.Sem C ⟧ M (λ x → mem (Vs x))
term-continuous {{C}} M ρ NE v v∈ with ⟦⟧-continuous {{C}} {ρ} {NE} M v v∈
... | ⟨ ρ′ , ⟨ fin , ⟨ ρ′⊆ , v∈′ ⟩ ⟩ ⟩ =
  ⟨ (λ x → proj₁ (fin x))
  , ⟨ (λ x → ⟨ proj₂ (proj₂ (fin x)) , (λ d d∈ → ρ′⊆ x d (proj₂ (proj₁ (proj₂ (fin x))) d d∈)) ⟩)
    , ⟦⟧-monotone {{ContinuousSemantics.Sem C}} M (λ x d d∈ → proj₁ (proj₁ (proj₂ (fin x))) d d∈) v v∈′ ⟩ ⟩

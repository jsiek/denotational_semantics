open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Unit using (tt)
open import Level using (lift; lower)
open import abt.Sig using (Sig; ■; ν; ∁; Result)
open import abt.Var using (Var)
open import abt.GSubst using (_•_)
open import SetsAsPredicates
open import NewDOpSig
open import NewEnv using (Env)

{-
  Renaming the variables of a term commutes with any monotone semantics:
  the renamed term, in an environment ρ, means what the original term
  means in the environment that maps x to ρ (r x).
-}
module Compiler.Model.Graph.Sem.RenameSem (Op : Set) (sig : Op → List Sig) where

open import abt.AbstractBindingTree Op sig renaming (ABT to AST)
open import Compiler.Lang.Rename Op sig
open import NewSemantics Op sig
open Semantics {{...}}

rename-⊆ : ∀ {A} {{_ : Semantics {A}}} (M : AST) r (ρ ρ' : Env A)
  → (∀ x → ρ (r x) ⊆ ρ' x) → ⟦ rename r M ⟧ ρ ⊆ ⟦ M ⟧ ρ'
rename-arg-⊆ : ∀ {A} {{_ : Semantics {A}}} {b} (a : Arg b) r (ρ ρ' : Env A)
  → (∀ x → ρ (r x) ⊆ ρ' x)
  → result-rel-pres _⊆_ b (⟦ rename-arg r a ⟧ₐ ρ) (⟦ a ⟧ₐ ρ')
rename-args-⊆ : ∀ {A} {{_ : Semantics {A}}} {bs} (args : Args bs) r (ρ ρ' : Env A)
  → (∀ x → ρ (r x) ⊆ ρ' x)
  → results-rel-pres _⊆_ bs (⟦ rename-args r args ⟧₊ ρ) (⟦ args ⟧₊ ρ')

rename-⊆ (` x) r ρ ρ' rel = rel x
rename-⊆ (op ⦅ args ⦆) r ρ ρ' rel =
  lower (mono-op op (⟦ rename-args r args ⟧₊ ρ) (⟦ args ⟧₊ ρ') (rename-args-⊆ args r ρ ρ' rel))

rename-arg-⊆ (ast M) r ρ ρ' rel = lift (rename-⊆ M r ρ ρ' rel)
rename-arg-⊆ (bind a) r ρ ρ' rel = λ X X' X⊆ → rename-arg-⊆ a (ext r) (X • ρ) (X' • ρ') (rel' X⊆)
  where
  rel' : ∀ {X X'} → X ⊆ X' → ∀ x → (X • ρ) (ext r x) ⊆ (X' • ρ') x
  rel' X⊆ zero = X⊆
  rel' X⊆ (suc x) = rel x
rename-arg-⊆ (clear a) r ρ ρ' rel = ⟦⟧-monotone-arg {ρ = ρ'} {ρ′ = ρ'} (clear a) (λ x d d∈ → d∈)

rename-args-⊆ nil r ρ ρ' rel = lift tt
rename-args-⊆ (cons a args) r ρ ρ' rel = ⟨ rename-arg-⊆ a r ρ ρ' rel , rename-args-⊆ args r ρ ρ' rel ⟩

rename-⊇ : ∀ {A} {{_ : Semantics {A}}} (M : AST) r (ρ ρ' : Env A)
  → (∀ x → ρ' x ⊆ ρ (r x)) → ⟦ M ⟧ ρ' ⊆ ⟦ rename r M ⟧ ρ
rename-arg-⊇ : ∀ {A} {{_ : Semantics {A}}} {b} (a : Arg b) r (ρ ρ' : Env A)
  → (∀ x → ρ' x ⊆ ρ (r x))
  → result-rel-pres _⊆_ b (⟦ a ⟧ₐ ρ') (⟦ rename-arg r a ⟧ₐ ρ)
rename-args-⊇ : ∀ {A} {{_ : Semantics {A}}} {bs} (args : Args bs) r (ρ ρ' : Env A)
  → (∀ x → ρ' x ⊆ ρ (r x))
  → results-rel-pres _⊆_ bs (⟦ args ⟧₊ ρ') (⟦ rename-args r args ⟧₊ ρ)

rename-⊇ (` x) r ρ ρ' rel = rel x
rename-⊇ (op ⦅ args ⦆) r ρ ρ' rel =
  lower (mono-op op (⟦ args ⟧₊ ρ') (⟦ rename-args r args ⟧₊ ρ) (rename-args-⊇ args r ρ ρ' rel))

rename-arg-⊇ (ast M) r ρ ρ' rel = lift (rename-⊇ M r ρ ρ' rel)
rename-arg-⊇ (bind a) r ρ ρ' rel = λ X' X X⊆ → rename-arg-⊇ a (ext r) (X • ρ) (X' • ρ') (rel' X⊆)
  where
  rel' : ∀ {X X'} → X' ⊆ X → ∀ x → (X' • ρ') x ⊆ (X • ρ) (ext r x)
  rel' X⊆ zero = X⊆
  rel' X⊆ (suc x) = rel x
rename-arg-⊇ (clear a) r ρ ρ' rel = ⟦⟧-monotone-arg {ρ = ρ'} {ρ′ = ρ'} (clear a) (λ x d d∈ → d∈)

rename-args-⊇ nil r ρ ρ' rel = lift tt
rename-args-⊇ (cons a args) r ρ ρ' rel = ⟨ rename-arg-⊇ a r ρ ρ' rel , rename-args-⊇ args r ρ ρ' rel ⟩

rename-≃ : ∀ {A} {{_ : Semantics {A}}} (M : AST) r (ρ ρ' : Env A)
  → (∀ x → ρ (r x) ≃ ρ' x) → ⟦ rename r M ⟧ ρ ≃ ⟦ M ⟧ ρ'
rename-≃ M r ρ ρ' rel =
  ⟨ rename-⊆ M r ρ ρ' (λ x → proj₁ (rel x)) , rename-⊇ M r ρ ρ' (λ x → proj₂ (rel x)) ⟩

{- a shifted term ignores the newest variable -}
shift-≃ : ∀ {A} {{_ : Semantics {A}}} (M : AST) (X : 𝒫 A) (ρ : Env A)
  → ⟦ shift M ⟧ (X • ρ) ≃ ⟦ M ⟧ ρ
shift-≃ M X ρ = rename-≃ M suc (X • ρ) ρ (λ x → ≃-refl)

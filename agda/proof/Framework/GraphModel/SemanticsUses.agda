{-

  A denotation depends only on the variables the term uses: for any
  semantics, if two environments agree on them, the term means the same
  in both. So a closed term means the same in every environment.

-}

open import Data.List using (List; []; _∷_)
open import Data.Nat using (zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Level using (lift; lower)
open import Relation.Binary.PropositionalEquality using (refl)

open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.DOpSig
open import proof.Framework.GraphModel.Env
open import Framework.abt.Sig

module proof.Framework.GraphModel.SemanticsUses (Op : Set) (sig : Op → List Sig) where

open import Framework.abt.AbstractBindingTree Op sig
open import Framework.Syntax.Uses Op sig
open import proof.Framework.GraphModel.Semantics Op sig
open Semantics {{...}}

module _ {A : Set} {{S : Semantics {A}}} where

  ⟦⟧-uses : ∀ (M : ABT) {ρ ρ′ : Env A} → (∀ x → Uses x M → ρ x ⊆ ρ′ x) → ⟦ M ⟧ ρ ⊆ ⟦ M ⟧ ρ′
  ⟦⟧-uses-arg : ∀ {b} (a : Arg b) {ρ ρ′ : Env A} → (∀ x → UsesArg x a → ρ x ⊆ ρ′ x)
    → result-rel-pres _⊆_ b (⟦ a ⟧ₐ ρ) (⟦ a ⟧ₐ ρ′)
  ⟦⟧-uses-args : ∀ {bs} (as : Args bs) {ρ ρ′ : Env A} → (∀ x → UsesArgs x as → ρ x ⊆ ρ′ x)
    → results-rel-pres _⊆_ bs (⟦ as ⟧₊ ρ) (⟦ as ⟧₊ ρ′)

  ⟦⟧-uses (` x) r = r x refl
  ⟦⟧-uses (op ⦅ as ⦆) {ρ} {ρ′} r = lower (mono-op op (⟦ as ⟧₊ ρ) (⟦ as ⟧₊ ρ′) (⟦⟧-uses-args as r))

  ⟦⟧-uses-arg (ast M) r = lift (⟦⟧-uses M r)
  ⟦⟧-uses-arg (bind a) r X Y X⊆ = ⟦⟧-uses-arg a r′
    where
    r′ : ∀ x → UsesArg x a → _
    r′ zero _ = X⊆
    r′ (suc x) u = r x u
  ⟦⟧-uses-arg (clear a) r = ⟦⟧-uses-arg a (λ _ _ d d∈ → d∈)

  ⟦⟧-uses-args nil r = ptt
  ⟦⟧-uses-args (cons a as) r =
    ⟨ ⟦⟧-uses-arg a (λ x u → r x (inj₁ u)) , ⟦⟧-uses-args as (λ x u → r x (inj₂ u)) ⟩

  {- a term that uses no variables means the same in every environment -}
  ⟦⟧-closed : ∀ (M : ABT) → (∀ x → Uses x M → ⊥) → ∀ (ρ ρ′ : Env A) → ⟦ M ⟧ ρ ≃ ⟦ M ⟧ ρ′
  ⟦⟧-closed M none ρ ρ′ = ⟨ ⟦⟧-uses M (λ x u → ⊥-elim (none x u)) , ⟦⟧-uses M (λ x u → ⊥-elim (none x u)) ⟩

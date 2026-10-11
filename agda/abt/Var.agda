{-# OPTIONS --without-K #-}
{- Extracted from the abt library (github.com/jsiek/abstract-binding-trees,
   commit 1387c40). -}
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Data.Nat using (ℕ; zero; suc; _<_; z≤n; s≤s; _+_)
open import Data.Empty.Polymorphic using (⊥)
open import Data.Unit.Polymorphic using (⊤)
open import Data.List using (List; []; _∷_; length; _++_)
open import Data.Product using (_×_)
open import Level using (levelOfType)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import abt.Sig

module abt.Var where

Var : Set
Var = ℕ

private
  variable
    ℓ : Level
    I : Set ℓ
    Γ Δ : List I
    x : Var
    A : I

_∋_⦂_ : List I → Var → I → Set (levelOfType I)
_∋_⦂_ {I = I} [] x A = ⊥
_∋_⦂_ (B ∷ Γ) zero A = A ≡ B
_∋_⦂_ (B ∷ Γ) (suc x) A = Γ ∋ x ⦂ A

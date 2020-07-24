open import Values
open import Data.Nat using (ℕ; zero; suc)
open import LambdaV using (Term; $; _·_; ƛ)
open LambdaV.ASTMod using (Var; Z; S_; `_; extensionality; Rename; Subst; ext)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Function using (_∘_)


module Environment
    (D : Set)
    (domain : Domain D)
    where

open Domain domain

{-
ext-nth : ∀ {Γ Δ v} {γ : Env Γ D} {δ : Env Δ D}
  → (ρ : Rename Γ Δ)
  → γ `⊑ (δ ∘ ρ)
    ------------------------------
  → (γ `, v) `⊑ ((δ `, v) ∘ ext ρ)
ext-nth ρ lt Z = Refl⊑
ext-nth ρ lt (S n′) = lt n′
-}

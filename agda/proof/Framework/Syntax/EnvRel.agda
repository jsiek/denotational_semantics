open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)
import Data.Maybe.Relation.Binary.Pointwise as M
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Framework.abt.Sig using (Sig)
open import Framework.abt.Var using (Var)
open import Framework.ListUtil using (_‼_)

{-
  Environments (lists of values, variable x the x-th) related through a
  renaming r of their variables (Framework/Syntax/Rename.agda): Ren r ρ₁ ρ₂
  when each variable x finds the same value (or none) at x in ρ₁ as at
  r x in ρ₂; EnvRel r ρ₁ ρ₂ (in Rel, for a relation _≈_ between the values
  of the two environments) when it finds related values (or none). Both
  extend under a binder (ext r), and EnvRel skips a value of ρ₂ that ρ₁
  does not see.
-}
module proof.Framework.Syntax.EnvRel (Op : Set) (sig : Op → List Sig) where

open import Framework.Syntax.Rename Op sig using (ext)

Ren : ∀ {A : Set} → (Var → Var) → List A → List A → Set
Ren r ρ₁ ρ₂ = ∀ x → ρ₂ ‼ r x ≡ ρ₁ ‼ x

ren-ext : ∀ {A : Set} {r} {ρ₁ ρ₂ : List A} v → Ren r ρ₁ ρ₂ → Ren (ext r) (v ∷ ρ₁) (v ∷ ρ₂)
ren-ext v rn zero = refl
ren-ext v rn (suc x) = rn x

module Rel {A B : Set} (_≈_ : A → B → Set) where

  data EnvRel (r : Var → Var) (ρ₁ : List A) (ρ₂ : List B) : Set where
    env : (∀ x → M.Pointwise _≈_ (ρ₁ ‼ x) (ρ₂ ‼ r x)) → EnvRel r ρ₁ ρ₂

  look : ∀ {r ρ₁ ρ₂} → EnvRel r ρ₁ ρ₂ → ∀ x → M.Pointwise _≈_ (ρ₁ ‼ x) (ρ₂ ‼ r x)
  look (env l) = l

  env-ext : ∀ {r ρ₁ ρ₂ v w} → v ≈ w → EnvRel r ρ₁ ρ₂ → EnvRel (ext r) (v ∷ ρ₁) (w ∷ ρ₂)
  env-ext r (env l) = env λ { zero → M.just r ; (suc x) → l x }

  env-skip : ∀ {r ρ₁ ρ₂ w} → EnvRel r ρ₁ ρ₂ → EnvRel (λ x → suc (r x)) ρ₁ (w ∷ ρ₂)
  env-skip (env l) = env l

open import Data.List using (List)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; subst₂)
open import Framework.abt.Sig using (Sig)

{-
  A relation between the terms of two signatures that is closed under
  substitution by related substitutions, from the same closure for
  renamings: the proof of closure is given once, for any relation P
  between substitutions that relates variables and is preserved under
  binders (sub≈), and gives closure under renaming (≈-rename) and then
  under every related substitution (≈-subst). The substitutions may be
  restricted by a predicate Ok that holds for renamings.
-}
module proof.Framework.Syntax.SubstRel (Op₁ : Set) (sig₁ : Op₁ → List Sig) (Op₂ : Set) (sig₂ : Op₂ → List Sig) where

open import Framework.abt.AbstractBindingTree Op₁ sig₁ using () renaming (ABT to AST₁; `_ to `₁_)
open import Framework.abt.AbstractBindingTree Op₂ sig₂ using () renaming (ABT to AST₂; `_ to `₂_)
import proof.Framework.Syntax.Subst Op₁ sig₁ as S₁
import proof.Framework.Syntax.Subst Op₂ sig₂ as S₂
import Framework.Syntax.Rename Op₁ sig₁ as R₁
import Framework.Syntax.Rename Op₂ sig₂ as R₂

module Closure (_≈_ : AST₁ → AST₂ → Set) (var≈ : ∀ {x} → (`₁ x) ≈ (`₂ x))
  (Ok : S₁.Subst → S₂.Subst → Set)
  (ok-var : ∀ {σ σ'} → (∀ x → Σ[ y ∈ ℕ ] σ x ≡ `₁ y × σ' x ≡ `₂ y) → Ok σ σ')
  (ok-exts : ∀ {σ σ'} → Ok σ σ' → Ok (S₁.exts σ) (S₂.exts σ'))
  (sub≈ : ∀ (P : S₁.Subst → S₂.Subst → Set)
          → (∀ {σ σ'} → P σ σ' → ∀ x → σ x ≈ σ' x) → (∀ {σ σ'} → P σ σ' → Ok σ σ')
          → (∀ {σ σ'} → P σ σ' → P (S₁.exts σ) (S₂.exts σ'))
          → ∀ {σ σ' M M'} → P σ σ' → M ≈ M' → S₁.sub σ M ≈ S₂.sub σ' M') where

  private
    RenP : S₁.Subst → S₂.Subst → Set
    RenP σ σ' = ∀ x → Σ[ y ∈ ℕ ] σ x ≡ `₁ y × σ' x ≡ `₂ y

    ren≈ : ∀ {σ σ'} → RenP σ σ' → ∀ x → σ x ≈ σ' x
    ren≈ p x with p x
    ... | y , e , e' rewrite e | e' = var≈

    ren-exts : ∀ {σ σ'} → RenP σ σ' → RenP (S₁.exts σ) (S₂.exts σ')
    ren-exts p zero = zero , refl , refl
    ren-exts p (suc x) with p x
    ... | y , e , e' = suc y , cong (R₁.rename suc) e , cong (R₂.rename suc) e'

  ≈-rename : ∀ r {M M'} → M ≈ M' → R₁.rename r M ≈ R₂.rename r M'
  ≈-rename r {M} {M'} m =
    subst₂ _≈_ (sym (S₁.rename-sub r M)) (sym (S₂.rename-sub r M'))
      (sub≈ RenP ren≈ ok-var ren-exts
            (λ x → r x , refl , refl) m)

  {- related substitutions -}
  SubP : S₁.Subst → S₂.Subst → Set
  SubP σ σ' = (∀ x → σ x ≈ σ' x) × Ok σ σ'

  sub-exts : ∀ {σ σ'} → SubP σ σ' → SubP (S₁.exts σ) (S₂.exts σ')
  sub-exts (p , ok) = (λ { zero → var≈ ; (suc x) → ≈-rename suc (p x) }) , ok-exts ok

  ≈-subst : ∀ {σ σ' M M'} → SubP σ σ' → M ≈ M' → S₁.sub σ M ≈ S₂.sub σ' M'
  ≈-subst = sub≈ SubP proj₁ proj₂ sub-exts

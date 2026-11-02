{-

  Substitution of *intrinsically* typed terms Tm Γ A, where Γ is
  a list of types (Framework/Membership.agda).
  (Recall that the other substitution module, `Subst.agda`,
  is of abstract binding trees.)

  Renaming and substitution are one traversal with a kit (Kit.agda),
  supplied by the client language. This module contains language-generic
  definitions of the following: `exts`, `varK`, `_•_`, `∅`,
  and given the traversal, `ren`, `tmK`, `sub` and `_[_]`.

  The properties of substitution are in proof/Framework/Syntax/TypedSubst.agda.

-}

open import Data.List using (List; []; _∷_)
open import Framework.Membership using (_∋_; Z; S)

module Framework.Syntax.TypedSubst {T : Set} (Tm : List T → T → Set) (`_ : ∀ {Γ A} → Γ ∋ A → Tm Γ A) where

open import Framework.Syntax.Kit {List T} {T} _∋_ (λ Γ A → A ∷ Γ) Tm public

module _ (𝒦 : Kit) where
  open Kit 𝒦

  {- `exts σ` lifts `σ` under a binder: the bound variable maps to itself,
     the others as under `σ`, weakened past the binder. -}
  exts : ∀ {Γ Δ B} → Sub 𝒦 Γ Δ → Sub 𝒦 (B ∷ Γ) (B ∷ Δ)
  exts σ Z = vr Z
  exts σ (S x) = wk (σ x)

{- The kit of variables. Its traversal is renaming. -}
varK : Kit
varK = record { K = _∋_ ; vr = λ x → x ; tm = `_ ; wk = S }

{- Explicit substitutions of terms: the cons `V • σ` maps the first
   variable to `V` and the others as `σ` does; `∅` is the empty substitution.
   (Their type `Sub tmK` is spelled out because `tmK` is defined below.) -}
infixr 5 _•_
_•_ : ∀ {Γ Δ A} → Tm Δ A → (∀ {B} → Γ ∋ B → Tm Δ B) → ∀ {B} → (A ∷ Γ) ∋ B → Tm Δ B
(V • σ) Z = V
(V • σ) (S x) = σ x

∅ : ∀ {Δ B} → [] ∋ B → Tm Δ B
∅ ()

{- Renaming and substitution: the traversal with `varK` and with `tmK`.
   The traversal is a parameter because `tmK` weakens a term by renaming it. -}
module Substitution (trav : (𝒦 : Kit) → ∀ {Γ Δ A} → Sub 𝒦 Γ Δ → Tm Γ A → Tm Δ A) where

  ren : ∀ {Γ Δ A} → (∀ {B} → Γ ∋ B → Δ ∋ B) → Tm Γ A → Tm Δ A
  ren r = trav varK r

  {- The kit of terms. Its traversal is substitution. -}
  tmK : Kit
  tmK = record { K = Tm ; vr = `_ ; tm = λ M → M ; wk = ren S }

  sub : ∀ {Γ Δ A} → (∀ {B} → Γ ∋ B → Tm Δ B) → Tm Γ A → Tm Δ A
  sub σ = trav tmK σ

  {- `N [ V ]` is the single substitution that substitutes the closed term
     `V` for the only free variable of `N`. -}
  _[_] : ∀ {A B} → Tm (A ∷ []) B → Tm [] A → Tm [] B
  N [ V ] = sub (V • ∅) N

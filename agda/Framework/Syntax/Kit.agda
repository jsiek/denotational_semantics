{-

  Kits, for renaming and substitution of intrinsically scoped (and
  typed) terms by one traversal (McBride, "Type-preserving renaming and
  substitution"): a kit says what a variable is mapped to (K), how a
  variable is one (vr), how one is a term (tm), and how one is moved
  under a binder (wk). Renaming is the traversal with the kit of
  variables, substitution the one with the kit of terms. Language
  independent: scopes S, types T, variables V, extension of a scope
  _▷_, and the terms Tm that a variable stands for.

-}

module Framework.Syntax.Kit {S T : Set} (V : S → T → Set) (_▷_ : S → T → S) (Tm : S → T → Set) where

record Kit : Set₁ where
  field
    K : S → T → Set
    vr : ∀ {Γ A} → V Γ A → K Γ A
    tm : ∀ {Γ A} → K Γ A → Tm Γ A
    wk : ∀ {Γ A B} → K Γ A → K (Γ ▷ B) A

{- a map of the variables of Γ to things of the kit in Δ -}
Sub : Kit → S → S → Set
Sub 𝒦 Γ Δ = ∀ {A} → V Γ A → Kit.K 𝒦 Δ A

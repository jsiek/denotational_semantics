{-

  The values of the Clos2 reduction semantics (Untyped.Semantics.Reduction.Clos3.agda):
  they reduce to val, and substitution keeps them values.

-}

module Untyped.proof.Semantics.Reduction.Clos3 where

open import Untyped.Semantics.Reduction.Clos3 public
open import Untyped.Language.Clos3
open import Semantics.Observation using (Obs; o-error)
open import proof.Framework.Reduction Obs o-error using (val)
open import proof.Framework.Reduction Obs o-error using (Each; []; _∷_) public
open import Framework.Syntax.SyntaxUtil using (_,,_; Nil)
open import Framework.Syntax.Subst Op sig using (sub; sub-args)

open import Data.List using (replicate)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

data Value : AST → Set where
  clos : ∀ {n a fvs} → Each Value fvs → Value (clos-op n ⦅ cons (clear a) fvs ⦆)
  lit : ∀ {B k} → Value (lit B k ⦅ Nil ⦆)
  tuple : ∀ {n as} → Each Value as → Value (tuple n ⦅ as ⦆)
  inl : ∀ {V} → Value V → Value (inl-op ⦅ V ,, Nil ⦆)
  inr : ∀ {V} → Value V → Value (inr-op ⦅ V ,, Nil ⦆)

Values : ∀ {n} → Args (replicate n ■) → Set
Values = Each Value

value-red : ∀ {V} → Value V → red V ≡ val
values-red : ∀ {n} {as : Args (replicate n ■)} → Values as → red-args as ≡ val
value-red (clos vs) rewrite values-red vs = refl
value-red lit = refl
value-red (tuple vs) rewrite values-red vs = refl
value-red (inl v) rewrite value-red v = refl
value-red (inr v) rewrite value-red v = refl
values-red [] = refl
values-red (v ∷ vs) rewrite value-red v | values-red vs = refl

value-sub : ∀ σ {V} → Value V → Value (sub σ V)
values-sub : ∀ σ {n} {as : Args (replicate n ■)} → Values as → Values (sub-args σ as)
value-sub σ (clos vs) = clos (values-sub σ vs)
value-sub σ lit = lit
value-sub σ (tuple vs) = tuple (values-sub σ vs)
value-sub σ (inl v) = inl (value-sub σ v)
value-sub σ (inr v) = inr (value-sub σ v)
values-sub σ [] = []
values-sub σ (v ∷ vs) = value-sub σ v ∷ values-sub σ vs

{-

  The values of the Clos5 reduction semantics (Semantics/Reduction/Clos5.agda):
  they reduce to val.

-}

module proof.Semantics.Reduction.Clos5 where

open import Semantics.Reduction.Clos5 public
open import Language.Clos5
open import Semantics.Reduction.Smallstep using (val)
open import Framework.Syntax.SyntaxUtil using (_,,_; Nil)

open import Data.List using (replicate)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

data Value : AST → Set
infixr 5 _∷_
data Values : ∀ {n} → Args (replicate n ■) → Set

data Value where
  fun : ∀ {k} → Value (fun-ref k ⦅ Nil ⦆)
  pair : ∀ {V W} → Value V → Value W → Value (pair-op ⦅ V ,, W ,, Nil ⦆)
  lit : ∀ {B k} → Value (lit B k ⦅ Nil ⦆)
  tuple : ∀ {n as} → Values as → Value (tuple n ⦅ as ⦆)
  inl : ∀ {V} → Value V → Value (inl-op ⦅ V ,, Nil ⦆)
  inr : ∀ {V} → Value V → Value (inr-op ⦅ V ,, Nil ⦆)

data Values where
  [] : Values Nil
  _∷_ : ∀ {n V} {as : Args (replicate n ■)} → Value V → Values as → Values (V ,, as)

value-red : ∀ {ds V} → Value V → red ds V ≡ val
values-red : ∀ {ds n} {as : Args (replicate n ■)} → Values as → red-args ds as ≡ val
value-red fun = refl
value-red {ds} (pair v w) rewrite value-red {ds} v | value-red {ds} w = refl
value-red lit = refl
value-red {ds} (tuple vs) rewrite values-red {ds} vs = refl
value-red {ds} (inl v) rewrite value-red {ds} v = refl
value-red {ds} (inr v) rewrite value-red {ds} v = refl
values-red [] = refl
values-red {ds} (v ∷ vs) rewrite value-red {ds} v | values-red {ds} vs = refl

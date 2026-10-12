{-

  The values of the Clos4 reduction semantics (Compiler/Reduction/Clos4.agda):
  they reduce to val, and substitution keeps them values.

-}

module proof.Compiler.Reduction.Clos4 where

open import Compiler.Reduction.Clos4 public
open import Compiler.Lang.Clos4
open import Compiler.Reduction.Smallstep using (val)
open import Framework.Syntax.SyntaxUtil using (_,,_; Nil)
open import Framework.Syntax.Subst Op sig using (sub; sub-args)

open import Data.List using (replicate)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

data Value : AST → Set
infixr 5 _∷_
data Values : ∀ {n} → Args (replicate n ■) → Set

data Value where
  fun : ∀ {a} → Value (fun-op ⦅ a ⦆)
  pair : ∀ {V W} → Value V → Value W → Value (pair-op ⦅ V ,, W ,, Nil ⦆)
  lit : ∀ {B k} → Value (lit B k ⦅ Nil ⦆)
  tuple : ∀ {n as} → Values as → Value (tuple n ⦅ as ⦆)
  inl : ∀ {V} → Value V → Value (inl-op ⦅ V ,, Nil ⦆)
  inr : ∀ {V} → Value V → Value (inr-op ⦅ V ,, Nil ⦆)

data Values where
  [] : Values Nil
  _∷_ : ∀ {n V} {as : Args (replicate n ■)} → Value V → Values as → Values (V ,, as)

value-red : ∀ {V} → Value V → red V ≡ val
values-red : ∀ {n} {as : Args (replicate n ■)} → Values as → red-args as ≡ val
value-red fun = refl
value-red (pair v w) rewrite value-red v | value-red w = refl
value-red lit = refl
value-red (tuple vs) rewrite values-red vs = refl
value-red (inl v) rewrite value-red v = refl
value-red (inr v) rewrite value-red v = refl
values-red [] = refl
values-red (v ∷ vs) rewrite value-red v | values-red vs = refl

value-sub : ∀ σ {V} → Value V → Value (sub σ V)
values-sub : ∀ σ {n} {as : Args (replicate n ■)} → Values as → Values (sub-args σ as)
value-sub σ (fun {cons (clear a) nil}) = fun
value-sub σ (pair v w) = pair (value-sub σ v) (value-sub σ w)
value-sub σ lit = lit
value-sub σ (tuple vs) = tuple (values-sub σ vs)
value-sub σ (inl v) = inl (value-sub σ v)
value-sub σ (inr v) = inr (value-sub σ v)
values-sub σ [] = []
values-sub σ (v ∷ vs) = value-sub σ v ∷ values-sub σ vs

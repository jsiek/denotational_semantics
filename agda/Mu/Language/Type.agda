{-

  The types of ISWIMμ and of the typed intermediate languages of its
  compiler (agda/Mu/): base types (Base of Framework/Primitives.agda:
  Nat, Int, 𝔹, Unit, Void and Blame), functions, n-ary tuples, binary
  sums and iso-recursive types μX.A, with type variables as de Bruijn
  indices (Ty n has n free type variables). The body of a μ is unrestricted:
  since fold and unfold are explicit coercions (iso-recursive types),
  types such as μX.X need no contractiveness condition. Terms are
  indexed by closed types (Type = Ty 0); a context is a list of them.

  * fold : A [ μ A ] → μ A and unfold : μ A → A [ μ A ] (in the
    languages) are the coercions of the isomorphism; they do nothing at
    run time.
  * code Δ A B, in FlatClosμ only: closed code that takes a tuple of type
    tup Δ (its environment) and an argument of type A.
  * A primitive's result: sub gives an integer, eq a boolean, the sum
    tup [] ⊹ tup [] (inl ⟨⟩ for true).

  Unlike Language/Typed/Type.agda there is no type Any of tagged values,
  no flat types, no tags, and no decidable equality: nothing tests a
  type at run time.

-}

module Mu.Language.Type where

open import Framework.Primitives using (Base; Int)
open import Language.Prim using (Prim; sub; eq)

open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)

infixr 7 _⇒_
infixr 6 _⊹_

data Ty (n : ℕ) : Set where
  base : Base → Ty n
  _⇒_ : Ty n → Ty n → Ty n
  tup : List (Ty n) → Ty n
  _⊹_ : Ty n → Ty n → Ty n
  code : List (Ty n) → Ty n → Ty n → Ty n
  var : Fin n → Ty n
  μ : Ty (suc n) → Ty n

Type : Set
Type = Ty 0

Ctx : Set
Ctx = List Type

open import Framework.Membership using (_∋_; Z; S; idx; lvl) public

out-ty : Prim → Type
out-ty sub = base Int
out-ty eq = tup [] ⊹ tup []

{- Renaming and substitution of type variables ---------------------------------}

tren : ∀ {n m} → (Fin n → Fin m) → Ty n → Ty m
trens : ∀ {n m} → (Fin n → Fin m) → List (Ty n) → List (Ty m)

private
  ext : ∀ {n m} → (Fin n → Fin m) → Fin (suc n) → Fin (suc m)
  ext r zero = zero
  ext r (suc x) = suc (r x)

tren r (base B) = base B
tren r (A ⇒ B) = tren r A ⇒ tren r B
tren r (tup Δ) = tup (trens r Δ)
tren r (A ⊹ B) = tren r A ⊹ tren r B
tren r (code Δ A B) = code (trens r Δ) (tren r A) (tren r B)
tren r (var x) = var (r x)
tren r (μ A) = μ (tren (ext r) A)
trens r [] = []
trens r (A ∷ Δ) = tren r A ∷ trens r Δ

tsubst : ∀ {n m} → (Fin n → Ty m) → Ty n → Ty m
tsubsts : ∀ {n m} → (Fin n → Ty m) → List (Ty n) → List (Ty m)

private
  exts : ∀ {n m} → (Fin n → Ty m) → Fin (suc n) → Ty (suc m)
  exts σ zero = var zero
  exts σ (suc x) = tren suc (σ x)

tsubst σ (base B) = base B
tsubst σ (A ⇒ B) = tsubst σ A ⇒ tsubst σ B
tsubst σ (tup Δ) = tup (tsubsts σ Δ)
tsubst σ (A ⊹ B) = tsubst σ A ⊹ tsubst σ B
tsubst σ (code Δ A B) = code (tsubsts σ Δ) (tsubst σ A) (tsubst σ B)
tsubst σ (var x) = σ x
tsubst σ (μ A) = μ (tsubst (exts σ) A)
tsubsts σ [] = []
tsubsts σ (A ∷ Δ) = tsubst σ A ∷ tsubsts σ Δ

{- A [ B ]: B for the type variable 0 of A -}
_[_] : ∀ {n} → Ty (suc n) → Ty n → Ty n
A [ B ] = tsubst (λ { zero → B ; (suc x) → var x }) A

{- the unfolding of μ A -}
unroll : ∀ {n} → Ty (suc n) → Ty n
unroll A = A [ μ A ]

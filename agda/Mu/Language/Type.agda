{-

  The types of ISWIMμ and of the typed intermediate languages of its
  compiler (agda/Mu/): base types (Base of Framework/Primitives.agda:
  Nat, Int, 𝔹, Unit, Void and Blame), functions, n-ary tuples, binary
  sums and iso-recursive types μX.A, with type variables as de Bruijn
  indices (Ty n has n free type variables). The body of a μ is contractive: it is
  not a variable nor another μ (no μX.X), so that unfolding is
  productive. Terms are indexed by closed types (Type = Ty 0); a
  context is a list of them.

  * fold : A [ μ A ] → μ A and unfold : μ A → A [ μ A ] (in the
    languages) are the coercions of the isomorphism; they do nothing at
    run time.
  * code Δ A B, in Clos4μ only: closed code that takes a tuple of type
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

open import Data.Empty using (⊥)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤)

infixr 7 _⇒_
infixr 6 _⊹_

data Ty (n : ℕ) : Set
Contractive : ∀ {n} → Ty n → Set

data Ty n where
  base : Base → Ty n
  _⇒_ : Ty n → Ty n → Ty n
  tup : List (Ty n) → Ty n
  _⊹_ : Ty n → Ty n → Ty n
  code : List (Ty n) → Ty n → Ty n → Ty n
  var : Fin n → Ty n
  μ : (A : Ty (suc n)) → {Contractive A} → Ty n

Contractive (var _) = ⊥
Contractive (μ _) = ⊥
Contractive _ = ⊤

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
tren-c : ∀ {n m} (r : Fin n → Fin m) A → Contractive A → Contractive (tren r A)

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
tren r (μ A {c}) = μ (tren (ext r) A) {tren-c (ext r) A c}
trens r [] = []
trens r (A ∷ Δ) = tren r A ∷ trens r Δ
tren-c r (base _) c = c
tren-c r (_ ⇒ _) c = c
tren-c r (tup _) c = c
tren-c r (_ ⊹ _) c = c
tren-c r (code _ _ _) c = c

tsubst : ∀ {n m} → (Fin n → Ty m) → Ty n → Ty m
tsubsts : ∀ {n m} → (Fin n → Ty m) → List (Ty n) → List (Ty m)
tsubst-c : ∀ {n m} (σ : Fin n → Ty m) A → Contractive A → Contractive (tsubst σ A)

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
tsubst σ (μ A {c}) = μ (tsubst (exts σ) A) {tsubst-c (exts σ) A c}
tsubsts σ [] = []
tsubsts σ (A ∷ Δ) = tsubst σ A ∷ tsubsts σ Δ
tsubst-c σ (base _) c = c
tsubst-c σ (_ ⇒ _) c = c
tsubst-c σ (tup _) c = c
tsubst-c σ (_ ⊹ _) c = c
tsubst-c σ (code _ _ _) c = c

{- A [ B ]: B for the type variable 0 of A -}
_[_] : ∀ {n} → Ty (suc n) → Ty n → Ty n
A [ B ] = tsubst (λ { zero → B ; (suc x) → var x }) A

{- the unfolding of μ A -}
unroll : ∀ {n} (A : Ty (suc n)) {c : Contractive A} → Ty n
unroll A {c} = A [ μ A {c} ]

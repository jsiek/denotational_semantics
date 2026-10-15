{-

  The types of ISWIMμ and of the typed intermediate languages of the
  pilot (agda/Mu/): base types, functions, n-ary tuples, binary sums and
  iso-recursive types μX.A, with type variables as de Bruijn indices (Ty
  n has n free type variables). The body of a μ is contractive: it is
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

ren : ∀ {n m} → (Fin n → Fin m) → Ty n → Ty m
rens : ∀ {n m} → (Fin n → Fin m) → List (Ty n) → List (Ty m)
ren-c : ∀ {n m} (r : Fin n → Fin m) A → Contractive A → Contractive (ren r A)

private
  ext : ∀ {n m} → (Fin n → Fin m) → Fin (suc n) → Fin (suc m)
  ext r zero = zero
  ext r (suc x) = suc (r x)

ren r (base B) = base B
ren r (A ⇒ B) = ren r A ⇒ ren r B
ren r (tup Δ) = tup (rens r Δ)
ren r (A ⊹ B) = ren r A ⊹ ren r B
ren r (code Δ A B) = code (rens r Δ) (ren r A) (ren r B)
ren r (var x) = var (r x)
ren r (μ A {c}) = μ (ren (ext r) A) {ren-c (ext r) A c}
rens r [] = []
rens r (A ∷ Δ) = ren r A ∷ rens r Δ
ren-c r (base _) c = c
ren-c r (_ ⇒ _) c = c
ren-c r (tup _) c = c
ren-c r (_ ⊹ _) c = c
ren-c r (code _ _ _) c = c

subst : ∀ {n m} → (Fin n → Ty m) → Ty n → Ty m
substs : ∀ {n m} → (Fin n → Ty m) → List (Ty n) → List (Ty m)
subst-c : ∀ {n m} (σ : Fin n → Ty m) A → Contractive A → Contractive (subst σ A)

private
  exts : ∀ {n m} → (Fin n → Ty m) → Fin (suc n) → Ty (suc m)
  exts σ zero = var zero
  exts σ (suc x) = ren suc (σ x)

subst σ (base B) = base B
subst σ (A ⇒ B) = subst σ A ⇒ subst σ B
subst σ (tup Δ) = tup (substs σ Δ)
subst σ (A ⊹ B) = subst σ A ⊹ subst σ B
subst σ (code Δ A B) = code (substs σ Δ) (subst σ A) (subst σ B)
subst σ (var x) = σ x
subst σ (μ A {c}) = μ (subst (exts σ) A) {subst-c (exts σ) A c}
substs σ [] = []
substs σ (A ∷ Δ) = subst σ A ∷ substs σ Δ
subst-c σ (base _) c = c
subst-c σ (_ ⇒ _) c = c
subst-c σ (tup _) c = c
subst-c σ (_ ⊹ _) c = c
subst-c σ (code _ _ _) c = c

{- A [ B ]: B for the type variable 0 of A -}
_[_] : ∀ {n} → Ty (suc n) → Ty n → Ty n
A [ B ] = subst (λ { zero → B ; (suc x) → var x }) A

{- the unfolding of μ A -}
unroll : ∀ {n} (A : Ty (suc n)) {c : Contractive A} → Ty n
unroll A {c} = A [ μ A {c} ]

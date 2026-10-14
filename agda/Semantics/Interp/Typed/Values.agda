{-

  The values of the clocked interpreters of the typed languages
  (Semantics/Interp/Typed/), indexed by their type, and the operations
  on them; C n is what the code of a closure with an environment of
  length n is in each language (a term, or in Clos5ᵀ a reference to a
  definition).

  A closure is a pair of code and the tuple of its environment, packed
  (pack): the code of a function is a value of type code n only in
  Clos4ᵀ and later, but every language uses the same shape. A value of
  type Any is a value of a flat type tagged with it (dyn); project is
  the only operation that can fail. An environment (or frame) is typed
  by its context.

-}

open import Data.Nat using (ℕ)

module Semantics.Interp.Typed.Values (C : ℕ → Set) where

open import Framework.Primitives using (Base; base-rep; Int)
open import Language.Prim using (Prim; sub; eq)
open import Language.Typed.Type renaming (_≟_ to _≟F_)
open import Semantics.Observation using (Obs; o-const; o-fun; o-tuple; o-inl; o-inr)
open import Semantics.Interp.Clock using (Result; ret; error)

open import Data.Bool using (if_then_else_)
open import Data.Fin using (Fin)
open import Data.Integer using (_-_; _≟_)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Vec using (Vec; []; _∷_; lookup)
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Nullary using (yes; no; does)

data Val : Ty → Set where
  code : ∀ {n} → C n → Val (code n)
  pack : ∀ {n} → Val (code n) → Val ⟪ tup n ⟫ → Val ⟪ fun ⟫
  const : ∀ {B} → base-rep B → Val ⟪ base B ⟫
  tup : ∀ {n} → Vec (Val Any) n → Val ⟪ tup n ⟫
  inl inr : Val Any → Val ⟪ sum ⟫
  dyn : (G : Flat) → Val ⟪ G ⟫ → Val Any

Env : Ctx → Set
Env = All Val

obs : ∀ {A} → Val A → Obs
obs-vec : ∀ {n} → Vec (Val Any) n → List Obs
obs (code _) = o-fun
obs (pack _ _) = o-fun
obs (const {B} c) = o-const B c
obs (tup vs) = o-tuple (obs-vec vs)
obs (inl v) = o-inl (obs v)
obs (inr v) = o-inr (obs v)
obs (dyn G v) = obs v
obs-vec [] = []
obs-vec (v ∷ vs) = obs v ∷ obs-vec vs

{- a primitive on two integers: eq gives inl ⟨⟩ for true -}
δ : ∀ p → Val ⟪ base Int ⟫ → Val ⟪ base Int ⟫ → Val ⟪ out-flat p ⟫
δ sub (const n) (const m) = const (n - m)
δ eq (const n) (const m) = if does (n ≟ m) then inl (dyn (tup 0) (tup [])) else inr (dyn (tup 0) (tup []))

{- component i of a tuple -}
nth : ∀ {n} → Fin n → Val ⟪ tup n ⟫ → Val Any
nth i (tup vs) = lookup vs i

{- the only error: a value of another flat type -}
project? : ∀ t → Val Any → Result (Val ⟪ flat t ⟫)
project? t (dyn G v) with G ≟F flat t
... | yes refl = ret v
... | no _ = error

{- the payload of an injection, to f for inl and g for inr -}
either : ∀ {B : Set} → Val ⟪ sum ⟫ → (Val Any → B) → (Val Any → B) → B
either (inl v) f g = f v
either (inr v) f g = g v

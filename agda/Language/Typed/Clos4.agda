{-

  Clos4ᵀ: Clos4, intrinsically typed. The output of typed delay
  (Compiler/Typed/Delay.agda).

  A closure is a pair of closed code and the tuple of its free
  variables, packed so that its type ⟪ fun ⟫ hides the length n of the
  tuple: ⟪ fun ⟫ is the existential ∃ n. code n × ⟪ tup n ⟫ (typed
  closure conversion, Minamide, Morrisett and Harper, POPL 1996), with
  the length a natural number, since every environment is a tuple of
  values of type Any.

  * code N : code n, for closed code N with the argument (variable 0)
    and the environment (variable 1, of type ⟪ tup n ⟫);
  * call L M N calls the code L with the environment M and the argument N;
  * pack L M : ⟪ fun ⟫ packs code and environment of the same length;
  * unpack L B opens a closure L of some length n and runs B n with the
    environment as variable 0 and the code as variable 1. The body is a
    family of terms, one for each length (an infinitely branching, but
    strictly positive, constructor), so the existential is eliminated
    without a check.

-}

module Language.Typed.Clos4 where

open import Framework.Primitives using (Base; base-rep; Int)
open import Language.Prim using (Prim)
open import Language.Typed.Type

open import Data.Fin using (Fin)
open import Data.List using ([]; _∷_)
open import Data.Nat using (ℕ)
open import Data.Vec using (Vec)

data Tm (Γ : Ctx) : Ty → Set where
  `_ : ∀ {A} → Γ ∋ A → Tm Γ A
  code : ∀ {n} → Tm (Any ∷ ⟪ tup n ⟫ ∷ []) Any → Tm Γ (code n)
  call : ∀ {n} → Tm Γ (code n) → Tm Γ ⟪ tup n ⟫ → Tm Γ Any → Tm Γ Any
  pack : ∀ {n} → Tm Γ (code n) → Tm Γ ⟪ tup n ⟫ → Tm Γ ⟪ fun ⟫
  unpack : Tm Γ ⟪ fun ⟫ → ((n : ℕ) → Tm (⟪ tup n ⟫ ∷ code n ∷ Γ) Any) → Tm Γ Any
  lit : (B : Base) → base-rep B → Tm Γ ⟪ base B ⟫
  tuple : ∀ {n} → Vec (Tm Γ Any) n → Tm Γ ⟪ tup n ⟫
  get : ∀ {n} → Fin n → Tm Γ ⟪ tup n ⟫ → Tm Γ Any
  inl inr : Tm Γ Any → Tm Γ ⟪ sum ⟫
  case : Tm Γ ⟪ sum ⟫ → Tm (Any ∷ Γ) Any → Tm (Any ∷ Γ) Any → Tm Γ Any
  prim : (p : Prim) → Tm Γ ⟪ base Int ⟫ → Tm Γ ⟪ base Int ⟫ → Tm Γ ⟪ out-flat p ⟫
  let′ : Tm Γ Any → Tm (Any ∷ Γ) Any → Tm Γ Any
  inject : (G : Flat) → Tm Γ ⟪ G ⟫ → Tm Γ Any
  project : (G : Flat) → Tm Γ Any → Tm Γ ⟪ G ⟫

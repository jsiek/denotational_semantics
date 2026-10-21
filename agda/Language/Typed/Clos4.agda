{-

  Clos4ᵀ: Clos4, intrinsically typed. The output of typed delay
  (Compiler/Delay.agda).

  A closure is a pair of closed code and the tuple of its free
  variables, packed so that its type ⟪ fun ⟫ hides the length n of the
  tuple: ⟪ fun ⟫ is the existential ∃ n. code n × ⟪ tup n ⟫ (typed
  closure conversion, Minamide, Morrisett and Harper, POPL 1996), with
  the length a natural number, since every environment is a tuple of
  values of type Any.

  * code N : code n, for closed code N with the argument (variable 0)
    and the environment (variable 1, of type ⟪ tup n ⟫);
  * pack L M : ⟪ fun ⟫ packs code and environment of the same length;
  * callc L M opens the closure L and calls its code with its
    environment and the argument M. It is the only elimination of the
    existential, and it is parametric in the length, so it needs no
    check and compiles to one sequence of instructions for every length
    (a body that could depend on the length, as an unpack into a family
    of terms indexed by it, could not be compiled to untyped code).

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
  pack : ∀ {n} → Tm Γ (code n) → Tm Γ ⟪ tup n ⟫ → Tm Γ ⟪ fun ⟫
  callc : Tm Γ ⟪ fun ⟫ → Tm Γ Any → Tm Γ Any
  lit : (B : Base) → base-rep B → Tm Γ ⟪ base B ⟫
  tuple : ∀ {n} → Vec (Tm Γ Any) n → Tm Γ ⟪ tup n ⟫
  get : ∀ {n} → Fin n → Tm Γ ⟪ tup n ⟫ → Tm Γ Any
  inl inr : Tm Γ Any → Tm Γ ⟪ sum ⟫
  case : Tm Γ ⟪ sum ⟫ → Tm (Any ∷ Γ) Any → Tm (Any ∷ Γ) Any → Tm Γ Any
  prim : (p : Prim) → Tm Γ ⟪ base Int ⟫ → Tm Γ ⟪ base Int ⟫ → Tm Γ ⟪ out-flat p ⟫
  let′ : Tm Γ Any → Tm (Any ∷ Γ) Any → Tm Γ Any
  inject : (G : Flat) → Tm Γ ⟪ G ⟫ → Tm Γ Any
  project : (t : Tag) → Tm Γ Any → Tm Γ ⟪ flat t ⟫

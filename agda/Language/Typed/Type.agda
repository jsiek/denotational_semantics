{-

  The types of the typed intermediate languages (Language/Typed/), after
  Essentials of Compilation, ch. 9 (the dynamically typed source becomes
  statically typed by cast insertion, Compiler/Typed/Cast.agda).

  * Any: a value of any flat type, tagged with it.
  * Flat types mirror the values of the untyped languages: a constant of
    a base type (Framework/Primitives), a tuple of n values of type Any, a
    sum (inl or inr of a value of type Any), and a function from Any to
    Any (in Clos2 and Clos3 a closure, in Clos4 a pair of code and
    environment whose length the type hides).
  * code n, in Clos4 only: closed code that takes a tuple of n values
    (its environment) and an argument, both as in Clos3.

  inject G turns a value of flat type G into one of type Any; project G
  turns it back, and is the only operation that can fail: it stops with
  a trapped error (o-error, ω) when the tag is not G. So the flat types
  need decidable equality.

  Contexts are lists of types, variables are typed de Bruijn indices.

-}

module Language.Typed.Type where

open import Framework.Primitives using (Base; Int)
open import Framework.PrimitivesDec using (_≟B_)
open import Language.Prim using (Prim; sub; eq)

open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)
import Data.Nat as N
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Relation.Nullary using (Dec; yes; no)

data Flat : Set where
  base : Base → Flat
  tup : ℕ → Flat
  sum : Flat
  fun : Flat

data Ty : Set where
  Any : Ty
  ⟪_⟫ : Flat → Ty
  code : ℕ → Ty

{- the flat type of a primitive's result: sub gives an integer, eq a
   sum (inl ⟨⟩ for true), as in Language/Prim -}
out-flat : Prim → Flat
out-flat sub = base Int
out-flat eq = sum

{- Decidable equality of flat types ---------------------------------------}

_≟_ : (G H : Flat) → Dec (G ≡ H)
base B ≟ base C with B ≟B C
... | yes refl = yes refl
... | no ne = no λ { refl → ne refl }
tup m ≟ tup n with m N.≟ n
... | yes refl = yes refl
... | no ne = no λ { refl → ne refl }
sum ≟ sum = yes refl
fun ≟ fun = yes refl
base _ ≟ tup _ = no λ ()
base _ ≟ sum = no λ ()
base _ ≟ fun = no λ ()
tup _ ≟ base _ = no λ ()
tup _ ≟ sum = no λ ()
tup _ ≟ fun = no λ ()
sum ≟ base _ = no λ ()
sum ≟ tup _ = no λ ()
sum ≟ fun = no λ ()
fun ≟ base _ = no λ ()
fun ≟ tup _ = no λ ()
fun ≟ sum = no λ ()

{- Contexts and variables -------------------------------------------------}

Ctx : Set
Ctx = List Ty

infix 4 _∋_
data _∋_ : Ctx → Ty → Set where
  Z : ∀ {Γ A} → (A ∷ Γ) ∋ A
  S : ∀ {Γ A B} → Γ ∋ A → (B ∷ Γ) ∋ A

{- the position of a variable, for environments indexed by ℕ -}
idx : ∀ {Γ A} → Γ ∋ A → ℕ
idx Z = zero
idx (S x) = suc (idx x)

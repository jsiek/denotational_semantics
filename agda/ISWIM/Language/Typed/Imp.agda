{-

  Impᵀ: Imp, intrinsically typed. The output of typed lift locals
  (Compiler/LiftLocals.agda), after Essentials of Compilation.

  A body runs in a frame of slots; the frame is typed by a context Δ,
  the types of the slots assigned so far (slot 0, the oldest, last), and
  a slot is a typed index into it (an atom var x, as in Monᵀ), so a slot
  out of the frame, or not yet assigned, cannot be read. x := e₁; e₂
  (assign) evaluates e₁ and assigns its value to the next slot, which
  e₂ sees; case a e₁ e₂ assigns the payload of a to the next slot and
  runs a branch. The frame's size is the deepest nesting of slots, which
  select instructions computes (Compiler/Select.agda). Simple
  expressions, without assignment or control flow, are shared with CFGᵀ.

-}

module Language.Typed.Imp where

open import Language.Prim using (Prim)
open import Language.Typed.Type
open import Language.Typed.Mon using (Atm; var; lit; ref) public

open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All)
open import Data.Nat using (ℕ)
open import Data.Vec using (Vec)
open import Framework.Primitives using (Int)

data Simple (Σ : List ℕ) (Δ : Ctx) : Ty → Set where
  atm : ∀ {A} → Atm Σ Δ A → Simple Σ Δ A
  pack : ∀ {n} → Atm Σ Δ (code n) → Atm Σ Δ ⟪ tup n ⟫ → Simple Σ Δ ⟪ fun ⟫
  callc : Atm Σ Δ ⟪ fun ⟫ → Atm Σ Δ Any → Simple Σ Δ Any
  tuple : ∀ {n} → Vec (Atm Σ Δ Any) n → Simple Σ Δ ⟪ tup n ⟫
  get : ∀ {n} → Fin n → Atm Σ Δ ⟪ tup n ⟫ → Simple Σ Δ Any
  inl inr : Atm Σ Δ Any → Simple Σ Δ ⟪ sum ⟫
  prim : (p : Prim) → Atm Σ Δ ⟪ base Int ⟫ → Atm Σ Δ ⟪ base Int ⟫ → Simple Σ Δ ⟪ out-flat p ⟫
  inject : (G : Flat) → Atm Σ Δ ⟪ G ⟫ → Simple Σ Δ Any
  project : (t : Tag) → Atm Σ Δ Any → Simple Σ Δ ⟪ flat t ⟫

data Exp (Σ : List ℕ) (Δ : Ctx) : Ty → Set where
  simple : ∀ {A} → Simple Σ Δ A → Exp Σ Δ A
  assign : ∀ {A B} → Exp Σ Δ A → Exp Σ (A ∷ Δ) B → Exp Σ Δ B
  case : Atm Σ Δ ⟪ sum ⟫ → Exp Σ (Any ∷ Δ) Any → Exp Σ (Any ∷ Δ) Any → Exp Σ Δ Any

{- a definition starts with its environment in slot 0 and its argument
   in slot 1; main with no slot -}
record Program : Set where
  constructor program
  field
    {table} : List ℕ
    defs : All (λ n → Exp table (Any ∷ ⟪ tup n ⟫ ∷ []) Any) table
    main : Exp table [] Any

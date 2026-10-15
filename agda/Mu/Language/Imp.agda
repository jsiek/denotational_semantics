{-

  Impμ: Imp, intrinsically typed, with recursive types. The output of
  lift locals (Mu/Compiler/LiftLocals.agda); as Impᵀ
  (Language/Typed/Imp.agda), with the types of Monμ.

  A body runs in a frame of slots typed by a context Δ (slot 0, the
  oldest, last); x := e₁; e₂ (assign) assigns the value of e₁ to the
  next slot, which e₂ sees; case a e₁ e₂ assigns the payload of a to the
  next slot and runs a branch. Simple expressions, without assignment or
  control flow, are shared with CFGμ.

-}

module Mu.Language.Imp where

open import Language.Prim using (Prim)
open import Mu.Language.Type
open import Mu.Language.Mon using (DSig; sig; Args; Atm; var; lit; ref) public
open import Mu.Framework.AllUtil using (All)

open import Data.List using (List; []; _∷_)
open import Framework.Primitives using (Int)

data Simple (Σ : List DSig) (Δ : Ctx) : Type → Set where
  atm : ∀ {A} → Atm Σ Δ A → Simple Σ Δ A
  pack : ∀ {Δ' A B} → Atm Σ Δ (code Δ' A B) → Atm Σ Δ (tup Δ') → Simple Σ Δ (A ⇒ B)
  callc : ∀ {A B} → Atm Σ Δ (A ⇒ B) → Atm Σ Δ A → Simple Σ Δ B
  tuple : ∀ {Δ'} → All (Atm Σ Δ) Δ' → Simple Σ Δ (tup Δ')
  get : ∀ {Δ' A} → Δ' ∋ A → Atm Σ Δ (tup Δ') → Simple Σ Δ A
  inl : ∀ {A B} → Atm Σ Δ A → Simple Σ Δ (A ⊹ B)
  inr : ∀ {A B} → Atm Σ Δ B → Simple Σ Δ (A ⊹ B)
  prim : (p : Prim) → Atm Σ Δ (base Int) → Atm Σ Δ (base Int) → Simple Σ Δ (out-ty p)
  fold : ∀ {A c} → Atm Σ Δ (unroll A {c}) → Simple Σ Δ (μ A {c})
  unfold : ∀ {A c} → Atm Σ Δ (μ A {c}) → Simple Σ Δ (unroll A {c})

data Exp (Σ : List DSig) (Δ : Ctx) : Type → Set where
  simple : ∀ {A} → Simple Σ Δ A → Exp Σ Δ A
  assign : ∀ {A B} → Exp Σ Δ A → Exp Σ (A ∷ Δ) B → Exp Σ Δ B
  case : ∀ {A B C} → Atm Σ Δ (A ⊹ B) → Exp Σ (A ∷ Δ) C → Exp Σ (B ∷ Δ) C → Exp Σ Δ C

{- a definition starts with its environment in slot 0 and its argument
   in slot 1; main with no slot -}
record Program (A : Type) : Set where
  constructor program
  field
    {table} : List DSig
    defs : All (λ s → Exp table (Args s) (DSig.cod s)) table
    main : Exp table [] A

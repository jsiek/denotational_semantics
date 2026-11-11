{-

  Impμ: Imp, intrinsically typed, with recursive types. The output of
  lift locals (FPC/Compiler/LiftLocals.agda); as Impᵀ
  (ISWIM/Language/Typed/Imp.agda), with the types of Monμ, but in a
  fixed frame (FPC/Language/Frame.agda).

  A body runs in a frame of slots of fixed types Δ, and an expression
  is typed by the slots initialized where it starts (I : Inits Δ). An
  atom reads an initialized slot. x := e₁; e₂ (assign x e₁ e₂) writes
  the value of e₁ to slot x, which e₂ reads; case a x y e₁ e₂ writes the
  payload of a to slot x and runs e₁ (for inl), or to slot y and runs
  e₂ (for inr). Both write slots that are not initialized, and so a
  write never overwrites a slot that the rest of the expression reads.
  Simple expressions, without assignment or control flow, are shared
  with CFGμ.

-}

module FPC.Language.Imp where

open import Framework.Primitives using (Base; base-rep; Int)
open import Language.Prim using (Prim)
open import FPC.Language.Type
open import FPC.Language.Mon using (DSig; sig; Args) public
open import FPC.Language.Frame public
open import Framework.Membership using (_⊑_)
open import FPC.Framework.AllUtil using (All)

open import Data.List using (List; []; _∷_)

{- atoms: an initialized slot, a literal or a reference to a
   definition -}
data Atm (Σ : List DSig) (Δ : Ctx) (I : Inits Δ) : Type → Set where
  var : ∀ {A} (x : Δ ∋ A) → .(x ∈ I) → Atm Σ Δ I A
  lit : (B : Base) → base-rep B → Atm Σ Δ I (base B)
  ref : ∀ {Δ' A B} → Σ ∋ sig Δ' A B → Atm Σ Δ I (code Δ' A B)

data Simple (Σ : List DSig) (Δ : Ctx) (I : Inits Δ) : Type → Set where
  atm : ∀ {A} → Atm Σ Δ I A → Simple Σ Δ I A
  pair : ∀ {Δ' A B} → Atm Σ Δ I (code Δ' A B) → Atm Σ Δ I (tup Δ')
    → Simple Σ Δ I (A ⇒ B)
  callc : ∀ {A B} → Atm Σ Δ I (A ⇒ B) → Atm Σ Δ I A → Simple Σ Δ I B
  tuple : ∀ {Δ'} → All (Atm Σ Δ I) Δ' → Simple Σ Δ I (tup Δ')
  get : ∀ {Δ' A} → Δ' ∋ A → Atm Σ Δ I (tup Δ') → Simple Σ Δ I A
  inl : ∀ {A B} → Atm Σ Δ I A → Simple Σ Δ I (A ⊹ B)
  inr : ∀ {A B} → Atm Σ Δ I B → Simple Σ Δ I (A ⊹ B)
  prim : (p : Prim) → Atm Σ Δ I (base Int) → Atm Σ Δ I (base Int)
    → Simple Σ Δ I (out-ty p)
  fold : ∀ {A} → Atm Σ Δ I (unroll A) → Simple Σ Δ I (μ A)
  unfold : ∀ {A} → Atm Σ Δ I (μ A) → Simple Σ Δ I (unroll A)

data Exp (Σ : List DSig) (Δ : Ctx) (I : Inits Δ) : Type → Set where
  simple : ∀ {A} → Simple Σ Δ I A → Exp Σ Δ I A
  assign : ∀ {A B} (x : Δ ∋ A) → .(x ∉ I) → Exp Σ Δ I A
    → Exp Σ Δ (I ⊕ x) B → Exp Σ Δ I B
  case : ∀ {A B C} → Atm Σ Δ I (A ⊹ B)
    → (x : Δ ∋ A) → .(x ∉ I) → (y : Δ ∋ B) → .(y ∉ I)
    → Exp Σ Δ (I ⊕ x) C → Exp Σ Δ (I ⊕ y) C → Exp Σ Δ I C

{- a body with parameters Γ: its frame, the slots of the parameters (a
   suffix of the frame, initialized at the start) and its expression -}
record Body (Σ : List DSig) (Γ : Ctx) (A : Type) : Set where
  constructor body
  field
    frame : Ctx
    params : Γ ⊑ frame
    exp : Exp Σ frame (initial params) A

{- a definition starts with its environment in slot 0 and its argument
   in slot 1 (the parameters Args s); main with no parameter -}
record Program (A : Type) : Set where
  constructor program
  field
    {table} : List DSig
    defs : All (λ s → Body table (Args s) (DSig.cod s)) table
    main : Body table [] A

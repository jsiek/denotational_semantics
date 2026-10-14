{-

  Monᵀ: monadic normal form of Clos5ᵀ, intrinsically. The output of
  typed remove complex operands (Compiler/Typed/RCO.agda).

  An atom is a variable, a literal or a reference to a definition. The
  operands of every operation, and the scrutinee of case, are atoms; the
  right-hand side and body of let and the branches of case are
  expressions. Untyped Mon is a predicate on Clos5 terms; Monᵀ is its own
  syntax, so that monadic form needs no proof, and its meaning is that
  of its embedding into Clos5ᵀ (⌜_⌝), so that it needs no semantics of
  its own.

-}

module Language.Typed.Mon where

open import Framework.Primitives using (Base; base-rep; Int)
open import Language.Prim using (Prim)
open import Language.Typed.Type
import Language.Typed.Clos5 as C

open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Nat using (ℕ)
open import Data.Vec using (Vec; []; _∷_)

data Atm (Σ : List ℕ) (Γ : Ctx) : Ty → Set where
  var : ∀ {A} → Γ ∋ A → Atm Σ Γ A
  lit : (B : Base) → base-rep B → Atm Σ Γ ⟪ base B ⟫
  ref : ∀ {n} → Σ ∋ n → Atm Σ Γ (code n)

data Exp (Σ : List ℕ) (Γ : Ctx) : Ty → Set where
  atm : ∀ {A} → Atm Σ Γ A → Exp Σ Γ A
  pack : ∀ {n} → Atm Σ Γ (code n) → Atm Σ Γ ⟪ tup n ⟫ → Exp Σ Γ ⟪ fun ⟫
  callc : Atm Σ Γ ⟪ fun ⟫ → Atm Σ Γ Any → Exp Σ Γ Any
  tuple : ∀ {n} → Vec (Atm Σ Γ Any) n → Exp Σ Γ ⟪ tup n ⟫
  get : ∀ {n} → Fin n → Atm Σ Γ ⟪ tup n ⟫ → Exp Σ Γ Any
  inl inr : Atm Σ Γ Any → Exp Σ Γ ⟪ sum ⟫
  case : Atm Σ Γ ⟪ sum ⟫ → Exp Σ (Any ∷ Γ) Any → Exp Σ (Any ∷ Γ) Any → Exp Σ Γ Any
  prim : (p : Prim) → Atm Σ Γ ⟪ base Int ⟫ → Atm Σ Γ ⟪ base Int ⟫ → Exp Σ Γ ⟪ out-flat p ⟫
  let′ : ∀ {A B} → Exp Σ Γ A → Exp Σ (A ∷ Γ) B → Exp Σ Γ B
  inject : (G : Flat) → Atm Σ Γ ⟪ G ⟫ → Exp Σ Γ Any
  project : (t : Tag) → Atm Σ Γ Any → Exp Σ Γ ⟪ flat t ⟫

record Program : Set where
  constructor program
  field
    {table} : List ℕ
    defs : All (λ n → Exp table (Any ∷ ⟪ tup n ⟫ ∷ []) Any) table
    main : Exp table [] Any

{- renaming the variables of an atom -}
ren : ∀ {Σ Γ Δ A} → (∀ {B} → Γ ∋ B → Δ ∋ B) → Atm Σ Γ A → Atm Σ Δ A
ren r (var x) = var (r x)
ren r (lit B c) = lit B c
ren r (ref f) = ref f

{- The embedding into Clos5ᵀ: the meaning of a Monᵀ program -}

⌜_⌝ᵃ : ∀ {Σ Γ A} → Atm Σ Γ A → C.Tm Σ Γ A
⌜ var x ⌝ᵃ = C.` x
⌜ lit B c ⌝ᵃ = C.lit B c
⌜ ref f ⌝ᵃ = C.fun-ref f

⌜_⌝ᵛ : ∀ {Σ Γ n} → Vec (Atm Σ Γ Any) n → Vec (C.Tm Σ Γ Any) n
⌜ [] ⌝ᵛ = []
⌜ a ∷ as ⌝ᵛ = ⌜ a ⌝ᵃ ∷ ⌜ as ⌝ᵛ

⌜_⌝ : ∀ {Σ Γ A} → Exp Σ Γ A → C.Tm Σ Γ A
⌜ atm a ⌝ = ⌜ a ⌝ᵃ
⌜ pack a b ⌝ = C.pack ⌜ a ⌝ᵃ ⌜ b ⌝ᵃ
⌜ callc a b ⌝ = C.callc ⌜ a ⌝ᵃ ⌜ b ⌝ᵃ
⌜ tuple as ⌝ = C.tuple ⌜ as ⌝ᵛ
⌜ get i a ⌝ = C.get i ⌜ a ⌝ᵃ
⌜ inl a ⌝ = C.inl ⌜ a ⌝ᵃ
⌜ inr a ⌝ = C.inr ⌜ a ⌝ᵃ
⌜ case a M N ⌝ = C.case ⌜ a ⌝ᵃ ⌜ M ⌝ ⌜ N ⌝
⌜ prim p a b ⌝ = C.prim p ⌜ a ⌝ᵃ ⌜ b ⌝ᵃ
⌜ let′ M N ⌝ = C.let′ ⌜ M ⌝ ⌜ N ⌝
⌜ inject G a ⌝ = C.inject G ⌜ a ⌝ᵃ
⌜ project t a ⌝ = C.project t ⌜ a ⌝ᵃ

⌜_⌝ₚ : Program → C.Program
⌜ program ds M ⌝ₚ = C.program (defs ds) ⌜ M ⌝
  where
  defs : ∀ {Σ ns} → All (λ n → Exp Σ (Any ∷ ⟪ tup n ⟫ ∷ []) Any) ns → All (C.Code Σ) ns
  defs [] = []
  defs (D ∷ ds) = ⌜ D ⌝ ∷ defs ds

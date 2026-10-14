{-

  CFGᵀ: CFG, intrinsically typed. The output of typed explicate control
  (Compiler/Typed/Explicate.agda), after Essentials of Compilation.

  A body is a control-flow graph of blocks; a block is a tail, typed by
  the frame context Δ it starts in (the types of the slots it may read,
  as in Impᵀ) and by the list Bs of the frame contexts of the blocks it
  may jump to. A label is a typed index into Bs, so a jump to a missing
  block, or to a block that reads a slot not assigned, cannot be
  written. The blocks of a body are listed newest first and each is
  typed over the blocks older than it (Blocks), so control flow is
  acyclic, as in CFG; the start may jump to any block.

  * return s: the value of s;
  * seq p s t: slot k := s, then t, where k is the length of Δ' (p : Δ' ⊑ Δ):
    the slots from k on are forgotten (they belong to a finished scope)
    and slot k is assigned anew;
  * goto l;
  * case a p l₁ l₂: slot k := the payload of the injection a, then jump to
    l₁ for inl and l₂ for inr.

-}

module Language.Typed.CFG where

open import Language.Typed.Type
open import Framework.Membership using (_⊑_)
open import Language.Typed.Imp using (Atm; Simple) public

open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All)
open import Data.Nat using (ℕ)

data Tail (Σ : List ℕ) (Bs : List Ctx) (Δ : Ctx) : Set where
  return : Simple Σ Δ Any → Tail Σ Bs Δ
  seq : ∀ {Δ' A} → Δ' ⊑ Δ → Simple Σ Δ A → Tail Σ Bs (A ∷ Δ') → Tail Σ Bs Δ
  goto : Bs ∋ Δ → Tail Σ Bs Δ
  case : ∀ {Δ'} → Atm Σ Δ ⟪ sum ⟫ → Δ' ⊑ Δ → Bs ∋ (Any ∷ Δ') → Bs ∋ (Any ∷ Δ') → Tail Σ Bs Δ

{- the blocks of a body, newest first, each over the older ones -}
data Blocks (Σ : List ℕ) : List Ctx → Set where
  [] : Blocks Σ []
  _▷_ : ∀ {Bs Δ} → Blocks Σ Bs → Tail Σ Bs Δ → Blocks Σ (Δ ∷ Bs)

record Body (Σ : List ℕ) (Δ : Ctx) : Set where
  constructor body
  field
    {labels} : List Ctx
    blocks : Blocks Σ labels
    start : Tail Σ labels Δ

record Program : Set where
  constructor program
  field
    {table} : List ℕ
    defs : All (λ n → Body table (Any ∷ ⟪ tup n ⟫ ∷ [])) table
    main : Body table []

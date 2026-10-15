{-

  CFGμ: CFG, intrinsically typed, with recursive types. The output of
  explicate control (Mu/Compiler/Explicate.agda); as CFGᵀ
  (Language/Typed/CFG.agda), with the types of Impμ.

  A body is a control-flow graph of blocks; a block is a tail, typed by
  the type R of the body's result, the frame context Δ it starts in and
  the list Bs of the frame contexts of the blocks it may jump to. The
  blocks of a body are listed newest first and each is typed over the
  blocks older than it (Blocks), so control flow is acyclic.

  * return s: the value of s;
  * seq p s t: slot k := s, then t, where k is the length of Δ' (p : Δ' ⊑ Δ);
  * goto l;
  * case a p l₁ l₂: slot k := the payload of the injection a, then jump to
    l₁ for inl (whose block reads the slot at the left type) and l₂ for
    inr (at the right type).

-}

module Mu.Language.CFG where

open import Mu.Language.Type
open import Framework.Membership using (_⊑_)
open import Mu.Language.Imp using (Sig; sig; Args; Atm; Simple) public
open import Mu.Framework.AllUtil using (All)

open import Data.List using (List; []; _∷_)

data Tail (Σ : List Sig) (R : Type) (Bs : List Ctx) (Δ : Ctx) : Set where
  return : Simple Σ Δ R → Tail Σ R Bs Δ
  seq : ∀ {Δ' A} → Δ' ⊑ Δ → Simple Σ Δ A → Tail Σ R Bs (A ∷ Δ') → Tail Σ R Bs Δ
  goto : Bs ∋ Δ → Tail Σ R Bs Δ
  case : ∀ {Δ' A B} → Atm Σ Δ (A ⊹ B) → Δ' ⊑ Δ → Bs ∋ (A ∷ Δ') → Bs ∋ (B ∷ Δ') → Tail Σ R Bs Δ

{- the blocks of a body, newest first, each over the older ones -}
data Blocks (Σ : List Sig) (R : Type) : List Ctx → Set where
  [] : Blocks Σ R []
  _▷_ : ∀ {Bs Δ} → Blocks Σ R Bs → Tail Σ R Bs Δ → Blocks Σ R (Δ ∷ Bs)

record Body (Σ : List Sig) (R : Type) (Δ : Ctx) : Set where
  constructor body
  field
    {labels} : List Ctx
    blocks : Blocks Σ R labels
    start : Tail Σ R labels Δ

record Program (A : Type) : Set where
  constructor program
  field
    {table} : List Sig
    defs : All (λ s → Body table (Sig.cod s) (Args s)) table
    main : Body table A []

{- block l of the blocks, with the blocks older than it (those it may
   jump to) -}
record Blk (Σ : List Sig) (R : Type) (Δ : Ctx) : Set where
  constructor blk
  field
    {older} : List Ctx
    blocks : Blocks Σ R older
    tail : Tail Σ R older Δ

block : ∀ {Σ R Bs Δ} → Blocks Σ R Bs → Bs ∋ Δ → Blk Σ R Δ
block (bs ▷ t) Z = blk bs t
block (bs ▷ t) (S l) = block bs l

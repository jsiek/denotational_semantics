{-

  CFGμ: CFG, intrinsically typed, with recursive types. The output of
  explicate control (FPC/Compiler/Explicate.agda); as CFGᵀ
  (ISWIM/Language/Typed/CFG.agda), with the types of Impμ, in its fixed
  frame (FPC/Language/Frame.agda).

  A body is a control-flow graph of blocks; a block is a tail, typed by
  the type R of the body's result, the frame Δ, the slots I initialized
  where it starts and the list Bs of those of the blocks it may jump
  to. The blocks of a body are listed newest first and each is typed
  over the blocks older than it (Blocks), so control flow is acyclic.

  * return s: the value of s;
  * seq x s p t: slot x := s, then t, which starts with the slots J
    (p : J ⊆ I ⊕ x: t may forget slots that it does not read);
  * goto l;
  * case a x y l₁ l₂: slot x := the payload of the injection a and jump
    to l₁ for inl, or slot y := the payload and jump to l₂ for inr.

-}

module FPC.Language.CFG where

open import FPC.Language.Type
open import Framework.Membership using (_⊑_)
open import FPC.Language.Imp using (DSig; sig; Args; Atm; Simple; Inits; _⊕_;
  _⊆_; initial) public
open import FPC.Framework.AllUtil using (All)

open import Data.List using (List; []; _∷_)

data Tail (Σ : List DSig) (R : Type) (Δ : Ctx) (Bs : List (Inits Δ))
  (I : Inits Δ) : Set where
  return : Simple Σ Δ I R → Tail Σ R Δ Bs I
  seq : ∀ {A J} (x : Δ ∋ A) → Simple Σ Δ I A → .(J ⊆ I ⊕ x)
    → Tail Σ R Δ Bs J → Tail Σ R Δ Bs I
  goto : Bs ∋ I → Tail Σ R Δ Bs I
  case : ∀ {A B} → Atm Σ Δ I (A ⊹ B) → (x : Δ ∋ A) (y : Δ ∋ B)
    → Bs ∋ (I ⊕ x) → Bs ∋ (I ⊕ y) → Tail Σ R Δ Bs I

{- the blocks of a body, newest first, each over the older ones -}
data Blocks (Σ : List DSig) (R : Type) (Δ : Ctx) : List (Inits Δ) → Set where
  [] : Blocks Σ R Δ []
  _▷_ : ∀ {Bs I} → Blocks Σ R Δ Bs → Tail Σ R Δ Bs I
    → Blocks Σ R Δ (I ∷ Bs)

{- a body with parameters Γ: its frame, the slots of the parameters, its
   blocks and its start -}
record Body (Σ : List DSig) (R : Type) (Γ : Ctx) : Set where
  constructor body
  field
    frame : Ctx
    params : Γ ⊑ frame
    {labels} : List (Inits frame)
    blocks : Blocks Σ R frame labels
    start : Tail Σ R frame labels (initial params)

record Program (A : Type) : Set where
  constructor program
  field
    {table} : List DSig
    defs : All (λ s → Body table (DSig.cod s) (Args s)) table
    main : Body table A []

{- block l of the blocks, with the blocks older than it (those it may
   jump to) -}
record Blk (Σ : List DSig) (R : Type) (Δ : Ctx) (I : Inits Δ) : Set where
  constructor blk
  field
    {older} : List (Inits Δ)
    blocks : Blocks Σ R Δ older
    tail : Tail Σ R Δ older I

block : ∀ {Σ R Δ Bs I} → Blocks Σ R Δ Bs → Bs ∋ I → Blk Σ R Δ I
block (bs ▷ t) Z = blk bs t
block (bs ▷ t) (S l) = block bs l

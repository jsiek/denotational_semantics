module Language.CFG where
{-

 CFG, the language after the explicate-control pass
 (Compiler/Explicate.agda), a C-like language after Essentials of
 Compilation: each body is a control-flow graph of blocks, and control
 flows only by goto, by the branches of case, and by return.

 A block is a tail: a sequence of assignments x := s of simple
 expressions (Language/Imp.agda), ending in return s, in a goto, or in
 case a x l₁ l₂, which assigns the payload of the injection a to slot x
 and jumps to block l₁ or l₂. Frames and slots are as in Imp, and so are
 calls, which are simple expressions; there is no nesting of control
 flow inside expressions, so a body returns a value, not a frame.

 The blocks of a body are listed newest first, as the global definitions
 are in Clos5: block l is the one with l blocks before it, and it may
 jump only to older blocks (labels below l); the start of a body may
 jump to any block. A jump to any other label goes wrong. So control
 flow within a body is acyclic, as is the code that explicate control
 produces (the language has no loops; recursion goes through calls).

 Informally, the semantics: a tail runs in a frame and produces a value.
 x := s; t evaluates s, assigns its value to slot x and runs t; return s
 produces the value of s; goto l runs block l; case a x l₁ l₂ assigns the
 payload of a to slot x and runs block l₁ if a is inl, l₂ if it is inr,
 and goes wrong otherwise. Reading or assigning a slot beyond the frame
 goes wrong. A call runs the start of the callee's body in a fresh frame,
 as in Imp.

-}

open import Language.Imp using (Atm; Simple) public

open import Data.List using (List; []; _∷_; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _≟_)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (yes; no)

data Tail : Set where
  return : Simple → Tail
  seq : ℕ → Simple → Tail → Tail           {- x := s; t -}
  goto : ℕ → Tail
  case : Atm → ℕ → ℕ → ℕ → Tail            {- case a: x := the payload; goto l₁ or l₂ -}

{- a body: the number of slots of its frame, its blocks (newest first),
   and its start -}
record Body : Set where
  constructor body
  field
    locals : ℕ
    blocks : List Tail
    start : Tail

{- the global definitions are listed newest first, as in Clos5 -}
record Program : Set where
  constructor program
  field
    defs : List Body
    main : Body

{- block l among bs (newest first), with the blocks older than it -}
block : List Tail → ℕ → Maybe (Tail × List Tail)
block [] l = nothing
block (t ∷ bs) l with l ≟ length bs
... | yes _ = just (t , bs)
... | no _ = block bs l

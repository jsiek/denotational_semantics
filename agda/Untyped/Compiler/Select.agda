module Untyped.Compiler.Select where
{-

 The select-instructions pass (CFG → X86), after Essentials of
 Compilation: each statement of a block becomes a few instructions, and
 the blocks keep their labels.

 - x := r computes r into x; return r computes r into %rax and returns.
 - Subtraction is two-address: a - b goes through %rax (movq a, %rax;
   subq b, %rax; movq %rax, x), so it is right also when x is b.
 - Equality compares and sets: cmpq b, a; sete x.
 - A call passes the free variables in %rdi and the argument in %rsi,
   and takes the result from %rax; the start of each global definition
   moves %rdi and %rsi to slots 0 and 1, where its body expects them.
 - case a x l₁ l₂ tests the tag of a, loads the payload into x, and
   jumps: testinl a; load payload a, x; je l₁ l₂.

-}

open import Untyped.Language.Imp as Imp using (Atm; var; lit; fun-ref; Simple)
open import Language.Prim using (sub; eq)
open import Untyped.Language.CFG as CFG using (Tail; return; seq; goto; case)
open import Language.X86

open import Data.List using (List; []; _∷_; _++_; map)

select-atm : Atm → Arg
select-atm (var x) = loc (var x)
select-atm (lit B k) = imm B k
select-atm (fun-ref k) = label k

{- r, computed into d -}
select-simple : Simple → Loc → List Instr
select-simple (Imp.atm a) d = movq (select-atm a) d ∷ []
select-simple (Imp.app f e a) d =
  movq (select-atm e) (reg rdi) ∷ movq (select-atm a) (reg rsi) ∷ callq (select-atm f)
  ∷ movq (loc (reg rax)) d ∷ []
select-simple (Imp.pair a b) d = alloc pair (select-atm a ∷ select-atm b ∷ []) d ∷ []
select-simple (Imp.fst a) d = load fst (select-atm a) d ∷ []
select-simple (Imp.snd a) d = load snd (select-atm a) d ∷ []
select-simple (Imp.tuple as) d = alloc tuple (map select-atm as) d ∷ []
select-simple (Imp.get i a) d = load (get i) (select-atm a) d ∷ []
select-simple (Imp.inl a) d = alloc inl (select-atm a ∷ []) d ∷ []
select-simple (Imp.inr a) d = alloc inr (select-atm a ∷ []) d ∷ []
select-simple (Imp.prim sub a b) d =
  movq (select-atm a) (reg rax) ∷ subq (select-atm b) (reg rax) ∷ movq (loc (reg rax)) d ∷ []
select-simple (Imp.prim eq a b) d = cmpq (select-atm b) (select-atm a) ∷ sete d ∷ []

select-tail : Tail → Block
select-tail (return r) = block (select-simple r (reg rax)) retq
select-tail (seq x r t) =
  block (select-simple r (var x) ++ Block.instrs (select-tail t)) (Block.jump (select-tail t))
select-tail (goto l) = block [] (jmp l)
select-tail (case a x l₁ l₂) =
  block (testinl (select-atm a) ∷ load payload (select-atm a) (var x) ∷ []) (je l₁ l₂)

{- the start of a global definition takes its parameters from the registers -}
prologue : List Instr
prologue = movq (loc (reg rdi)) (var 0) ∷ movq (loc (reg rsi)) (var 1) ∷ []

select-body : List Instr → CFG.Body → Body
select-body pre (CFG.body n bs t) =
  body n (map select-tail bs) (block (pre ++ Block.instrs (select-tail t)) (Block.jump (select-tail t)))

{- the pass, for a whole program -}
select : CFG.Program → Program
select (CFG.program ds b) = program (map (select-body prologue) ds) (select-body [] b)

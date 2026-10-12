module Compiler.Lang.X86 where
{-

 X86, the language after the select-instructions pass
 (Compile/Select.agda): x86 with variables, after Essentials of
 Compilation, over abstract values.

 A body is a control-flow graph of blocks, as in CFG (Lang/CFG.agda),
 but a block is a sequence of instructions ending in a jump. The
 locations are the slots of the current frame (the variables) and the
 registers %rax, %rdi and %rsi; an operand is a location, an immediate,
 or the label of a global definition. Besides the locations, the
 machine has a flag, set by comparisons and tests and read by sete and
 je.

 The values are those of the earlier languages: integers, code
 pointers, pairs, tuples and injections. The heap is abstract: alloc
 builds a pair, tuple or injection from its operands, and load takes a
 field of one; there are no addresses.

 Informally, the semantics of the instructions, which run in a frame and
 a register file and go wrong where stated:
   movq a, d          d := a
   subq a, d          d := d - a; both integers
   cmpq a₂, a₁        flag := (a₁ = a₂); both integers
   sete d             d := inl ⟨⟩ if the flag is set, inr ⟨⟩ if not;
                      no flag goes wrong
   testinl a          flag := whether a is an inl; a an injection
   alloc s as, d      d := the object of shape s with fields as
                      (a pair of two, a tuple of any number, an
                      injection of one)
   load f a, d        d := field f of a: fst or snd of a pair, the i-th
                      component of a tuple of n, the payload of an
                      injection
   callq a            a must be a code pointer, to definition k: run the
                      body of definition k with %rdi and %rsi as they
                      are, and continue with %rax as it returns; the
                      caller's frame is untouched (the registers and the
                      flag are not saved)
 A block ends with retq (return %rax), jmp l, or je l₁ l₂ (jump to l₁ if
 the flag is set and to l₂ if not; no flag goes wrong). Reading or
 assigning a slot beyond the frame goes wrong. Jumps are as in CFG:
 blocks are listed newest first, block l may jump only to older blocks,
 and the start of a body to any block. A body runs in a fresh frame of
 max(2, locals) slots holding 0 (the start of a global definition first
 moves %rdi and %rsi, its free variables and argument, to slots 0 and
 1); main runs with the registers holding 0 and no flag.

-}

open import Primitives using (Base; base-rep)

open import Data.Fin using (Fin)
open import Data.List using (List)
open import Data.Nat using (ℕ)

data Reg : Set where
  rax rdi rsi : Reg

data Loc : Set where
  var : ℕ → Loc                           {- a slot of the current frame -}
  reg : Reg → Loc

data Arg : Set where
  loc : Loc → Arg
  imm : (B : Base) → base-rep B → Arg
  label : ℕ → Arg                         {- the code of a global definition -}

{- the objects that alloc builds -}
data Shape : Set where
  pair tuple inl inr : Shape

{- the fields that load takes -}
data Field : Set where
  fst snd : Field
  get : ∀ {n} → Fin n → Field
  payload : Field

data Instr : Set where
  movq : Arg → Loc → Instr
  subq : Arg → Loc → Instr
  cmpq : Arg → Arg → Instr
  sete : Loc → Instr
  testinl : Arg → Instr
  alloc : Shape → List Arg → Loc → Instr
  load : Field → Arg → Loc → Instr
  callq : Arg → Instr

data Jump : Set where
  retq : Jump
  jmp : ℕ → Jump
  je : ℕ → ℕ → Jump

record Block : Set where
  constructor block
  field
    instrs : List Instr
    jump : Jump

{- a body: the number of slots of its frame, its blocks (newest first),
   and its start -}
record Body : Set where
  constructor body
  field
    locals : ℕ
    blocks : List Block
    start : Block

record Program : Set where
  constructor program
  field
    defs : List Body
    main : Body

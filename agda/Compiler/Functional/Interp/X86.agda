{-

  A clocked interpreter for X86 (Lang/X86.agda), the output of select
  instructions. The machine state is a frame (the slots, as in Imp and
  CFG) and a register file: %rax, %rdi and %rsi each hold a value or
  are unset, and the flag is set (true or false) or unset; reading an
  unset register or flag goes wrong. The values and the
  operations on them are those of Clos5 (Interp/Clos5.agda): subq is
  prim? sub, cmpq compares integers as prim? eq does, and alloc and load
  build and take apart pairs, tuples and injections.

  A block runs its instructions in order, each passing the state on to
  the rest (continuation-passing, so the instructions of a block nest),
  then its jump: retq returns %rax, jmp l and je l₁ l₂ jump. callq a
  reads a, %rdi and %rsi, checks that a is a code pointer (as in CFG),
  and runs the start of the callee's body in a fresh frame
  (max(2, locals) slots of 0) with %rdi and %rsi as they are, %rax unset
  and no flag; the caller continues in its own frame with %rax the
  result and %rdi, %rsi and the flag unset. main runs in a frame of
  locals zeros, with %rax 0 and the rest unset.

  As in CFG (Interp/CFG.agda), only calls tick the clock (see the design
  note in Clock.agda), and a jump to l walks the list of blocks it may
  jump to (newest first) and runs block l with the blocks older than
  it, so the interpreter is structurally recursive on the clock, the
  list of blocks, and the instructions of a block.

-}

module Compiler.Functional.Interp.X86 where

open import Compiler.Lang.X86
open import Compiler.Lang.Prim using (sub; eq; Out; int; bool)
open import Compiler.Observation using (δ?)
open import Framework.ListUtil using (_‼_)
open import Compiler.Functional.Clock
open import Compiler.Functional.Interp.Clos5
  using (Val; code; pair; const; tup; inl; inr; obs; out; prim?; project; first; second)
open import Compiler.Functional.Interp.Imp using (Frame; zero-val; _[_]≔_)

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; []; _∷_; reverse; replicate; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _∸_; _≟_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (yes; no)

record Regs : Set where
  constructor regs
  field
    %rax %rdi %rsi : Maybe Val
    flag : Maybe Bool
open Regs public

State : Set
State = Frame × Regs

{- the value at a location -}
read : State → Loc → Result Val
read (φ , ρ) (var x) = from-maybe (φ ‼ x)
read (φ , ρ) (reg rax) = from-maybe (%rax ρ)
read (φ , ρ) (reg rdi) = from-maybe (%rdi ρ)
read (φ , ρ) (reg rsi) = from-maybe (%rsi ρ)

{- the value of an operand -}
arg : State → Arg → Result Val
arg s (loc l) = read s l
arg s (imm B k) = ret (const B k)
arg s (label k) = ret (code k)

{- the values of the operands, onto vs in reverse, then k -}
args : ∀ {A : Set} → State → List Val → List Arg → (List Val → Result A) → Result A
args s vs [] k = k vs
args s vs (a ∷ as) k = do v ← arg s a; args s (v ∷ vs) as k

{- d := v, then k -}
write : ∀ {A : Set} → State → Loc → Val → (State → Result A) → Result A
write (φ , ρ) (var x) v k = do φ' ← from-maybe (φ [ x ]≔ v); k (φ' , ρ)
write (φ , ρ) (reg rax) v k = k (φ , record ρ { %rax = just v })
write (φ , ρ) (reg rdi) v k = k (φ , record ρ { %rdi = just v })
write (φ , ρ) (reg rsi) v k = k (φ , record ρ { %rsi = just v })

{- flag := b, then k -}
set-flag : ∀ {A : Set} → State → Bool → (State → Result A) → Result A
set-flag (φ , ρ) b k = k (φ , record ρ { flag = just b })

{- the truth value of an equality -}
bool? : Out → Result Bool
bool? (bool b) = ret b
bool? (int n) = wrong

{- whether an injection is an inl -}
tag? : Val → Result Bool
tag? (inl v) = ret true
tag? (inr v) = ret false
tag? _ = wrong

alloc? : Shape → List Val → Result Val
alloc? pair (v ∷ w ∷ []) = ret (pair v w)
alloc? tuple vs = ret (tup vs)
alloc? inl (v ∷ []) = ret (inl v)
alloc? inr (v ∷ []) = ret (inr v)
alloc? _ _ = wrong

load? : Field → Val → Result Val
load? fst v = first v
load? snd v = second v
load? (get i) v = project i v
load? payload (inl v) = ret v
load? payload (inr v) = ret v
load? payload _ = wrong

{- an instruction other than callq, then k -}
step : ∀ {A : Set} → State → Instr → (State → Result A) → Result A
step s (movq a d) k = do v ← arg s a; write s d v k
step s (subq a d) k = do w ← arg s a; v ← read s d; u ← from-maybe (prim? sub v w); write s d u k
step s (cmpq a₂ a₁) k =
  do v ← arg s a₁; w ← arg s a₂; o ← from-maybe (δ? eq (obs v) (obs w)); b ← bool? o; set-flag s b k
step s (sete d) k = do b ← from-maybe (flag (proj₂ s)); write s d (out (bool b)) k
step s (testinl a) k = do v ← arg s a; b ← tag? v; set-flag s b k
step s (alloc sh as d) k = args s [] as λ vs → do v ← alloc? sh (reverse vs); write s d v k
step s (load f a d) k = do v ← arg s a; w ← load? f v; write s d w k
step s (callq a) k = wrong                   {- run handles callq -}

{- the interpreter for a program with global definitions ds -}
module _ (ds : List Body) where

  {- the definition a code pointer refers to, counting from the oldest -}
  code? : Val → Maybe Body
  code? (code k) = reverse ds ‼ k
  code? _ = nothing

  {- the instructions is, then the jump j, which may jump to the blocks bs -}
  run : ℕ → List Block → State → List Instr → Jump → Result Val
  {- jmp l, among the blocks bs -}
  jump : ℕ → List Block → State → ℕ → Result Val
  call : ℕ → Maybe Body → Val → Val → Result Val

  run ck bs (φ , ρ) (callq a ∷ is) j =
    do f ← arg (φ , ρ) a; e ← from-maybe (%rdi ρ); w ← from-maybe (%rsi ρ); v ← call ck (code? f) e w
       run ck bs (φ , regs (just v) nothing nothing nothing) is j
  run ck bs s (i ∷ is) j = step s i λ s' → run ck bs s' is j
  run ck bs (φ , ρ) [] retq = from-maybe (%rax ρ)
  run ck bs s [] (jmp l) = jump ck bs s l
  run ck bs s [] (je l₁ l₂) = do b ← from-maybe (flag (proj₂ s)); jump ck bs s (if b then l₁ else l₂)

  jump ck [] s l = wrong
  jump ck (block is j ∷ bs) s l with l ≟ length bs
  ... | yes _ = run ck bs s is j
  ... | no _ = jump ck bs s l

  call ck nothing e w = wrong
  call zero (just b) e w = timeout
  call (suc ck) (just (body n bs (block is j))) e w =
    run ck bs (zero-val ∷ zero-val ∷ replicate (n ∸ 2) zero-val , regs nothing (just e) (just w) nothing) is j

{- a program starts with main, in a frame of zeros -}
sem : Program → Semantics
sem (program ds (body n bs (block is j))) =
  semantics Val obs (λ ck → run ds ck bs (replicate n zero-val , regs (just zero-val) nothing nothing nothing) is j)

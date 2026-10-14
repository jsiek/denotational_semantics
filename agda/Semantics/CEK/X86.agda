{-

  An abstract machine for X86 (Language/X86.agda), one instruction (or
  jump) per step. Values are those of the Clos5 machine, and frames are
  lists of slots (Semantics/CEK/Values.agda). A state
    run is j bs σ f φ ρ
  runs the instructions is and then the jump j, with the blocks bs that
  j may jump to (as in CFG: those older than the current block, or all
  of the body's at its start), the call stack σ, the flag f (if set),
  the frame φ and the registers ρ (each holds a value or is unset).

  The instructions are as in the header of Language/X86.agda; each errors
  on an operand that is unset or beyond the frame, on a value of the
  wrong kind, or on a destination beyond the frame. The primitives (subq,
  cmpq) are those of the earlier machines (prim?, δ?). alloc reads its
  operands left to right and builds an object of its shape and arity;
  load takes a field.

  callq a, with a code k and %rdi and %rsi set, pushes the caller's
  remaining instructions, jump, blocks and frame, and runs the start of
  definition k in a fresh frame of max(2, locals) slots of zeros, with
  %rdi and %rsi as they are, %rax unset and no flag. retq reads %rax:
  to the empty stack it stops with the observation of %rax; otherwise it
  pops the caller, which continues with %rax as it is and %rdi, %rsi
  and the flag unset (clobbered by the call). jmp l and je l₁ l₂ run block l of bs,
  with the blocks older than it; a missing block, or je with no flag,
  errors. main runs in a frame of locals zeros, with %rax holding 0,
  %rdi and %rsi unset and no flag.

-}

module Semantics.CEK.X86 where

open import Framework.Primitives using (Int)
open import Language.X86
open import Language.Prim using (sub; eq; Out; bool)
open import Semantics.Observation
open import Semantics.CEK.Smallstep using (Machine; Next; next; stop; machine)
open import Semantics.CEK.Values
open import Semantics.CEK.Values using (Frame; _[_]≔_; zeros) public
  using (Val; code; pair; const; tup; inl; inr; obs; out; prim?) public
open import Framework.ListUtil using (_‼_; proj)

open import Data.Bool using (Bool; true; false)
open import Data.Integer using (0ℤ)
open import Data.List using (List; []; _∷_; length; reverse)
open import Data.Maybe using (Maybe; just; nothing; _>>=_)
open import Data.Nat using (ℕ; _≟_; _+_; _∸_)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (yes; no)

Regs : Set
Regs = Reg → Maybe Val

_[_↦_] : Regs → Reg → Maybe Val → Regs
(ρ [ rax ↦ v ]) rax = v
(ρ [ rdi ↦ v ]) rdi = v
(ρ [ rsi ↦ v ]) rsi = v
(ρ [ _ ↦ v ]) r = ρ r

data Stack : Set where
  halt : Stack
  retK : List Instr → Jump → List Block → Frame → Stack → Stack   {- the caller -}

data State : Set where
  run : List Instr → Jump → List Block → Stack → Maybe Bool → Frame → Regs → State

read : Frame → Regs → Loc → Maybe Val
read φ ρ (var x) = φ ‼ x
read φ ρ (reg r) = ρ r

arg : Frame → Regs → Arg → Maybe Val
arg φ ρ (loc l) = read φ ρ l
arg φ ρ (imm B k) = just (const B k)
arg φ ρ (label k) = just (code k)

{- the values of the operands as, after those of earlier ones (vs, in
   reverse), given to k -}
args : Frame → Regs → List Val → List Arg → (List Val → Maybe Val) → Maybe Val
args φ ρ vs [] k = k (reverse vs)
args φ ρ vs (a ∷ as) k = arg φ ρ a >>= λ v → args φ ρ (v ∷ vs) as k

build : Shape → List Val → Maybe Val
build pair (v ∷ w ∷ []) = just (pair v w)
build tuple vs = just (tup vs)
build inl (v ∷ []) = just (inl v)
build inr (v ∷ []) = just (inr v)
build _ _ = nothing

get-field : Field → Val → Maybe Val
get-field fst (pair v w) = just v
get-field snd (pair v w) = just w
get-field (get i) (tup vs) = proj i vs
get-field payload (inl v) = just v
get-field payload (inr v) = just v
get-field _ _ = nothing

{- the flag of a comparison of two integers, as the primitive eq says -}
truth : Maybe Out → Maybe Bool
truth (just (bool b)) = just b
truth _ = nothing

cmp : Val → Val → Maybe Bool
cmp v w = truth (δ? eq (obs v) (obs w))

is-inl : Val → Maybe Bool
is-inl (inl v) = just true
is-inl (inr v) = just false
is-inl _ = nothing

{- what sete stores: inl ⟨⟩ or inr ⟨⟩, as the primitive eq produces -}
bit : Bool → Val
bit b = out (bool b)

{- continue in the frame, if there is one -}
upd : Maybe Frame → Regs → (Frame → Regs → State) → Next State
upd (just φ) ρ k = next (k φ ρ)
upd nothing ρ k = stop o-error

{- d := v, then continue -}
put : Loc → Maybe Val → Frame → Regs → (Frame → Regs → State) → Next State
put d nothing φ ρ k = stop o-error
put (var x) (just v) φ ρ k = upd (φ [ x ]≔ v) ρ k
put (reg r) (just v) φ ρ k = next (k φ (ρ [ r ↦ just v ]))

{- set the flag, then continue -}
test : Maybe Bool → (Maybe Bool → State) → Next State
test (just b) k = next (k (just b))
test nothing k = stop o-error

{- definition k, counting from the oldest -}
global : List Body → ℕ → Maybe Body
global ds k = reverse ds ‼ k

{- block l among bs (newest first), with the blocks older than it -}
block-at : List Block → ℕ → Maybe (Block × List Block)
block-at [] l = nothing
block-at (b ∷ bs) l with l ≟ length bs
... | yes _ = just (b , bs)
... | no _ = block-at bs l

goto : Maybe (Block × List Block) → Stack → Maybe Bool → Frame → Regs → Next State
goto (just (b , bs)) σ f φ ρ = next (run (Block.instrs b) (Block.jump b) bs σ f φ ρ)
goto nothing σ f φ ρ = stop o-error

{- the registers %rax, %rdi and %rsi -}
regs : Maybe Val → Maybe Val → Maybe Val → Regs
regs a d s rax = a
regs a d s rdi = d
regs a d s rsi = s

{- run the start of a body in a fresh frame of max(2, locals) slots,
   with %rdi and %rsi set -}
call : Maybe Body → Stack → Maybe Val → Maybe Val → Next State
call (just (body n bs b)) σ (just e) (just w) =
  next (run (Block.instrs b) (Block.jump b) bs σ nothing (zeros (2 + (n ∸ 2))) (regs nothing (just e) (just w)))
call _ σ _ _ = stop o-error

callq? : List Body → Maybe Val → Stack → Regs → Next State
callq? ds (just (code k)) σ ρ = call (global ds k) σ (ρ rdi) (ρ rsi)
callq? ds _ σ ρ = stop o-error

{- return %rax to the caller -}
back : Maybe Val → List Instr → Jump → List Block → Frame → Stack → Next State
back (just v) is j bs φ σ = next (run is j bs σ nothing φ (regs (just v) nothing nothing))
back nothing is j bs φ σ = stop o-error

halt? : Maybe Val → Next State
halt? (just v) = stop (obs v)
halt? nothing = stop o-error

{- the machine for a program with global definitions ds -}
step : List Body → State → Next State
step ds (run (movq a d ∷ is) j bs σ f φ ρ) = put d (arg φ ρ a) φ ρ (run is j bs σ f)
step ds (run (subq a d ∷ is) j bs σ f φ ρ) =
  put d (arg φ ρ a >>= λ w → read φ ρ d >>= λ v → prim? sub v w) φ ρ (run is j bs σ f)
step ds (run (cmpq a₂ a₁ ∷ is) j bs σ f φ ρ) =
  test (arg φ ρ a₁ >>= λ v → arg φ ρ a₂ >>= λ w → cmp v w) λ f' → run is j bs σ f' φ ρ
step ds (run (sete d ∷ is) j bs σ (just b) φ ρ) = put d (just (bit b)) φ ρ (run is j bs σ (just b))
step ds (run (sete d ∷ is) j bs σ nothing φ ρ) = stop o-error
step ds (run (testinl a ∷ is) j bs σ f φ ρ) = test (arg φ ρ a >>= is-inl) λ f' → run is j bs σ f' φ ρ
step ds (run (alloc s as d ∷ is) j bs σ f φ ρ) = put d (args φ ρ [] as (build s)) φ ρ (run is j bs σ f)
step ds (run (load fl a d ∷ is) j bs σ f φ ρ) = put d (arg φ ρ a >>= get-field fl) φ ρ (run is j bs σ f)
step ds (run (callq a ∷ is) j bs σ f φ ρ) = callq? ds (arg φ ρ a) (retK is j bs φ σ) ρ
step ds (run [] retq bs halt f φ ρ) = halt? (ρ rax)
step ds (run [] retq bs (retK is j bs' φ' σ) f φ ρ) = back (ρ rax) is j bs' φ' σ
step ds (run [] (jmp l) bs σ f φ ρ) = goto (block-at bs l) σ f φ ρ
step ds (run [] (je l₁ l₂) bs σ (just true) φ ρ) = goto (block-at bs l₁) σ (just true) φ ρ
step ds (run [] (je l₁ l₂) bs σ (just false) φ ρ) = goto (block-at bs l₂) σ (just false) φ ρ
step ds (run [] (je l₁ l₂) bs σ nothing φ ρ) = stop o-error


{- a program starts with the start of its main body -}
sem : Program → Machine
sem (program ds (body n bs b)) =
  machine State (step ds) (run (Block.instrs b) (Block.jump b) bs halt nothing (zeros n) (regs (just (const Int 0ℤ)) nothing nothing))

{-

  X86ᵀ: a typed assembly language, after Morrisett, Walker, Crary and
  Glew's TAL, intrinsically typed in the style of Rouvoet et al.'s
  typed compilation to typed bytecode. A pilot (Theorems/TAL.agda): the
  output of typed select instructions (Compiler/SelectTAL.agda), with
  the instructions of X86 (Language/X86.agda) and their meaning.

  An instruction is typed by the machine state it starts in and the one
  it leaves (Instr Σ n ψ ψ'); a state type (St) gives
  * the type of each register: a type, or nothing (unset);
  * the frame: the types of the slots assigned so far, a context Δ as
    in CFGᵀ (slot x : Δ ∋ A is at level lvl x), in a frame of n slots;
    writing slot k (k the length of Δ', p : Δ' ⊑ Δ) gives it a type and
    forgets the slots after it, and needs k < n;
  * the open closure, if any (below);
  * whether the flag is set.
  A sequence (Seq) is instructions ending in a jump, typed by the state
  it starts in; a block starts with its frame, unset registers and no
  flag, so a label (Bs ∋ Δ, the frame its block expects) is a typed
  index, and a jump to a missing block, a read of an unset register or
  of a slot not assigned, the flag when it is not set, and a slot
  beyond the frame cannot be written.

  The type of a closure, ⟪ fun ⟫, hides the length of its environment
  (∃ n. code n × ⟪ tup n ⟫). load fst x, r opens the closure in slot x:
  r gets the type codeα of its code, α the length of its environment,
  and the state records that x is open; load snd x, r, of the open
  closure, gives r the type tupα. Opening forgets the registers of type
  codeα or tupα of an earlier closure; writing a slot, or a call,
  closes the closure. callq a needs a : codeα, %rdi : tupα and %rsi :
  Any, as code n expects; it leaves %rax : Any and %rdi, %rsi and the
  flag unset. A definition starts with %rdi : ⟪ tup n ⟫ and %rsi : Any.

  The only check is project's: chk t x, d moves slot x : Any to d at
  ⟪ flat t ⟫, and is the trapped error when x holds another kind. It
  is a pseudo-instruction for the X86 test of t and the move (check,
  Compiler/Select.agda), which clobber %rax or the flag: chk leaves
  %rax unset and no flag. A value of type ⟪ G ⟫ is one of type Any
  (a ↑, as inject is a move in X86).

  A typed proof argument (an equation for a register, a frame bound) is
  not an operand: without the types, the instructions are those of X86.

-}

module Language.Typed.X86 where

open import Framework.Primitives using (Base; base-rep; Int)
open import Language.Typed.Type
open import Framework.Membership using (_⊑_)
open import Language.Typed.Mon using (Atm; var; lit; ref) public
open import Language.X86 using (Reg; rax; rdi; rsi) public

open import Data.Bool using (Bool; true; false)
open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; length)
open import Data.List.Relation.Unary.All using (All)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _<_)
open import Data.Vec using (Vec)
open import Relation.Binary.PropositionalEquality using (_≡_)

{- the types of registers: a type, or the code or environment of the
   open closure -}
data RTy : Set where
  ty : Ty → RTy
  codeα tupα : RTy

ℤty : RTy
ℤty = ty ⟪ base Int ⟫

{- the types of the registers (nothing: unset) -}
record Regs : Set where
  constructor rt
  field ax di si : Maybe RTy

infixl 6 _‹_›
_‹_› : Regs → Reg → Maybe RTy
Γ ‹ rax › = Regs.ax Γ
Γ ‹ rdi › = Regs.di Γ
Γ ‹ rsi › = Regs.si Γ

_[_↦_] : Regs → Reg → Maybe RTy → Regs
Γ [ rax ↦ τ ] = rt τ (Regs.di Γ) (Regs.si Γ)
Γ [ rdi ↦ τ ] = rt (Regs.ax Γ) τ (Regs.si Γ)
Γ [ rsi ↦ τ ] = rt (Regs.ax Γ) (Regs.di Γ) τ

unset : Regs
unset = rt nothing nothing nothing

{- a register of an earlier closure's code or environment is unset -}
forgetα : Maybe RTy → Maybe RTy
forgetα (just (ty A)) = just (ty A)
forgetα _ = nothing

wipe : Regs → Regs
wipe Γ = rt (forgetα (Regs.ax Γ)) (forgetα (Regs.di Γ)) (forgetα (Regs.si Γ))

{- the type of a machine state -}
record St : Set where
  constructor st
  field
    rs : Regs
    fr : Ctx
    op : Maybe (fr ∋ ⟪ fun ⟫)   {- the slot of the open closure -}
    fl : Bool                  {- the flag is set -}

{- after a call: %rax : Any -}
returned : Ctx → St
returned Δ = st (rt (just (ty Any)) nothing nothing) Δ nothing false

{- operands: a register, or an atom (a slot, an immediate or a label,
   as in Monᵀ) -}
data Arg (Σ : List ℕ) (ψ : St) : RTy → Set where
  atom : ∀ {A} → Atm Σ (St.fr ψ) A → Arg Σ ψ (ty A)
  reg : ∀ r {τ} → St.rs ψ ‹ r › ≡ just τ → Arg Σ ψ τ
  _↑ : ∀ {G} → Arg Σ ψ (ty ⟪ G ⟫) → Arg Σ ψ (ty Any)

{- destinations, in a frame of n slots -}
data Dst (n : ℕ) : St → RTy → St → Set where
  reg : ∀ {Γ Δ O F τ} r → Dst n (st Γ Δ O F) τ (st (Γ [ r ↦ just τ ]) Δ O F)
  slot : ∀ {Γ Δ Δ' O F A} (p : Δ' ⊑ Δ) → .(length Δ' < n) → Dst n (st Γ Δ O F) (ty A) (st Γ (A ∷ Δ') nothing F)

{- what alloc builds -}
data Obj (Σ : List ℕ) (ψ : St) : Ty → Set where
  pair : ∀ {m} → Arg Σ ψ (ty (code m)) → Arg Σ ψ (ty ⟪ tup m ⟫) → Obj Σ ψ ⟪ fun ⟫
  tuple : ∀ {m} → Vec (Arg Σ ψ (ty Any)) m → Obj Σ ψ ⟪ tup m ⟫
  inl inr : Arg Σ ψ (ty Any) → Obj Σ ψ ⟪ sum ⟫

{- the fields load takes, other than a closure's -}
data Field : Ty → Ty → Set where
  get : ∀ {m} → Fin m → Field ⟪ tup m ⟫ Any
  payload : Field ⟪ sum ⟫ Any

data Instr (Σ : List ℕ) (n : ℕ) : St → St → Set where
  movq : ∀ {ψ τ ψ'} → Arg Σ ψ τ → Dst n ψ τ ψ' → Instr Σ n ψ ψ'
  subq : ∀ {Γ Δ O F} → Arg Σ (st Γ Δ O F) ℤty → ∀ r → Γ ‹ r › ≡ just ℤty
    → Instr Σ n (st Γ Δ O F) (st (Γ [ r ↦ just ℤty ]) Δ O F)
  cmpq : ∀ {Γ Δ O F} → Arg Σ (st Γ Δ O F) ℤty → Arg Σ (st Γ Δ O F) ℤty → Instr Σ n (st Γ Δ O F) (st Γ Δ O true)
  sete : ∀ {Γ Δ O ψ'} → Dst n (st Γ Δ O true) (ty ⟪ sum ⟫) ψ' → Instr Σ n (st Γ Δ O true) ψ'
  testinl : ∀ {Γ Δ O F} → Arg Σ (st Γ Δ O F) (ty ⟪ sum ⟫) → Instr Σ n (st Γ Δ O F) (st Γ Δ O true)
  alloc : ∀ {ψ A ψ'} → Obj Σ ψ A → Dst n ψ (ty A) ψ' → Instr Σ n ψ ψ'
  load : ∀ {ψ A B ψ'} → Field A B → Arg Σ ψ (ty A) → Dst n ψ (ty B) ψ' → Instr Σ n ψ ψ'
  {- load fst x, r: open the closure in slot x -}
  loadfst : ∀ {Γ Δ O F} (x : Δ ∋ ⟪ fun ⟫) r → Instr Σ n (st Γ Δ O F) (st (wipe Γ [ r ↦ just codeα ]) Δ (just x) F)
  {- load snd x, r, of the open closure x -}
  loadsnd : ∀ {Γ Δ x F} r → Instr Σ n (st Γ Δ (just x) F) (st (Γ [ r ↦ just tupα ]) Δ (just x) F)
  callq : ∀ {Γ Δ O F} → Arg Σ (st Γ Δ O F) codeα → Γ ‹ rdi › ≡ just tupα → Γ ‹ rsi › ≡ just (ty Any)
    → Instr Σ n (st Γ Δ O F) (returned Δ)
  {- project's check, and the move -}
  chk : ∀ {Γ Δ O F ψ'} (t : Tag) → Δ ∋ Any → Dst n (st (Γ [ rax ↦ nothing ]) Δ O false) (ty ⟪ flat t ⟫) ψ'
    → Instr Σ n (st Γ Δ O F) ψ'

{- instructions, then a jump, to the blocks Bs -}
infixr 5 _∷_
data Seq (Σ : List ℕ) (n : ℕ) (Bs : List Ctx) : St → Set where
  _∷_ : ∀ {ψ ψ'} → Instr Σ n ψ ψ' → Seq Σ n Bs ψ' → Seq Σ n Bs ψ
  retq : ∀ {Γ Δ O F} → Γ ‹ rax › ≡ just (ty Any) → Seq Σ n Bs (st Γ Δ O F)
  jmp : ∀ {Γ Δ O F} → Bs ∋ Δ → Seq Σ n Bs (st Γ Δ O F)
  je : ∀ {Γ Δ O} → Bs ∋ Δ → Bs ∋ Δ → Seq Σ n Bs (st Γ Δ O true)

{- a block starts with its frame -}
entry : Ctx → St
entry Δ = st unset Δ nothing false

{- the blocks of a body, newest first, each over the older ones -}
data Blocks (Σ : List ℕ) (n : ℕ) : List Ctx → Set where
  [] : Blocks Σ n []
  _▷_ : ∀ {Bs Δ} → Blocks Σ n Bs → Seq Σ n Bs (entry Δ) → Blocks Σ n (Δ ∷ Bs)

{- a body: the number of slots of its frame, its blocks and its start -}
record Body (Σ : List ℕ) (ψ : St) : Set where
  constructor body
  field
    locals : ℕ
    {labels} : List Ctx
    blocks : Blocks Σ locals labels
    start : Seq Σ locals labels ψ

{- a definition of code n starts with its environment in %rdi and its
   argument in %rsi -}
called : ℕ → St
called m = st (rt nothing (just (ty ⟪ tup m ⟫)) (just (ty Any))) [] nothing false

record Program : Set where
  constructor program
  field
    {table} : List ℕ
    defs : All (λ m → Body table (called m)) table
    main : Body table (entry [])

{- block l, with the blocks older than it -}
record Blk (Σ : List ℕ) (n : ℕ) (Δ : Ctx) : Set where
  constructor blk
  field
    {older} : List Ctx
    blocks : Blocks Σ n older
    start : Seq Σ n older (entry Δ)

block : ∀ {Σ n Bs Δ} → Blocks Σ n Bs → Bs ∋ Δ → Blk Σ n Δ
block (bs ▷ k) Z = blk bs k
block (bs ▷ k) (S l) = block bs l

{-

  X86μ: the typed assembly language of FPC's compiler, the target of the
  compiler, the output of select instructions (FPC/Compiler/Select.agda).
  As X86ᵀ (ISWIM/Language/Typed/X86.agda), with the types of CFGμ, and with
  no check: nothing traps.

  A body runs in a fixed frame of slots of types Δ, as in CFGμ
  (FPC/Language/Frame.agda). An instruction is typed by the machine
  state it starts in and the one it leaves (Instr Σ ψ ψ'); a state type
  (St Δ) gives the type of each register (a type, or nothing: unset),
  the initialized slots, the open closure, if any, and whether the flag
  is set. A sequence (Seq Σ Δ R Bs ψ) is also typed by the type R of
  its body's result (what retq returns).

  The type of a closure, A ⇒ B, hides the types Δ of its environment
  (∃ Δ. code Δ A B × tup Δ). load fst x, r opens the closure in slot
  x : A ⇒ B: r gets the type codeα A B of its code, α standing for the
  hidden Δ, and the state records that x is open; load snd x, r, of the
  open closure, gives r the type tupα of its environment. As in X86ᵀ,
  where α stands for the hidden length of an environment, the witness
  is never named in a type: codeα and tupα refer to the closure opened
  last, opening wipes the registers of type codeα or tupα of an
  earlier closure, and so a register of type codeα A B and one of type
  tupα always belong to the same closure. Only the argument and result
  types, which the type of the closure shows, are in codeα A B. callq a
  needs a : codeα A B, %rdi : tupα and %rsi : A; it leaves %rax : B and
  %rdi, %rsi and the flag unset. A slot write closes the open closure,
  so load snd x reads the slot that load fst x opened. A definition of
  signature sig Δ A B starts with %rdi : tup Δ and %rsi : A.

  fold and unfold are moves: a value of type unroll A is one of type
  μ A (an ↑), and back (an ↓), as inject is a move in X86ᵀ.

  A case on an injection is the pseudo-instruction case x y z l₁ l₂ (a
  jump, the end of a sequence), for the instructions
    testinl x; je L; load payload x, z; jmp l₂;
    L: load payload x, y; jmp l₁
  of X86ᵀ's case. As chk is in X86ᵀ, it is typed as one instruction.

  Informally, the instructions:
    movq a, d          d := a
    subq a, r          r := r - a (integers)
    cmpq a₂, a₁        flag := (a₁ = a₂) (integers)
    sete d             d := inl ⟨⟩ if the flag is set, inr ⟨⟩ if not
    alloc o, d         d := the pair, tuple or injection o
    load i a, d        d := component i of the tuple a
    load fst x, r      r := the code of the closure in slot x (opens it)
    load snd x, r      r := the environment of the open closure
    callq a            run the definition of the code a with %rdi and
                       %rsi, and continue with its result in %rax
    retq               return %rax
    jmp l              run block l in the frame as it is
    case x y z l₁ l₂   for an inl in slot x, slot y := its payload and
                       run block l₁; for an inr, slot z := its payload
                       and run block l₂

-}

module FPC.Language.X86 where

open import Framework.Primitives using (Base; base-rep; Int)
open import FPC.Language.Type
open import FPC.Language.Imp using (DSig; sig; Args; Atm; var; lit; ref; Inits;
  none; _∈_; _⊕_; _⊆_) public
open import Language.Reg public
open import FPC.Framework.AllUtil using (All)

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_)

{- the types of registers: a type, or the code or environment of the
   open closure -}
data RTy : Set where
  ty : Type → RTy
  codeα : Type → Type → RTy
  tupα : RTy

ℤty : RTy
ℤty = ty (base Int)

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
wipeα : Maybe RTy → Maybe RTy
wipeα (just (ty A)) = just (ty A)
wipeα _ = nothing

wipe : Regs → Regs
wipe Γ = rt (wipeα (Regs.ax Γ)) (wipeα (Regs.di Γ)) (wipeα (Regs.si Γ))

{- the slot of the open closure -}
record Open (Δ : Ctx) : Set where
  constructor opened
  field
    {dom cod} : Type
    slot : Δ ∋ dom ⇒ cod

{- the type of a machine state, in a frame of type Δ -}
record St (Δ : Ctx) : Set where
  constructor st
  field
    rs : Regs
    ini : Inits Δ          {- the initialized slots -}
    op : Maybe (Open Δ)    {- the open closure -}
    fl : Bool              {- the flag is set -}

{- after a call: %rax : B -}
returned : ∀ {Δ} → Inits Δ → Type → St Δ
returned I B = st (rt (just (ty B)) nothing nothing) I nothing false

{- operands: a register, or an atom (an initialized slot, an immediate
   or a label, as in Impμ), folded or unfolded -}
data Arg (Σ : List DSig) {Δ : Ctx} (ψ : St Δ) : RTy → Set where
  atom : ∀ {A} → Atm Σ Δ (St.ini ψ) A → Arg Σ ψ (ty A)
  reg : ∀ r {τ} → St.rs ψ ‹ r › ≡ just τ → Arg Σ ψ τ
  _↑ : ∀ {A} → Arg Σ ψ (ty (unroll A)) → Arg Σ ψ (ty (μ A))
  _↓ : ∀ {A} → Arg Σ ψ (ty (μ A)) → Arg Σ ψ (ty (unroll A))

{- destinations: a register, or a slot x, after which the rest starts
   with the initialized slots J (p : J ⊆ I ⊕ x) and no open closure -}
data Dst {Δ : Ctx} : St Δ → RTy → St Δ → Set where
  reg : ∀ {Γ I O F τ} r → Dst (st Γ I O F) τ (st (Γ [ r ↦ just τ ]) I O F)
  slot : ∀ {Γ I J O F A} (x : Δ ∋ A) → .(J ⊆ I ⊕ x)
    → Dst (st Γ I O F) (ty A) (st Γ J nothing F)

{- what alloc builds -}
data Obj (Σ : List DSig) {Δ : Ctx} (ψ : St Δ) : Type → Set where
  pair : ∀ {Δ' A B} → Arg Σ ψ (ty (code Δ' A B)) → Arg Σ ψ (ty (tup Δ'))
    → Obj Σ ψ (A ⇒ B)
  tuple : ∀ {Δ'} → All (λ A → Arg Σ ψ (ty A)) Δ' → Obj Σ ψ (tup Δ')
  inl : ∀ {A B} → Arg Σ ψ (ty A) → Obj Σ ψ (A ⊹ B)
  inr : ∀ {A B} → Arg Σ ψ (ty B) → Obj Σ ψ (A ⊹ B)

data Instr (Σ : List DSig) {Δ : Ctx} : St Δ → St Δ → Set where
  movq : ∀ {ψ τ ψ'} → Arg Σ ψ τ → Dst ψ τ ψ' → Instr Σ ψ ψ'
  subq : ∀ {Γ I O F} → Arg Σ (st Γ I O F) ℤty → ∀ r → Γ ‹ r › ≡ just ℤty
    → Instr Σ (st Γ I O F) (st (Γ [ r ↦ just ℤty ]) I O F)
  cmpq : ∀ {Γ I O F} → Arg Σ (st Γ I O F) ℤty → Arg Σ (st Γ I O F) ℤty
    → Instr Σ (st Γ I O F) (st Γ I O true)
  sete : ∀ {Γ I O ψ'} → Dst (st Γ I O true) (ty (tup [] ⊹ tup [])) ψ'
    → Instr Σ (st Γ I O true) ψ'
  alloc : ∀ {ψ A ψ'} → Obj Σ ψ A → Dst ψ (ty A) ψ' → Instr Σ ψ ψ'
  load : ∀ {ψ Δ' A ψ'} → Δ' ∋ A → Arg Σ ψ (ty (tup Δ')) → Dst ψ (ty A) ψ'
    → Instr Σ ψ ψ'
  {- load fst x, r: open the closure in slot x -}
  loadfst : ∀ {Γ I O F A B} (x : Δ ∋ A ⇒ B) → .(x ∈ I) → ∀ r
    → Instr Σ (st Γ I O F)
      (st (wipe Γ [ r ↦ just (codeα A B) ]) I (just (opened x)) F)
  {- load snd x, r, of the open closure x -}
  loadsnd : ∀ {Γ I x F} r
    → Instr Σ (st Γ I (just x) F) (st (Γ [ r ↦ just tupα ]) I (just x) F)
  callq : ∀ {Γ I O F A B} → Arg Σ (st Γ I O F) (codeα A B)
    → Γ ‹ rdi › ≡ just tupα → Γ ‹ rsi › ≡ just (ty A)
    → Instr Σ (st Γ I O F) (returned I B)

{- instructions, then a jump, to the blocks Bs, in a body of result R
   and frame Δ -}
infixr 5 _∷_
data Seq (Σ : List DSig) (Δ : Ctx) (R : Type) (Bs : List (Inits Δ))
  : St Δ → Set where
  _∷_ : ∀ {ψ ψ'} → Instr Σ ψ ψ' → Seq Σ Δ R Bs ψ' → Seq Σ Δ R Bs ψ
  retq : ∀ {Γ I O F} → Γ ‹ rax › ≡ just (ty R) → Seq Σ Δ R Bs (st Γ I O F)
  jmp : ∀ {Γ I O F} → Bs ∋ I → Seq Σ Δ R Bs (st Γ I O F)
  case : ∀ {Γ I O F A B} (x : Δ ∋ A ⊹ B) → .(x ∈ I)
    → (y : Δ ∋ A) (z : Δ ∋ B) → Bs ∋ (I ⊕ y) → Bs ∋ (I ⊕ z)
    → Seq Σ Δ R Bs (st Γ I O F)

{- a block starts with its initialized slots -}
entry : ∀ {Δ} → Inits Δ → St Δ
entry I = st unset I nothing false

{- the blocks of a body, newest first, each over the older ones -}
data Blocks (Σ : List DSig) (Δ : Ctx) (R : Type) : List (Inits Δ) → Set where
  [] : Blocks Σ Δ R []
  _▷_ : ∀ {Bs I} → Blocks Σ Δ R Bs → Seq Σ Δ R Bs (entry I)
    → Blocks Σ Δ R (I ∷ Bs)

{- a body: its frame Δ, its blocks and its start, in the state ψ Δ -}
record Body (Σ : List DSig) (R : Type) (ψ : (Δ : Ctx) → St Δ) : Set where
  constructor body
  field
    frame : Ctx
    {labels} : List (Inits frame)
    blocks : Blocks Σ frame R labels
    start : Seq Σ frame R labels (ψ frame)

{- a definition of signature s starts with its environment in %rdi and
   its argument in %rsi, and no slot initialized -}
called : DSig → (Δ : Ctx) → St Δ
called s Δ =
  st (rt nothing (just (ty (tup (DSig.env s)))) (just (ty (DSig.dom s))))
  (none Δ) nothing false

{- main starts with no register and no slot initialized -}
begin : (Δ : Ctx) → St Δ
begin Δ = entry (none Δ)

record Program (A : Type) : Set where
  constructor program
  field
    {table} : List DSig
    defs : All (λ s → Body table (DSig.cod s) (called s)) table
    main : Body table A begin

{- block l, with the blocks older than it -}
record Blk (Σ : List DSig) (Δ : Ctx) (R : Type) (I : Inits Δ) : Set where
  constructor blk
  field
    {older} : List (Inits Δ)
    blocks : Blocks Σ Δ R older
    start : Seq Σ Δ R older (entry I)

block : ∀ {Σ Δ R Bs I} → Blocks Σ Δ R Bs → Bs ∋ I → Blk Σ Δ R I
block (bs ▷ k) Z = blk bs k
block (bs ▷ k) (S l) = block bs l

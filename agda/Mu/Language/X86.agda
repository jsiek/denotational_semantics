{-

  X86μ: the typed assembly language of ISWIMμ's compiler, the target of the
  compiler, the output of select instructions (Mu/Compiler/Select.agda).
  As X86ᵀ (Language/Typed/X86.agda), with the types of CFGμ, and with
  no check: nothing traps.

  An instruction is typed by the machine state it starts in and the one
  it leaves (Instr Σ n ψ ψ'); a state type (St) gives the type of each
  register (a type, or nothing: unset), the frame (the types of the
  slots assigned so far, a context Δ, in a frame of n slots), the open
  closure, if any, and whether the flag is set. A sequence (Seq Σ n R
  Bs ψ) is also typed by the type R of its body's result (what retq
  returns).

  The type of a closure, A ⇒ B, hides the types Δ of its environment
  (∃ Δ. code Δ A B × tup Δ). load fst x, r opens the closure in slot
  x : A ⇒ B: r gets the type codeα A B of its code, α standing for the
  hidden Δ, and the state records that x is open; load snd x, r, of the
  open closure, gives r the type tupα of its environment. As in X86ᵀ,
  where α stands for the hidden length of an environment, the witness
  is never named in a type: codeα and tupα refer to the closure opened
  last, opening forgets the registers of type codeα or tupα of an
  earlier closure, and so a register of type codeα A B and one of type
  tupα always belong to the same closure. Only the argument and result
  types, which the type of the closure shows, are in codeα A B. callq a
  needs a : codeα A B, %rdi : tupα and %rsi : A; it leaves %rax : B and
  %rdi, %rsi and the flag unset. A definition of signature sig Δ A B
  starts with %rdi : tup Δ and %rsi : A.

  fold and unfold are moves: a value of type unroll A is one of type
  μ A (an ↑), and back (an ↓), as inject is a move in X86ᵀ.

  A case on an injection is the pseudo-instruction case x p l₁ l₂ (a
  jump, the end of a sequence), for the three instructions
    testinl x; load payload x, slot k; je l₁ l₂
  of X86ᵀ's case: the payload's slot has the left type in block l₁ and
  the right type in block l₂, which no state type between the load and
  the jump can give it. As chk is in X86ᵀ, it is typed as one
  instruction, and erases to the three.

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
    case x p l₁ l₂     slot k := the payload of the injection in slot x,
                       then run block l₁ for inl, l₂ for inr

-}

module Mu.Language.X86 where

open import Framework.Primitives using (Base; base-rep; Int)
open import Mu.Language.Type
open import Framework.Membership using (_⊑_)
open import Mu.Language.Mon using (DSig; sig; Args; Atm; var; lit; ref) public
open import Language.Reg public
open import Mu.Framework.AllUtil using (All)

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _<_)
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
forgetα : Maybe RTy → Maybe RTy
forgetα (just (ty A)) = just (ty A)
forgetα _ = nothing

wipe : Regs → Regs
wipe Γ = rt (forgetα (Regs.ax Γ)) (forgetα (Regs.di Γ)) (forgetα (Regs.si Γ))

{- the slot of the open closure -}
record Open (Δ : Ctx) : Set where
  constructor opened
  field
    {dom cod} : Type
    slot : Δ ∋ dom ⇒ cod

{- the type of a machine state -}
record St : Set where
  constructor st
  field
    rs : Regs
    fr : Ctx
    op : Maybe (Open fr)   {- the open closure -}
    fl : Bool              {- the flag is set -}

{- after a call: %rax : B -}
returned : Ctx → Type → St
returned Δ B = st (rt (just (ty B)) nothing nothing) Δ nothing false

{- operands: a register, or an atom (a slot, an immediate or a label,
   as in Monμ), folded or unfolded -}
data Arg (Σ : List DSig) (ψ : St) : RTy → Set where
  atom : ∀ {A} → Atm Σ (St.fr ψ) A → Arg Σ ψ (ty A)
  reg : ∀ r {τ} → St.rs ψ ‹ r › ≡ just τ → Arg Σ ψ τ
  _↑ : ∀ {A c} → Arg Σ ψ (ty (unroll A {c})) → Arg Σ ψ (ty (μ A {c}))
  _↓ : ∀ {A c} → Arg Σ ψ (ty (μ A {c})) → Arg Σ ψ (ty (unroll A {c}))

{- destinations, in a frame of n slots -}
data Dst (n : ℕ) : St → RTy → St → Set where
  reg : ∀ {Γ Δ O F τ} r → Dst n (st Γ Δ O F) τ (st (Γ [ r ↦ just τ ]) Δ O F)
  slot : ∀ {Γ Δ Δ' O F A} (p : Δ' ⊑ Δ) → .(length Δ' < n) → Dst n (st Γ Δ O F) (ty A) (st Γ (A ∷ Δ') nothing F)

{- what alloc builds -}
data Obj (Σ : List DSig) (ψ : St) : Type → Set where
  pair : ∀ {Δ A B} → Arg Σ ψ (ty (code Δ A B)) → Arg Σ ψ (ty (tup Δ)) → Obj Σ ψ (A ⇒ B)
  tuple : ∀ {Δ} → All (λ A → Arg Σ ψ (ty A)) Δ → Obj Σ ψ (tup Δ)
  inl : ∀ {A B} → Arg Σ ψ (ty A) → Obj Σ ψ (A ⊹ B)
  inr : ∀ {A B} → Arg Σ ψ (ty B) → Obj Σ ψ (A ⊹ B)

data Instr (Σ : List DSig) (n : ℕ) : St → St → Set where
  movq : ∀ {ψ τ ψ'} → Arg Σ ψ τ → Dst n ψ τ ψ' → Instr Σ n ψ ψ'
  subq : ∀ {Γ Δ O F} → Arg Σ (st Γ Δ O F) ℤty → ∀ r → Γ ‹ r › ≡ just ℤty
    → Instr Σ n (st Γ Δ O F) (st (Γ [ r ↦ just ℤty ]) Δ O F)
  cmpq : ∀ {Γ Δ O F} → Arg Σ (st Γ Δ O F) ℤty → Arg Σ (st Γ Δ O F) ℤty → Instr Σ n (st Γ Δ O F) (st Γ Δ O true)
  sete : ∀ {Γ Δ O ψ'} → Dst n (st Γ Δ O true) (ty (tup [] ⊹ tup [])) ψ' → Instr Σ n (st Γ Δ O true) ψ'
  alloc : ∀ {ψ A ψ'} → Obj Σ ψ A → Dst n ψ (ty A) ψ' → Instr Σ n ψ ψ'
  load : ∀ {ψ Δ A ψ'} → Δ ∋ A → Arg Σ ψ (ty (tup Δ)) → Dst n ψ (ty A) ψ' → Instr Σ n ψ ψ'
  {- load fst x, r: open the closure in slot x -}
  loadfst : ∀ {Γ Δ O F A B} (x : Δ ∋ A ⇒ B) r
    → Instr Σ n (st Γ Δ O F) (st (wipe Γ [ r ↦ just (codeα A B) ]) Δ (just (opened x)) F)
  {- load snd x, r, of the open closure x -}
  loadsnd : ∀ {Γ Δ x F} r → Instr Σ n (st Γ Δ (just x) F) (st (Γ [ r ↦ just tupα ]) Δ (just x) F)
  callq : ∀ {Γ Δ O F A B} → Arg Σ (st Γ Δ O F) (codeα A B) → Γ ‹ rdi › ≡ just tupα → Γ ‹ rsi › ≡ just (ty A)
    → Instr Σ n (st Γ Δ O F) (returned Δ B)

{- instructions, then a jump, to the blocks Bs, in a body of result R -}
infixr 5 _∷_
data Seq (Σ : List DSig) (n : ℕ) (R : Type) (Bs : List Ctx) : St → Set where
  _∷_ : ∀ {ψ ψ'} → Instr Σ n ψ ψ' → Seq Σ n R Bs ψ' → Seq Σ n R Bs ψ
  retq : ∀ {Γ Δ O F} → Γ ‹ rax › ≡ just (ty R) → Seq Σ n R Bs (st Γ Δ O F)
  jmp : ∀ {Γ Δ O F} → Bs ∋ Δ → Seq Σ n R Bs (st Γ Δ O F)
  case : ∀ {Γ Δ Δ' O F A B} → Δ ∋ A ⊹ B → (p : Δ' ⊑ Δ) → .(length Δ' < n)
    → Bs ∋ (A ∷ Δ') → Bs ∋ (B ∷ Δ') → Seq Σ n R Bs (st Γ Δ O F)

{- a block starts with its frame -}
entry : Ctx → St
entry Δ = st unset Δ nothing false

{- the blocks of a body, newest first, each over the older ones -}
data Blocks (Σ : List DSig) (n : ℕ) (R : Type) : List Ctx → Set where
  [] : Blocks Σ n R []
  _▷_ : ∀ {Bs Δ} → Blocks Σ n R Bs → Seq Σ n R Bs (entry Δ) → Blocks Σ n R (Δ ∷ Bs)

{- a body: the number of slots of its frame, its blocks and its start -}
record Body (Σ : List DSig) (R : Type) (ψ : St) : Set where
  constructor body
  field
    locals : ℕ
    {labels} : List Ctx
    blocks : Blocks Σ locals R labels
    start : Seq Σ locals R labels ψ

{- a definition of signature s starts with its environment in %rdi and
   its argument in %rsi -}
called : DSig → St
called s = st (rt nothing (just (ty (tup (DSig.env s)))) (just (ty (DSig.dom s)))) [] nothing false

record Program (A : Type) : Set where
  constructor program
  field
    {table} : List DSig
    defs : All (λ s → Body table (DSig.cod s) (called s)) table
    main : Body table A (entry [])

{- block l, with the blocks older than it -}
record Blk (Σ : List DSig) (n : ℕ) (R : Type) (Δ : Ctx) : Set where
  constructor blk
  field
    {older} : List Ctx
    blocks : Blocks Σ n R older
    start : Seq Σ n R older (entry Δ)

block : ∀ {Σ n R Bs Δ} → Blocks Σ n R Bs → Bs ∋ Δ → Blk Σ n R Δ
block (bs ▷ k) Z = blk bs k
block (bs ▷ k) (S l) = block bs l

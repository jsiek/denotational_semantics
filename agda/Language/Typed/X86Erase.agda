{-

  The erasure of X86ᵀ (Language/Typed/X86.agda) into X86
  (Language/X86.agda), a pilot (Theorems/TAL.agda): not a pass of the
  compiler, which ends at X86ᵀ, but the statement that typed select
  emits today's instructions (proof/Compiler/SelectTALErase.agda). The
  types, the proofs about registers and frame bounds and the operand
  coercion ↑ disappear; chk t x, d is X86's test of t on x and the move
  (check, Compiler/Select.agda); a slot is its level.

-}

module Language.Typed.X86Erase where

open import Language.Typed.Type
open import Language.Typed.X86
import Language.X86 as L
open import Compiler.Select using (check; select-atm)

open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Nat using (ℕ)
open import Data.Vec using (Vec; toList; map)

eArg : ∀ {Σ ψ τ} → Arg Σ ψ τ → L.Arg
eArg (atom a) = select-atm a
eArg (reg r _) = L.loc (L.reg r)
eArg (a ↑) = eArg a

eDst : ∀ {n ψ τ ψ'} → Dst n ψ τ ψ' → L.Loc
eDst (reg r) = L.reg r
eDst (slot {Δ' = Δ'} p _) = L.var (length Δ')

slot-of : ∀ {Δ : Ctx} {A} → Δ ∋ A → L.Arg
slot-of x = L.loc (L.var (lvl x))

eInstr : ∀ {Σ n ψ ψ'} → Instr Σ n ψ ψ' → List L.Instr
eInstr (movq a d) = L.movq (eArg a) (eDst d) ∷ []
eInstr (subq a r _) = L.subq (eArg a) (L.reg r) ∷ []
eInstr (cmpq a₂ a₁) = L.cmpq (eArg a₂) (eArg a₁) ∷ []
eInstr (sete d) = L.sete (eDst d) ∷ []
eInstr (testinl a) = L.testinl (eArg a) ∷ []
eInstr (alloc (pair c e) d) = L.alloc L.pair (eArg c ∷ eArg e ∷ []) (eDst d) ∷ []
eInstr (alloc (tuple as) d) = L.alloc L.tuple (toList (map eArg as)) (eDst d) ∷ []
eInstr (alloc (inl a) d) = L.alloc L.inl (eArg a ∷ []) (eDst d) ∷ []
eInstr (alloc (inr a) d) = L.alloc L.inr (eArg a ∷ []) (eDst d) ∷ []
eInstr (load (get i) a d) = L.load (L.get i) (eArg a) (eDst d) ∷ []
eInstr (load payload a d) = L.load L.payload (eArg a) (eDst d) ∷ []
eInstr (loadfst x r) = L.load L.fst (slot-of x) (L.reg r) ∷ []
eInstr (loadsnd {x = x} r) = L.load L.snd (slot-of x) (L.reg r) ∷ []
eInstr (callq a _ _) = L.callq (eArg a) ∷ []
eInstr (chk t x d) = check t (slot-of x) ++ L.movq (slot-of x) (eDst d) ∷ []

eSeq : ∀ {Σ n Bs ψ} → Seq Σ n Bs ψ → L.Block
eSeq (i ∷ k) = L.block (eInstr i ++ L.Block.instrs (eSeq k)) (L.Block.jump (eSeq k))
eSeq (retq _) = L.block [] L.retq
eSeq (jmp l) = L.block [] (L.jmp (lvl l))
eSeq (je l₁ l₂) = L.block [] (L.je (lvl l₁) (lvl l₂))

eBlocks : ∀ {Σ n Bs} → Blocks Σ n Bs → List L.Block
eBlocks [] = []
eBlocks (bs ▷ k) = eSeq k ∷ eBlocks bs

eBody : ∀ {Σ ψ} → Body Σ ψ → L.Body
eBody (body n bs k) = L.body n (eBlocks bs) (eSeq k)

eDefs : ∀ {Σ ms} → All (λ m → Body Σ (called m)) ms → List L.Body
eDefs [] = []
eDefs (d ∷ ds) = eBody d ∷ eDefs ds

erase : Program → L.Program
erase (program ds b) = L.program (eDefs ds) (eBody b)

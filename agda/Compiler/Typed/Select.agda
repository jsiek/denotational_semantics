{-

  Typed select instructions (CFGᵀ → X86), after Essentials of
  Compilation, as the untyped pass (Compiler/Select.agda). X86 stays
  untyped, and so does its machine.

  * A slot is the X86 variable at its level (its position from the
    oldest slot, Framework/Membership.lvl); a reference to a definition,
    and a label, are their levels too, which are the numbers X86 uses
    (counted from the oldest). The frame of a body has as many slots as
    the deepest level its tails write (depth).
  * inject is a move: an X86 value carries its own kind.
  * project t a errs unless a holds a value of tag t, and then moves a.
    The test is an existing X86 instruction that errs on a value of any
    other kind and otherwise only clobbers %rax or the flag (check):
    an integer: movq a, %rax; subq $0, %rax; a sum: testinl a; a
    function (a closure, a pair): load fst a, %rax; a tuple of n + 1
    components: load (get 0) a, %rax.
  * callc f a opens the closure f: load fst f, %rax (its code);
    load snd f, %rdi (its environment); movq a, %rsi; callq %rax.
  * The rest as in the untyped pass.

-}

module Compiler.Typed.Select where

open import Framework.Primitives using (Int)
open import Language.Prim using (sub; eq)
open import Language.Typed.Type
open import Framework.Membership using (_⊑_; lvl)
open import Language.Typed.CFG as CFG using (Tail; return; seq; goto; case; Blocks; _▷_)
import Language.Typed.Imp as I
open I using (var; lit; ref)
open import Language.X86

open import Data.Fin using (zero)
open import Data.Integer using (0ℤ)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Nat using (ℕ; suc; _⊔_)
open import Data.Vec using (Vec; toList; map)

select-atm : ∀ {Σ Δ A} → I.Atm Σ Δ A → Arg
select-atm (var x) = loc (var (lvl x))
select-atm (lit B c) = imm B c
select-atm (ref f) = label (lvl f)

{- instructions that err unless a holds a value of tag t -}
check : Tag → Arg → List Instr
check tint a = movq a (reg rax) ∷ subq (imm Int 0ℤ) (reg rax) ∷ []
check tsum a = testinl a ∷ []
check tfun a = load fst a (reg rax) ∷ []
check (ttup n i) a = load (get i) a (reg rax) ∷ []

{- s, computed into d -}
select-simple : ∀ {Σ Δ A} → I.Simple Σ Δ A → Loc → List Instr
select-simple (I.atm a) d = movq (select-atm a) d ∷ []
select-simple (I.pack c e) d = alloc pair (select-atm c ∷ select-atm e ∷ []) d ∷ []
select-simple (I.callc f a) d =
  load fst (select-atm f) (reg rax) ∷ load snd (select-atm f) (reg rdi) ∷ movq (select-atm a) (reg rsi)
  ∷ callq (loc (reg rax)) ∷ movq (loc (reg rax)) d ∷ []
select-simple (I.tuple as) d = alloc tuple (toList (map select-atm as)) d ∷ []
select-simple (I.get i a) d = load (get i) (select-atm a) d ∷ []
select-simple (I.inl a) d = alloc inl (select-atm a ∷ []) d ∷ []
select-simple (I.inr a) d = alloc inr (select-atm a ∷ []) d ∷ []
select-simple (I.prim sub a b) d =
  movq (select-atm a) (reg rax) ∷ subq (select-atm b) (reg rax) ∷ movq (loc (reg rax)) d ∷ []
select-simple (I.prim eq a b) d = cmpq (select-atm b) (select-atm a) ∷ sete d ∷ []
select-simple (I.inject G a) d = movq (select-atm a) d ∷ []
select-simple (I.project t a) d = check t (select-atm a) ++ movq (select-atm a) d ∷ []

select-tail : ∀ {Σ Bs Δ} → Tail Σ Bs Δ → Block
select-tail (return s) = block (select-simple s (reg rax)) retq
select-tail (seq {Δ'} p s t) =
  block (select-simple s (var (length Δ')) ++ Block.instrs (select-tail t)) (Block.jump (select-tail t))
select-tail (goto l) = block [] (jmp (lvl l))
select-tail (case {Δ'} a p l₁ l₂) =
  block (testinl (select-atm a) ∷ load payload (select-atm a) (var (length Δ')) ∷ []) (je (lvl l₁) (lvl l₂))

{- the number of slots a tail uses -}
depth : ∀ {Σ Bs Δ} → Tail Σ Bs Δ → ℕ
depth {Δ = Δ} (return s) = length Δ
depth {Δ = Δ} (seq p s t) = length Δ ⊔ depth t
depth {Δ = Δ} (goto l) = length Δ
depth {Δ = Δ} (case {Δ'} a p l₁ l₂) = length Δ ⊔ suc (length Δ')

select-blocks : ∀ {Σ Bs} → Blocks Σ Bs → List Block
select-blocks CFG.[] = []
select-blocks (bs ▷ t) = select-tail t ∷ select-blocks bs

blocks-depth : ∀ {Σ Bs} → Blocks Σ Bs → ℕ
blocks-depth CFG.[] = 0
blocks-depth (bs ▷ t) = depth t ⊔ blocks-depth bs

select-body : ∀ {Σ Δ} → List Instr → CFG.Body Σ Δ → Body
select-body pre (CFG.body bs t) =
  body (blocks-depth bs ⊔ depth t) (select-blocks bs)
    (block (pre ++ Block.instrs (select-tail t)) (Block.jump (select-tail t)))

{- the start of a definition takes its environment and argument from
   %rdi and %rsi into slots 0 and 1 -}
prologue : List Instr
prologue = movq (loc (reg rdi)) (var 0) ∷ movq (loc (reg rsi)) (var 1) ∷ []

{- the pass, for a whole program -}
select : CFG.Program → Program
select (CFG.program ds b) = program (defs ds) (select-body [] b)
  where
  defs : ∀ {Σ ns} → All (λ n → CFG.Body Σ (Any ∷ ⟪ tup n ⟫ ∷ [])) ns → List Body
  defs [] = []
  defs (d ∷ ds) = select-body prologue d ∷ defs ds

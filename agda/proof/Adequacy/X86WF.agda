{-

  Well-formed X86 programs, the precondition of soundness and adequacy
  for the X86 machine (Adequacy/X86.agda); compile-x86 produces them
  from closed ISWIM programs (Adequacy/X86CompileWF.agda).

  * Each label refers to an older definition (L, as RB for Clos5): the
    semantics interprets each definition with the table of the older
    ones only, while the machine looks labels up in the whole table.

  * Each slot read is within the frame (S): a slot beyond the frame
    reads as init = {ω}, while the machine errors.

  * The table of the program is consistent: soundness approximates the
    value of a location by a finite part of its denotation, which a
    binder accepts only if it is consistent.

  OK L S a says that the operand a satisfies these; Code L S is that the
  operands an instruction reads do (subq also reads its destination).

-}

module proof.Adequacy.X86WF where

open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.Domain using (Con)
open import Language.X86
open import Semantics.Graph.X86 using (table)

open import Data.List using (List; []; _∷_; length)
open import Data.List.Relation.Unary.All using (All)
open import Data.Nat using (ℕ; _<_; _⊔_)
open import Data.Product using (_×_)
open import Data.Unit using (⊤)

OK : (ℕ → Set) → (ℕ → Set) → Arg → Set
OK L S (loc (var x)) = S x
OK L S (loc (reg g)) = ⊤
OK L S (imm B k) = ⊤
OK L S (label k) = L k

Reads : (ℕ → Set) → (ℕ → Set) → Instr → Set
Reads L S (movq a d) = OK L S a
Reads L S (subq a d) = OK L S a × OK L S (loc d)
Reads L S (cmpq a₂ a₁) = OK L S a₂ × OK L S a₁
Reads L S (sete d) = ⊤
Reads L S (testinl a) = OK L S a
Reads L S (alloc s as d) = All (OK L S) as
Reads L S (load f a d) = OK L S a
Reads L S (callq a) = OK L S a

Code : (ℕ → Set) → (ℕ → Set) → List Instr → Set
Code L S [] = ⊤
Code L S (i ∷ is) = Reads L S i × Code L S is

{- every block of a body, labels below K and slots below n -}
BodyOK : ℕ → ℕ → Body → Set
BodyOK K n (body _ bs b) = All (λ c → Code (_< K) (_< n) (Block.instrs c)) (b ∷ bs)

{- the definitions, newest first -}
DefsWF : List Body → Set
DefsWF [] = ⊤
DefsWF (b ∷ bs) = BodyOK (length bs) (2 ⊔ Body.locals b) b × DefsWF bs

WF : Program → Set
WF (program ds b) = DefsWF ds × BodyOK (length ds) (Body.locals b) b × (∀ k → Con (table ds k))

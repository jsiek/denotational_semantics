{-

  Well-formed X86 programs, for the graph model with errors
  (Semantics/GraphErr/X86.agda): the precondition of soundness and
  adequacy for the X86 machine (GraphErr/X86.agda); the compilers produce
  them from closed ISWIM programs (Adequacy/GraphErr/EndToEnd.agda; for the
  preserved untyped compiler, GraphErr/X86CompileWF.agda in agda/Untyped/).

  Each label refers to an older definition (L): the semantics interprets
  each definition with the table of the older ones only, while the
  machine looks labels up in the whole table.

  Unlike in the graph model (Adequacy/X86WF.agda), nothing is required of
  the slots read: a slot beyond the frame reads as init = {ω}, and the
  machine errors there too. Nor is the table required to be consistent:
  the table of every program is (GraphErr/X86Consistent.agda).

  OK L a says that the operand a satisfies L; Code L is that the operands
  each instruction reads do.

-}

module proof.Adequacy.GraphErr.X86WF where

open import Language.X86

open import Data.List using (List; []; _∷_; _++_; length; map; replicate)
open import Data.List.Properties using (length-map; length-++; ++-assoc)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤_)
open import Data.Nat.Properties using (<-≤-trans; m≤n+m; n<1+n)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ-syntax)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (yes; no)

OK : (ℕ → Set) → Arg → Set
OK L (loc l) = ⊤
OK L (imm B k) = ⊤
OK L (label k) = L k

Reads : (ℕ → Set) → Instr → Set
Reads L (movq a d) = OK L a
Reads L (subq a d) = OK L a
Reads L (cmpq a₂ a₁) = OK L a₂ × OK L a₁
Reads L (sete d) = ⊤
Reads L (testinl a) = OK L a
Reads L (alloc s as d) = All (OK L) as
Reads L (load f a d) = OK L a
Reads L (callq a) = OK L a

Code : (ℕ → Set) → List Instr → Set
Code L [] = ⊤
Code L (i ∷ is) = Reads L i × Code L is

{- every block of a body, labels below K -}
BodyOK : ℕ → Body → Set
BodyOK K (body _ bs b) = All (λ c → Code (_< K) (Block.instrs c)) (b ∷ bs)

{- the definitions, newest first -}
DefsWF : List Body → Set
DefsWF [] = ⊤
DefsWF (b ∷ bs) = BodyOK (length bs) b × DefsWF bs

WF : Program → Set
WF (program ds b) = DefsWF ds × BodyOK (length ds) b

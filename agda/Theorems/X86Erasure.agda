{-

  An assurance, not part of the compiler or of the comparison (not in
  the totals): X86ᵀ (Language/Typed/X86.agda) is X86 (Language/X86.agda)
  with types. Erasing the types (erase, Language/Typed/X86Erase.agda)
  keeps the meaning of every X86ᵀ program, with no precondition but its
  typing, in the CEK column's machines (Semantics/CEK/Typed/X86.agda,
  Semantics/CEK/X86.agda): they are Equivalent (the same observations,
  o-error included, and divergence together). And the erased program
  errs only where X86ᵀ runs a chk that fails: none of X86's other
  trapped errors (a missing slot, label or definition, an unset
  register or flag, a value of the wrong kind) is reached. The proof is
  proof/Assurance/X86Erasure.agda.

  And the code select emits is, without its types, that of select into
  untyped X86, the target of the typed pipeline before X86ᵀ
  (Compiler/SelectX86.agda): the erasure drops the types, the proofs
  about registers and frame bounds and the coercion ↑, and expands
  chk t x, d to X86's test of t on x and the move
  (proof/Compiler/SelectErase.agda).

-}

module Theorems.X86Erasure where

open import Semantics.Observation using (o-error)
open import Semantics.CEK.Smallstep using (Equivalent; Terminates; Star; State; start)
open import Language.Typed.Type using (Tag; flat; Any; ⟪_⟫; _∋_)
open import Language.Typed.X86
open import Language.Typed.X86Erase using (erase)
open import Framework.Lookup using (_!_)
import Semantics.CEK.Typed.X86 as X86ᵀₘ
import Semantics.CEK.X86 as X86ₘ
import proof.Assurance.X86Erasure as Proof
import Language.Typed.CFG as CFGᵀ
open import Compiler.Select using (select)
import Compiler.SelectX86 as SelectX86
import proof.Compiler.SelectErase as SelectErase

open import Data.Bool using (false)
open import Data.List using (List)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_)

{- erasure keeps the meaning of every X86ᵀ program -}
erase-correct : ∀ (P : Program) → Equivalent (X86ᵀₘ.sem P) (X86ₘ.sem (erase P))
erase-correct = Proof.erase-correct

{- a state of the X86ᵀ machine at a chk t x, d that fails: slot x holds
   a value of another kind than t -}
data FailedChk {Σ : List ℕ} : X86ᵀₘ.State Σ → Set where
  failed : ∀ {n Bs Γ Δ O F ψ'} {t : Tag} {x : Δ ∋ Any}
    {d : Dst n (st (Γ [ rax ↦ nothing ]) Δ O false) (ty ⟪ flat t ⟫) ψ'} {k : Seq Σ n Bs ψ'} {bs σ η}
    {m : X86ᵀₘ.Mach Σ η (st Γ Δ O F)}
    → X86ᵀₘ.proj? t (X86ᵀₘ.frame m ! x) ≡ nothing → FailedChk (X86ᵀₘ.run (chk t x d ∷ k) bs σ η m)

{- the erased program errs only when X86ᵀ reaches a chk that fails (and,
   by erase-correct, it errs whenever X86ᵀ does) -}
erase-errors : ∀ (P : Program) → Terminates (X86ₘ.sem (erase P)) o-error
  → Σ[ s ∈ State (X86ᵀₘ.sem P) ] Star (X86ᵀₘ.sem P) (start (X86ᵀₘ.sem P)) s × FailedChk s
erase-errors P h with proj₂ (Equivalent.terminates (Proof.erase-correct P) o-error) h
... | s , τ , fin = s , τ , Proof.only-chk (Program.defs P) FailedChk failed s fin

{- select emits the instructions of select into untyped X86 -}
select-erase : ∀ (P : CFGᵀ.Program) → erase (select P) ≡ SelectX86.select P
select-erase = SelectErase.select-erase

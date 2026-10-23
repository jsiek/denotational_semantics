{-

  The machines of ISWIMμ and X86μ never stop with an error: a machine
  stops only when it returns a value to the empty continuation (stack),
  and no value is observed as o-error. Their steps have no error case
  (typed values are taken apart by total functions), so the proof is by
  inspection of the step function: every other state steps. The X86μ
  machine is also the reduction column's (it has no binders).

-}

module Mu.proof.Semantics.AbstractMachines.NoError where

open import Mu.Language.Type
open import Semantics.Observation using (Obs; o-error; Answer)
open import Semantics.CEK.Smallstep using (Terminates; Final; next; stop)
import Mu.Language.ISWIM as L
import Mu.Semantics.AbstractMachines.ISWIM as I
import Mu.Semantics.AbstractMachines.GlobalFun as C5
open import Mu.Language.X86
open import Mu.Semantics.AbstractMachines.X86 using (State; run; halt; retK; enter; step; sem; cast; regs; _⦅_⦆)
open import Mu.Framework.AllUtil using (All)

open import Data.List using (List; [])
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym)
open import Relation.Nullary using (¬_)

{- a machine whose final states stop with answers never stops with o-error -}
module _ {S : Set} {stp : S → _} {s₀ : S} where
  no-error : (∀ s {o} → stp s ≡ stop o → Answer o) → ¬ Terminates (Semantics.CEK.Smallstep.machine S stp s₀) o-error
  no-error h (s , _ , fin) = h s fin refl

{- ISWIMμ -----------------------------------------------------------------------}

iswim-answer : ∀ {A} (v : I.Val A) → Answer (I.obs v)
iswim-answer (I.clo _ _) ()
iswim-answer (I.const _) ()
iswim-answer (I.tup _) ()
iswim-answer (I.inl _) ()
iswim-answer (I.inr _) ()
iswim-answer (I.fold v) = iswim-answer v

iswim-stops : ∀ s {o} → I.step s ≡ stop o → Answer o
iswim-stops (I.eval (L.` x) ρ κ) ()
iswim-stops (I.eval (L.lam N) ρ κ) ()
iswim-stops (I.eval (L.app L M) ρ κ) ()
iswim-stops (I.eval (L.lit B c) ρ κ) ()
iswim-stops (I.eval (L.tuple Ms) ρ κ) ()
iswim-stops (I.eval (L.get i M) ρ κ) ()
iswim-stops (I.eval (L.inl M) ρ κ) ()
iswim-stops (I.eval (L.inr M) ρ κ) ()
iswim-stops (I.eval (L.case L M N) ρ κ) ()
iswim-stops (I.eval (L.prim p L M) ρ κ) ()
iswim-stops (I.eval (L.let′ M N) ρ κ) ()
iswim-stops (I.eval (L.fold M) ρ κ) ()
iswim-stops (I.eval (L.unfold M) ρ κ) ()
iswim-stops (I.ret v I.halt) refl = iswim-answer v
iswim-stops (I.ret f (I.appL M ρ κ)) ()
iswim-stops (I.ret w (I.appR (I.clo N ρ) κ)) ()
iswim-stops (I.ret v (I.tupK vs Ms ρ κ)) ()
iswim-stops (I.ret (I.tup vs) (I.getK i κ)) ()
iswim-stops (I.ret v (I.inlK κ)) ()
iswim-stops (I.ret v (I.inrK κ)) ()
iswim-stops (I.ret (I.inl v) (I.caseK M N ρ κ)) ()
iswim-stops (I.ret (I.inr v) (I.caseK M N ρ κ)) ()
iswim-stops (I.ret (I.const n) (I.primL p M ρ κ)) ()
iswim-stops (I.ret (I.const m) (I.primR p n κ)) ()
iswim-stops (I.ret v (I.letK N ρ κ)) ()
iswim-stops (I.ret v (I.foldK κ)) ()
iswim-stops (I.ret (I.fold v) (I.unfoldK κ)) ()

iswim-no-error : ∀ {A} (M : L.Tm [] A) → ¬ Terminates (I.sem M) o-error
iswim-no-error M = no-error iswim-stops

{- X86μ --------------------------------------------------------------------------}

clos5-answer : ∀ {Σ A} (v : C5.Val Σ A) → Answer (C5.obs v)
clos5-answer (C5.code _) ()
clos5-answer (C5.pack _ _) ()
clos5-answer (C5.const _) ()
clos5-answer (C5.tup _) ()
clos5-answer (C5.inl _) ()
clos5-answer (C5.inr _) ()
clos5-answer (C5.fold v) = clos5-answer v

module _ {Σ : List DSig} (ds : All (λ s → Body Σ (DSig.cod s) (called s)) Σ) where

  enter-next : ∀ {η A B} (c : C5.Val Σ (code η A B)) e w σ {o} → enter ds c e w σ ≡ stop o → Answer o
  enter-next (C5.code f) e w σ ()

  x86-stops : ∀ s {o} → step ds s ≡ stop o → Answer o
  x86-stops (run (movq a d ∷ k) bs σ η m) ()
  x86-stops (run (subq a r e ∷ k) bs σ η m) ()
  x86-stops (run (cmpq a₂ a₁ ∷ k) bs σ η m) ()
  x86-stops (run (sete d ∷ k) bs σ η m) ()
  x86-stops (run (alloc o d ∷ k) bs σ η m) ()
  x86-stops (run (load i a d ∷ k) bs σ η m) ()
  x86-stops (run (loadfst x r ∷ k) bs σ η m) ()
  x86-stops (run (loadsnd r ∷ k) bs σ η m) ()
  x86-stops (run (callq a e₁ e₂ ∷ k) bs σ η m) = enter-next _ _ _ _
  x86-stops (run (retq e) bs halt η m) refl = clos5-answer (cast e (regs m ⦅ rax ⦆))
  x86-stops (run (retq e) bs (retK k bs' φ σ) η m) ()
  x86-stops (run (jmp l) bs σ η m) ()
  x86-stops (run (case x p _ l₁ l₂) bs σ η m) ()

x86-no-error : ∀ {A} (P : Program A) → ¬ Terminates (sem P) o-error
x86-no-error (program ds (body n bs k)) = no-error (x86-stops ds)

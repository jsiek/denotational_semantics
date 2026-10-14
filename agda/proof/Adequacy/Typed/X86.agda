{-

  The typed compiler produces well-formed X86 programs
  (proof/Adequacy/X86WF.agda), so that today's soundness and adequacy for
  the X86 machine (proof/Adequacy/X86.agda) apply to compile-x86's
  output: its operands refer only to older definitions and read slots
  within the frame (proof/Adequacy/Typed/X86Refs.agda), and its table
  is consistent, since it means what the Clos5ᵀ table means (the table
  lemmas of the passes) and a label beyond the table means ∅.

-}

module proof.Adequacy.Typed.X86 where

open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.Domain using (Con; Con-⊆)
open import Language.Typed.Type hiding (_≟_)
import Language.Typed.Clos5 as C5
open import Language.X86 using (Program; program)
open import Compiler.EncloseScope using (Closed)
open import Compiler.Typed.RCO using (rco-program; rco)
open import Compiler.Typed.LiftLocals using (lift-program; lift)
open import Compiler.Typed.Explicate using (explicate; explicate-body)
open import Compiler.Typed.Select using (select; select-defs)
open import Compiler.Typed.Pipeline using (compile; compile₄; compile-x86)
import Semantics.Graph.X86 as X
open import proof.Semantics.Graph.Typed.Clos5 using (table-con)
open import proof.Correctness.Typed.Graph.RCOCorrect using (table-rco)
open import proof.Correctness.Typed.Graph.LiftLocalsCorrect using (table-lift)
open import proof.Correctness.Typed.Graph.ExplicateCorrect using (table-explicate)
open import proof.Correctness.Typed.Graph.SelectCorrect using (table-select; table-beyond)
open import proof.Compiler.Typed.GlobalizeOlder using (globalize-older)
open import proof.Adequacy.Typed.X86Refs using (code-wf; len-sel)
open import proof.Adequacy.X86WF using (WF)

open import Data.List using (List; []; _∷_; length)
open import Data.List.Relation.Unary.All using () renaming (map to All-map)
open import Data.Nat using (ℕ; _<_; _≟_; _<?_)
open import Data.Nat.Properties using (≮⇒≥; ≤∧≢⇒<; ≤-pred)
open import Data.Product using (Σ-syntax; _,_; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import Relation.Nullary using (yes; no)

{- every level below the length of a table is that of a reference -}
at : ∀ (Σ : List ℕ) k → k < length Σ → Σ[ n ∈ ℕ ] Σ[ f ∈ Σ ∋ n ] lvl f ≡ k
at (n ∷ Σ) k k< with k ≟ length Σ
... | yes refl = n , Z , refl
... | no k≢ with at Σ k (≤∧≢⇒< (≤-pred k<) k≢)
...   | m , f , e = m , S f , e

x86-con : ∀ (P : C5.Program) k → Con (X.table (Program.defs (select (explicate (lift-program (rco-program P))))) k)
x86-con (C5.program {Σ} ds M) k with k <? length Σ
... | yes k< with at Σ k k<
...   | _ , f , refl = Con-⊆ (table-con ds f) λ d d∈ →
  proj₁ (table-rco ds f) d (proj₁ (table-lift R f) d (proj₁ (table-explicate (All-map lift R) f) d
    (proj₁ (table-select (All-map explicate-body (All-map lift R)) f) d d∈)))
  where R = All-map (λ D → rco D (λ x → x)) ds
x86-con (C5.program {Σ} ds M) k | no k≮ =
  subst Con (sym (table-beyond (select-defs DS) k (subst (λ m → m Data.Nat.≤ k) (sym (len-sel DS)) (≮⇒≥ k≮)))) λ _ _ ()
  where DS = All-map explicate-body (All-map lift (All-map (λ D → rco D (λ x → x)) ds))

compile-x86-wf : ∀ M → Closed M → WF (compile-x86 M)
compile-x86-wf M _ with code-wf (compile M) (globalize-older (compile₄ M))
... | wd , wm = wd , wm , x86-con (compile M)

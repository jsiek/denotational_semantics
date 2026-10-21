{-

  The compiler, observed through the machines, in the graph model with
  errors: for a closed ISWIM program M, the ISWIM machine on M and the
  Clos5 machine on compile M (and the X86 machine on compile-x86 M) stop
  with an error together, stop with the same constants, stop with an
  answer together, and diverge together.

  Each follows from adequacy at both ends (Adequacy/GraphErr/ISWIM.agda,
  Clos5.agda, X86.agda) and from the compiler's correctness in the model
  (Correctness/GraphErr/CompilerCorrect.agda, Same).

-}

module Untyped.proof.Adequacy.GraphErr.EndToEnd where

open import Framework.Primitives using (base-rep)
open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.Domain using (Value; ω; ρ₀) renaming (const to dconst)
open import Framework.GraphModel.ErrorMonad using (val∈)
open import Language.ISWIM using (AST)
open import Semantics.Observation using (Obs; o-const; o-error; Converges; _⇔_)
open import proof.Semantics.CEK.Smallstep using (Terminates; Diverges)
open import Semantics.CEK.Smallstep using (Machine)
import Semantics.CEK.ISWIM as ISWIMₘ
import Untyped.Semantics.CEK.Clos5 as Clos5ₘ
import Semantics.CEK.X86 as X86ₘ
open import Untyped.Compiler.Pipeline using (compile; compile-x86)
open import Compiler.EncloseScope using (Closed)
open import Untyped.proof.Correctness.GraphErr.CompilerCorrect using (compile-same; compile-x86-same)
import proof.Adequacy.GraphErr.ISWIM as A
import Untyped.proof.Adequacy.GraphErr.Clos5 as A5
import Untyped.proof.Adequacy.GraphErr.X86CompileWF as Aₓ
open import proof.Adequacy.GraphErr.Agree using (Agree; agree; ⇔-sym) public

open import Data.Product using (_×_; Σ-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; subst)
open import Relation.Nullary using (¬_)

{- the ISWIM machine and the Clos5 machine on the compiled program -}
end-to-end : ∀ M → Closed M → Agree (ISWIMₘ.sem M) (Clos5ₘ.sem (compile M))
end-to-end M c =
  agree (compile-same M c) (A.error-iff M c) (A5.clos5-error-iff M c) (A.const-iff M c) (A5.clos5-const-iff M c)
    (A.converges-iff M c) (A5.clos5-converges-iff M c) (A.diverges-iff M c) (A5.clos5-diverges-iff M c)

{- the ISWIM machine and the X86 machine on the compiled program -}
end-to-end-x86 : ∀ M → Closed M → Agree (ISWIMₘ.sem M) (X86ₘ.sem (compile-x86 M))
end-to-end-x86 M c =
  agree (compile-x86-same M c) (A.error-iff M c) (Aₓ.x86-error-iff M c) (A.const-iff M c) (Aₓ.x86-const-iff M c)
    (A.converges-iff M c) (Aₓ.x86-converges-iff M c) (A.diverges-iff M c) (Aₓ.x86-diverges-iff M c)

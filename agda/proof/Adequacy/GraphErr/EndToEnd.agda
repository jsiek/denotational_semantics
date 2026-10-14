{-

  Adequacy of the graph model with errors for the typed compiler
  (Compiler/Pipeline.agda): the denotation of compile M (Clos5ᵀ)
  tells the three outcomes of the machine apart, for a closed ISWIM
  program M.

  Clos5ᵀ: not a logical relation of its own. The ISWIM machine on M and
  the Clos5ᵀ machine on compile M agree on every outcome (the CEK
  column, Correctness/CEK/PipelineSim.agda), the denotations of M
  and compile M are the Same (Correctness/GraphErr/
  CompilerCorrect.agda), and the ISWIM machine is adequate
  (Adequacy/GraphErr/ISWIM.agda).

-}

module proof.Adequacy.GraphErr.EndToEnd where

open import Framework.Primitives using (base-rep)
open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.Domain using (Value; ω; ρ₀) renaming (const to dconst)
open import Language.ISWIM using (AST)
open import Semantics.Observation using (o-const; o-error; Converges; _⇔_)
open import proof.Semantics.CEK.Smallstep using (Terminates; Diverges)
import Semantics.CEK.ISWIM as ISWIMₘ
import Semantics.CEK.Typed.Clos5 as Clos5ᵀₘ
open import Semantics.GraphErr.Typed.Clos5 using (⟦_⟧₅)
open import Semantics.GraphErr.ISWIM using (⟦_⟧)
open import Compiler.Pipeline using (compile; compile₄)
open import Compiler.EncloseScope using (Closed)
open import proof.Correctness.GraphErr.CompilerCorrect using (Same; compile-same₅)
open import proof.Correctness.CEK.PipelineSim using (compile-error; compile-const; compile-converges; compile-diverges)
import proof.Adequacy.GraphErr.ISWIM as A
open import proof.Compiler.GlobalizeOlder using (globalize-older)
open import proof.Adequacy.GraphErr.Agree using (Agree; agree; ⇔-sym; ⇔-trans; Same-sym; empty-Same) public

open import Data.List using (List; []; _∷_; length)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Product using (_×_; Σ-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Unit using (tt)
open import Data.Nat using (_<_)
open import Relation.Binary.PropositionalEquality using (_≢_; refl)
open import Relation.Nullary using (¬_)

{- The Clos5ᵀ machine ------------------------------------------------------------}

private
  S : ∀ M → Closed M → Same ⟦ compile M ⟧₅ (⟦ M ⟧ ρ₀)
  S M c = Same-sym (compile-same₅ M c)

clos5-error-iff : ∀ M → Closed M → (ω ∈ ⟦ compile M ⟧₅) ⇔ Terminates (Clos5ᵀₘ.sem (compile M)) o-error
clos5-error-iff M c = ⇔-trans (proj₁ (S M c)) (⇔-trans (A.error-iff M c) (compile-error M c))

clos5-const-iff : ∀ M → Closed M → ∀ {B} {k : base-rep B}
  → (dconst k ∈ ⟦ compile M ⟧₅) ⇔ Terminates (Clos5ᵀₘ.sem (compile M)) (o-const B k)
clos5-const-iff M c {B} {k} =
  ⇔-trans (proj₁ (proj₂ (S M c)) k) (⇔-trans (A.const-iff M c) (compile-const M c B k))

clos5-converges-iff : ∀ M → Closed M
  → (Σ[ d ∈ Value ] d ∈ ⟦ compile M ⟧₅ × d ≢ ω) ⇔ Converges (Terminates (Clos5ᵀₘ.sem (compile M)))
clos5-converges-iff M c =
  ⇔-trans (proj₂ (proj₂ (S M c))) (⇔-trans (A.converges-iff M c) (compile-converges M c))

clos5-diverges-iff : ∀ M → Closed M
  → Diverges (Clos5ᵀₘ.sem (compile M)) ⇔ (∀ d → ¬ (d ∈ ⟦ compile M ⟧₅))
clos5-diverges-iff M c =
  ⇔-trans (⇔-sym (compile-diverges M c))
    (⇔-trans (A.diverges-iff M c) ⟨ empty-Same (Same-sym (S M c)) , empty-Same (S M c) ⟩)

{- The compiler, observed through the machines ------------------------------------}

end-to-end : ∀ M → Closed M → Agree (ISWIMₘ.sem M) (Clos5ᵀₘ.sem (compile M))
end-to-end M c =
  agree (compile-same₅ M c) (A.error-iff M c) (clos5-error-iff M c) (A.const-iff M c) (clos5-const-iff M c)
    (A.converges-iff M c) (clos5-converges-iff M c) (A.diverges-iff M c) (clos5-diverges-iff M c)

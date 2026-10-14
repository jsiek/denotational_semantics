{-

  Adequacy of the graph model with errors for the typed compiler
  (Compiler/Typed/Pipeline.agda): the denotation of compile M (Clos5ᵀ)
  and of compile-x86 M (X86) tells the three outcomes of the machine
  apart, for a closed ISWIM program M.

  X86: the semantics and the machine are the untyped ones, so this is
  their adequacy (Adequacy/GraphErr/X86.agda) for well-formed programs,
  and the typed compiler's programs are well formed: its labels refer to
  older definitions (Adequacy/Typed/X86.agda proves more, slots in the
  frame and consistency, for the graph model's X86 adequacy).

  Clos5ᵀ: not a logical relation of its own. The ISWIM machine on M and
  the Clos5ᵀ machine on compile M agree on every outcome (the CEK
  column, Correctness/Typed/CEK/PipelineSim.agda), the denotations of M
  and compile M are the Same (Correctness/Typed/GraphErr/
  CompilerCorrect.agda), and the ISWIM machine is adequate
  (Adequacy/GraphErr/ISWIM.agda).

-}

module proof.Adequacy.Typed.GraphErr where

open import Framework.Primitives using (base-rep)
open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.Domain using (Value; ω; ρ₀) renaming (const to dconst)
open import Language.ISWIM using (AST)
open import Language.X86 using (Program; program; Body; body; Block; Instr; Arg; loc; imm; label;
  movq; subq; cmpq; sete; testinl; alloc; load; callq)
open import Semantics.Observation using (o-const; o-error; Converges; _⇔_)
open import proof.Semantics.CEK.Smallstep using (Terminates; Diverges)
import Semantics.CEK.ISWIM as ISWIMₘ
import Semantics.CEK.Typed.Clos5 as Clos5ᵀₘ
import Semantics.CEK.X86 as X86ₘ
open import Semantics.GraphErr.Typed.Clos5 using (⟦_⟧₅)
open import Semantics.GraphErr.ISWIM using (⟦_⟧)
open import Semantics.GraphErr.X86 using () renaming (⟦_⟧ₚ to ⟦_⟧ₓ)
open import Compiler.Typed.Pipeline using (compile; compile-x86)
open import Compiler.EncloseScope using (Closed)
open import proof.Correctness.Typed.GraphErr.CompilerCorrect using (Same; compile-same₅)
open import proof.Correctness.Typed.GraphErr.SelectCorrect using (compile-x86-same)
open import proof.Correctness.GraphErr.CompilerCorrect using (⇔-trans)
open import proof.Correctness.Typed.CEK.PipelineSim using (compile-error; compile-const; compile-converges; compile-diverges)
import proof.Adequacy.GraphErr.ISWIM as A
import proof.Adequacy.GraphErr.X86 as Aₓ
import proof.Adequacy.GraphErr.X86WF as E
import proof.Adequacy.X86WF as P
import proof.Adequacy.Typed.X86 as T
open import proof.Adequacy.GraphErr.EndToEnd using (Agree; agree; ⇔-sym) public

open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Product using (_×_; Σ-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Unit using (tt)
open import Data.Nat using (_<_)
open import Relation.Binary.PropositionalEquality using (_≢_; refl)
open import Relation.Nullary using (¬_)

{- The X86 programs of the typed compiler are well formed ----------------------}

{- the conditions of the graph model's X86 adequacy include those of the
   graph model with errors (which does not ask about slots) -}
private
  ok : ∀ {L S} a → P.OK L S a → E.OK L a
  ok (loc _) _ = tt
  ok (imm _ _) _ = tt
  ok (label _) r = r

  oks : ∀ {L S as} → All (P.OK L S) as → All (E.OK L) as
  oks [] = []
  oks {as = a ∷ _} (r ∷ rs) = ok a r ∷ oks rs

  reads : ∀ {L S} i → P.Reads L S i → E.Reads L i
  reads (movq a _) r = ok a r
  reads (subq a _) ⟨ r , _ ⟩ = ok a r
  reads (cmpq a₂ a₁) ⟨ r₂ , r₁ ⟩ = ⟨ ok a₂ r₂ , ok a₁ r₁ ⟩
  reads (sete _) _ = tt
  reads (testinl a) r = ok a r
  reads (alloc _ _ _) r = oks r
  reads (load _ a _) r = ok a r
  reads (callq a) r = ok a r

  code : ∀ {L S} is → P.Code L S is → E.Code L is
  code [] _ = tt
  code (i ∷ is) ⟨ r , rs ⟩ = ⟨ reads i r , code is rs ⟩

  blocks : ∀ {K n} cs → All (λ c → P.Code (_< K) (_< n) (Block.instrs c)) cs
    → All (λ c → E.Code (_< K) (Block.instrs c)) cs
  blocks [] [] = []
  blocks (c ∷ cs) (r ∷ rs) = code (Block.instrs c) r ∷ blocks cs rs

  body-ok : ∀ {K n} b → P.BodyOK K n b → E.BodyOK K b
  body-ok (body _ bs b) r = blocks (b ∷ bs) r

  defs : ∀ ds → P.DefsWF ds → E.DefsWF ds
  defs [] _ = tt
  defs (b ∷ bs) ⟨ r , rs ⟩ = ⟨ body-ok b r , defs bs rs ⟩

wf : ∀ P → P.WF P → E.WF P
wf (program ds b) ⟨ wd , ⟨ wb , _ ⟩ ⟩ = ⟨ defs ds wd , body-ok b wb ⟩

compile-x86-wf : ∀ M → Closed M → E.WF (compile-x86 M)
compile-x86-wf M c = wf (compile-x86 M) (T.compile-x86-wf M c)

x86-error-iff : ∀ M → Closed M → (ω ∈ ⟦ compile-x86 M ⟧ₓ) ⇔ Terminates (X86ₘ.sem (compile-x86 M)) o-error
x86-error-iff M c = Aₓ.error-iff (compile-x86 M) (compile-x86-wf M c)

x86-const-iff : ∀ M → Closed M → ∀ {B} {k : base-rep B}
  → (dconst k ∈ ⟦ compile-x86 M ⟧ₓ) ⇔ Terminates (X86ₘ.sem (compile-x86 M)) (o-const B k)
x86-const-iff M c = Aₓ.const-iff (compile-x86 M) (compile-x86-wf M c)

x86-converges-iff : ∀ M → Closed M
  → (Σ[ d ∈ Value ] d ∈ ⟦ compile-x86 M ⟧ₓ × d ≢ ω) ⇔ Converges (Terminates (X86ₘ.sem (compile-x86 M)))
x86-converges-iff M c = Aₓ.converges-iff (compile-x86 M) (compile-x86-wf M c)

x86-diverges-iff : ∀ M → Closed M
  → Diverges (X86ₘ.sem (compile-x86 M)) ⇔ (∀ d → ¬ (d ∈ ⟦ compile-x86 M ⟧ₓ))
x86-diverges-iff M c = Aₓ.diverges-iff (compile-x86 M) (compile-x86-wf M c)

{- The Clos5ᵀ machine ------------------------------------------------------------}

private
  Same-sym : ∀ {D E} → Same D E → Same E D
  Same-sym ⟨ e , ⟨ c , v ⟩ ⟩ = ⟨ ⇔-sym e , ⟨ (λ k → ⇔-sym (c k)) , ⇔-sym v ⟩ ⟩

  {- a set is empty exactly when it has neither ω nor another element -}
  empty-Same : ∀ {D E} → Same D E → (∀ d → ¬ (d ∈ D)) → (∀ d → ¬ (d ∈ E))
  empty-Same ⟨ ⟨ _ , ωE→ ⟩ , ⟨ _ , ⟨ _ , vE→ ⟩ ⟩ ⟩ empty d d∈ =
    let d≢ : d ≢ ω
        d≢ = λ { refl → empty ω (ωE→ d∈) }
        ⟨ d' , ⟨ d'∈ , _ ⟩ ⟩ = vE→ ⟨ d , ⟨ d∈ , d≢ ⟩ ⟩
    in empty d' d'∈

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

end-to-end-x86 : ∀ M → Closed M → Agree (ISWIMₘ.sem M) (X86ₘ.sem (compile-x86 M))
end-to-end-x86 M c =
  agree (compile-x86-same M c) (A.error-iff M c) (x86-error-iff M c) (A.const-iff M c) (x86-const-iff M c)
    (A.converges-iff M c) (x86-converges-iff M c) (A.diverges-iff M c) (x86-diverges-iff M c)

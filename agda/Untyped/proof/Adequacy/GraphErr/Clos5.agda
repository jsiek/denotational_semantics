{-

  Soundness and adequacy of the graph model with errors
  (Semantics/GraphErr/Clos5.agda, ⟦_⟧ₚ, here ⟦_⟧₅) for the Clos5 machine
  (Semantics/CEK/Clos5.agda), for well-formed programs (WF,
  Adequacy/GraphErr/Clos5WF.agda: each definition refers only to older
  ones and main to existing ones), which the compiler produces
  (compile-wf).

  Unlike the graph model, where errors and divergence both denote ∅
  (proof/Adequacy/Clos5.agda), the denotation tells all three outcomes of
  the machine apart:

    error-iff     : ω ∈ ⟦ P ⟧₅ exactly when the machine stops with an
                    error;
    const-iff     : const k ∈ ⟦ P ⟧₅ exactly when it stops with k;
    converges-iff : ⟦ P ⟧₅ has an element other than ω exactly when it
                    stops with an answer (and soundness/adequacy relate
                    the shapes of the answers and the elements);
    diverges-iff  : ⟦ P ⟧₅ is empty exactly when it diverges.

  and clos5-error-iff, clos5-const-iff, clos5-converges-iff and
  clos5-diverges-iff are these for the programs compile M of closed
  ISWIM programs M.

  Soundness is in GraphErr/Clos5Soundness.agda, adequacy (the logical
  relation) in GraphErr/Clos5LogRel.agda. Divergence from emptiness is
  constructive, as for ISWIM (Adequacy/GraphErr/ISWIM.agda): a run that
  reaches a final state reaches it with some observation, and soundness
  gives an element for each observation, including o-error.

-}

module Untyped.proof.Adequacy.GraphErr.Clos5 where

open import Framework.Primitives using (base-rep)
open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.Domain using (Value; ω) renaming (const to dconst)
open import Language.ISWIM using (AST)
open import Untyped.Language.Clos5 using (Program; program)
open import Untyped.Semantics.GraphErr.Clos5 using () renaming (⟦_⟧ₚ to ⟦_⟧₅)
open import Semantics.Observation
open import proof.Semantics.CEK.Smallstep
  using (Terminates; Diverges; diverges-not-terminates; never-final-diverges)
import Untyped.Semantics.CEK.Clos5 as Clos5ₘ
open import Untyped.Semantics.CEK.Clos5 using (ret; halt; obs)
open import Untyped.Compiler.Pipeline using (compile)
open import Compiler.CaptureScope using (Closed)
open import Untyped.proof.Compiler.HoistTable using (⊑-refl)
open import proof.Adequacy.Common using (ShapeOf; shape-answer; shape-const)
open import proof.Adequacy.GraphErr.Soundness using (shape-ω)
open import Untyped.proof.Adequacy.GraphErr.Clos5WF using (WF; compile-wf) public
open import Untyped.proof.Adequacy.GraphErr.Clos5Soundness using (soundness; sound-error) public
import Untyped.proof.Adequacy.GraphErr.Clos5Common as C
import Untyped.proof.Adequacy.GraphErr.Clos5LogRel as LR

open import Data.Product using (_×_; Σ-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (inj₁; inj₂)
open import Data.List using ([])
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; subst)
open import Relation.Nullary using (¬_)

{- Adequacy --------------------------------------------------------------------}

related : ∀ ds M → WF (program ds M) → ∀ {d} → d ∈ ⟦ program ds M ⟧₅ → LR.ℝ ds d [] M
related ds M ⟨ wfd , rb ⟩ d∈ = LR.adequate ds M (LR.tab ds ds ⊑-refl wfd) rb (LR.𝔾-[] ds) d∈

{- an element other than ω is witnessed by a run to an answer of its shape -}
adequacy : ∀ P → WF P → ∀ {d} → d ∈ ⟦ P ⟧₅ → d ≢ ω
  → Σ[ o ∈ Obs ] Terminates (Clos5ₘ.sem P) o × ShapeOf o d
adequacy (program ds M) wf {d} d∈ d≢ with LR.conv ds (related ds M wf d∈) d≢
... | ⟨ v , ⟨ e , r ⟩ ⟩ =
  ⟨ obs v , ⟨ ⟨ ret v halt , ⟨ C.↠→star ds (e halt) , refl ⟩ ⟩ , LR.𝕍-shape ds d v r ⟩ ⟩

{- ω is witnessed by a run to an error -}
adequacy-error : ∀ P → WF P → ω ∈ ⟦ P ⟧₅ → Terminates (Clos5ₘ.sem P) o-error
adequacy-error (program ds M) wf ω∈ with LR.err ds (related ds M wf ω∈) halt
... | ⟨ t , ⟨ τ , st ⟩ ⟩ = ⟨ t , ⟨ C.↠→star ds τ , st ⟩ ⟩

{- every element is witnessed by a run that terminates -}
adequacy-terminates : ∀ P → WF P → ∀ {d} → d ∈ ⟦ P ⟧₅ → Σ[ o ∈ Obs ] Terminates (Clos5ₘ.sem P) o
adequacy-terminates (program ds M) wf {d} d∈ with related ds M wf d∈
... | inj₁ ⟨ refl , _ ⟩ = ⟨ o-error , adequacy-error (program ds M) wf d∈ ⟩
... | inj₂ ⟨ v , ⟨ e , _ ⟩ ⟩ = ⟨ obs v , ⟨ ret v halt , ⟨ C.↠→star ds (e halt) , refl ⟩ ⟩ ⟩

{- Soundness, for every observation -------------------------------------------}

sound-const : ∀ P → WF P → ∀ {B} {k : base-rep B}
  → Terminates (Clos5ₘ.sem P) (o-const B k) → dconst k ∈ ⟦ P ⟧₅
sound-const P wf t with soundness P wf t (λ ())
... | ⟨ d , ⟨ d∈ , refl ⟩ ⟩ = d∈

{- a program that terminates has an element in its denotation -}
sound-terminates : ∀ P → WF P → ∀ {o} → Terminates (Clos5ₘ.sem P) o → Σ[ d ∈ Value ] d ∈ ⟦ P ⟧₅
sound-terminates P wf {o-error} t = ⟨ ω , sound-error P wf t ⟩
sound-terminates P wf {o-const B k} t = ⟨ _ , proj₁ (proj₂ (soundness P wf t (λ ()))) ⟩
sound-terminates P wf {o-fun} t = ⟨ _ , proj₁ (proj₂ (soundness P wf t (λ ()))) ⟩
sound-terminates P wf {o-tuple os} t = ⟨ _ , proj₁ (proj₂ (soundness P wf t (λ ()))) ⟩
sound-terminates P wf {o-inl o} t = ⟨ _ , proj₁ (proj₂ (soundness P wf t (λ ()))) ⟩
sound-terminates P wf {o-inr o} t = ⟨ _ , proj₁ (proj₂ (soundness P wf t (λ ()))) ⟩

{- Characterizations, for well-formed programs ----------------------------------}

{- ω ∈ ⟦ P ⟧₅ exactly when the machine stops with an error -}
error-iff : ∀ P → WF P → (ω ∈ ⟦ P ⟧₅) ⇔ Terminates (Clos5ₘ.sem P) o-error
error-iff P wf = ⟨ adequacy-error P wf , sound-error P wf ⟩

{- ⟦ P ⟧₅ contains the constant k exactly when the machine stops with it -}
const-iff : ∀ P → WF P → ∀ {B} {k : base-rep B}
  → (dconst k ∈ ⟦ P ⟧₅) ⇔ Terminates (Clos5ₘ.sem P) (o-const B k)
const-iff P wf {B} {k} = ⟨ A , sound-const P wf ⟩
  where
  A : dconst k ∈ ⟦ P ⟧₅ → Terminates (Clos5ₘ.sem P) (o-const B k)
  A k∈ with adequacy P wf k∈ (λ ())
  ... | ⟨ o , ⟨ t , sh ⟩ ⟩ = subst (Terminates (Clos5ₘ.sem P)) (shape-const sh) t

{- ⟦ P ⟧₅ has an element other than ω exactly when the machine stops
   with an answer -}
converges-iff : ∀ P → WF P
  → (Σ[ d ∈ Value ] d ∈ ⟦ P ⟧₅ × d ≢ ω) ⇔ Converges (Terminates (Clos5ₘ.sem P))
converges-iff P wf = ⟨ A , B ⟩
  where
  A : (Σ[ d ∈ Value ] d ∈ ⟦ P ⟧₅ × d ≢ ω) → Converges (Terminates (Clos5ₘ.sem P))
  A ⟨ d , ⟨ d∈ , d≢ ⟩ ⟩ with adequacy P wf d∈ d≢
  ... | ⟨ o , ⟨ t , sh ⟩ ⟩ = ⟨ o , ⟨ shape-answer sh , t ⟩ ⟩
  B : Converges (Terminates (Clos5ₘ.sem P)) → Σ[ d ∈ Value ] d ∈ ⟦ P ⟧₅ × d ≢ ω
  B ⟨ o , ⟨ ans , t ⟩ ⟩ with soundness P wf t ans
  ... | ⟨ d , ⟨ d∈ , sh ⟩ ⟩ = ⟨ d , ⟨ d∈ , (λ { refl → shape-ω o sh }) ⟩ ⟩

{- ⟦ P ⟧₅ is empty exactly when the machine diverges -}
diverges-iff : ∀ P → WF P → Diverges (Clos5ₘ.sem P) ⇔ (∀ d → ¬ (d ∈ ⟦ P ⟧₅))
diverges-iff P wf =
  ⟨ (λ div d d∈ → diverges-not-terminates div (proj₂ (adequacy-terminates P wf d∈)))
  , (λ empty → never-final-diverges (λ σ fin → let ⟨ d , d∈ ⟩ = sound-terminates P wf ⟨ _ , ⟨ σ , fin ⟩ ⟩
                                              in empty d d∈)) ⟩

{- The programs of the compiler ---------------------------------------------------}

clos5-error-iff : ∀ M → Closed M → (ω ∈ ⟦ compile M ⟧₅) ⇔ Terminates (Clos5ₘ.sem (compile M)) o-error
clos5-error-iff M _ = error-iff (compile M) (compile-wf M)

clos5-const-iff : ∀ M → Closed M → ∀ {B} {k : base-rep B}
  → (dconst k ∈ ⟦ compile M ⟧₅) ⇔ Terminates (Clos5ₘ.sem (compile M)) (o-const B k)
clos5-const-iff M _ = const-iff (compile M) (compile-wf M)

clos5-converges-iff : ∀ M → Closed M
  → (Σ[ d ∈ Value ] d ∈ ⟦ compile M ⟧₅ × d ≢ ω) ⇔ Converges (Terminates (Clos5ₘ.sem (compile M)))
clos5-converges-iff M _ = converges-iff (compile M) (compile-wf M)

clos5-diverges-iff : ∀ M → Closed M
  → Diverges (Clos5ₘ.sem (compile M)) ⇔ (∀ d → ¬ (d ∈ ⟦ compile M ⟧₅))
clos5-diverges-iff M _ = diverges-iff (compile M) (compile-wf M)

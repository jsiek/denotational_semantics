{-

  Soundness and adequacy of the graph model with errors
  (Semantics/GraphErr/X86.agda, ⟦_⟧ₚ, here ⟦_⟧ₓ) for the X86 machine
  (Semantics/CEK/X86.agda), for well-formed programs (WF,
  Adequacy/GraphErr/X86WF.agda: each label refers to an older
  definition), which the compilers produce. As for Clos5
  (Adequacy/GraphErr/Clos5.agda), the denotation tells all three outcomes
  of the machine apart:

    error-iff     : ω ∈ ⟦ P ⟧ₓ exactly when the machine stops with an
                    error;
    const-iff     : const k ∈ ⟦ P ⟧ₓ exactly when it stops with k;
    converges-iff : ⟦ P ⟧ₓ has an element other than ω exactly when it
                    stops with an answer (and soundness/adequacy relate
                    the shapes of the answers and the elements);
    diverges-iff  : ⟦ P ⟧ₓ is empty exactly when it diverges.

  (For the programs compile-x86 M of the typed compiler, see
  Adequacy/Typed/GraphErr.agda.)

  Soundness is in GraphErr/X86Soundness.agda (with the consistency of
  the table of every program, GraphErr/X86Consistent.agda), adequacy
  (the logical relation) in GraphErr/X86LogRel.agda. Divergence from
  emptiness is constructive, as for ISWIM: a run that reaches a final
  state reaches it with some observation, and soundness gives an element
  for each observation, including o-error.

-}

module proof.Adequacy.GraphErr.X86 where

open import Framework.Primitives using (base-rep)
open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.Domain using (Value; ω) renaming (const to dconst)
open import Language.ISWIM using (AST)
open import Language.X86 using (Program; program; body)
open import Semantics.GraphErr.X86 using () renaming (⟦_⟧ₚ to ⟦_⟧ₓ)
open import Semantics.Observation
open import proof.Semantics.CEK.Smallstep
  using (Terminates; Diverges; diverges-not-terminates; never-final-diverges)
import Semantics.CEK.X86 as X86ₘ
open import Semantics.CEK.X86 using (halt; halt?; obs)
open import proof.Adequacy.Common using (ShapeOf; shape-answer; shape-const)
open import proof.Adequacy.GraphErr.Soundness using (shape-ω)
open import proof.Adequacy.GraphErr.X86WF using (WF) public
open import proof.Adequacy.GraphErr.X86Consistent using (table-con) public
open import proof.Adequacy.GraphErr.X86Soundness using (soundness; sound-error) public
import proof.Adequacy.GraphErr.X86Common as C
import proof.Adequacy.GraphErr.X86LogRel as LR

open import Data.Empty using (⊥-elim)
open import Data.Product using (_×_; Σ-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; subst)
open import Relation.Nullary using (¬_)

{- Adequacy --------------------------------------------------------------------}

{- an element other than ω is witnessed by a run to an answer of its shape -}
adequacy : ∀ P → WF P → ∀ {d} → d ∈ ⟦ P ⟧ₓ → d ≢ ω
  → Σ[ o ∈ Obs ] Terminates (X86ₘ.sem P) o × ShapeOf o d
adequacy (program ds (body n bs b)) ⟨ wfd , ok ⟩ {d} d∈ d≢ with LR.adequate-main ds wfd ok d∈
... | inj₁ ⟨ e , _ ⟩ = ⊥-elim (d≢ e)
... | inj₂ ⟨ v , ⟨ r , rv ⟩ ⟩ with r halt
... | ⟨ _ , ⟨ _ , ⟨ _ , ⟨ _ , ⟨ τ , e ⟩ ⟩ ⟩ ⟩ ⟩ =
  ⟨ obs v , ⟨ ⟨ _ , ⟨ C.↠→star ds τ , cong halt? e ⟩ ⟩ , LR.𝕍-shape ds d v rv ⟩ ⟩

{- ω is witnessed by a run to an error -}
adequacy-error : ∀ P → WF P → ω ∈ ⟦ P ⟧ₓ → Terminates (X86ₘ.sem P) o-error
adequacy-error (program ds (body n bs b)) ⟨ wfd , ok ⟩ ω∈ with LR.adequate-main ds wfd ok ω∈
... | inj₁ ⟨ _ , er ⟩ with er halt
... | ⟨ t , ⟨ τ , st ⟩ ⟩ = ⟨ t , ⟨ C.↠→star ds τ , st ⟩ ⟩
adequacy-error (program ds (body n bs b)) ⟨ wfd , ok ⟩ ω∈ | inj₂ ⟨ v , ⟨ _ , rv ⟩ ⟩ = ⊥-elim (LR.𝕍-ω ds {v} rv)

{- every element is witnessed by a run that terminates -}
adequacy-terminates : ∀ P → WF P → ∀ {d} → d ∈ ⟦ P ⟧ₓ → Σ[ o ∈ Obs ] Terminates (X86ₘ.sem P) o
adequacy-terminates (program ds (body n bs b)) wf@(⟨ wfd , ok ⟩) {d} d∈ with LR.adequate-main ds wfd ok d∈
... | inj₁ ⟨ refl , _ ⟩ = ⟨ o-error , adequacy-error (program ds (body n bs b)) wf d∈ ⟩
... | inj₂ ⟨ v , ⟨ r , _ ⟩ ⟩ with r halt
... | ⟨ _ , ⟨ _ , ⟨ _ , ⟨ _ , ⟨ τ , e ⟩ ⟩ ⟩ ⟩ ⟩ = ⟨ obs v , ⟨ _ , ⟨ C.↠→star ds τ , cong halt? e ⟩ ⟩ ⟩

{- Soundness, for every observation -------------------------------------------}

sound-const : ∀ P → WF P → ∀ {B} {k : base-rep B}
  → Terminates (X86ₘ.sem P) (o-const B k) → dconst k ∈ ⟦ P ⟧ₓ
sound-const P wf t with soundness P wf t (λ ())
... | ⟨ d , ⟨ d∈ , refl ⟩ ⟩ = d∈

{- a program that terminates has an element in its denotation -}
sound-terminates : ∀ P → WF P → ∀ {o} → Terminates (X86ₘ.sem P) o → Σ[ d ∈ Value ] d ∈ ⟦ P ⟧ₓ
sound-terminates P wf {o-error} t = ⟨ ω , sound-error P wf t ⟩
sound-terminates P wf {o-const B k} t = ⟨ _ , proj₁ (proj₂ (soundness P wf t (λ ()))) ⟩
sound-terminates P wf {o-fun} t = ⟨ _ , proj₁ (proj₂ (soundness P wf t (λ ()))) ⟩
sound-terminates P wf {o-tuple os} t = ⟨ _ , proj₁ (proj₂ (soundness P wf t (λ ()))) ⟩
sound-terminates P wf {o-inl o} t = ⟨ _ , proj₁ (proj₂ (soundness P wf t (λ ()))) ⟩
sound-terminates P wf {o-inr o} t = ⟨ _ , proj₁ (proj₂ (soundness P wf t (λ ()))) ⟩

{- Characterizations, for well-formed programs ----------------------------------}

{- ω ∈ ⟦ P ⟧ₓ exactly when the machine stops with an error -}
error-iff : ∀ P → WF P → (ω ∈ ⟦ P ⟧ₓ) ⇔ Terminates (X86ₘ.sem P) o-error
error-iff P wf = ⟨ adequacy-error P wf , sound-error P wf ⟩

{- ⟦ P ⟧ₓ contains the constant k exactly when the machine stops with it -}
const-iff : ∀ P → WF P → ∀ {B} {k : base-rep B}
  → (dconst k ∈ ⟦ P ⟧ₓ) ⇔ Terminates (X86ₘ.sem P) (o-const B k)
const-iff P wf {B} {k} = ⟨ A , sound-const P wf ⟩
  where
  A : dconst k ∈ ⟦ P ⟧ₓ → Terminates (X86ₘ.sem P) (o-const B k)
  A k∈ with adequacy P wf k∈ (λ ())
  ... | ⟨ o , ⟨ t , sh ⟩ ⟩ = subst (Terminates (X86ₘ.sem P)) (shape-const sh) t

{- ⟦ P ⟧ₓ has an element other than ω exactly when the machine stops
   with an answer -}
converges-iff : ∀ P → WF P
  → (Σ[ d ∈ Value ] d ∈ ⟦ P ⟧ₓ × d ≢ ω) ⇔ Converges (Terminates (X86ₘ.sem P))
converges-iff P wf = ⟨ A , B ⟩
  where
  A : (Σ[ d ∈ Value ] d ∈ ⟦ P ⟧ₓ × d ≢ ω) → Converges (Terminates (X86ₘ.sem P))
  A ⟨ d , ⟨ d∈ , d≢ ⟩ ⟩ with adequacy P wf d∈ d≢
  ... | ⟨ o , ⟨ t , sh ⟩ ⟩ = ⟨ o , ⟨ shape-answer sh , t ⟩ ⟩
  B : Converges (Terminates (X86ₘ.sem P)) → Σ[ d ∈ Value ] d ∈ ⟦ P ⟧ₓ × d ≢ ω
  B ⟨ o , ⟨ ans , t ⟩ ⟩ with soundness P wf t ans
  ... | ⟨ d , ⟨ d∈ , sh ⟩ ⟩ = ⟨ d , ⟨ d∈ , (λ { refl → shape-ω o sh }) ⟩ ⟩

{- ⟦ P ⟧ₓ is empty exactly when the machine diverges -}
diverges-iff : ∀ P → WF P → Diverges (X86ₘ.sem P) ⇔ (∀ d → ¬ (d ∈ ⟦ P ⟧ₓ))
diverges-iff P wf =
  ⟨ (λ div d d∈ → diverges-not-terminates div (proj₂ (adequacy-terminates P wf d∈)))
  , (λ empty → never-final-diverges (λ σ fin → let ⟨ d , d∈ ⟩ = sound-terminates P wf ⟨ _ , ⟨ σ , fin ⟩ ⟩
                                              in empty d d∈)) ⟩

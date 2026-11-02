{-

  Soundness and adequacy of the graph model with errors
  (Semantics/GraphErr/ISWIM.agda) for the ISWIM machine
  (Semantics/CEK/ISWIM.agda), for closed programs, started in ρ₀ (every
  variable means {ω}) and in the empty environment.

  Unlike the graph model, where errors and divergence both denote ∅
  (proof/Adequacy/ISWIM.agda), the denotation tells all three outcomes
  of the machine apart:

    error-iff     : ω ∈ ⟦ M ⟧ ρ₀ exactly when the machine stops with an
                    error;
    const-iff     : const k ∈ ⟦ M ⟧ ρ₀ exactly when it stops with k;
    converges-iff : ⟦ M ⟧ ρ₀ has an element other than ω exactly when it
                    stops with an answer (and soundness/adequacy relate
                    the shapes of the answers and the elements);
    diverges-iff  : ⟦ M ⟧ ρ₀ is empty exactly when it diverges.

  Soundness is in GraphErr/Soundness.agda, adequacy (the logical
  relation) in GraphErr/LogRel.agda. Divergence from emptiness is
  constructive: the machine is a total step function, so a run that
  reaches a final state reaches it with some observation, and soundness
  gives an element for each observation, including o-error.

-}

module proof.Adequacy.GraphErr.ISWIM where

open import Framework.Primitives using (Base; base-rep)
open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.Domain using (Value; ω; ρ₀) renaming (const to dconst)
open import Language.ISWIM
open import proof.Semantics.GraphErr.ISWIM using (⟦_⟧)
open import Semantics.Observation
open import proof.Semantics.CEK.Smallstep
  using (Terminates; Diverges; diverges-not-terminates; never-final-diverges; next; stop)
open import Semantics.CEK.ISWIM
open import Compiler.CaptureScope using (Closed)
open import proof.Framework.Syntax.Uses Op sig using (uses-bound)
open import proof.Adequacy.Common using (ShapeOf; shape-answer; shape-const; ↠→star)
open import proof.Adequacy.GraphErr.Soundness using (soundness; sound-error; shape-ω) public
open import proof.Adequacy.GraphErr.LogRel

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([])
open import Data.Nat using (_<_)
open import Data.Nat.Properties using (n≮0)
open import Data.Product using (_×_; Σ-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; subst)
open import Relation.Nullary using (¬_)

{- Adequacy --------------------------------------------------------------------}

closed-𝔾 : ∀ M → Closed M → 𝔾 (UsesP M) ρ₀ []
closed-𝔾 M c x u = ⊥-elim (n≮0 (subst (x <_) c (uses-bound x M u)))

{- an element other than ω is witnessed by a run to an answer of its shape -}
adequacy : ∀ M → Closed M → ∀ {d} → d ∈ ⟦ M ⟧ ρ₀ → d ≢ ω
  → Σ[ o ∈ Obs ] Terminates (sem M) o × ShapeOf o d
adequacy M c {d} d∈ d≢ with conv (adequate M (closed-𝔾 M c) d∈) d≢
... | ⟨ v , ⟨ e , r ⟩ ⟩ =
  ⟨ obs v , ⟨ ⟨ ret v halt , ⟨ ↠→star (e halt) , refl ⟩ ⟩ , 𝕍-shape d v r ⟩ ⟩

{- ω is witnessed by a run to an error -}
adequacy-error : ∀ M → Closed M → ω ∈ ⟦ M ⟧ ρ₀ → Terminates (sem M) o-error
adequacy-error M c ω∈ with err (adequate M (closed-𝔾 M c) ω∈) halt
... | ⟨ t , ⟨ τ , st ⟩ ⟩ = ⟨ t , ⟨ ↠→star τ , st ⟩ ⟩

{- every element is witnessed by a run that terminates -}
adequacy-terminates : ∀ M → Closed M → ∀ {d} → d ∈ ⟦ M ⟧ ρ₀ → Σ[ o ∈ Obs ] Terminates (sem M) o
adequacy-terminates M c {d} d∈ with adequate M (closed-𝔾 M c) d∈
... | inj₁ ⟨ refl , _ ⟩ = ⟨ o-error , adequacy-error M c d∈ ⟩
... | inj₂ ⟨ v , ⟨ e , _ ⟩ ⟩ = ⟨ obs v , ⟨ ret v halt , ⟨ ↠→star (e halt) , refl ⟩ ⟩ ⟩

{- Soundness, for every observation -------------------------------------------}

sound-const : ∀ M {B} {k : base-rep B} → Terminates (sem M) (o-const B k) → dconst k ∈ ⟦ M ⟧ ρ₀
sound-const M t with soundness M t (λ ())
... | ⟨ d , ⟨ d∈ , refl ⟩ ⟩ = d∈

{- a program that terminates has an element in its denotation -}
sound-terminates : ∀ M {o} → Terminates (sem M) o → Σ[ d ∈ Value ] d ∈ ⟦ M ⟧ ρ₀
sound-terminates M {o-error} t = ⟨ ω , sound-error M t ⟩
sound-terminates M {o-const B k} t = ⟨ _ , proj₁ (proj₂ (soundness M t (λ ()))) ⟩
sound-terminates M {o-fun} t = ⟨ _ , proj₁ (proj₂ (soundness M t (λ ()))) ⟩
sound-terminates M {o-tuple os} t = ⟨ _ , proj₁ (proj₂ (soundness M t (λ ()))) ⟩
sound-terminates M {o-inl o} t = ⟨ _ , proj₁ (proj₂ (soundness M t (λ ()))) ⟩
sound-terminates M {o-inr o} t = ⟨ _ , proj₁ (proj₂ (soundness M t (λ ()))) ⟩

{- Characterizations ------------------------------------------------------------}

{- ω ∈ ⟦ M ⟧ ρ₀ exactly when the machine stops with an error -}
error-iff : ∀ M → Closed M → (ω ∈ ⟦ M ⟧ ρ₀) ⇔ Terminates (sem M) o-error
error-iff M c = ⟨ adequacy-error M c , sound-error M ⟩

{- ⟦ M ⟧ ρ₀ contains the constant k exactly when the machine stops with it -}
const-iff : ∀ M → Closed M → ∀ {B} {k : base-rep B}
  → (dconst k ∈ ⟦ M ⟧ ρ₀) ⇔ Terminates (sem M) (o-const B k)
const-iff M c {B} {k} = ⟨ A , sound-const M ⟩
  where
  A : dconst k ∈ ⟦ M ⟧ ρ₀ → Terminates (sem M) (o-const B k)
  A k∈ with adequacy M c k∈ (λ ())
  ... | ⟨ o , ⟨ t , sh ⟩ ⟩ = subst (Terminates (sem M)) (shape-const sh) t

{- ⟦ M ⟧ ρ₀ has an element other than ω exactly when the machine stops
   with an answer -}
converges-iff : ∀ M → Closed M
  → (Σ[ d ∈ Value ] d ∈ ⟦ M ⟧ ρ₀ × d ≢ ω) ⇔ Converges (Terminates (sem M))
converges-iff M c = ⟨ A , B ⟩
  where
  A : (Σ[ d ∈ Value ] d ∈ ⟦ M ⟧ ρ₀ × d ≢ ω) → Converges (Terminates (sem M))
  A ⟨ d , ⟨ d∈ , d≢ ⟩ ⟩ with adequacy M c d∈ d≢
  ... | ⟨ o , ⟨ t , sh ⟩ ⟩ = ⟨ o , ⟨ shape-answer sh , t ⟩ ⟩
  B : Converges (Terminates (sem M)) → Σ[ d ∈ Value ] d ∈ ⟦ M ⟧ ρ₀ × d ≢ ω
  B ⟨ o , ⟨ ans , t ⟩ ⟩ with soundness M t ans
  ... | ⟨ d , ⟨ d∈ , sh ⟩ ⟩ = ⟨ d , ⟨ d∈ , (λ { refl → shape-ω o sh }) ⟩ ⟩

{- ⟦ M ⟧ ρ₀ is empty exactly when the machine diverges -}
diverges-iff : ∀ M → Closed M → Diverges (sem M) ⇔ (∀ d → ¬ (d ∈ ⟦ M ⟧ ρ₀))
diverges-iff M c =
  ⟨ (λ div d d∈ → diverges-not-terminates div (proj₂ (adequacy-terminates M c d∈)))
  , (λ empty → never-final-diverges (λ σ fin → let ⟨ d , d∈ ⟩ = sound-terminates M ⟨ _ , ⟨ σ , fin ⟩ ⟩
                                              in empty d d∈)) ⟩

{-

  Soundness and adequacy of the graph model of ISWIMμ
  (Mu/Semantics/GraphModel/ISWIM.agda) with respect to its clocked
  interpreter (Mu/Semantics/ClockedInterpreters/ISWIM.agda), for closed programs of
  any type, started in ρ₀ on the denotational side and in the empty
  environment on the interpreter's, as Mu/proof/Adequacy/AbstractMachines/ISWIM.agda
  is for the ISWIMμ machine:

    soundness (Mu/proof/Adequacy/Soundness.agda): what the interpreter
      returns at some clock denotes a part of ⟦ M ⟧ ρ₀, and it never
      errs;
    adequacy (Mu/proof/Adequacy/LogRel.agda): every d ∈ ⟦ M ⟧ ρ₀ is
      related to the value the interpreter returns from some clock on.

  So ⟦ M ⟧ ρ₀ contains const k exactly when the interpreter terminates
  with o-const B k (const-iff), and it is empty exactly when the
  interpreter diverges (diverges-iff). This is the source half of the
  graph model's end-to-end theorem (Mu/proof/Adequacy/EndToEnd.agda),
  and the bridge at ISWIMμ of the mixed proof, which joins a pass
  proved in the graph model to passes proved by the interpreters
  (Mu/proof/Mixed/CompilerMixed.agda).

-}

module Mu.proof.Adequacy.ISWIM where

open import Framework.Primitives using (base-rep)
open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.Domain using (Value) renaming (const to dconst)
open import Mu.Semantics.GraphModel.Closed using (ρ₀)
open import proof.Semantics.Interp.Clock using (Result; timeout; ret; outcome; Terminates; Diverges)
open import Mu.Language.ISWIM using (Tm)
open import Mu.Semantics.GraphModel.ISWIM using (⟦_⟧)
open import Mu.Semantics.ClockedInterpreters.ISWIM using (Val; eval; sem; obs)
open import Semantics.Observation using (o-const; _⇔_)
open import Mu.proof.Adequacy.Soundness using (timeout; ret; Sound; sound; 𝒱-const; 𝒱-ne)
open import Mu.proof.Adequacy.LogRel using (𝕍; adequate; 𝕍-const)

open import Data.Empty using (⊥-elim)
open import Data.List using ([])
open import Mu.Framework.AllUtil using ([])
open import Data.Maybe using (just)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_×_; Σ-syntax) renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; trans)
open import Relation.Nullary using (¬_)

private
  just-inj : ∀ {X : Set} {a b : X} → just a ≡ just b → a ≡ b
  just-inj refl = refl

  {- a sound result observed as a constant: the constant is in D -}
  const-in : ∀ {A} {r : Result (Val A)} {D B} {k : base-rep B} → Sound r D
    → outcome obs r ≡ just (o-const B k) → dconst k ∈ D
  const-in (ret {v} v⊆) e = v⊆ _ (𝒱-const v (just-inj e))

  {- a sound result in an empty D times out -}
  empty-timeout : ∀ {A} {r : Result (Val A)} {D} → Sound r D → ¬ nonempty D → r ≡ timeout
  empty-timeout timeout ne = refl
  empty-timeout (ret {v} v⊆) ne with 𝒱-ne v
  ... | ⟨ d , d∈ ⟩ = ⊥-elim (ne ⟨ d , v⊆ d d∈ ⟩)

{- adequacy: an element of the denotation is related to the value the
   interpreter returns from some clock on -}
returns : ∀ {A} (M : Tm [] A) {d} → d ∈ ⟦ M ⟧ ρ₀ → Σ[ v ∈ Val A ] Σ[ ck ∈ _ ] eval ck [] M ≡ ret v × 𝕍 d v
returns M d∈ with adequate M (λ ()) d∈
... | ⟨ v , ⟨ ⟨ c , e ⟩ , r ⟩ ⟩ = ⟨ v , ⟨ c , ⟨ e c ≤-refl , r ⟩ ⟩ ⟩

const-iff : ∀ {A} (M : Tm [] A) {B} {k : base-rep B} → (dconst k ∈ ⟦ M ⟧ ρ₀) ⇔ Terminates (sem M) (o-const B k)
const-iff M =
  ⟨ (λ k∈ → let ⟨ v , ⟨ ck , ⟨ e , r ⟩ ⟩ ⟩ = returns M k∈ in
       ⟨ ck , trans (cong (outcome obs) e) (cong just (𝕍-const v r)) ⟩)
  , (λ { ⟨ ck , e ⟩ → const-in (sound ck [] M) e }) ⟩

diverges-iff : ∀ {A} (M : Tm [] A) → Diverges (sem M) ⇔ (¬ nonempty (⟦ M ⟧ ρ₀))
diverges-iff M =
  ⟨ (λ { div ⟨ d , d∈ ⟩ → let ⟨ v , ⟨ ck , ⟨ e , _ ⟩ ⟩ ⟩ = returns M d∈ in ret≢timeout (trans (sym e) (div ck)) })
  , (λ ne ck → empty-timeout (sound ck [] M) ne) ⟩
  where
  ret≢timeout : ∀ {X : Set} {v : X} → ¬ (Result.ret v ≡ Result.timeout)
  ret≢timeout ()

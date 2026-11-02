{-

  Soundness and adequacy of the graph model of FPC
  (FPC/Semantics/GraphModel/FPC.agda) with respect to its reduction
  semantics (FPC/Semantics/ReductionSemantics/FPC.agda), for closed
  programs of any type, started in ρ₀ on the denotational side, as
  FPC/proof/Adequacy/FPC.agda is for the clocked interpreter:

    soundness (FPC/proof/Adequacy/ReductionSemantics/Soundness.agda): a
      step preserves the meaning of a term, and a value denotes a
      nonempty set, and a term that is not a value takes a step;
    adequacy (FPC/proof/Adequacy/ReductionSemantics/LogRel.agda): every
      d ∈ ⟦ M ⟧ ρ₀ is related to the value M reduces to.

  So ⟦ M ⟧ ρ₀ contains const k exactly when the reduction terminates
  with o-const B k (const-iff), and it is empty exactly when the
  reduction diverges (diverges-iff): a program with an empty denotation
  is never a value, so it always takes a step, to a program with the
  same (empty) denotation.

-}

module FPC.proof.Adequacy.ReductionSemantics.FPC where

open import Framework.Primitives using (base-rep)
open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.Domain using (Value) renaming (const to dconst)
open import FPC.Semantics.GraphModel.Closed using (ρ₀)
open import FPC.Language.FPC using (Tm)
open import FPC.Semantics.GraphModel.FPC using (⟦_⟧)
open import FPC.proof.Semantics.ReductionSemantics.FPC
  using (red; obs; sem; sub-id; value-red; lam; lit; tuple; inl; inr; fold)
  renaming (Value to Val; ∅ to ∅ₛ)
open import Semantics.Observation using (Obs; o-const; o-error; _⇔_)
open import Semantics.Reduction.Smallstep using (Terminates; Diverges; Star; ε; _◅_; Final; Steps; zero; suc; val; error; to; toNext; stop)
open import proof.Framework.Smallstep Obs using (diverges-not-terminates)
open import proof.Framework.Reduction Obs o-error using (Star*; toNext-to) renaming (ε to ε*; _◅_ to _◅*_)
open import FPC.proof.Semantics.GraphModel.Binders using (ne-≃)
open import FPC.proof.Adequacy.ReductionSemantics.Soundness using (progress; val-value; val-ne; step-≃; run-≃)
open import FPC.proof.Adequacy.ReductionSemantics.LogRel using (_⇓_; 𝕍; adequate; 𝕍-const)

open import Data.Empty using (⊥-elim)
open import Data.List using ([])
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; Σ-syntax; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; subst)
open import Relation.Nullary using (¬_)

private
  {- runs of the reduction are runs of its machine, and back -}
  star→ : ∀ {A} {M₀ M N : Tm [] A} → Star* red M N → Star (sem M₀) M N
  star→ ε* = ε
  star→ {M = M} (s ◅* σ) = cong (toNext (obs M)) s ◅ star→ σ

  star← : ∀ {A} {M₀ M N : Tm [] A} → Star (sem M₀) M N → Star* red M N
  star← ε = ε*
  star← (s ◅ σ) = toNext-to s ◅* star← σ

  {- a value stops, with its observation -}
  final : ∀ {A} {M₀ V : Tm [] A} → Val V → Final (sem M₀) V (obs V)
  final {V = V} v = cong (toNext (obs V)) (value-red v)

  {- the denotation of a value observed as a constant holds it -}
  obs-const : ∀ {A B} {k : base-rep B} {V : Tm [] A} → Val V → obs V ≡ o-const B k → dconst k ∈ ⟦ V ⟧ ρ₀
  obs-const lit refl = ⟨ refl , refl ⟩
  obs-const (fold v) e = obs-const v e
  obs-const lam ()
  obs-const (tuple vs) ()
  obs-const (inl v) ()
  obs-const (inr v) ()

  stop-val : ∀ {X : Set} {o o' : Obs} → toNext {X} o val ≡ stop o' → o ≡ o'
  stop-val refl = refl

  stop-error : ∀ {X : Set} {o o' : Obs} → toNext {X} o error ≡ stop o' → o-error ≡ o'
  stop-error refl = refl

  {- a term at which the machine stops with a constant is a value whose
     denotation holds it -}
  stop-const : ∀ {A B} {k : base-rep B} (V : Tm [] A) → toNext (obs V) (red V) ≡ stop (o-const B k) → dconst k ∈ ⟦ V ⟧ ρ₀
  stop-const V e with red V in eV
  ... | val = obs-const (val-value V eV) (stop-val e)
  ... | error with stop-error {o = obs V} e
  ...   | ()

{- adequacy: an element of the denotation is related to the value the
   program reduces to -}
returns : ∀ {A} (M : Tm [] A) {d} → d ∈ ⟦ M ⟧ ρ₀ → Σ[ V ∈ Tm [] A ] M ⇓ V × 𝕍 d V
returns M d∈ with adequate M {σ = ∅ₛ} (λ ()) d∈
... | ⟨ V , ⟨ e , r ⟩ ⟩ = ⟨ V , ⟨ subst (_⇓ V) (sub-id {σ = ∅ₛ} (λ ()) M) e , r ⟩ ⟩

const-iff : ∀ {A} (M : Tm [] A) {B} {k : base-rep B} → (dconst k ∈ ⟦ M ⟧ ρ₀) ⇔ Terminates (sem M) (o-const B k)
const-iff M =
  ⟨ (λ k∈ → let ⟨ V , ⟨ ⟨ σ , v ⟩ , r ⟩ ⟩ = returns M k∈ in
       ⟨ V , ⟨ star→ σ , subst (Final (sem M) V) (𝕍-const V r) (final {M₀ = M} v) ⟩ ⟩)
  , (λ { ⟨ V , ⟨ σ , fin ⟩ ⟩ → proj₂ (run-≃ (star← σ)) _ (stop-const V fin) }) ⟩

diverges-iff : ∀ {A} (M : Tm [] A) → Diverges (sem M) ⇔ (¬ nonempty (⟦ M ⟧ ρ₀))
diverges-iff M =
  ⟨ (λ { div ⟨ d , d∈ ⟩ → let ⟨ V , ⟨ ⟨ σ , v ⟩ , _ ⟩ ⟩ = returns M d∈ in
         diverges-not-terminates div ⟨ V , ⟨ star→ σ , final {M₀ = M} v ⟩ ⟩ })
  , (λ ne n → run n M ne) ⟩
  where
  {- a term with an empty denotation takes n steps, for every n -}
  run : ∀ n (N : Tm [] _) → ¬ nonempty (⟦ N ⟧ ρ₀) → Σ[ N' ∈ Tm [] _ ] Steps (sem M) n N N'
  run ℕ.zero N ne = ⟨ N , zero ⟩
  run (ℕ.suc n) N ne with progress N
  ... | inj₁ v = ⊥-elim (ne (val-ne v))
  ... | inj₂ ⟨ N₁ , e ⟩ with run n N₁ (λ ne₁ → ne (ne-≃ (≃-sym (step-≃ N e)) ne₁))
  ...   | ⟨ N' , ss ⟩ = ⟨ N' , suc (cong (toNext (obs N)) e) ss ⟩

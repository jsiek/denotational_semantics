{-

  Simplify, observed through the ISWIM machine, by the graph model with
  errors: the correctness of simplify in that model
  (proof/Correctness/GraphErr/SimplifyCorrect.agda) and adequacy
  (ISWIM.agda) give that a closed program and its simplification stop
  with an error together, terminate with the same constants, terminate
  with an answer together, and diverge together, the last three
  outcomes that the graph model alone cannot tell apart.

-}

module Untyped.proof.Adequacy.GraphErr.Simplify where

open import Framework.Primitives using (base-rep)
open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.Domain using (Value; ω; ρ₀) renaming (const to dconst)
open import Language.ISWIM using (AST)
open import Compiler.Simplify using (simplify)
open import Compiler.EncloseScope using (Closed)
open import proof.Compiler.SimplifyScope using (simplify-closed)
open import proof.Correctness.GraphErr.SimplifyCorrect using (simplify-correct)
open import Semantics.Observation
open import proof.Semantics.GraphErr.ISWIM using (⟦_⟧)
open import proof.Semantics.CEK.Smallstep using (Terminates; Diverges)
open import Semantics.CEK.ISWIM using (sem)
open import proof.Adequacy.GraphErr.ISWIM using (error-iff; const-iff; converges-iff; diverges-iff)

open import Data.Product using (_×_; Σ-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality using (_≢_)
open import Relation.Nullary using (¬_)

private
  {- through ⟦ M ⟧ ρ₀ ≃ ⟦ simplify M ⟧ ρ₀ -}
  via : ∀ {A B : Set} (P Q : 𝒫 Value → Set) {D E : 𝒫 Value}
    → (P D → P E) → (P E → P D) → (P D ⇔ A) → (P E ⇔ B) → A ⇔ B
  via P Q f g a b = ⟨ (λ x → proj₁ b (f (proj₂ a x))) , (λ y → proj₁ a (g (proj₂ b y))) ⟩

simplify-error : ∀ M → Closed M → Terminates (sem M) o-error ⇔ Terminates (sem (simplify M)) o-error
simplify-error M c =
  via (ω ∈_) (ω ∈_) {⟦ M ⟧ ρ₀} {⟦ simplify M ⟧ ρ₀} (proj₁ eq ω) (proj₂ eq ω) (error-iff M c) (error-iff (simplify M) (simplify-closed M c))
  where eq = simplify-correct M c

simplify-const : ∀ M → Closed M → ∀ {B} (k : base-rep B)
  → Terminates (sem M) (o-const B k) ⇔ Terminates (sem (simplify M)) (o-const B k)
simplify-const M c k =
  via (dconst k ∈_) (dconst k ∈_) {⟦ M ⟧ ρ₀} {⟦ simplify M ⟧ ρ₀} (proj₁ eq _) (proj₂ eq _) (const-iff M c) (const-iff (simplify M) (simplify-closed M c))
  where eq = simplify-correct M c

simplify-converges : ∀ M → Closed M → Converges (Terminates (sem M)) ⇔ Converges (Terminates (sem (simplify M)))
simplify-converges M c =
  via V V {⟦ M ⟧ ρ₀} {⟦ simplify M ⟧ ρ₀} (λ { ⟨ d , ⟨ d∈ , d≢ ⟩ ⟩ → ⟨ d , ⟨ proj₁ eq d d∈ , d≢ ⟩ ⟩ })
          (λ { ⟨ d , ⟨ d∈ , d≢ ⟩ ⟩ → ⟨ d , ⟨ proj₂ eq d d∈ , d≢ ⟩ ⟩ })
      (converges-iff M c) (converges-iff (simplify M) (simplify-closed M c))
  where
  eq = simplify-correct M c
  V : 𝒫 Value → Set
  V D = Σ[ d ∈ Value ] d ∈ D × d ≢ ω

simplify-diverges : ∀ M → Closed M → Diverges (sem M) ⇔ Diverges (sem (simplify M))
simplify-diverges M c =
  ⟨ (λ dv → proj₂ (diverges-iff (simplify M) (simplify-closed M c))
               (λ d d∈ → proj₁ (diverges-iff M c) dv d (proj₂ eq d d∈)))
  , (λ dv → proj₂ (diverges-iff M c)
               (λ d d∈ → proj₁ (diverges-iff (simplify M) (simplify-closed M c)) dv d (proj₁ eq d d∈))) ⟩
  where eq = simplify-correct M c

{-

  Forward simulations, in the spirit of CompCert's Smallstep library, and
  the end theorem that a forward simulation between deterministic, total
  transition systems makes them equivalent; equivalence composes.
  See the design note in Smallstep.agda.

-}

module Compiler.Operational.Simulation where

open import Compiler.Operational.Observation
open import Compiler.Operational.Smallstep

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _+_; _<_; s≤s; z≤n)
open import Data.Nat.Properties using (+-identityʳ; m<m+n)
open import Data.Nat.Induction using (<-wellFounded)
open import Data.Product using (_×_; Σ; Σ-syntax; _,_; proj₁; proj₂)
open import Data.Product.Relation.Binary.Lex.Strict using (×-Lex; ×-wellFounded)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Induction.WellFounded using (WellFounded; Acc; acc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

{- Forward simulations --------------------------------------------------------}

record FSim (L₁ L₂ : Semantics) : Set₁ where
  field
    Index : Set
    _≺_ : Index → Index → Set
    wf : WellFounded _≺_
    match : Index → State L₁ → State L₂ → Set
    init : ∀ {s₁} → Initial L₁ s₁
      → Σ[ i ∈ Index ] Σ[ s₂ ∈ State L₂ ] Initial L₂ s₂ × match i s₁ s₂
    final : ∀ {i s₁ s₂ o} → match i s₁ s₂ → Final L₁ s₁ o → Final L₂ s₂ o
    step : ∀ {i s₁ s₂ s₁'} → match i s₁ s₂ → Step L₁ s₁ s₁'
      → Σ[ i' ∈ Index ] Σ[ s₂' ∈ State L₂ ]
          (Plus L₂ s₂ s₂' ⊎ (Star L₂ s₂ s₂' × i' ≺ i)) × match i' s₁' s₂'

module _ {L₁ L₂ : Semantics} (F : FSim L₁ L₂) where
  open FSim F

  sim-star : ∀ {i s₁ s₂ s₁'} → match i s₁ s₂ → Star L₁ s₁ s₁'
    → Σ[ i' ∈ Index ] Σ[ s₂' ∈ State L₂ ] Star L₂ s₂ s₂' × match i' s₁' s₂'
  sim-star m ε = _ , _ , ε , m
  sim-star m (st ◅ σ) with step m st
  ... | i₁ , s₂₁ , r , m₁ with sim-star m₁ σ
  ...   | i' , s₂' , τ , m' = i' , s₂' , star-of r ◅◅ τ , m'
    where
    star-of : ∀ {s s' i' i} → Plus L₂ s s' ⊎ (Star L₂ s s' × i' ≺ i) → Star L₂ s s'
    star-of (inj₁ π) = plus→star π
    star-of (inj₂ (σ , _)) = σ

{- Simulations of machines in which every step is matched by a target plus ---}

plus-simulation : ∀ {S₁ : Set} {step : S₁ → Next S₁} {s₀ : S₁} {L₂ : Semantics}
  → (R : S₁ → State L₂ → Set)
  → (Σ[ s₂ ∈ State L₂ ] Initial L₂ s₂ × R s₀ s₂)
  → (∀ {s₁ s₂} → R s₁ s₂ → Answers L₂ R (step s₁) s₂)
  → FSim (machine S₁ step s₀) L₂
plus-simulation {S₁} {step} {s₀} {L₂} R (s₂ , i₂ , m₀) sim = record
  { Index = ⊤
  ; _≺_ = λ _ _ → ⊥
  ; wf = λ _ → acc (λ ())
  ; match = λ _ → R
  ; init = λ { refl → tt , s₂ , i₂ , m₀ }
  ; final = final
  ; step = step'
  }
  where
  final : ∀ {s₁ s₂ o} → R s₁ s₂ → step s₁ ≡ stop o → Final L₂ s₂ o
  final {s₁} m eq with step s₁ | sim m
  final m refl | stop o | stops fin = fin

  step' : ∀ {i : ⊤} {s₁ s₂ s₁'} → R s₁ s₂ → step s₁ ≡ next s₁'
    → Σ[ i' ∈ ⊤ ] Σ[ s₂' ∈ State L₂ ] (Plus L₂ s₂ s₂' ⊎ (Star L₂ s₂ s₂' × ⊥)) × R s₁' s₂'
  step' {s₁ = s₁} m eq with step s₁ | sim m
  step' m refl | next s₁' | steps π m' = tt , _ , inj₁ π , m'

{- Simulations of machines in which a source step may also be matched by no
   target step (stuttering), when the index of the match decreases -------}

data Answers≺ {S₁ : Set} (L₂ : Semantics) (R : ℕ → S₁ → State L₂ → Set) (i : ℕ)
  : Next S₁ → State L₂ → Set where
  stops : ∀ {o s₂} → Final L₂ s₂ o → Answers≺ L₂ R i (stop o) s₂
  steps : ∀ {j s₁' s₂ s₂'} → Plus L₂ s₂ s₂' → R j s₁' s₂' → Answers≺ L₂ R i (next s₁') s₂
  stutters : ∀ {j s₁' s₂} → j < i → R j s₁' s₂ → Answers≺ L₂ R i (next s₁') s₂

measure-simulation : ∀ {S₁ : Set} {step : S₁ → Next S₁} {s₀ : S₁} {L₂ : Semantics}
  → (R : ℕ → S₁ → State L₂ → Set)
  → (Σ[ i ∈ ℕ ] Σ[ s₂ ∈ State L₂ ] Initial L₂ s₂ × R i s₀ s₂)
  → (∀ {i s₁ s₂} → R i s₁ s₂ → Answers≺ L₂ R i (step s₁) s₂)
  → FSim (machine S₁ step s₀) L₂
measure-simulation {S₁} {step} {s₀} {L₂} R (i₀ , s₂ , i₂ , m₀) sim = record
  { Index = ℕ
  ; _≺_ = _<_
  ; wf = <-wellFounded
  ; match = R
  ; init = λ { refl → i₀ , s₂ , i₂ , m₀ }
  ; final = final
  ; step = step'
  }
  where
  final : ∀ {i s₁ s₂ o} → R i s₁ s₂ → step s₁ ≡ stop o → Final L₂ s₂ o
  final {s₁ = s₁} m eq with step s₁ | sim m
  final m refl | stop o | stops fin = fin

  step' : ∀ {i s₁ s₂ s₁'} → R i s₁ s₂ → step s₁ ≡ next s₁'
    → Σ[ i' ∈ ℕ ] Σ[ s₂' ∈ State L₂ ] (Plus L₂ s₂ s₂' ⊎ (Star L₂ s₂ s₂' × i' < i)) × R i' s₁' s₂'
  step' {s₁ = s₁} m eq with step s₁ | sim m
  step' m refl | next s₁' | steps π m' = _ , _ , inj₁ π , m'
  step' m refl | next s₁' | stutters lt m' = _ , _ , inj₂ (ε , lt) , m'

{- The end theorem ------------------------------------------------------------}

record Equivalent (L₁ L₂ : Semantics) : Set where
  field
    terminates : SameObs (Terminates L₁) (Terminates L₂)
    diverges : Diverges L₁ ⇔ Diverges L₂

{- equivalence composes -}
equiv-trans : ∀ {L₁ L₂ L₃} → Equivalent L₁ L₂ → Equivalent L₂ L₃ → Equivalent L₁ L₃
equiv-trans E F = record
  { terminates = λ o → (λ t → proj₁ (F.terminates o) (proj₁ (E.terminates o) t))
                     , (λ t → proj₂ (E.terminates o) (proj₂ (F.terminates o) t))
  ; diverges = (λ d → proj₁ F.diverges (proj₁ E.diverges d))
             , (λ d → proj₂ E.diverges (proj₂ F.diverges d)) }
  where module E = Equivalent E
        module F = Equivalent F

module _ {L₁ L₂ : Semantics} (F : FSim L₁ L₂) where
  open FSim F

  forward-terminates : ∀ {o} → Terminates L₁ o → Terminates L₂ o
  forward-terminates (s₀ , s , i₀ , σ , fin) with init i₀
  ... | i , t₀ , j₀ , m with sim-star F m σ
  ...   | i' , t , τ , m' = t₀ , t , j₀ , τ , final m' fin

  {- a target run to a final state is matched by a source run: by induction
     on the length of the target run and, for stuttering steps, the index -}
  private
    _⋖_ : ℕ × Index → ℕ × Index → Set
    _⋖_ = ×-Lex _≡_ _<_ _≺_

    lt-skip : ∀ {n' k n} → n' + suc k ≡ n → n' < n
    lt-skip {n'} refl = m<m+n n' (s≤s z≤n)

    {- where a run of n steps from s₂ to a final state goes after k steps -}
    skip : Deterministic L₂ → ∀ {k n s₂ s₂' t o} {i i' : Index} → Final L₂ t o
      → Steps L₂ (suc k) s₂ s₂' → Steps L₂ n s₂ t
      → Σ[ n' ∈ ℕ ] (n' , i') ⋖ (n , i) × Steps L₂ n' s₂' t
    skip D fin σ τ with steps-det-skip D σ τ fin
    ... | n' , eq , τ' = n' , inj₁ (lt-skip eq) , τ'

  back : Progressive L₁ → Deterministic L₂ → ∀ {t o} → Final L₂ t o
    → ∀ n i → Acc _⋖_ (n , i) → ∀ {s₁ s₂} → match i s₁ s₂
    → Steps L₂ n s₂ t → Σ[ s ∈ State L₁ ] Star L₁ s₁ s × Final L₁ s o
  back P D fin n i (acc rec) {s₁} m τ with Progressive.progress P s₁
  back P D fin n i (acc rec) {s₁} m zero | inj₁ (o' , fin₁)
    with Deterministic.final-det D (final m fin₁) fin
  ... | refl = s₁ , ε , fin₁
  back P D fin n i (acc rec) m (suc st _) | inj₁ (o' , fin₁) =
    ⊥-elim (Deterministic.final-nostep D (final m fin₁) st)
  back P D fin n i (acc rec) m τ | inj₂ (s₁' , st) with step m st
  ... | i' , s₂' , inj₁ (plus st₂ σ₂) , m'
    with skip D {i = i} {i'} fin (proj₂ (star→steps (st₂ ◅ σ₂))) τ
  ...   | n' , lt , τ' with back P D fin n' i' (rec lt) m' τ'
  ...     | s , σ , fin₁ = s , st ◅ σ , fin₁
  back P D fin n i (acc rec) m τ | inj₂ (s₁' , st)
    | i' , s₂' , inj₂ (σ₂ , dec) , m' with star→steps σ₂
  ... | zero , zero with back P D fin n i' (rec (inj₂ (refl , dec))) m' τ
  ...   | s , σ , fin₁ = s , st ◅ σ , fin₁
  back P D fin n i (acc rec) m τ | inj₂ (s₁' , st)
    | i' , s₂' , inj₂ (σ₂ , dec) , m' | suc k , σk
    with skip D {i = i} {i'} fin σk τ
  ... | n' , lt , τ' with back P D fin n' i' (rec lt) m' τ'
  ...   | s , σ , fin₁ = s , st ◅ σ , fin₁

  backward-terminates : Progressive L₁ → Deterministic L₂
    → ∀ {o} → Terminates L₂ o → Terminates L₁ o
  backward-terminates P D (t₀ , t , j₀ , τ , fin) with Progressive.initial-exists P
  ... | s₀ , i₀ with init i₀
  ... | i , t₀' , j₀' , m with Deterministic.initial-unique D j₀ j₀'
  ... | refl with star→steps τ
  ... | n , τn with back P D fin n i (×-wellFounded <-wellFounded wf (n , i)) m τn
  ... | s , σ , fin₁ = s₀ , s , i₀ , σ , fin₁

  {- the end theorem: a forward simulation between deterministic, total
     systems preserves and reflects termination with each observation, and
     divergence -}
  equivalent : Deterministic L₁ → Progressive L₁ → Deterministic L₂ → Progressive L₂
    → Equivalent L₁ L₂
  equivalent D₁ P₁ D₂ P₂ = record
    { terminates = λ o → forward-terminates , backward-terminates P₁ D₂
    ; diverges = div→ , div←
    }
    where
    div→ : Diverges L₁ → Diverges L₂
    div→ d@(s₀ , i₀ , _) with init i₀
    ... | i , t₀ , j₀ , m = never-final-diverges P₂ j₀ λ τ fin →
      diverges-not-terminates D₁ d (backward-terminates P₁ D₂ (t₀ , _ , j₀ , τ , fin))

    div← : Diverges L₂ → Diverges L₁
    div← d with Progressive.initial-exists P₁
    ... | s₀ , i₀ = never-final-diverges P₁ i₀ λ σ fin →
      diverges-not-terminates D₂ d (forward-terminates (s₀ , _ , i₀ , σ , fin))

{-

  Forward simulations, in the spirit of CompCert's Smallstep library, and
  the end theorem that a forward simulation between deterministic, total
  transition systems makes them equivalent; equivalence composes.
  See the design note in Smallstep.agda.

-}

module proof.Framework.Simulation (Obs : Set) where

open import Framework.Iff using (_⇔_)
open import Framework.Smallstep Obs

open import Data.Empty using (⊥-elim)
open import Data.Nat using (ℕ; suc; _+_; _<_; s≤s; z≤n)
open import Data.Nat.Properties using (m<m+n)
open import Data.Nat.Induction using (<-wellFounded)
open import Data.Product using (_×_; Σ-syntax; _,_; proj₁; proj₂)
open import Data.Product.Relation.Binary.Lex.Strict using (×-Lex; ×-wellFounded)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Induction.WellFounded using (Acc; acc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

{- Forward simulations --------------------------------------------------------}

{- How a target state answers one step of a source machine when a match
   has index i: by stopping with the same observation, by taking one or
   more steps to a matching state, or by taking none (stuttering), when
   the index decreases -}
data Answers≺ {S₁ : Set} (L₂ : Machine) (R : ℕ → S₁ → State L₂ → Set) (i : ℕ)
  : Next S₁ → State L₂ → Set where
  stops : ∀ {o s₂} → Final L₂ s₂ o → Answers≺ L₂ R i (stop o) s₂
  steps : ∀ {j s₁' s₂ s₂'} → Plus L₂ s₂ s₂' → R j s₁' s₂' → Answers≺ L₂ R i (next s₁') s₂
  stutters : ∀ {j s₁' s₂} → j < i → R j s₁' s₂ → Answers≺ L₂ R i (next s₁') s₂

record FSim (L₁ L₂ : Machine) : Set₁ where
  field
    match : ℕ → State L₁ → State L₂ → Set
    init : Σ[ i ∈ ℕ ] match i (start L₁) (start L₂)
    sim : ∀ {i s₁ s₂} → match i s₁ s₂ → Answers≺ L₂ match i (Machine.step L₁ s₁) s₂

{- simulations in which every step is matched by a target plus -}
plus-simulation : ∀ {L₁ L₂ : Machine} (R : State L₁ → State L₂ → Set) → R (start L₁) (start L₂)
  → (∀ {s₁ s₂} → R s₁ s₂ → Answers L₂ R (Machine.step L₁ s₁) s₂) → FSim L₁ L₂
plus-simulation {L₂ = L₂} R m₀ sim = record
  { match = λ _ → R ; init = 0 , m₀ ; sim = λ m → lift (sim m) }
  where
  lift : ∀ {i a s₂} → Answers L₂ R a s₂ → Answers≺ L₂ (λ _ → R) i a s₂
  lift (stops fin) = stops fin
  lift (steps π m) = steps {j = 0} π m

{- The end theorem ------------------------------------------------------------}

record Equivalent (L₁ L₂ : Machine) : Set where
  field
    terminates : ∀ o → Terminates L₁ o ⇔ Terminates L₂ o
    diverges : Diverges L₁ ⇔ Diverges L₂

module _ {L₁ L₂ : Machine} (F : FSim L₁ L₂) where
  open FSim F
  open Machine L₁ using (step)

  {- one source step is matched by a target plus, or by none and a smaller
     index -}
  sim-step : ∀ {i s₁ s₁' s₂} → match i s₁ s₂ → step s₁ ≡ next s₁'
    → Σ[ j ∈ ℕ ] ((Σ[ s₂' ∈ State L₂ ] Plus L₂ s₂ s₂' × match j s₁' s₂') ⊎ (j < i × match j s₁' s₂))
  sim-step {s₁ = s₁} m st with step s₁ | sim m
  sim-step m refl | next _ | steps π m' = _ , inj₁ (_ , π , m')
  sim-step m refl | next _ | stutters lt m' = _ , inj₂ (lt , m')

  sim-final : ∀ {i s₁ s₂ o} → match i s₁ s₂ → step s₁ ≡ stop o → Final L₂ s₂ o
  sim-final {s₁ = s₁} m eq with step s₁ | sim m
  sim-final m refl | stop o | stops fin = fin

  sim-star : ∀ {i s₁ s₂ s₁'} → match i s₁ s₂ → Star L₁ s₁ s₁'
    → Σ[ j ∈ ℕ ] Σ[ s₂' ∈ State L₂ ] Star L₂ s₂ s₂' × match j s₁' s₂'
  sim-star m ε = _ , _ , ε , m
  sim-star m (st ◅ σ) with sim-step m st
  ... | _ , inj₂ (_ , m') = sim-star m' σ
  ... | _ , inj₁ (_ , π , m') with sim-star m' σ
  ...   | j , s₂' , τ , m'' = j , s₂' , plus→star π ◅◅ τ , m''

  forward-terminates : ∀ {o} → Terminates L₁ o → Terminates L₂ o
  forward-terminates (s , σ , fin) with sim-star (proj₂ init) σ
  ... | _ , t , τ , m = t , τ , sim-final m fin

  {- a target run to a final state is matched by a source run: by induction
     on the length of the target run and, for stuttering steps, the index -}
  private
    _⋖_ : ℕ × ℕ → ℕ × ℕ → Set
    _⋖_ = ×-Lex _≡_ _<_ _<_

    lt-skip : ∀ {n' k n} → n' + suc k ≡ n → n' < n
    lt-skip {n'} refl = m<m+n n' (s≤s z≤n)

  back : ∀ {t o} → Final L₂ t o
    → ∀ n i → Acc _⋖_ (n , i) → ∀ {s₁ s₂} → match i s₁ s₂
    → Steps L₂ n s₂ t → Σ[ s ∈ State L₁ ] Star L₁ s₁ s × Final L₁ s o
  back fin n i (acc rec) {s₁} m τ with step s₁ in eq
  back fin _ i (acc rec) {s₁} m zero | stop o' with final-det {L = L₂} (sim-final m eq) fin
  ... | refl = s₁ , ε , eq
  back fin _ i (acc rec) m (suc st _) | stop o' = ⊥-elim (final-nostep {L = L₂} (sim-final m eq) st)
  back fin n i (acc rec) {s₁} m τ | next s₁' with sim-step m eq
  ... | j , inj₂ (lt , m') with back fin n j (rec (inj₂ (refl , lt))) m' τ
  ...   | s , σ , fin₁ = s , eq ◅ σ , fin₁
  back fin n i (acc rec) {s₁} m τ | next s₁' | j , inj₁ (_ , plus st₂ σ₂ , m')
    with steps-det-skip (proj₂ (star→steps (st₂ ◅ σ₂))) τ fin
  ... | n' , e , τ' with back fin n' j (rec (inj₁ (lt-skip e))) m' τ'
  ...   | s , σ , fin₁ = s , eq ◅ σ , fin₁

  backward-terminates : ∀ {o} → Terminates L₂ o → Terminates L₁ o
  backward-terminates (t , τ , fin) with star→steps τ
  ... | n , τn = back fin n (proj₁ init) (×-wellFounded <-wellFounded <-wellFounded _)
                   (proj₂ init) τn

  {- the end theorem: a forward simulation between machines (deterministic
     and total) preserves and reflects termination with each observation,
     and divergence -}
  equivalent : Equivalent L₁ L₂
  equivalent = record
    { terminates = λ o → forward-terminates , backward-terminates
    ; diverges = (λ d → never-final-diverges λ τ fin →
                          diverges-not-terminates d (backward-terminates (_ , τ , fin)))
               , (λ d → never-final-diverges λ σ fin →
                          diverges-not-terminates d (forward-terminates (_ , σ , fin)))
    }

{- equivalence composes -}
equiv-trans : ∀ {L₁ L₂ L₃} → Equivalent L₁ L₂ → Equivalent L₂ L₃ → Equivalent L₁ L₃
equiv-trans E F = record
  { terminates = λ o → (λ t → proj₁ (F.terminates o) (proj₁ (E.terminates o) t))
                     , (λ t → proj₂ (E.terminates o) (proj₂ (F.terminates o) t))
  ; diverges = (λ d → proj₁ F.diverges (proj₁ E.diverges d))
             , (λ d → proj₂ E.diverges (proj₂ F.diverges d)) }
  where module E = Equivalent E
        module F = Equivalent F

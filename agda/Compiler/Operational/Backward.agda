{-

  Backward simulations, in the spirit of CompCert's Smallstep library, for
  comparison with the forward simulations of Simulation.agda.

  The passes are proved correct by forward simulations, and the backward
  direction comes from determinism of the machines (Simulation.equivalent).
  This module is the generic part of an experiment that measures the cost
  of proving the backward direction directly, as one must for a
  non-deterministic language. Nothing here uses determinism.

  A backward simulation matches each target state with a source state.
  The target is the one that moves:

  * the start of the target matches the start of the source;
  * when the target stops with o, the source reaches a stop with o;
  * a target step is answered by a source plus, or by a source star that
    decreases a well-founded measure (the source waits while the target
    takes administrative steps).

  All our machines are total (stuck means stopping with o-wrong), so,
  unlike CompCert, no safety premise on the source is needed.

  Divergence of a target is here an infinite run (Forever): for a
  non-deterministic system, "a run of every length n" (Smallstep.Diverges)
  does not give one infinite run without König's lemma and determinism.
  The measure makes the simulation productive: along an infinite target
  run, the source cannot wait forever.

-}

module Compiler.Operational.Backward where

open import Compiler.Operational.Observation
open import Compiler.Operational.Smallstep

open import Data.Nat using (ℕ; zero; suc; _<_)
open import Data.Nat.Induction using (<-wellFounded)
open import Data.Product using (_×_; Σ-syntax; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Induction.WellFounded using (WellFounded; Acc; acc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

{- Infinite runs -------------------------------------------------------------}

Forever : (L : Machine) → State L → Set
Forever L s = Σ[ f ∈ (ℕ → State L) ] f 0 ≡ s × (∀ n → Step L (f n) (f (suc n)))

Diverges∞ : Machine → Set
Diverges∞ L = Forever L (start L)

{- an infinite run has runs of every length -}
diverges∞→diverges : ∀ {L} → Diverges∞ L → Diverges L
diverges∞→diverges {L} (f , e , st) n = f n , subst (λ s → Steps L n s (f n)) e (go n f st)
  where
  go : ∀ n (g : ℕ → State L) → (∀ k → Step L (g k) (g (suc k))) → Steps L n (g 0) (g n)
  go zero g st = zero
  go (suc n) g st = suc (st 0) (go n (λ k → g (suc k)) (λ k → st (suc k)))

{- Backward simulations ------------------------------------------------------}

record BSim (L₁ L₂ : Machine) : Set₁ where
  field
    Index : Set
    _≺_ : Index → Index → Set
    wf : WellFounded _≺_
    match : Index → State L₁ → State L₂ → Set
    init : Σ[ i ∈ Index ] match i (start L₁) (start L₂)
    final : ∀ {i s₁ s₂ o} → match i s₁ s₂ → Final L₂ s₂ o
      → Σ[ s₁' ∈ State L₁ ] Star L₁ s₁ s₁' × Final L₁ s₁' o
    step : ∀ {i s₁ s₂ s₂'} → match i s₁ s₂ → Step L₂ s₂ s₂'
      → Σ[ i' ∈ Index ] Σ[ s₁' ∈ State L₁ ]
          (Plus L₁ s₁ s₁' ⊎ (Star L₁ s₁ s₁' × i' ≺ i)) × match i' s₁' s₂'

{- The end theorems ----------------------------------------------------------}

module _ {L₁ L₂ : Machine} (B : BSim L₁ L₂) where
  open BSim B

  private
    star-of : ∀ {i' i a b} → Plus L₁ a b ⊎ (Star L₁ a b × i' ≺ i) → Star L₁ a b
    star-of (inj₁ π) = plus→star π
    star-of (inj₂ (σ , _)) = σ

  {- a target run to a stop is matched by a source run, by induction on it -}
  back-star : ∀ {i s₁ s₂ t o} → match i s₁ s₂ → Star L₂ s₂ t → Final L₂ t o
    → Σ[ s ∈ State L₁ ] Star L₁ s₁ s × Final L₁ s o
  back-star m ε fin = final m fin
  back-star m (st ◅ τ) fin with step m st
  ... | i' , s₁' , r , m' with back-star m' τ fin
  ...   | s , σ , fin₁ = s , star-of r ◅◅ σ , fin₁

  backward-terminates : ∀ {o} → Terminates L₂ o → Terminates L₁ o
  backward-terminates (t , τ , fin) = back-star (proj₂ init) τ fin

  {- along an infinite target run, the source eventually takes a step -}
  module _ {f : ℕ → State L₂} (run : ∀ n → Step L₂ (f n) (f (suc n))) where

    productive : ∀ {i} → Acc _≺_ i → ∀ {k s₁} → match i s₁ (f k)
      → Σ[ k' ∈ ℕ ] Σ[ i' ∈ Index ] Σ[ s₁' ∈ State L₁ ] Plus L₁ s₁ s₁' × match i' s₁' (f k')
    productive (acc rec) {k} m with step m (run k)
    ... | i' , s₁' , inj₁ π , m' = suc k , i' , s₁' , π , m'
    ... | i' , s₁' , inj₂ (σ , lt) , m' with productive (rec lt) m'
    ...   | k'' , i'' , s₁'' , π , m'' = k'' , i'' , s₁'' , star-plus σ π , m''

    {- a source state on its way to one matching a state of the run -}
    Ahead : State L₁ → Set
    Ahead s = Σ[ k ∈ ℕ ] Σ[ i ∈ Index ] Σ[ s₁ ∈ State L₁ ] Star L₁ s s₁ × match i s₁ (f k)

    advance : ∀ {s} → Ahead s → Σ[ s' ∈ State L₁ ] Step L₁ s s' × Ahead s'
    advance (k , i , s₁ , st ◅ σ , m) = _ , st , k , i , s₁ , σ , m
    advance (k , i , s₁ , ε , m) with productive (wf i) m
    ... | k' , i' , s₁' , plus st σ , m' = _ , st , k' , i' , s₁' , σ , m'

  backward-diverges : Diverges∞ L₂ → Diverges∞ L₁
  backward-diverges (f , e , run) = (λ n → proj₁ (g n)) , refl , λ n → proj₁ (proj₂ (advance run (proj₂ (g n))))
    where
    g : ℕ → Σ[ s ∈ State L₁ ] Ahead run s
    g zero = start L₁ , 0 , proj₁ init , start L₁ , ε , subst (match _ (start L₁)) (sym e) (proj₂ init)
    g (suc n) = proj₁ (advance run (proj₂ (g n))) , proj₂ (proj₂ (advance run (proj₂ (g n))))

{- Backward simulations whose target is a machine ----------------------------}

{- How a source state answers what a target machine does next: by reaching
   a stop with the same observation, by a plus to a state that matches the
   next target state, or by waiting, when the measure decreases -}
data Reflects (L₁ : Machine) {S₂ : Set} (R : ℕ → State L₁ → S₂ → Set) (i : ℕ)
  (s₁ : State L₁) : Next S₂ → Set where
  stops : ∀ {o s₁'} → Star L₁ s₁ s₁' → Final L₁ s₁' o → Reflects L₁ R i s₁ (stop o)
  steps : ∀ {j s₁' s₂'} → Plus L₁ s₁ s₁' → R j s₁' s₂' → Reflects L₁ R i s₁ (next s₂')
  waits : ∀ {j s₂'} → j < i → R j s₁ s₂' → Reflects L₁ R i s₁ (next s₂')

machine-bsim : ∀ {L₁ L₂ : Machine}
  → (R : ℕ → State L₁ → State L₂ → Set)
  → (Σ[ i ∈ ℕ ] R i (start L₁) (start L₂))
  → (∀ {i s₁ s₂} → R i s₁ s₂ → Reflects L₁ R i s₁ (Machine.step L₂ s₂))
  → BSim L₁ L₂
machine-bsim {L₁} {L₂} R init sim = record
  { Index = ℕ
  ; _≺_ = _<_
  ; wf = <-wellFounded
  ; match = R
  ; init = init
  ; final = final
  ; step = step'
  }
  where
  open Machine L₂ using (step)
  final : ∀ {i s₁ s₂ o} → R i s₁ s₂ → step s₂ ≡ stop o
    → Σ[ s₁' ∈ State L₁ ] Star L₁ s₁ s₁' × Final L₁ s₁' o
  final {s₂ = s₂} m eq with step s₂ | sim m
  final m refl | stop o | stops σ fin = _ , σ , fin

  step' : ∀ {i s₁ s₂ s₂'} → R i s₁ s₂ → step s₂ ≡ next s₂'
    → Σ[ i' ∈ ℕ ] Σ[ s₁' ∈ State L₁ ] (Plus L₁ s₁ s₁' ⊎ (Star L₁ s₁ s₁' × i' < i)) × R i' s₁' s₂'
  step' {s₂ = s₂} m eq with step s₂ | sim m
  step' m refl | next s₂' | steps π m' = _ , _ , inj₁ π , m'
  step' m refl | next s₂' | waits lt m' = _ , _ , inj₂ (ε , lt) , m'

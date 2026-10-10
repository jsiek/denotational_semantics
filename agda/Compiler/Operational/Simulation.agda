{-

  Forward simulations, in the spirit of CompCert's Smallstep library:
  their composition, and the end theorem that a forward simulation
  between deterministic, total transition systems makes them equivalent.
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
open import Relation.Binary.Construct.Closure.Transitive as TC using (TransClosure; [_]; _∷ʳ_)
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

  {- one step of a plus: either a target plus, or a target star with the
     index decreasing in the transitive closure -}
  sim-plus : ∀ {i s₁ s₁' s₁'' s₂} → match i s₁ s₂ → Step L₁ s₁ s₁' → Star L₁ s₁' s₁''
    → Σ[ i' ∈ Index ] Σ[ s₂' ∈ State L₂ ]
        (Plus L₂ s₂ s₂' ⊎ (Star L₂ s₂ s₂' × TransClosure _≺_ i' i)) × match i' s₁'' s₂'
  sim-plus m st ε with step m st
  ... | i' , s₂' , inj₁ π , m' = i' , s₂' , inj₁ π , m'
  ... | i' , s₂' , inj₂ (σ , lt) , m' = i' , s₂' , inj₂ (σ , [ lt ]) , m'
  sim-plus m st (st' ◅ σ) with step m st
  ... | i₁ , s₂₁ , r , m₁ with sim-plus m₁ st' σ
  ...   | i' , s₂' , r' , m' = i' , s₂' , combine r r' , m'
    where
    combine : ∀ {a b c i₁ i' i} → Plus L₂ a b ⊎ (Star L₂ a b × i₁ ≺ i)
      → Plus L₂ b c ⊎ (Star L₂ b c × TransClosure _≺_ i' i₁)
      → Plus L₂ a c ⊎ (Star L₂ a c × TransClosure _≺_ i' i)
    combine (inj₁ π) r' = inj₁ (plus-star π (star-of r'))
      where star-of : ∀ {b c} → Plus L₂ b c ⊎ (Star L₂ b c × _) → Star L₂ b c
            star-of (inj₁ π) = plus→star π
            star-of (inj₂ (σ , _)) = σ
    combine (inj₂ (σ₁ , lt₁)) (inj₁ π) = inj₁ (star-plus σ₁ π)
    combine (inj₂ (σ₁ , lt₁)) (inj₂ (σ₂ , lt₂)) = inj₂ (σ₁ ◅◅ σ₂ , lt₂ ∷ʳ lt₁)

{- Composition ----------------------------------------------------------------}

compose : ∀ {L₁ L₂ L₃} → FSim L₁ L₂ → FSim L₂ L₃ → FSim L₁ L₃
compose {L₁} {L₂} {L₃} F G = record
  { Index = Idx
  ; _≺_ = _⊏_
  ; wf = ×-wellFounded (TC.wellFounded G._≺_ G.wf) F.wf
  ; match = M
  ; init = init
  ; final = λ { (s₂ , m₁ , m₂) fin → G.final m₂ (F.final m₁ fin) }
  ; step = step
  }
  where
  module F = FSim F
  module G = FSim G

  Idx = G.Index × F.Index
  _⊏_ : Idx → Idx → Set
  _⊏_ = ×-Lex _≡_ (TransClosure G._≺_) F._≺_

  M : Idx → State L₁ → State L₃ → Set
  M (j , i) s₁ s₃ = Σ[ s₂ ∈ State L₂ ] F.match i s₁ s₂ × G.match j s₂ s₃

  Res : Idx → State L₃ → State L₁ → Set
  Res ji s₃ s₁' = Σ[ ji' ∈ Idx ] Σ[ s₃' ∈ State L₃ ]
    (Plus L₃ s₃ s₃' ⊎ (Star L₃ s₃ s₃' × ji' ⊏ ji)) × M ji' s₁' s₃'

  init : ∀ {s₁} → Initial L₁ s₁ → Σ[ ji ∈ Idx ] Σ[ s₃ ∈ State L₃ ] Initial L₃ s₃ × M ji s₁ s₃
  init i₁ with F.init i₁
  ... | i , s₂ , i₂ , m₁ with G.init i₂
  ...   | j , s₃ , i₃ , m₂ = (j , i) , s₃ , i₃ , s₂ , m₁ , m₂

  {- after the first simulation took a plus in L₂ -}
  after-plus : ∀ {j i i' s₁' s₂' s₃} → F.match i' s₁' s₂'
    → (Σ[ j' ∈ G.Index ] Σ[ s₃' ∈ State L₃ ]
         (Plus L₃ s₃ s₃' ⊎ (Star L₃ s₃ s₃' × TransClosure G._≺_ j' j)) × G.match j' s₂' s₃')
    → Res (j , i) s₃ s₁'
  after-plus {i' = i'} m₁' (j' , s₃' , inj₁ π , m₂') = (j' , i') , s₃' , inj₁ π , _ , m₁' , m₂'
  after-plus {i' = i'} m₁' (j' , s₃' , inj₂ (σ , lt) , m₂') =
    (j' , i') , s₃' , inj₂ (σ , inj₁ lt) , _ , m₁' , m₂'

  step : ∀ {ji s₁ s₃ s₁'} → M ji s₁ s₃ → Step L₁ s₁ s₁' → Res ji s₃ s₁'
  step {j , i} (s₂ , m₁ , m₂) st with F.step m₁ st
  ... | i' , s₂' , inj₁ (plus st₂ σ₂) , m₁' = after-plus m₁' (sim-plus G m₂ st₂ σ₂)
  ... | i' , s₂' , inj₂ (ε , lt) , m₁' = (j , i') , _ , inj₂ (ε , inj₂ (refl , lt)) , s₂' , m₁' , m₂
  ... | i' , s₂' , inj₂ (st₂ ◅ σ₂ , lt) , m₁' = after-plus m₁' (sim-plus G m₂ st₂ σ₂)

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

{- The end theorem ------------------------------------------------------------}

record Equivalent (L₁ L₂ : Semantics) : Set where
  field
    terminates : SameObs (Terminates L₁) (Terminates L₂)
    diverges : Diverges L₁ ⇔ Diverges L₂

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

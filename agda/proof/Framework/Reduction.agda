{-

  Lemmas about reduction semantics (Framework/Reduction.agda), and forward
  simulations between them (proof/Framework/Simulation.agda):

  * runs of a reduction (Star*, Plus*), on terms or on the operands of a
    tuple, and a run of a subterm as a run in a context that reduces that
    subterm first (a frame: star-in, plus-in);
  * how a target term answers the reduction of a source term (Ans): by a
    run to a related value, by a run to a stuck term, or by one or more
    steps to a term related to the reduct; and congruence (ans-in);
  * the end theorem: if the reduction of every source term is answered
    by every related target term, and related values are observed alike,
    the two machines are equivalent (red-equivalent).

-}

module proof.Framework.Reduction (Obs : Set) (o-wrong : Obs) where

open import Framework.Smallstep Obs
open import proof.Framework.Smallstep Obs using (Plus; plus)
open import proof.Framework.Simulation Obs using (FSim; Answers≺; stops; steps; runs; equivalent)
open import Framework.Reduction Obs o-wrong public

open import Framework.abt.Sig using (Sig; ■)
open import Framework.abt.AbstractBindingTree using (ABT; Args; nil; cons; ast)
open import Framework.ListUtil using (args→list)

open import Data.List using (List; []; _∷_; replicate)
open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_)
open import Data.Product using (_×_; Σ-syntax; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)

toNext-to : ∀ {A o} {r : Red A} {M} → toNext o r ≡ next M → r ≡ to M
toNext-to {r = to _} refl = refl

{- a value in the context continues -}
val-in : ∀ {A B} {f : A → B} {r k} → r ≡ val → step-in f r k ≡ k
val-in refl = refl

{- Runs ------------------------------------------------------------------------}

module _ {T : Set} (red : T → Red T) where

  infixr 5 _◅_
  data Star* : T → T → Set where
    ε : ∀ {X} → Star* X X
    _◅_ : ∀ {X Y Z} → red X ≡ to Y → Star* Y Z → Star* X Z

  data Plus* : T → T → Set where
    plus : ∀ {X Y Z} → red X ≡ to Y → Star* Y Z → Plus* X Z

module _ {T : Set} {red : T → Red T} where

  infixr 5 _◅◅_
  _◅◅_ : ∀ {X Y Z} → Star* red X Y → Star* red Y Z → Star* red X Z
  ε ◅◅ τ = τ
  (s ◅ σ) ◅◅ τ = s ◅ (σ ◅◅ τ)

  star-plus : ∀ {X Y Z} → Star* red X Y → Plus* red Y Z → Plus* red X Z
  star-plus ε π = π
  star-plus (s ◅ σ) (plus s' τ) = plus s (σ ◅◅ (s' ◅ τ))

  plus-star : ∀ {X Y Z} → Plus* red X Y → Star* red Y Z → Plus* red X Z
  plus-star (plus s σ) τ = plus s (σ ◅◅ τ)

  {- one step -}
  one : ∀ {X Y} → red X ≡ to Y → Plus* red X Y
  one s = plus s ε

{- g is a frame: g X reduces X first, and then continues with κ X -}
record Frame {T U : Set} (redT : T → Red T) (redU : U → Red U) (g : T → U) : Set where
  constructor frame
  field
    κ : T → Red U
    eq : ∀ X → redU (g X) ≡ step-in g (redT X) (κ X)

module _ {T U : Set} {redT : T → Red T} {redU : U → Red U} {g : T → U}
         (F : Frame redT redU g) where
  open Frame F

  step-in-to : ∀ {X Y} → redT X ≡ to Y → redU (g X) ≡ to (g Y)
  step-in-to s = trans (eq _) (cong (λ r → step-in g r (κ _)) s)

  star-in : ∀ {X Y} → Star* redT X Y → Star* redU (g X) (g Y)
  star-in ε = ε
  star-in (s ◅ σ) = step-in-to s ◅ star-in σ

  plus-in : ∀ {X Y} → Plus* redT X Y → Plus* redU (g X) (g Y)
  plus-in (plus s σ) = plus (step-in-to s) (star-in σ)

  wrong-in : ∀ {X} → redT X ≡ wrong → redU (g X) ≡ wrong
  wrong-in e = trans (eq _) (cong (λ r → step-in g r (κ _)) e)

{- a frame in a frame -}
step-in-∘ : ∀ {A B C : Set} {f : B → C} {h : A → B} r {k k'}
  → step-in f (step-in h r k) k' ≡ step-in (λ x → f (h x)) r (step-in f k k')
step-in-∘ val = refl
step-in-∘ wrong = refl
step-in-∘ (to _) = refl

frame-∘ : ∀ {T U V : Set} {redT : T → Red T} {redU : U → Red U} {redV : V → Red V}
  {h : T → U} {f : U → V} → Frame redT redU h → Frame redU redV f → Frame redT redV (λ x → f (h x))
frame-∘ {redT = redT} {h = h} {f = f} (frame κh eqh) (frame κf eqf) =
  frame _ (λ X → trans (eqf _) (trans (cong (λ r → step-in f r (κf (h X))) (eqh X)) (step-in-∘ {f = f} {h = h} (redT X))))

{- Answers ---------------------------------------------------------------------}

{- how a target term M' answers the reduction r of a source term M, for a
   relation R between source and target terms and a predicate Val on the
   target's values -}
data Ans {S T : Set} (red : T → Red T) (Val : T → Set) (R : S → T → Set) (M : S)
  : Red S → T → Set where
  val : ∀ {M' V'} → Star* red M' V' → Val V' → R M V' → Ans red Val R M val M'
  wrong : ∀ {M' W'} → Star* red M' W' → red W' ≡ wrong → Ans red Val R M wrong M'
  to : ∀ {M₁ M' M₁'} → Plus* red M' M₁' → R M₁ M₁' → Ans red Val R M (to M₁) M'

module _ {S T : Set} {red : T → Red T} {Val : T → Set} {R : S → T → Set} where

  ans-star : ∀ {M r X Y} → Star* red X Y → Ans red Val R M r Y → Ans red Val R M r X
  ans-star σ (val τ v m) = val (σ ◅◅ τ) v m
  ans-star σ (wrong τ w) = wrong (σ ◅◅ τ) w
  ans-star σ (to π m) = to (star-plus σ π) m

  ans-step : ∀ {M r X Y} → red X ≡ to Y → Ans red Val R M r Y → Ans red Val R M r X
  ans-step s = ans-star (s ◅ ε)

  {- a source subterm that is a value -}
  ans-skip : ∀ {A} {f : A → S} {r k M X} → r ≡ val → Ans red Val R M k X → Ans red Val R M (step-in f r k) X
  ans-skip refl a = a

{- congruence: the reduction of the subterm X of f X, in the frame g -}
ans-in : ∀ {S S' T U : Set} {redT : T → Red T} {redU : U → Red U} {ValT : T → Set} {ValU : U → Set}
  {R : S → T → Set} {R' : S' → U → Set} {f : S → S'} {g : T → U} {X X' r k}
  → Frame redT redU g → (∀ {Y Y'} → R Y Y' → R' (f Y) (g Y'))
  → Ans redT ValT R X r X'
  → (∀ {V'} → ValT V' → R X V' → Ans redU ValU R' (f X) k (g V'))
  → Ans redU ValU R' (f X) (step-in f r k) (g X')
ans-in G c (to π m) k = to (plus-in G π) (c m)
ans-in G c (wrong σ w) k = wrong (star-in G σ) (wrong-in G w)
ans-in G c (val σ v m) k = ans-star (star-in G σ) (k v m)

{- The operands of tuples ------------------------------------------------------}

{- the operands of two tuples, related pointwise -}
data Pw {Op₁ Op₂ : Set} {sig₁ : Op₁ → List Sig} {sig₂ : Op₂ → List Sig}
  (R : ABT Op₁ sig₁ → ABT Op₂ sig₂ → Set)
  : ∀ {n} → Args Op₁ sig₁ (replicate n ■) → Args Op₂ sig₂ (replicate n ■) → Set where
  [] : Pw R nil nil
  _∷_ : ∀ {n M M'} {as : Args Op₁ sig₁ (replicate n ■)} {as' : Args Op₂ sig₂ (replicate n ■)}
    → R M M' → Pw R as as' → Pw R (cons (ast M) as) (cons (ast M') as')

module _ {Op₁ Op₂ : Set} {sig₁ : Op₁ → List Sig} {sig₂ : Op₂ → List Sig}
         {R : ABT Op₁ sig₁ → ABT Op₂ sig₂ → Set} where

  pw-map : ∀ {S} → (∀ {M M'} → R M M' → S M M') → ∀ {n as as'} → Pw R {n} as as' → Pw S as as'
  pw-map f [] = []
  pw-map f (r ∷ rs) = f r ∷ pw-map f rs

  pw-list : ∀ {n as as'} → Pw R {n} as as' → Pointwise R (args→list as) (args→list as')
  pw-list [] = []
  pw-list (r ∷ rs) = r ∷ pw-list rs

{- The end theorem -------------------------------------------------------------}

module _ {A B : Set} {obs₁ : A → Obs} {red₁ : A → Red A} {obs₂ : B → Obs} {red₂ : B → Red B}
  {Val : B → Set} (val-red : ∀ {V} → Val V → red₂ V ≡ val)
  (R : A → B → Set) (sim : ∀ {M M'} → R M M' → Ans red₂ Val R M (red₁ M) M')
  (obs-R : ∀ {V V'} → R V V' → red₁ V ≡ val → Val V' → obs₁ V ≡ obs₂ V') where

  private
    module _ (P : B) where
      L₂ = reduction obs₂ red₂ P

      star : ∀ {X Y} → Star* red₂ X Y → Star L₂ X Y
      star ε = ε
      star (s ◅ σ) = cong (toNext (obs₂ _)) s ◅ star σ

      finish : ∀ {i X Y o} → Star* red₂ X Y → Final L₂ Y o → Answers≺ L₂ (λ _ → R) i (stop o) X
      finish ε fin = stops fin
      finish (s ◅ σ) fin = runs (plus (cong (toNext (obs₂ _)) s) (star σ)) fin

      answer : ∀ {i M M' r} → red₁ M ≡ r → Ans red₂ Val R M r M'
        → Answers≺ L₂ (λ _ → R) i (toNext (obs₁ M) r) M'
      answer e (val σ v m) rewrite obs-R m e v = finish σ (cong (toNext (obs₂ _)) (val-red v))
      answer e (wrong σ w) = finish σ (cong (toNext (obs₂ _)) w)
      answer e (to (plus s σ) m) = steps {j = 0} (plus (cong (toNext (obs₂ _)) s) (star σ)) m

  red-fsim : ∀ {M M'} → R M M' → FSim (reduction obs₁ red₁ M) (reduction obs₂ red₂ M')
  red-fsim {M' = P} m = record { match = λ _ → R ; init = 0 , m ; sim = λ m → answer P refl (sim m) }

  red-equivalent : ∀ {M M'} → R M M' → Equivalent (reduction obs₁ red₁ M) (reduction obs₂ red₂ M')
  red-equivalent m = equivalent (red-fsim m)

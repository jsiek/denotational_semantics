{-

  Lemmas about the clocked semantics of Framework/Clocked.agda: the end
  theorem composes (equiv-trans), the laws of the Result monad, and
  clock-for-clock correctness (clocked, clocked-≡): related results, for
  every clock, make programs equivalent. Clock-monotone correctness
  (clocked-le, clocked-back), for a pass after which the target needs
  less clock than the source: results stable from some clock on
  (Stable), and the backward direction (Back).

-}

module proof.Framework.Clocked (Obs : Set) (o-wrong : Obs) where

open import Framework.Clocked Obs o-wrong
open Semantics using (Val; run)

open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe.Relation.Binary.Pointwise as M
open import Data.Nat using (ℕ; _≤_; _⊔_)
open import Data.Nat.Properties using (m≤m⊔n; m≤n⊔m; ≤-trans; ≤-refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

private variable
  A B C A' B' : Set

equiv-trans : ∀ {P₁ P₂ P₃} → Equivalent P₁ P₂ → Equivalent P₂ P₃ → Equivalent P₁ P₃
equiv-trans E F = record
  { terminates = λ o → (λ t → to (T F o) (to (T E o) t)) , (λ t → from (T E o) (from (T F o) t))
  ; diverges = (λ d → to (D F) (to (D E) d)) , (λ d → from (D E) (from (D F) d)) }
  where
  open Equivalent renaming (terminates to T; diverges to D)
  open Data.Product renaming (proj₁ to to; proj₂ to from)

{- The Result monad -------------------------------------------------------------}

bind-cong : ∀ (r : Result A) {f g : A → Result B} → (∀ v → f v ≡ g v) → (r >>= f) ≡ (r >>= g)
bind-cong timeout h = refl
bind-cong wrong h = refl
bind-cong (ret v) h = h v

bind≡ : ∀ {r₁ r₂ : Result A} {f g : A → Result B} → r₁ ≡ r₂ → (∀ v → f v ≡ g v) → (r₁ >>= f) ≡ (r₂ >>= g)
bind≡ {r₁ = r} refl = bind-cong r

bind-assoc : ∀ (r : Result A) {f : A → Result B} {g : B → Result C} → ((r >>= f) >>= g) ≡ (r >>= λ v → f v >>= g)
bind-assoc timeout = refl
bind-assoc wrong = refl
bind-assoc (ret v) = refl

bind-ret : ∀ (r : Result A) → (r >>= ret) ≡ r
bind-ret timeout = refl
bind-ret wrong = refl
bind-ret (ret v) = refl

{- Clock-for-clock correctness ---------------------------------------------------}

data RelResult (R : A → B → Set) : Result A → Result B → Set where
  timeout : RelResult R timeout timeout
  wrong : RelResult R wrong wrong
  ret : ∀ {v w} → R v w → RelResult R (ret v) (ret w)

bind-rel : ∀ {R : A → B → Set} {R' : A' → B' → Set} {r₁ r₂ f g}
  → RelResult R r₁ r₂ → (∀ {v w} → R v w → RelResult R' (f v) (g w))
  → RelResult R' (r₁ >>= f) (r₂ >>= g)
bind-rel timeout k = timeout
bind-rel wrong k = wrong
bind-rel (ret r) k = k r

from-maybe-rel : ∀ {R : A → B → Set} {mv mw}
  → M.Pointwise R mv mw → RelResult R (from-maybe mv) (from-maybe mw)
from-maybe-rel (M.just r) = ret r
from-maybe-rel M.nothing = wrong

≡→rel : ∀ {r₁ r₂ : Result A} → r₁ ≡ r₂ → RelResult _≡_ r₁ r₂
≡→rel {r₁ = timeout} refl = timeout
≡→rel {r₁ = wrong} refl = wrong
≡→rel {r₁ = ret v} refl = ret refl

{- equal results, then related continuations -}
bind-rel≡ : ∀ {R : B → C → Set} {r r' : Result A} {f g}
  → r ≡ r' → (∀ v → RelResult R (f v) (g v)) → RelResult R (r >>= f) (r' >>= g)
bind-rel≡ e k = bind-rel (≡→rel e) λ { refl → k _ }

rel-weaken : ∀ {R S : A → B → Set} {r₁ r₂} → (∀ {v w} → R v w → S v w) → RelResult R r₁ r₂ → RelResult S r₁ r₂
rel-weaken h timeout = timeout
rel-weaken h wrong = wrong
rel-weaken h (ret r) = ret (h r)

{- related results, the second mapped by g -}
rel-map : ∀ {R : A → B → Set} {S : A → C → Set} {r₁ r₂} {g : B → C}
  → (∀ {v w} → R v w → S v (g w)) → RelResult R r₁ r₂ → RelResult S r₁ (r₂ >>= λ w → ret (g w))
rel-map h timeout = timeout
rel-map h wrong = wrong
rel-map h (ret r) = ret (h r)

{- related results, for every clock, make programs equivalent -}
clocked : ∀ {P₁ P₂} (R : Val P₁ → Val P₂ → Set)
  → (∀ {v w} → R v w → Semantics.obs P₁ v ≡ Semantics.obs P₂ w)
  → (∀ ck → RelResult R (run P₁ ck) (run P₂ ck)) → Equivalent P₁ P₂
clocked {P₁} {P₂} R obs≈ rel = record
  { terminates = λ o → (λ { (ck , e) → ck , trans (sym (same (rel ck))) e })
                     , (λ { (ck , e) → ck , trans (same (rel ck)) e })
  ; diverges = (λ d ck → fwd (rel ck) (d ck)) , (λ d ck → bwd (rel ck) (d ck)) }
  where
  same : ∀ {r₁ r₂} → RelResult R r₁ r₂
    → outcome (Semantics.obs P₁) r₁ ≡ outcome (Semantics.obs P₂) r₂
  same timeout = refl
  same wrong = refl
  same (ret r) rewrite obs≈ r = refl

  fwd : ∀ {r₁ r₂} → RelResult R r₁ r₂ → r₁ ≡ timeout → r₂ ≡ timeout
  fwd timeout _ = refl

  bwd : ∀ {r₁ r₂} → RelResult R r₁ r₂ → r₂ ≡ timeout → r₁ ≡ timeout
  bwd timeout _ = refl

{- the same result, for every clock, of programs with the same values -}
clocked-≡ : ∀ {V} {obs : V → Obs} {r₁ r₂} → (∀ ck → r₁ ck ≡ r₂ ck) → Equivalent (semantics V obs r₁) (semantics V obs r₂)
clocked-≡ e = clocked _≡_ (cong _) λ ck → ≡→rel (e ck)

{- Clock-monotone correctness ----------------------------------------------------}

{- r₁ is related to r₂, or times out -}
data LeResult (R : A → B → Set) : Result A → Result B → Set where
  timeout : ∀ {r} → LeResult R timeout r
  wrong : LeResult R wrong wrong
  ret : ∀ {v w} → R v w → LeResult R (ret v) (ret w)

{- r times out, or r' is r -}
data _⊑ᵣ_ {A : Set} : Result A → Result A → Set where
  timeout : ∀ {r} → timeout ⊑ᵣ r
  same : ∀ {r} → r ⊑ᵣ r

{- the results of f grow with the clock -}
Mono : (ℕ → Result A) → Set
Mono f = ∀ {ck ck'} → ck ≤ ck' → f ck ⊑ᵣ f ck'

⊑-bind : ∀ {r₁ r₂ : Result A} {f g : A → Result B} → r₁ ⊑ᵣ r₂ → (∀ v → f v ⊑ᵣ g v) → (r₁ >>= f) ⊑ᵣ (r₂ >>= g)
⊑-bind timeout k = timeout
⊑-bind {r₁ = timeout} same k = timeout
⊑-bind {r₁ = wrong} same k = same
⊑-bind {r₁ = ret v} same k = k v

⊑-eq : ∀ {r r' : Result A} → r ⊑ᵣ r' → ¬ r ≡ timeout → r' ≡ r
⊑-eq timeout t = ⊥-elim (t refl)
⊑-eq same t = refl

bind-le : ∀ {R : A → B → Set} {R' : A' → B' → Set} {r₁ r₂} {f : A → Result A'} {g : B → Result B'}
  → LeResult R r₁ r₂ → (∀ {v w} → r₁ ≡ ret v → R v w → LeResult R' (f v) (g w)) → LeResult R' (r₁ >>= f) (r₂ >>= g)
bind-le timeout k = timeout
bind-le wrong k = wrong
bind-le (ret r) k = k refl r

le-⊑ : ∀ {R : A → B → Set} {r₁ r₂ r₂'} → LeResult R r₁ r₂ → r₂ ⊑ᵣ r₂' → LeResult R r₁ r₂'
le-⊑ timeout _ = timeout
le-⊑ r same = r

from-maybe-le : ∀ {R : A → B → Set} {mv mw} → M.Pointwise R mv mw → LeResult R (from-maybe mv) (from-maybe mw)
from-maybe-le (M.just r) = ret r
from-maybe-le M.nothing = wrong

{- when P₂ needs no more clock than P₁ (at each clock, P₁'s result is P₂'s
   or a timeout), P₂'s results grow with the clock, and P₂ returns only
   when P₁ does for some clock, the programs are equivalent -}
clocked-le : ∀ {P₁ P₂} (R : Val P₁ → Val P₂ → Set)
  → (∀ {v w} → R v w → Semantics.obs P₁ v ≡ Semantics.obs P₂ w)
  → Mono (run P₂)
  → (∀ ck → LeResult R (run P₁ ck) (run P₂ ck))
  → (∀ ck → ¬ run P₂ ck ≡ timeout → Σ[ ck' ∈ ℕ ] ¬ run P₁ ck' ≡ timeout)
  → Equivalent P₁ P₂
clocked-le {P₁} {P₂} R obs≈ mono le def = record
  { terminates = λ o → (λ { (ck , e) → ck , trans (sym (same-out (le ck) (λ t → nt e t))) e })
                     , (λ { (ck , e) → back ck e })
  ; diverges = (λ d ck → fwd-div d ck) , (λ d ck → bwd-div (le ck) (d ck)) }
  where
  nt : ∀ {C : Set} {obs : C → _} {r o} → outcome obs r ≡ just o → ¬ r ≡ timeout
  nt e refl with e
  ... | ()

  same-out : ∀ {r₁ r₂} → LeResult R r₁ r₂ → ¬ r₁ ≡ timeout
    → outcome (Semantics.obs P₁) r₁ ≡ outcome (Semantics.obs P₂) r₂
  same-out timeout t = ⊥-elim (t refl)
  same-out wrong t = refl
  same-out (ret r) t rewrite obs≈ r = refl

  le-nt : ∀ {r₁ r₂} → LeResult R r₁ r₂ → ¬ r₁ ≡ timeout → ¬ r₂ ≡ timeout
  le-nt timeout t = ⊥-elim (t refl)
  le-nt wrong t ()
  le-nt (ret _) t ()

  back : ∀ {o} ck → outcome (Semantics.obs P₂) (run P₂ ck) ≡ just o → Terminates P₁ o
  back ck e with def ck (nt e)
  ... | ck' , t' =
    ck' , trans (same-out (le ck') t')
            (trans (cong (outcome (Semantics.obs P₂))
                     (trans (sym (⊑-eq (mono (m≤n⊔m ck ck')) (le-nt (le ck') t')))
                            (⊑-eq (mono (m≤m⊔n ck ck')) (nt e))))
                   e)

  fwd-div : Diverges P₁ → ∀ ck → run P₂ ck ≡ timeout
  fwd-div d ck = go (run P₂ ck) refl
    where
    go : ∀ r → run P₂ ck ≡ r → run P₂ ck ≡ timeout
    go timeout e = e
    go wrong e = ⊥-elim (proj₂ (def ck (λ t → wt (trans (sym e) t))) (d _))
      where wt : _≡_ {A = Result (Val P₂)} wrong timeout → ⊥
            wt ()
    go (ret v) e = ⊥-elim (proj₂ (def ck (λ t → rt (trans (sym e) t))) (d _))
      where rt : _≡_ {A = Result (Val P₂)} (ret v) timeout → ⊥
            rt ()

  bwd-div : ∀ {r₁ r₂} → LeResult R r₁ r₂ → r₂ ≡ timeout → r₁ ≡ timeout
  bwd-div timeout _ = refl

{- Results that are the same from some clock on --------------------------------}

Stable : (ℕ → Result A) → Result A → Set
Stable f r = Σ[ c ∈ ℕ ] (∀ ck → c ≤ ck → f ck ≡ r)

st-now : ∀ {f : ℕ → Result A} {r} → (∀ ck → f ck ≡ r) → Stable f r
st-now e = 0 , λ ck _ → e ck

st-bind : ∀ {f : ℕ → Result A} {g : ℕ → A → Result B} {v r}
  → Stable f (ret v) → Stable (λ ck → g ck v) r → Stable (λ ck → f ck >>= g ck) r
st-bind {g = g} (c₁ , e₁) (c₂ , e₂) =
  c₁ ⊔ c₂ , λ ck le → trans (cong (λ r → r >>= g ck) (e₁ ck (≤-trans (m≤m⊔n c₁ c₂) le))) (e₂ ck (≤-trans (m≤n⊔m c₁ c₂) le))

st-wrong : ∀ {f : ℕ → Result A} {g : ℕ → A → Result B} → Stable f wrong → Stable (λ ck → f ck >>= g ck) wrong
st-wrong {g = g} (c , e) = c , λ ck le → cong (λ r → r >>= g ck) (e ck le)

stable-unique : ∀ {f : ℕ → Result A} {r r'} → Stable f r → Stable f r' → r ≡ r'
stable-unique (c , e) (c' , e') = trans (sym (e (c ⊔ c') (m≤m⊔n c c'))) (e' (c ⊔ c') (m≤n⊔m c c'))

{- at each clock, f times out or returns the value it returns from some clock on -}
run-at : ∀ {f : ℕ → Result A} {v} → Mono f → Stable f (ret v) → ∀ ck → f ck ≡ timeout ⊎ f ck ≡ ret v
run-at {f = f} mono (c , e) ck = ⊑-ret (subst (f ck ⊑ᵣ_) (e (ck ⊔ c) (m≤n⊔m ck c)) (mono (m≤m⊔n ck c)))
  where ⊑-ret : ∀ {r v} → r ⊑ᵣ ret v → r ≡ timeout ⊎ r ≡ ret v
        ⊑-ret timeout = inj₁ refl
        ⊑-ret same = inj₂ refl

{- a value of f at some clock is the value it returns from some clock on -}
stable-ret : ∀ {f : ℕ → Result A} {v w ck} → Mono f → Stable f (ret v) → f ck ≡ ret w → w ≡ v
stable-ret {ck = ck} mono σ e with run-at mono σ ck
... | inj₁ e' with () ← trans (sym e) e'
... | inj₂ e' with refl ← trans (sym e) e' = refl

{- f, which returns v from some clock on, then g -}
le-stable : ∀ {R : B → C → Set} {f : ℕ → Result A} {v} {g : A → Result B} {r₂} ck
  → Mono f → Stable f (ret v) → LeResult R (g v) r₂ → LeResult R (f ck >>= g) r₂
le-stable {g = g} ck mono σ k with run-at mono σ ck
... | inj₁ e = subst (λ x → LeResult _ (x >>= g) _) (sym e) timeout
... | inj₂ e = subst (λ x → LeResult _ (x >>= g) _) (sym e) k

{- Backward: if r₂ does not time out, f has a related result from some clock on -}
Back : (A → B → Set) → (ℕ → Result A) → Result B → Set
Back R f r₂ = ¬ r₂ ≡ timeout → Σ[ r₁ ∈ _ ] Stable f r₁ × RelResult R r₁ r₂

back-bind : ∀ {R : A → B → Set} {R' : A' → B' → Set} {f : ℕ → Result A} {h : ℕ → A → Result A'}
  {r₂ : Result B} {g : B → Result B'}
  → Back R f r₂ → (∀ {v w} → Stable f (ret v) → R v w → Back R' (λ ck → h ck v) (g w))
  → Back R' (λ ck → f ck >>= h ck) (r₂ >>= g)
back-bind {r₂ = timeout} k₁ k₂ nt = ⊥-elim (nt refl)
back-bind {r₂ = wrong} k₁ k₂ nt with k₁ (λ ())
... | .wrong , st , wrong = wrong , st-wrong st , wrong
back-bind {r₂ = ret w} k₁ k₂ nt with k₁ (λ ())
... | .(ret _) , st , ret r with k₂ st r nt
...   | r' , st' , rr = r' , st-bind st st' , rr

back-wrong : ∀ {R : A → B → Set} {f : ℕ → Result A} → (∀ ck → f ck ≡ wrong) → Back R f wrong
back-wrong e _ = wrong , st-now e , wrong

back-maybe : ∀ {R : A → B → Set} {mv mw} → M.Pointwise R mv mw → Back R (λ _ → from-maybe mv) (from-maybe mw)
back-maybe (M.just r) _ = _ , st-now (λ _ → refl) , ret r
back-maybe M.nothing _ = wrong , st-now (λ _ → refl) , wrong

{- f, which returns v from some clock on, then g -}
back-run : ∀ {R : B → C → Set} {f : ℕ → Result A} {g : ℕ → A → Result B} {v r₂}
  → Stable f (ret v) → Back R (λ ck → g ck v) r₂ → Back R (λ ck → f ck >>= g ck) r₂
back-run σ k nt with k nt
... | r , st , rr = r , st-bind σ st , rr

{- when P₂ needs no more clock than P₁, P₂'s results grow with the clock,
   and P₁ catches up with P₂ (Back), the programs are equivalent -}
clocked-back : ∀ {P₁ P₂} (R : Val P₁ → Val P₂ → Set)
  → (∀ {v w} → R v w → Semantics.obs P₁ v ≡ Semantics.obs P₂ w)
  → Mono (run P₂)
  → (∀ ck → LeResult R (run P₁ ck) (run P₂ ck))
  → (∀ ck → Back R (run P₁) (run P₂ ck))
  → Equivalent P₁ P₂
clocked-back R obs≈ mono le back = clocked-le R obs≈ mono le λ ck nt → src (back ck nt) nt
  where
  nt-rel : ∀ {r₁ r₂} → RelResult R r₁ r₂ → ¬ r₂ ≡ timeout → ¬ r₁ ≡ timeout
  nt-rel timeout nt _ = nt refl
  nt-rel wrong _ ()
  nt-rel (ret _) _ ()

  src : ∀ {f r₂} → Σ[ r₁ ∈ _ ] Stable f r₁ × RelResult R r₁ r₂ → ¬ r₂ ≡ timeout → Σ[ ck ∈ ℕ ] ¬ f ck ≡ timeout
  src (_ , (c , e) , rr) nt = c , λ t → nt-rel rr nt (trans (sym (e c ≤-refl)) t)

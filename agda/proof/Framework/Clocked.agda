{-

  Lemmas about the clocked semantics of Framework/Clocked.agda: the end
  theorem composes (equiv-trans), and clock-for-clock correctness
  (clocked): related results, for every clock, make programs equivalent.

-}

module proof.Framework.Clocked (Obs : Set) (o-wrong : Obs) where

open import Framework.Clocked Obs o-wrong
open Semantics using (Val; run)

open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe.Relation.Binary.Pointwise as M
open import Data.Nat using (ℕ; _≤_; _⊔_)
open import Data.Nat.Properties using (m≤m⊔n; m≤n⊔m)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Data.Product using (Σ-syntax; _,_; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

private variable
  A B A' B' : Set

equiv-trans : ∀ {P₁ P₂ P₃} → Equivalent P₁ P₂ → Equivalent P₂ P₃ → Equivalent P₁ P₃
equiv-trans E F = record
  { terminates = λ o → (λ t → to (T F o) (to (T E o) t)) , (λ t → from (T E o) (from (T F o) t))
  ; diverges = (λ d → to (D F) (to (D E) d)) , (λ d → from (D E) (from (D F) d)) }
  where
  open Equivalent renaming (terminates to T; diverges to D)
  open Data.Product renaming (proj₁ to to; proj₂ to from)

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

{- when P₂ needs no more clock than P₁ (at each clock, P₁'s result is P₂'s
   or a timeout), P₂'s results grow with the clock, and P₂ returns only
   when P₁ does for some clock, the programs are equivalent -}
clocked-le : ∀ {P₁ P₂} (R : Val P₁ → Val P₂ → Set)
  → (∀ {v w} → R v w → Semantics.obs P₁ v ≡ Semantics.obs P₂ w)
  → (∀ {ck ck'} → ck ≤ ck' → run P₂ ck ⊑ᵣ run P₂ ck')
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

  ⊑-eq : ∀ {C : Set} {r r' : Result C} → r ⊑ᵣ r' → ¬ r ≡ timeout → r' ≡ r
  ⊑-eq timeout t = ⊥-elim (t refl)
  ⊑-eq same t = refl

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

{-

  Functional big-step semantics with a clock, in the style of CakeML, for
  any type Obs of observations with an observation o-wrong of going
  wrong: results of clocked interpreters, the end theorem (Equivalent),
  and clock-for-clock correctness (clocked).

  Language independent: instantiated at a compiler's observations (for
  this compiler, Compiler/Functional/Clock.agda, which has the design note
  for its interpreters and proofs).

-}

module Clocked (Obs : Set) (o-wrong : Obs) where

open import Iff using (_⇔_)

open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe.Relation.Binary.Pointwise as M
open import Data.Nat using (ℕ)
open import Data.Product using (Σ-syntax; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

private variable
  A B A' B' : Set

data Result (A : Set) : Set where
  timeout : Result A
  wrong : Result A
  ret : A → Result A

infixl 1 _>>=_
_>>=_ : Result A → (A → Result B) → Result B
timeout >>= f = timeout
wrong >>= f = wrong
ret v >>= f = f v

{- a lookup or projection, which goes wrong if there is nothing -}
from-maybe : Maybe A → Result A
from-maybe (just v) = ret v
from-maybe nothing = wrong

{- The end theorem -------------------------------------------------------------}

{- a program, run with a clock -}
record Semantics : Set₁ where
  constructor semantics
  field
    Val : Set
    obs : Val → Obs
    run : ℕ → Result Val
open Semantics using (Val; run)

outcome : (A → Obs) → Result A → Maybe Obs
outcome obs timeout = nothing
outcome obs wrong = just o-wrong
outcome obs (ret v) = just (obs v)

module _ (P : Semantics) where
  open Semantics P using (obs)

  Terminates : Obs → Set
  Terminates o = Σ[ ck ∈ ℕ ] outcome obs (run P ck) ≡ just o

  Diverges : Set
  Diverges = ∀ ck → run P ck ≡ timeout

record Equivalent (P₁ P₂ : Semantics) : Set where
  field
    terminates : ∀ o → Terminates P₁ o ⇔ Terminates P₂ o
    diverges : Diverges P₁ ⇔ Diverges P₂

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

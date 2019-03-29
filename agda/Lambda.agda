module Lambda where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_)
open import Data.Bool
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)
open import Data.Unit using (⊤; tt)
open import Function using (_∘_)
open import Function.Equivalence using (_⇔_; equivalence)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable using (map)
open import Relation.Nullary.Negation using (contraposition)
open import Relation.Nullary.Product using (_×-dec_)

infix  4  _⊢_
infix  4  _∋_
infixl 5  _,_

infix  6  ƛ_
infix  6  `_
infix  6  $_
infixl 7  _·_

data Type : Set where
  ★ : Type

data Context : Set where
  ∅   : Context
  _,_ : Context → Type → Context

data _∋_ : Context → Type → Set where

  Z : ∀ {Γ A}
     ---------
   → Γ , A ∋ A

  S_ : ∀ {Γ A B}
    → Γ ∋ A
      ---------
    → Γ , B ∋ A

data Base : Set where
  Nat : Base
  𝔹 : Base

data Prim : Set where
  `_ : Base → Prim
  _⇒_ : Base → Prim → Prim

base-rep : Base → Set 
base-rep Nat = ℕ
base-rep 𝔹 = Bool

rep : Prim → Set
rep (` b) = base-rep b
rep (b ⇒ p) = base-rep b → rep p

base-eq? : (B : Base) → (B' : Base) → Dec (B ≡ B')
base-eq? Nat Nat = yes refl
base-eq? Nat 𝔹 = no (λ ())
base-eq? 𝔹 Nat = no (λ ())
base-eq? 𝔹 𝔹 = yes refl

prim-eq? : (P : Prim) → (P' : Prim) → Dec (P ≡ P')
prim-eq? (` B) (` B')
    with base-eq? B B'
... | yes eq rewrite eq = yes refl
... | no neq = no G
    where G : ¬ ` B ≡ ` B'
          G refl = neq refl
prim-eq? (` B) (B' ⇒ P') = no λ ()
prim-eq? (B ⇒ P) (` B') = no (λ ())
prim-eq? (B ⇒ P) (B' ⇒ P')
    with base-eq? B B' | prim-eq? P P'
... | yes b-eq | yes p-eq = yes (Eq.cong₂ _⇒_ b-eq p-eq)
... | yes b-eq | no p-neq = no G
    where G : ¬ (B ⇒ P) ≡ (B' ⇒ P')
          G refl = p-neq refl
prim-eq? (B ⇒ P) (B' ⇒ P') | no b-neq  | _ = no G
    where G : ¬ (B ⇒ P) ≡ (B' ⇒ P')
          G refl = b-neq refl

data _⊢_ : Context → Type → Set where

  $_ :  ∀ {Γ}{p : Prim} → rep p → Γ ⊢ ★
  
  `_ : ∀ {Γ A}
    → Γ ∋ A
      -----
    → Γ ⊢ A

  ƛ_  :  ∀ {Γ}
    → Γ , ★ ⊢ ★
      ---------
    → Γ ⊢ ★

  _·_ : ∀ {Γ}
    → Γ ⊢ ★
    → Γ ⊢ ★
      ------
    → Γ ⊢ ★

count : ∀ {Γ} → ℕ → Γ ∋ ★
count {Γ , ★} zero     =  Z
count {Γ , ★} (suc n)  =  S (count n)
count {∅}     _        =  ⊥-elim impossible
  where postulate impossible : ⊥

#_ : ∀ {Γ} → ℕ → Γ ⊢ ★
# n  =  ` count n

Rename : Context → Context → Set
Rename Γ Δ = ∀{A} → Γ ∋ A → Δ ∋ A

ext : ∀ {Γ Δ} → Rename Γ Δ
    -----------------------------------
  → (∀ {A B} → Γ , B ∋ A → Δ , B ∋ A)
ext ρ Z      =  Z
ext ρ (S x)  =  S (ρ x)

rename : ∀ {Γ Δ}
  → Rename Γ Δ
    ------------------------
  → (∀ {A} → Γ ⊢ A → Δ ⊢ A)
rename ρ (` x)          =  ` (ρ x)
rename ρ ($_ {p = p} k) =  $_ {p = p} k
rename ρ (ƛ N)          =  ƛ (rename (ext ρ) N)
rename ρ (L · M)        =  (rename ρ L) · (rename ρ M)

exts : ∀ {Γ Δ} → (∀ {A} → Γ ∋ A → Δ ⊢ A)
    ----------------------------------
  → (∀ {A B} → Γ , B ∋ A → Δ , B ⊢ A)
exts σ Z      =  ` Z
exts σ (S x)  =  rename S_ (σ x)

subst : ∀ {Γ Δ}
  → (∀ {A} → Γ ∋ A → Δ ⊢ A)
    ------------------------
  → (∀ {A} → Γ ⊢ A → Δ ⊢ A)
subst σ (` x)          =  σ x
subst{Γ}{Δ} σ ($_ {Γ} {p} k) = ($_ {Δ} {p} k)
subst σ (ƛ N)          =  ƛ (subst (exts σ) N)
subst σ (L · M)        =  (subst σ L) · (subst σ M)

subst-zero : ∀ {Γ B} → (Γ ⊢ B) → ∀ {A} → (Γ , B ∋ A) → (Γ ⊢ A)
subst-zero M Z      =  M
subst-zero M (S x)  =  ` x

_[_] : ∀ {Γ A B}
        → Γ , B ⊢ A
        → Γ ⊢ B 
          ---------
        → Γ ⊢ A
_[_] {Γ} {A} {B} N M =  subst {Γ , B} {Γ} (subst-zero M) {A} N

data TermValue : ∀ {Γ A} → Γ ⊢ A → Set where

  V-ƛ : ∀ {Γ} {N : Γ , ★ ⊢ ★}
      -----------
    → TermValue (ƛ N)

  V-const : ∀ {Γ} {p : Prim} {k : rep p}
      ------------------------
    → TermValue {Γ} ($_ {Γ}{p} k)

  V-var : ∀ {Γ}{A}{x : Γ ∋ A}
      ----------------------
    → TermValue {Γ}{A} (` x)


infix 2 _—→_

data _—→_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where

  ξ₁-rule : ∀ {Γ} {L L′ M : Γ ⊢ ★}
    → L —→ L′
      ----------------
    → L · M —→ L′ · M

  ξ₂-rule : ∀ {Γ} {L M M′ : Γ ⊢ ★}
    → TermValue L
    → M —→ M′
      ----------------
    → L · M —→ L · M′

  β-rule : ∀ {Γ} {N : Γ , ★ ⊢ ★} {M : Γ ⊢ ★}
    → TermValue M
      ---------------------------------
    → (ƛ N) · M —→ N [ M ]

  δ-rule : ∀ {Γ}{B}{P} {f : base-rep B → rep P} {k : base-rep B}
      ---------------------------------------------------------
    → ($_ {Γ} {B ⇒ P} f) · ($_ {Γ}{` B} k) —→ ($_ {Γ}{P} (f k))


infix  2 _—↠_
infix  1 begin_
infixr 2 _—→⟨_⟩_
infix  3 _∎

data _—↠_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where

  _∎ : ∀ {Γ A} (M : Γ ⊢ A)
      --------
    → M —↠ M

  _—→⟨_⟩_ : ∀ {Γ A} (L : Γ ⊢ A) {M N : Γ ⊢ A}
    → L —→ M
    → M —↠ N
      ---------
    → L —↠ N

begin_ : ∀ {Γ} {A} {M N : Γ ⊢ A}
  → M —↠ N
    ------
  → M —↠ N
begin M—↠N = M—↠N


data Progress (M : ∅ ⊢ ★) : Set where
  step : ∀{N : ∅ ⊢ ★}
     → M —→ N
     → Progress M

  done : TermValue M → Progress M

  stuck : Progress M

progress : (M : ∅ ⊢ ★) → Progress M
progress ($ k) = done V-const
progress (` ())
progress (ƛ d) = done V-ƛ
progress (L · M)
    with progress L
... | step L→L' = step (ξ₁-rule L→L')
... | done (V-var{x = ()})
... | stuck = stuck
progress (L · M) | done V-ƛ
        with progress M
...     | step M→M' = step (ξ₂-rule V-ƛ M→M')
...     | done Mv = step (β-rule Mv)
...     | stuck = stuck
progress (($ k) · M) | done (V-const {p = ` B}) = stuck
progress (($ f) · M) | done (V-const {p = B ⇒ P})
        with progress M
...     | step M→M' = step (ξ₂-rule V-const M→M')
...     | stuck = stuck
...     | done V-ƛ = stuck
...     | done (V-var{x = ()})
...     | done (V-const{p = P'})
           with prim-eq? P' (` B) 
...        | yes refl = step δ-rule
...        | no neq = stuck

data Finished {Γ A} (N : Γ ⊢ A) : Set where
   done :
       TermValue N
       -----------
     → Finished N
   out-of-gas :
       ----------
       Finished N
   stuck :
       ----------
       Finished N

data Steps : ∀ {A} → ∅ ⊢ A → Set where
  steps : ∀ {A} {L N : ∅ ⊢ A}
    → L —↠ N
    → Finished N
      ----------
    → Steps L

eval : ℕ → (L : ∅ ⊢ ★) → Steps L
eval zero    L                     =  steps (L ∎) out-of-gas
eval (suc m) L with progress L
... | done VL                      =  steps (L ∎) (done VL)
... | stuck                        = steps (L ∎) stuck
... | step {M} L—→M with eval m M
...    | steps M—↠N fin            =  steps (L —→⟨ L—→M ⟩ M—↠N) fin

run : ℕ → (∅ ⊢ ★) → (∅ ⊢ ★)
run zero    L                     =  L
run (suc m) L with progress L
... | done VL                      = L
... | stuck                        = L
... | step {M} L—→M                = run m M

_ : run 2 ((ƛ (` Z)) · ($ 1)) ≡ $ 1
_ = refl

inc : ∅ ⊢ ★
inc = ($_ {p = Nat ⇒ (` Nat)} λ x → x + 1)

_ : run 2 (inc · ($ 2)) ≡ $ 3
_ = refl



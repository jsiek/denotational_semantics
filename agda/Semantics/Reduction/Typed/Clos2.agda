{-

  A reduction semantics for Clos2ᵀ (Language/Typed/Clos2.agda), as for
  ISWIMᵀ (Semantics/Reduction/Typed/ISWIM.agda). A closure evaluates its
  free variables left to right; applying it to a value W substitutes W
  and their values for the variables of its code, which no other
  substitution enters.

-}

module Semantics.Reduction.Typed.Clos2 where

open import Framework.Primitives using (Int)
open import Language.Prim using (Prim)
import Language.Prim as P
open import Language.Typed.Type renaming (_≟_ to _≟F_)
open import Language.Typed.Clos2
open import Semantics.Observation using (Obs; o-const; o-fun; o-tuple; o-inl; o-inr; o-error)
open import Semantics.Reduction.Smallstep using (Machine; Red; val; error; to; step-in; reduction)
open import Framework.ReductionVec Obs o-error using (red-∷)

open import Data.Bool using (if_then_else_)
open import Data.Fin using (Fin; zero; suc)
open import Data.Integer using (ℤ; _-_; _≟_)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; suc)
open import Data.Unit using (⊤; tt)
open import Data.Vec using (Vec; []; _∷_; lookup)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (Dec; yes; no; does)

{- Renaming and substitution ----------------------------------------------}

open import Framework.Syntax.Kit {ℕ} {⊤} (λ k _ → Fin k) (λ k _ → suc k) (λ k _ → Tm k Any) public

module _ (𝒦 : Kit) where
  open Kit 𝒦

  exts : ∀ {k k'} → Sub 𝒦 k k' → Sub 𝒦 (suc k) (suc k')
  exts σ zero = vr zero
  exts σ (suc x) = wk (σ x)

  trav : ∀ {k k' A} → Sub 𝒦 k k' → Tm k A → Tm k' A
  travs : ∀ {k k' n} → Sub 𝒦 k k' → Vec (Tm k Any) n → Vec (Tm k' Any) n
  trav σ (` x) = tm (σ x)
  trav σ (clos N Ms) = clos N (travs σ Ms)
  trav σ (app L M) = app (trav σ L) (trav σ M)
  trav σ (lit B c) = lit B c
  trav σ (tuple Ms) = tuple (travs σ Ms)
  trav σ (get i M) = get i (trav σ M)
  trav σ (inl M) = inl (trav σ M)
  trav σ (inr M) = inr (trav σ M)
  trav σ (case L M N) = case (trav σ L) (trav (exts σ) M) (trav (exts σ) N)
  trav σ (prim p L M) = prim p (trav σ L) (trav σ M)
  trav σ (let′ M N) = let′ (trav σ M) (trav (exts σ) N)
  trav σ (inject G M) = inject G (trav σ M)
  trav σ (project t M) = project t (trav σ M)
  travs σ [] = []
  travs σ (M ∷ Ms) = trav σ M ∷ travs σ Ms

varK : Kit
varK = record { K = λ k _ → Fin k ; vr = λ x → x ; tm = `_ ; wk = suc }

ren : ∀ {k k' A} → (Fin k → Fin k') → Tm k A → Tm k' A
ren r = trav varK r

tmK : Kit
tmK = record { K = λ k _ → Tm k Any ; vr = `_ ; tm = λ M → M ; wk = ren suc }

sub : ∀ {k k' A} → (Fin k → Tm k' Any) → Tm k A → Tm k' A
sub σ = trav tmK σ


{- substituting a value for variable 0 -}
_[_] : ∀ {A} → Tm 1 A → Tm 0 Any → Tm 0 A
N [ V ] = sub (λ _ → V) N

{- The reduction ----------------------------------------------------------}

obs : ∀ {A} → Tm 0 A → Obs
obss : ∀ {n} → Vec (Tm 0 Any) n → List Obs
obs (clos _ _) = o-fun
obs (lit B c) = o-const B c
obs (tuple Ms) = o-tuple (obss Ms)
obs (inl M) = o-inl (obs M)
obs (inr M) = o-inr (obs M)
obs (inject G M) = obs M
obs _ = o-error
obss [] = []
obss (M ∷ Ms) = obs M ∷ obss Ms

{- the term of a primitive's result: eq gives inl ⟨⟩ for true -}
out : ∀ {k} p → ℤ → ℤ → Tm k ⟪ out-flat p ⟫
out P.sub n m = lit Int (n - m)
out P.eq n m = if does (n ≟ m) then inl unit else inr unit
  where unit = inject (tup 0) (tuple [])

{- the redexes, once the operands are values (on terms of any type, so
   that the other shapes need no unification of types) -}
β : ∀ {A} → Tm 0 A → Tm 0 Any → Red (Tm 0 Any)
β (clos N Vs) W = to (sub (lookup (W ∷ Vs)) N)
β _ W = error

get? : ∀ {A n} → Fin n → Tm 0 A → A ≡ ⟪ tup n ⟫ → Red (Tm 0 Any)
get? i (tuple Vs) refl = to (lookup Vs i)
get? i _ _ = error

case? : ∀ {A} → Tm 0 A → Tm 1 Any → Tm 1 Any → Red (Tm 0 Any)
case? (inl V) M N = to (M [ V ])
case? (inr V) M N = to (N [ V ])
case? _ M N = error

prim? : ∀ p {A B} → Tm 0 A → Tm 0 B → Red (Tm 0 ⟪ out-flat p ⟫)
prim? p (lit Int n) (lit Int m) = to (out p n m)
prim? p _ _ = error

{- the only error: a value injected from another flat type -}
proj-dec : ∀ {G H} → Dec (G ≡ H) → Tm 0 ⟪ G ⟫ → Red (Tm 0 ⟪ H ⟫)
proj-dec (yes refl) V = to V
proj-dec (no _) V = error

project? : ∀ t {A} → Tm 0 A → Red (Tm 0 ⟪ flat t ⟫)
project? t (inject G V) = proj-dec (G ≟F flat t) V
project? t _ = error

red : ∀ {A} → Tm 0 A → Red (Tm 0 A)
reds : ∀ {n} → Vec (Tm 0 Any) n → Red (Vec (Tm 0 Any) n)
red (` ())
red (clos N Ms) = step-in (clos N) (reds Ms) val
red (app L M) = step-in (λ L' → app L' M) (red L) (step-in (app L) (red M) (β L M))
red (lit B c) = val
red (tuple Ms) = step-in tuple (reds Ms) val
red (get i M) = step-in (get i) (red M) (get? i M refl)
red (inl M) = step-in inl (red M) val
red (inr M) = step-in inr (red M) val
red (case L M N) = step-in (λ L' → case L' M N) (red L) (case? L M N)
red (prim p L M) = step-in (λ L' → prim p L' M) (red L) (step-in (prim p L) (red M) (prim? p L M))
red (let′ M N) = step-in (λ M' → let′ M' N) (red M) (to (N [ M ]))
red (inject G M) = step-in (inject G) (red M) val
red (project t M) = step-in (project t) (red M) (project? t M)
reds [] = val
reds (M ∷ Ms) = red-∷ M Ms (red M) (reds Ms)

sem : Tm 0 Any → Machine
sem M = reduction obs red M

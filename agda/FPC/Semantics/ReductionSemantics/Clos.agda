{-

  A reduction semantics for Closμ (FPC/Language/Clos.agda), as for
  FPC (FPC/Semantics/ReductionSemantics/FPC.agda) and Clos2ᵀ
  (ISWIM/Semantics/Reduction/Typed/Clos2.agda). A closure evaluates its free
  variables left to right; applying it to a value W substitutes W and
  their values for the variables of its code, which no other
  substitution enters.

-}

module FPC.Semantics.ReductionSemantics.Clos where

open import Framework.Primitives using (Int)
open import Language.Prim using (Prim)
import Language.Prim as P
open import FPC.Language.Type hiding (_[_])
open import FPC.Language.Clos
open import FPC.Framework.AllUtil using (All; []; _∷_; lookup)
open import Semantics.Observation using (Obs; o-const; o-fun; o-tuple; o-inl; o-inr; o-error)
open import Semantics.Reduction.Smallstep using (Machine; Red; val; error; to; step-in; reduction)
open import FPC.Framework.ReductionAll Obs o-error using (red-∷)

open import Data.Bool using (if_then_else_)
open import Data.Integer using (ℤ; _-_; _≟_)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (does)

{- Renaming and substitution: the traversal, the rest by
   Framework/Syntax/TypedSubst.agda ------------------------------------------}

open import Framework.Syntax.TypedSubst Tm `_ public

module _ (𝒦 : Kit) where
  open Kit 𝒦

  trav : ∀ {Γ Δ A} → Sub 𝒦 Γ Δ → Tm Γ A → Tm Δ A
  travs : ∀ {Γ Δ Δ'} → Sub 𝒦 Γ Δ → All (Tm Γ) Δ' → All (Tm Δ) Δ'
  trav σ (` x) = tm (σ x)
  trav σ (clos N Ms) = clos N (travs σ Ms)
  trav σ (app L M) = app (trav σ L) (trav σ M)
  trav σ (lit B c) = lit B c
  trav σ (tuple Ms) = tuple (travs σ Ms)
  trav σ (get i M) = get i (trav σ M)
  trav σ (inl M) = inl (trav σ M)
  trav σ (inr M) = inr (trav σ M)
  trav σ (case L M N) = case (trav σ L) (trav (exts 𝒦 σ) M) (trav (exts 𝒦 σ) N)
  trav σ (prim p L M) = prim p (trav σ L) (trav σ M)
  trav σ (let′ M N) = let′ (trav σ M) (trav (exts 𝒦 σ) N)
  trav σ (fold M) = fold (trav σ M)
  trav σ (unfold M) = unfold (trav σ M)
  travs σ [] = []
  travs σ (M ∷ Ms) = trav σ M ∷ travs σ Ms

open Substitution trav public

{- The reduction ----------------------------------------------------------}

obs : ∀ {A} → Tm [] A → Obs
obss : ∀ {Δ} → All (Tm []) Δ → List Obs
obs (clos _ _) = o-fun
obs (lit B c) = o-const B c
obs (tuple Ms) = o-tuple (obss Ms)
obs (inl M) = o-inl (obs M)
obs (inr M) = o-inr (obs M)
obs (fold M) = obs M
obs _ = o-error
obss [] = []
obss (M ∷ Ms) = obs M ∷ obss Ms

{- the term of a primitive's result: eq gives inl ⟨⟩ for true -}
out : ∀ {Γ} p → ℤ → ℤ → Tm Γ (out-ty p)
out P.sub n m = lit Int (n - m)
out P.eq n m = if does (n ≟ m) then inl (tuple []) else inr (tuple [])

{- the redexes, once the operands are values -}
β : ∀ {C A B} → Tm [] C → C ≡ A ⇒ B → Tm [] A → Red (Tm [] B)
β (clos N Vs) refl W = to (sub (W • lookup Vs) N)
β _ _ W = error

get? : ∀ {C Δ A} → Δ ∋ A → Tm [] C → C ≡ tup Δ → Red (Tm [] A)
get? i (tuple Vs) refl = to (lookup Vs i)
get? i _ _ = error

case? : ∀ {C A B D} → Tm [] C → C ≡ A ⊹ B → Tm (A ∷ []) D → Tm (B ∷ []) D → Red (Tm [] D)
case? (inl V) refl M N = to (M [ V ])
case? (inr V) refl M N = to (N [ V ])
case? _ _ M N = error

prim? : ∀ p {A B} → Tm [] A → Tm [] B → Red (Tm [] (out-ty p))
prim? p (lit Int n) (lit Int m) = to (out p n m)
prim? p _ _ = error

unfold? : ∀ {C A} → Tm [] C → C ≡ μ A → Red (Tm [] (unroll A))
unfold? (fold V) refl = to V
unfold? _ _ = error

red : ∀ {A} → Tm [] A → Red (Tm [] A)
reds : ∀ {Δ} → All (Tm []) Δ → Red (All (Tm []) Δ)
red (` ())
red (clos N Ms) = step-in (clos N) (reds Ms) val
red (app L M) = step-in (λ L' → app L' M) (red L) (step-in (app L) (red M) (β L refl M))
red (lit B c) = val
red (tuple Ms) = step-in tuple (reds Ms) val
red (get i M) = step-in (get i) (red M) (get? i M refl)
red (inl M) = step-in inl (red M) val
red (inr M) = step-in inr (red M) val
red (case L M N) = step-in (λ L' → case L' M N) (red L) (case? L refl M N)
red (prim p L M) = step-in (λ L' → prim p L' M) (red L) (step-in (prim p L) (red M) (prim? p L M))
red (let′ M N) = step-in (λ M' → let′ M' N) (red M) (to (N [ M ]))
red (fold M) = step-in fold (red M) val
red (unfold M) = step-in unfold (red M) (unfold? M refl)
reds [] = val
reds (M ∷ Ms) = red-∷ M Ms (red M) (reds Ms)

sem : ∀ {A} → Tm [] A → Machine
sem M = reduction obs red M

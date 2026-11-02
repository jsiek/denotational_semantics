{-

  A reduction semantics for FPC (Mu/Language/FPC.agda), as for
  ISWIMᵀ (Semantics/Reduction/Typed/ISWIM.agda): call by value, left to
  right, by substitution, on closed terms of any type, with the same
  order of evaluation as the CEK machine (Mu/Semantics/AbstractMachines/FPC.agda).
  A term of type A reduces to one of type A, so there is no case for an
  operand of the wrong kind or for a variable, and nothing is stuck:
  unfold (fold V) reduces to V.

  Renaming and substitution are one traversal with a kit
  (Mu/Language/FPCSubst.agda, which the simplify pass shares, on
  Framework/Syntax/TypedSubst.agda).

  The redexes take an equation between the operand's type and the
  expected one (C ≡ A ⇒ B): a term cannot be split at a concrete type,
  since unfold's type A [ μ A ] does not unify with one (the design
  note's green slime), so they split it at a generic type, and the
  equation then.

-}

module Mu.Semantics.ReductionSemantics.FPC where

open import Framework.Primitives using (Int)
open import Language.Prim using (Prim)
import Language.Prim as P
open import Mu.Language.Type hiding (_[_])
open import Mu.Language.FPC
open import Mu.Framework.AllUtil using (All; []; _∷_; lookup)
open import Semantics.Observation using (Obs; o-const; o-fun; o-tuple; o-inl; o-inr; o-error)
open import Semantics.Reduction.Smallstep using (Machine; Red; val; error; to; step-in; reduction)
open import Mu.Framework.ReductionAll Obs o-error using (red-∷)

open import Data.Bool using (if_then_else_)
open import Data.Integer using (ℤ; _-_; _≟_)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (does)

{- Renaming and substitution (shared with simplify) ------------------------}

open import Mu.Language.FPCSubst public

{- The reduction ----------------------------------------------------------}

obs : ∀ {A} → Tm [] A → Obs
obss : ∀ {Δ} → All (Tm []) Δ → List Obs
obs (lam _) = o-fun
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
β (lam N) refl W = to (N [ W ])
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
red (lam N) = val
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

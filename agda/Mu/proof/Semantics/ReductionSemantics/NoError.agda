{-

  The reduction semantics of ISWIMμ (Mu/Semantics/ReductionSemantics/ISWIM.agda)
  never stops with an error. Its redexes have catch-all error cases (a
  term cannot be split at a concrete type, the design note's green
  slime, so they split it at a generic type with an equation), and obs
  one for terms that are not values; none is reached. Progress, by
  induction on a closed term: it is a value (Value, and red gives val)
  or it reduces; a value of a function, tuple, sum, integer or
  recursive type has the form of its type (the cases of Value at that
  type), so each redex reduces. A value is observed as an answer.

-}

module Mu.proof.Semantics.ReductionSemantics.NoError where

open import Mu.Language.Type hiding (_[_])
open import Mu.Language.ISWIM
open import Mu.Semantics.ReductionSemantics.ISWIM
open import Mu.proof.Semantics.ReductionSemantics.ISWIM using (Value; lam; lit; tuple; inl; inr; fold)
open import Semantics.Observation using (Obs; o-error; Answer)
open import Mu.proof.Framework.ReductionAll Obs o-error using (Each; []; _∷_)
open import Mu.Framework.AllUtil using (All; []; _∷_)
open import Semantics.Reduction.Smallstep using (Red; val; to; step-in; toNext; Terminates; Next; next; stop)
open import Data.Empty using (⊥)

open import Data.List using ([])
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; cong)
open import Relation.Nullary using (¬_)

{- a value, or a term that reduces -}
data Prog {X : Set} (V : X → Set) (M : X) (r : Red X) : Set where
  value : V M → r ≡ val → Prog V M r
  steps : ∀ N → r ≡ to N → Prog V M r

private
  {- reduce in a context, or go on once the subterm is a value -}
  ctx : ∀ {A B : Set} {V : A → Set} {M : A} {V' : B → Set} {M' : B} {f : A → B} {r k} → Prog V M r
    → (V M → r ≡ val → Prog V' M' k) → Prog V' M' (step-in f r k)
  ctx (steps N refl) h = steps _ refl
  ctx (value v refl) h = h v refl

progress : ∀ {A} (M : Tm [] A) → Prog Value M (red M)
progresses : ∀ {Δ} (Ms : All (Tm []) Δ) → Prog (Each Value) Ms (reds Ms)

progress (` ())
progress (lam N) = value lam refl
progress (app L M) = ctx (progress L) λ { lam eL → ctx (progress M) λ vM eM → steps _ refl }
progress (lit B c) = value lit refl
progress (tuple Ms) = ctx (progresses Ms) λ vs e → value (tuple vs) refl
progress (get i M) = ctx (progress M) λ { (tuple vs) e → steps _ refl }
progress (inl M) = ctx (progress M) λ v e → value (inl v) refl
progress (inr M) = ctx (progress M) λ v e → value (inr v) refl
progress (case L M N) = ctx (progress L) λ { (inl v) e → steps _ refl ; (inr v) e → steps _ refl }
progress (prim p L M) = ctx (progress L) λ { lit eL → ctx (progress M) λ { lit eM → steps _ refl } }
progress (let′ M N) = ctx (progress M) λ v e → steps _ refl
progress (fold M) = ctx (progress M) λ v e → value (fold v) refl
progress (unfold M) = ctx (progress M) λ { (fold v) e → steps _ refl }

progresses [] = value [] refl
progresses (M ∷ Ms) = ctx (progress M) λ v e → ctx (progresses Ms) λ vs es → value (v ∷ vs) refl

value-answer : ∀ {A} {V : Tm [] A} → Value V → Answer (obs V)
value-answer lam ()
value-answer lit ()
value-answer (tuple vs) ()
value-answer (inl v) ()
value-answer (inr v) ()
value-answer (fold v) = value-answer v

iswim-no-error : ∀ {A} (M : Tm [] A) → ¬ Terminates (sem M) o-error
iswim-no-error M (s , _ , fin) = go (progress s) fin
  where
  go : Prog Value s (red s) → toNext (obs s) (red s) ≡ stop o-error → ⊥
  go (value v e) f = value-answer v (cong stopped (trans (sym (cong (toNext (obs s)) e)) f))
    where
    stopped : Next (Tm [] _) → Obs
    stopped (stop o) = o
    stopped (next _) = o-error
  go (steps N e) f with trans (sym (cong (toNext (obs s)) e)) f
  ... | ()

{-

  Lemmas shared by the simulation proofs of the typed closure-conversion
  passes (proof/Correctness/CEK/*Sim.agda): the typed machines
  collect a tuple's values in a list, with an equation for its length
  (Framework/VecUtil.agda), and two machines that collect related values
  build related tuples, whatever their equations.

-}

module proof.Correctness.CEK.Common where

open import Framework.VecUtil using (toVec; collected)
open import proof.Semantics.CEK.Smallstep

open import Data.List using (List; []; _∷_; length; reverse)
open import Data.List.Relation.Binary.Pointwise as L using ([]; _∷_; reverse⁺)
open import Data.Nat using (ℕ; _+_)
open import Data.Vec using (Vec; []; _∷_; toList)
open import Data.Vec.Properties using (toList∘fromList)
open import Data.List.Properties using (length-reverse)
open import Data.Nat.Properties using (+-identityʳ)
open import Data.Vec.Relation.Binary.Pointwise.Inductive as V using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst₂)

private variable
  A B : Set
  R : A → B → Set
  n : ℕ

toList-toVec : (vs : List A) (e : length vs ≡ n) → toList (toVec vs e) ≡ vs
toList-toVec vs refl = toList∘fromList vs

{- vectors whose lists are related are related -}
fromList-pw : ∀ {m n} (xs : Vec A m) (ys : Vec B n) → L.Pointwise R (toList xs) (toList ys)
  → V.Pointwise R xs ys
fromList-pw [] [] [] = []
fromList-pw (x ∷ xs) (y ∷ ys) (r ∷ rs) = r ∷ fromList-pw xs ys rs

toVec≈ : ∀ {vs ws} → L.Pointwise R vs ws → (e : length vs ≡ n) (e' : length ws ≡ n)
  → V.Pointwise R (toVec vs e) (toVec ws e')
toVec≈ {vs = vs} {ws} rs e e' =
  fromList-pw _ _ (subst₂ (L.Pointwise _) (sym (toList-toVec vs e)) (sym (toList-toVec ws e')) rs)

len-rev : (vs : List A) → length vs + 0 ≡ n → length (reverse vs) ≡ n
len-rev vs e = trans (length-reverse vs) (trans (sym (+-identityʳ _)) e)

toList-collected : (vs : List A) (e : length vs + 0 ≡ n) → toList (collected vs e) ≡ reverse vs
toList-collected vs e = toList-toVec (reverse vs) (len-rev vs e)

collected≈ : ∀ {vs ws} → L.Pointwise R vs ws → (e : length vs + 0 ≡ n) (e' : length ws + 0 ≡ n)
  → V.Pointwise R (collected vs e) (collected ws e')
collected≈ {vs = vs} {ws} rs e e' = toVec≈ (reverse⁺ rs) (len-rev vs e) (len-rev ws e')

{- two machines that both stop with the same observation or both step to
   related states (for project, where both decide the same equation) -}
data Lock {S₁ S₂ : Set} (R : S₁ → S₂ → Set) : Next S₁ → Next S₂ → Set where
  same-stop : ∀ {o} → Lock R (stop o) (stop o)
  same-next : ∀ {s₁ s₂} → R s₁ s₂ → Lock R (next s₁) (next s₂)

lock : ∀ {S₁ : Set} {L₂ : Machine} {R : S₁ → State L₂ → Set} {a s₂}
  → Lock R a (Machine.step L₂ s₂) → Answers L₂ R a s₂
lock {L₂ = L₂} {s₂ = s₂} l with Machine.step L₂ s₂ in eq
lock same-stop | stop o = stops eq
lock (same-next m) | next s = steps₁ eq m

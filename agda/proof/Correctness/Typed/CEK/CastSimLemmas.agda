{-

  Lemmas about lists and primitives for the CEK proof of cast insertion
  (CastSim.agda): copies of lemmas of the adequacy proofs
  (proof/Adequacy/Common.agda, proof/Adequacy/GraphErr/LogRel.agda), so
  that the pilot's CEK proof does not import adequacy.

-}

module proof.Correctness.Typed.CEK.CastSimLemmas where

open import Framework.Primitives using (Int; Nat; 𝔹; Unit; Void; Blame)
open import Framework.ListUtil using (has-length; proj)
open import Semantics.Observation

open import Data.Bool using (true; false)
open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_; length)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong)

has-length→length : ∀ {A : Set} n (xs : List A) → has-length n xs ≡ true → length xs ≡ n
has-length→length zero [] _ = refl
has-length→length (suc n) (x ∷ xs) h = cong suc (has-length→length n xs h)
has-length→length zero (x ∷ xs) ()
has-length→length (suc n) [] ()

length→has-length : ∀ {A : Set} n (xs : List A) → length xs ≡ n → has-length n xs ≡ true
length→has-length zero [] refl = refl
length→has-length (suc n) (x ∷ xs) refl = length→has-length n xs refl

proj-just-length : ∀ {A : Set} {n} (i : Fin n) (vs : List A) {v} → proj i vs ≡ just v → length vs ≡ n
proj-just-length {n = suc n} zero (v ∷ vs) eq with has-length n vs in h
proj-just-length {n = suc n} zero (v ∷ vs) refl | true = cong suc (has-length→length n vs h)
proj-just-length {n = suc n} zero (v ∷ vs) () | false
proj-just-length (suc i) (v ∷ vs) eq = cong suc (proj-just-length i vs eq)

δ?-nothing₁ : ∀ p o₁ o₂ → (∀ n → o₁ ≢ o-const Int n) → δ? p o₁ o₂ ≡ nothing
δ?-nothing₁ p (o-const Int n) o₂ f = ⊥-elim (f n refl)
δ?-nothing₁ p (o-const Nat k) o₂ f = refl
δ?-nothing₁ p (o-const 𝔹 k) o₂ f = refl
δ?-nothing₁ p (o-const Unit k) o₂ f = refl
δ?-nothing₁ p (o-const Void k) o₂ f = refl
δ?-nothing₁ p (o-const Blame k) o₂ f = refl
δ?-nothing₁ p o-fun o₂ f = refl
δ?-nothing₁ p (o-tuple os) o₂ f = refl
δ?-nothing₁ p (o-inl o) o₂ f = refl
δ?-nothing₁ p (o-inr o) o₂ f = refl
δ?-nothing₁ p o-error o₂ f = refl

δ?-nothing₂ : ∀ p o₁ o₂ → (∀ m → o₂ ≢ o-const Int m) → δ? p o₁ o₂ ≡ nothing
δ?-nothing₂ p (o-const Int n) (o-const Int m) f = ⊥-elim (f m refl)
δ?-nothing₂ p (o-const Int n) (o-const Nat k) f = refl
δ?-nothing₂ p (o-const Int n) (o-const 𝔹 k) f = refl
δ?-nothing₂ p (o-const Int n) (o-const Unit k) f = refl
δ?-nothing₂ p (o-const Int n) (o-const Void k) f = refl
δ?-nothing₂ p (o-const Int n) (o-const Blame k) f = refl
δ?-nothing₂ p (o-const Int n) o-fun f = refl
δ?-nothing₂ p (o-const Int n) (o-tuple os) f = refl
δ?-nothing₂ p (o-const Int n) (o-inl o) f = refl
δ?-nothing₂ p (o-const Int n) (o-inr o) f = refl
δ?-nothing₂ p (o-const Int n) o-error f = refl
δ?-nothing₂ p (o-const Nat k) o₂ f = refl
δ?-nothing₂ p (o-const 𝔹 k) o₂ f = refl
δ?-nothing₂ p (o-const Unit k) o₂ f = refl
δ?-nothing₂ p (o-const Void k) o₂ f = refl
δ?-nothing₂ p (o-const Blame k) o₂ f = refl
δ?-nothing₂ p o-fun o₂ f = refl
δ?-nothing₂ p (o-tuple os) o₂ f = refl
δ?-nothing₂ p (o-inl o) o₂ f = refl
δ?-nothing₂ p (o-inr o) o₂ f = refl
δ?-nothing₂ p o-error o₂ f = refl

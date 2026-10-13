{-

  Definitions shared by the soundness and adequacy proofs for ISWIM
  (see Adequacy/ISWIM.agda for the overview):

  * s ↠ t, runs of the ISWIM machine from any state (the generic Runs
    of proof/Framework/Runs.agda);
  * ShapeOf o d, when a denotational value d has the shape of an
    observation o: the constant itself, a function entry, an entry of
    the right component of a tuple of the right size, a left or right
    injection. A function is also observed through the entries ⦅ u , v ⦆
    of a pair, which is how closures are represented after delay
    (Adequacy/Clos5.agda); the ISWIM semantics never produces them.

-}

module proof.Adequacy.Common where

open import Framework.Primitives using (Base; base-rep; Int)
open import Language.Prim using (Prim; Out; δ)
open import proof.Framework.GraphModel.Domain
  using (Value; const; _↦_; ν; ω; ⦅_,_⦆; tup[_]_; left; right; ⟨⟩)
open import Semantics.Observation
open import proof.Framework.Runs using (module Runs)
open import proof.Framework.ListUtil using (has-length)
open import Semantics.CEK.ISWIM

open import Data.Bool using (true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin; zero; suc)
open import Data.Integer using (ℤ)
open import Data.Maybe using (just)
open import Data.List using (List; []; _∷_; length)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; Σ-syntax; _,_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

{- the runs of the ISWIM machine -}
open Runs step public

{- Shapes of observations -----------------------------------------------------}

ShapeOf : Obs → Value → Set
ShapeAt : ∀ {n} → Fin n → List Obs → Value → Set

ShapeOf (o-const B k) d = d ≡ const {B} k
ShapeOf o-fun ν = ⊤
ShapeOf o-fun (V ↦ w) = ⊤
ShapeOf o-fun ⦅ u , v ⦆ = ⊤
ShapeOf (o-tuple os) ⟨⟩ = os ≡ []
ShapeOf (o-tuple os) (tup[ i ] d) = ShapeAt i os d
ShapeOf (o-inl o) (left d) = ShapeOf o d
ShapeOf (o-inr o) (right d) = ShapeOf o d
ShapeOf _ _ = ⊥

ShapeAt {suc n} zero (o ∷ os) d = length os ≡ n × ShapeOf o d
ShapeAt (suc i) (o ∷ os) d = ShapeAt i os d
ShapeAt _ [] d = ⊥

shape-answer : ∀ {o d} → ShapeOf o d → Answer o
shape-answer {o-error} {const k} () refl
shape-answer {o-const B k} s ()
shape-answer {o-fun} s ()
shape-answer {o-tuple os} s ()
shape-answer {o-inl o} s ()
shape-answer {o-inr o} s ()
shape-answer {o-error} {V ↦ w} () refl
shape-answer {o-error} {ν} () refl
shape-answer {o-error} {ω} () refl
shape-answer {o-error} {⦅ u , v ⦆} () refl
shape-answer {o-error} {tup[ i ] d} () refl
shape-answer {o-error} {left d} () refl
shape-answer {o-error} {right d} () refl
shape-answer {o-error} {⟨⟩} () refl

{- the only observation of the shape of a constant is that constant -}
shape-const : ∀ {o B} {k : base-rep B} → ShapeOf o (const k) → o ≡ o-const B k
shape-const {o-const B k} refl = refl
shape-const {o-fun} ()
shape-const {o-tuple os} ()
shape-const {o-inl o} ()
shape-const {o-inr o} ()
shape-const {o-error} ()

{- a primitive is defined only on two integers -}
δ?-inv : ∀ p o₁ o₂ {r : Out} → δ? p o₁ o₂ ≡ just r
  → Σ[ n ∈ ℤ ] Σ[ m ∈ ℤ ] o₁ ≡ o-const Int n × o₂ ≡ o-const Int m × r ≡ δ p n m
δ?-inv p (o-const Int n) (o-const Int m) refl = n , m , refl , refl , refl

{- Lengths ----------------------------------------------------------------------}

has-length→length : ∀ {A : Set} n (xs : List A) → has-length n xs ≡ true → length xs ≡ n
has-length→length zero [] _ = refl
has-length→length (suc n) (x ∷ xs) h = cong suc (has-length→length n xs h)
has-length→length zero (x ∷ xs) ()
has-length→length (suc n) [] ()

length→has-length : ∀ {A : Set} n (xs : List A) → length xs ≡ n → has-length n xs ≡ true
length→has-length zero [] refl = refl
length→has-length (suc n) (x ∷ xs) refl = length→has-length n xs refl

length-obs-list : ∀ vs → length (obs-list vs) ≡ length vs
length-obs-list [] = refl
length-obs-list (v ∷ vs) = cong suc (length-obs-list vs)

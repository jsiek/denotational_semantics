{-

  List operations shared by the machines: looking up a variable in an
  environment, and projecting from a tuple of a given size.

-}

module Compiler.Operational.Machine.Common where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_; length)
open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe.Relation.Binary.Pointwise as M
open import Data.Nat using (ℕ; zero; suc; _<_; s≤s; z≤n)
open import Data.Product using (Σ-syntax; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

private variable
  A B : Set

{- the x-th element, if there is one -}
_‼_ : List A → ℕ → Maybe A
[] ‼ x = nothing
(v ∷ vs) ‼ zero = just v
(v ∷ vs) ‼ suc x = vs ‼ x

‼-< : ∀ (vs : List A) x → x < length vs → Σ[ v ∈ A ] vs ‼ x ≡ just v
‼-< (v ∷ vs) zero _ = v , refl
‼-< (v ∷ vs) (suc x) (s≤s x<) = ‼-< vs x x<

has-length : ℕ → List A → Bool
has-length zero [] = true
has-length (suc n) (_ ∷ vs) = has-length n vs
has-length _ _ = false

{- component i of a tuple, if the tuple has n components -}
proj : ∀ {n} → Fin n → List A → Maybe A
proj {n = suc n} zero (v ∷ vs) = if has-length n vs then just v else nothing
proj (suc i) (v ∷ vs) = proj i vs
proj _ [] = nothing

module _ {R : A → B → Set} where

  has-length-pw : ∀ n {vs ws} → Pointwise R vs ws → has-length n vs ≡ has-length n ws
  has-length-pw zero [] = refl
  has-length-pw zero (_ ∷ _) = refl
  has-length-pw (suc n) [] = refl
  has-length-pw (suc n) (_ ∷ rs) = has-length-pw n rs

  proj-pw : ∀ {n} (i : Fin n) {vs ws} → Pointwise R vs ws → M.Pointwise R (proj i vs) (proj i ws)
  proj-pw zero [] = M.nothing
  proj-pw (suc i) [] = M.nothing
  proj-pw (suc i) (r ∷ rs) = proj-pw i rs
  proj-pw {n = suc n} zero {_ ∷ vs} {_ ∷ ws} (r ∷ rs) rewrite has-length-pw n rs
    with has-length n ws
  ... | true = M.just r
  ... | false = M.nothing

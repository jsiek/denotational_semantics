{-

  Relations between the values of two typed interpreters
  (Semantics/Interp/Typed/Values.agda, with codes C₁ and C₂), for the
  proofs of the passes between typed languages: values are related
  (_≈_) when they have the same shape, codes are related by Code, and
  a closure of code c and environment vs is related to one of code c'
  and environment ws when vs is related pointwise to some vs' and Clo
  relates c, vs', c' and ws (Same Code: c and c' are related by Code
  and ws is vs'; optimize also drops some of vs'). Related values are
  observed alike, and the operations on them give related results.

-}

open import Data.Nat using (ℕ)

module proof.Semantics.Interp.Typed.Rel {C₁ C₂ : ℕ → Set} where

open import Framework.Primitives using (base-rep)
open import Language.Prim using (sub; eq)
open import Language.Typed.Type renaming (_≟_ to _≟F_)
open import Semantics.Observation using (o-tuple; o-inl; o-inr)
open import proof.Semantics.Interp.Clock using (Result; RelResult; ret; error)
import Semantics.Interp.Typed.Values as V
private
  module S = V C₁
  module T = V C₂

open import Data.Bool using (true; false)
open import Data.Integer using (_≟_)
open import Data.Fin using (Fin)
open import Data.Vec using (Vec; []; _∷_)
open import Data.List using (List)
import Data.List as List
open import Data.Vec.Relation.Binary.Pointwise.Inductive using (Pointwise; []; _∷_; lookup) public
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
open import Relation.Nullary using (yes; no; does)

{- a closure relation that relates the codes and keeps the environment -}
data Same (Code : ∀ {n} → C₁ n → C₂ n → Set)
  : ∀ {n m} → C₁ n → Vec (T.Val Any) n → C₂ m → Vec (T.Val Any) m → Set where
  same : ∀ {n} {c : C₁ n} {c' vs} → Code c c' → Same Code c vs c' vs

module Rel (Code : ∀ {n} → C₁ n → C₂ n → Set)
           (Clo : ∀ {n m} → C₁ n → Vec (T.Val Any) n → C₂ m → Vec (T.Val Any) m → Set) where

  infix 4 _≈_
  data _≈_ : ∀ {A} → S.Val A → T.Val A → Set where
    code≈ : ∀ {n} {c : C₁ n} {c'} → Code c c' → S.code c ≈ T.code c'
    pack≈ : ∀ {n m} {c : C₁ n} {c' : C₂ m} {vs vs' ws} → Pointwise _≈_ vs vs' → Clo c vs' c' ws
      → S.pack (S.code c) (S.tup vs) ≈ T.pack (T.code c') (T.tup ws)
    const≈ : ∀ {B} {k : base-rep B} → S.const k ≈ T.const k
    tup≈ : ∀ {n} {vs : Vec _ n} {ws} → Pointwise _≈_ vs ws → S.tup vs ≈ T.tup ws
    inl≈ : ∀ {v w} → v ≈ w → S.inl v ≈ T.inl w
    inr≈ : ∀ {v w} → v ≈ w → S.inr v ≈ T.inr w
    dyn≈ : ∀ {G v w} → v ≈ w → S.dyn G v ≈ T.dyn G w

  obs≈ : ∀ {A} {v : S.Val A} {w} → v ≈ w → S.obs v ≡ T.obs w
  obs≈-vec : ∀ {n} {vs : Vec _ n} {ws} → Pointwise _≈_ vs ws → S.obs-vec vs ≡ T.obs-vec ws
  obs≈ (code≈ _) = refl
  obs≈ (pack≈ _ _) = refl
  obs≈ const≈ = refl
  obs≈ (tup≈ rs) = cong o-tuple (obs≈-vec rs)
  obs≈ (inl≈ r) = cong o-inl (obs≈ r)
  obs≈ (inr≈ r) = cong o-inr (obs≈ r)
  obs≈ (dyn≈ r) = obs≈ r
  obs≈-vec [] = refl
  obs≈-vec (r ∷ rs) = cong₂ List._∷_ (obs≈ r) (obs≈-vec rs)

  δ≈ : ∀ p {v₁ v₂ w₁ w₂} → v₁ ≈ w₁ → v₂ ≈ w₂ → S.δ p v₁ v₂ ≈ T.δ p w₁ w₂
  δ≈ sub const≈ const≈ = const≈
  δ≈ eq (const≈ {k = n}) (const≈ {k = m}) with does (n ≟ m)
  ... | true = inl≈ (dyn≈ (tup≈ []))
  ... | false = inr≈ (dyn≈ (tup≈ []))

  nth≈ : ∀ {n} (i : Fin n) {v w} → v ≈ w → S.nth i v ≈ T.nth i w
  nth≈ i (tup≈ rs) = lookup rs i

  project≈ : ∀ t {v w} → v ≈ w → RelResult _≈_ (S.project? t v) (T.project? t w)
  project≈ t (dyn≈ {G} r) with G ≟F flat t
  ... | yes refl = ret r
  ... | no _ = error

  either≈ : ∀ {B C : Set} {R : B → C → Set} {u u'} {f₁ f₂ : S.Val Any → Result B} {g₁ g₂ : T.Val Any → Result C}
    → u ≈ u' → (∀ {v w} → v ≈ w → RelResult R (f₁ v) (g₁ w)) → (∀ {v w} → v ≈ w → RelResult R (f₂ v) (g₂ w))
    → RelResult R (S.either u f₁ f₂) (T.either u' g₁ g₂)
  either≈ (inl≈ r) h₁ h₂ = h₁ r
  either≈ (inr≈ r) h₁ h₂ = h₂ r

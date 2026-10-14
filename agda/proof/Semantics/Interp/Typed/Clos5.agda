{-

  Lemmas about the interpreter of Clos5ᵀ (Semantics/Interp/Typed/Clos5.agda)
  on the embedding of Monᵀ (Language/Typed/Mon.agda), shared by the
  proofs of rco and lift locals: an embedded atom evaluates, without
  calling anything, to its value as Impᵀ reads it
  (Semantics/Interp/Typed/Imp.agda), and a definition of a mapped table
  is the mapped definition.

-}

module proof.Semantics.Interp.Typed.Clos5 where

open import Language.Typed.Type
open import Language.Typed.Mon using (Atm; var; lit; ref; ⌜_⌝ᵃ; ⌜_⌝ᵛ)
import Language.Typed.Clos5 as C
open import proof.Semantics.Interp.Clock
open import Semantics.Interp.Typed.Clos5 using (module Vals; eval; evals)
open import Framework.Lookup using (_!_)
open import Semantics.Interp.Typed.Imp using (atom)

open import Data.List using (List)
open import Data.List.Relation.Unary.All using (All; []; _∷_) renaming (map to All-map)
open import Data.Nat using (ℕ)
open import Data.Vec using (Vec; []; _∷_; map)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

def-map : ∀ {P Q : ℕ → Set} {Σ n} (g : ∀ {m} → P m → Q m) (ds : All P Σ) (x : Σ ∋ n) → All-map g ds ! x ≡ g (ds ! x)
def-map g (d ∷ ds) Z = refl
def-map g (d ∷ ds) (S x) = def-map g ds x

module _ {Σ : List ℕ} {ds : All (C.Code Σ) Σ} {ck : ℕ} where
  open Vals Σ

  atm-bind : ∀ {Γ A B} {φ : Env Γ} (a : Atm Σ Γ A) {f : Val A → Result B}
    → (eval ds ck φ ⌜ a ⌝ᵃ >>= f) ≡ f (atom φ a)
  atm-bind (var x) = refl
  atm-bind (lit B c) = refl
  atm-bind (ref g) = refl

  eval-atom : ∀ {Γ A} {φ : Env Γ} (a : Atm Σ Γ A) → eval ds ck φ ⌜ a ⌝ᵃ ≡ ret (atom φ a)
  eval-atom a = trans (sym (bind-ret _)) (atm-bind a)

  atoms-bind : ∀ {Γ n B} {φ : Env Γ} (as : Vec (Atm Σ Γ Any) n) {f : Vec (Val Any) n → Result B}
    → (evals ds ck φ ⌜ as ⌝ᵛ >>= f) ≡ f (map (atom φ) as)
  atoms-bind [] = refl
  atoms-bind {φ = φ} (a ∷ as) = trans (bind-assoc (eval ds ck φ ⌜ a ⌝ᵃ)) (trans (atm-bind a) (trans (bind-assoc (evals ds ck φ ⌜ as ⌝ᵛ)) (atoms-bind as)))

either-cong : ∀ {Σ} {B : Set} (u : Vals.Val Σ ⟪ sum ⟫) {f₁ f₂ g₁ g₂ : Vals.Val Σ Any → B}
  → (∀ v → f₁ v ≡ g₁ v) → (∀ v → f₂ v ≡ g₂ v) → Vals.either Σ u f₁ f₂ ≡ Vals.either Σ u g₁ g₂
either-cong (Vals.inl v) h₁ h₂ = h₁ v
either-cong (Vals.inr v) h₁ h₂ = h₂ v

{-

  Lemmas about the interpreter of GlobalFunμ (Mu/Semantics/ClockedInterpreters/GlobalFun.agda)
  on the embedding of Monμ (Mu/Language/Mon.agda), shared by the proofs
  of rco and lift locals, as proof/Semantics/Interp/Typed/Clos5.agda: an
  embedded atom evaluates, without calling anything, to its value as
  Impμ reads it (Mu/Semantics/ClockedInterpreters/Imp.agda), and a definition of a
  mapped table is the mapped definition.

-}

module Mu.proof.Semantics.ClockedInterpreters.GlobalFun where

open import Mu.Language.Type
open import Mu.Language.Mon using (DSig; Atm; var; lit; ref; ⌜_⌝ᵃ; ⌜_⌝ᵛ)
import Mu.Language.GlobalFun as C
open import Mu.Framework.AllUtil using (All; []; _∷_; lookup; map)
open import proof.Semantics.Interp.Clock
open import Mu.Semantics.ClockedInterpreters.GlobalFun using (module Vals; eval; evals)
open import Mu.Semantics.ClockedInterpreters.Imp using (atom)

open import Data.List using (List)
open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

def-map : ∀ {X : Set} {P Q : X → Set} {Σ s} (g : ∀ {s} → P s → Q s) (ds : All P Σ) (x : Σ ∋ s) → lookup (map g ds) x ≡ g (lookup ds x)
def-map g (d ∷ ds) Z = refl
def-map g (d ∷ ds) (S x) = def-map g ds x

module _ {Σ : List DSig} {ds : All (C.Code Σ) Σ} {ck : ℕ} where
  open Vals Σ

  atm-bind : ∀ {Γ A B} {φ : Env Γ} (a : Atm Σ Γ A) {f : Val A → Result B}
    → (eval ds ck φ ⌜ a ⌝ᵃ >>= f) ≡ f (atom φ a)
  atm-bind (var x) = refl
  atm-bind (lit B c) = refl
  atm-bind (ref g) = refl

  eval-atom : ∀ {Γ A} {φ : Env Γ} (a : Atm Σ Γ A) → eval ds ck φ ⌜ a ⌝ᵃ ≡ ret (atom φ a)
  eval-atom a = trans (sym (bind-ret _)) (atm-bind a)

  atoms-bind : ∀ {Γ Δ B} {φ : Env Γ} (as : All (Atm Σ Γ) Δ) {f : All Val Δ → Result B}
    → (evals ds ck φ ⌜ as ⌝ᵛ >>= f) ≡ f (map (atom φ) as)
  atoms-bind [] = refl
  atoms-bind {φ = φ} (a ∷ as) = trans (bind-assoc (eval ds ck φ ⌜ a ⌝ᵃ)) (trans (atm-bind a) (trans (bind-assoc (evals ds ck φ ⌜ as ⌝ᵛ)) (atoms-bind as)))

either-cong : ∀ {Σ A B} {X : Set} (u : Vals.Val Σ (A ⊹ B)) {f₁ g₁ : Vals.Val Σ A → X} {f₂ g₂ : Vals.Val Σ B → X}
  → (∀ v → f₁ v ≡ g₁ v) → (∀ v → f₂ v ≡ g₂ v) → Vals.either Σ u f₁ f₂ ≡ Vals.either Σ u g₁ g₂
either-cong (Vals.inl v) h₁ h₂ = h₁ v
either-cong (Vals.inr v) h₁ h₂ = h₂ v

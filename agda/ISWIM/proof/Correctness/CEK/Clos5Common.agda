{-

  Lemmas about the Clos5ᵀ machine (Semantics/CEK/Typed/Clos5.agda) on
  the embedding of Monᵀ atoms (Language/Typed/Mon.agda), shared by the
  simulation proofs of remove complex operands and lift locals: an atom
  evaluates to its value (atom, Semantics/CEK/Typed/Imp.agda) in one
  step, and a tuple of atoms to the tuple of their values.

-}

module proof.Correctness.CEK.Clos5Common where

open import Language.Typed.Type
open import Language.Typed.Clos5 using (Program; program; Code; Tm)
open import Language.Typed.Mon using (Atm; var; lit; ref; ⌜_⌝ᵃ; ⌜_⌝ᵛ)
open import Semantics.CEK.Typed.Clos5
open import Semantics.CEK.Typed.Imp using (atom)
open import proof.Semantics.CEK.Smallstep using (next; Star; ε; _◅_)
open import Framework.VecUtil using (_<><_)

open import Data.List using (List; [])
open import Data.List.Relation.Unary.All using (All)
open import Data.Nat using (ℕ)
open import Data.Vec using (Vec; []; _∷_; map)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

module _ {Σ : List ℕ} (ds : All (Code Σ) Σ) (M₀ : Tm Σ [] Any) where

  private L = sem (program ds M₀)

  atm-step : ∀ {Δ A} {φ : Env Σ Δ} {κ} (a : Atm Σ Δ A) → step ds (eval ⌜ a ⌝ᵃ φ κ) ≡ next (ret (atom φ a) κ)
  atm-step (var x) = refl
  atm-step (lit B c) = refl
  atm-step (ref f) = refl

  tuple-atoms : ∀ {Δ m j} {φ : Env Σ Δ} {κ} (vs : Vec _ m) (as : Vec (Atm Σ Δ Any) j)
    → Star L (tuple-next vs ⌜ as ⌝ᵛ φ κ) (ret (tup (vs <>< map (atom φ) as)) κ)
  tuple-atoms vs [] = ε
  tuple-atoms {φ = φ} vs (a ∷ as) = atm-step a ◅ (refl ◅ tuple-atoms (atom φ a ∷ vs) as)

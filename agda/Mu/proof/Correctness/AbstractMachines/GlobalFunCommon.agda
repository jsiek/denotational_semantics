{-

  Lemmas about the GlobalFunμ machine (Mu/Semantics/AbstractMachines/GlobalFun.agda) on the
  embedding of Monμ atoms (Mu/Language/Mon.agda), shared by the
  simulation proofs of remove complex operands and lift locals, as
  proof/Correctness/CEK/Clos5Common.agda: an atom evaluates to its value
  (atom, Mu/Semantics/AbstractMachines/Imp.agda) in one step, and the rest of a tuple
  of atoms to the values so far followed by theirs. Since the machine
  collects a tuple's values newest first in front of the types still to
  come (_<><_), this needs no equation about lengths.

-}

module Mu.proof.Correctness.AbstractMachines.GlobalFunCommon where

open import Mu.Language.Type
open import Mu.Language.GlobalFun using (DSig; Program; program; Code; Tm)
open import Mu.Language.Mon using (Atm; var; lit; ref; ⌜_⌝ᵃ; ⌜_⌝ᵛ)
open import Mu.Framework.AllUtil using (All; []; _∷_; map; _<><_; _<><ᵃ_)
open import Mu.Semantics.AbstractMachines.GlobalFun
open import Mu.Semantics.AbstractMachines.Imp using (atom)
open import proof.Semantics.CEK.Smallstep using (next; Star; ε; _◅_)

open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

module _ {Σ : List DSig} (ds : All (Code Σ) Σ) {T} (M₀ : Tm Σ [] T) where

  private L = sem (program ds M₀)

  atm-step : ∀ {Δ A} {φ : Env Σ Δ} {κ} (a : Atm Σ Δ A) → step ds (eval ⌜ a ⌝ᵃ φ κ) ≡ next (ret (atom φ a) κ)
  atm-step (var x) = refl
  atm-step (lit B c) = refl
  atm-step (ref f) = refl

  tuple-atoms : ∀ {Δ Δ' Δs} {φ : Env Σ Δ} {κ : Cont Σ (tup (Δ' <>< Δs))} (vs : All (Val Σ) Δ') (as : All (Atm Σ Δ) Δs)
    → Star L (tuple-next vs ⌜ as ⌝ᵛ φ κ) (ret (tup (vs <><ᵃ map (atom φ) as)) κ)
  tuple-atoms vs [] = ε
  tuple-atoms {φ = φ} vs (a ∷ as) = atm-step a ◅ (refl ◅ tuple-atoms (atom φ a ∷ vs) as)

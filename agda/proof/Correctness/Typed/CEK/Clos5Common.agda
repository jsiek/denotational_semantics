{-

  Lemmas about the Clos5ᵀ machine (Semantics/CEK/Typed/Clos5.agda) on
  the embedding of Monᵀ atoms (Language/Typed/Mon.agda), shared by the
  simulation proofs of remove complex operands and lift locals: an atom
  evaluates to its value (atom, Semantics/CEK/Typed/Imp.agda) in one
  step, and a tuple of atoms to the tuple of their values.

-}

module proof.Correctness.Typed.CEK.Clos5Common where

open import Language.Typed.Type
open import Language.Typed.Clos5 using (Program; program; Code; Tm)
open import Language.Typed.Mon using (Atm; var; lit; ref; ⌜_⌝ᵃ; ⌜_⌝ᵛ)
open import Semantics.CEK.Typed.Clos5
open import Semantics.CEK.Typed.Imp using (atom)
open import proof.Semantics.CEK.Smallstep using (next; Star; ε; _◅_)
open import proof.Correctness.Typed.CEK.Common using (toList-collected)
open import Framework.VecUtil using (more; collected)

open import Data.List using (List; []; _∷_; _++_; _∷ʳ_; length; reverse)
open import Data.List.Properties using (unfold-reverse; ++-assoc; ++-identityʳ)
open import Data.List.Relation.Unary.All using (All)
open import Data.Nat using (ℕ; _+_)
open import Data.Product using (Σ-syntax; _,_)
open import Data.Vec using (Vec; []; _∷_; map; toList)
open import Data.Vec.Properties using (toList-injective; cast-is-id)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

{- the values of atoms, pushed on the values so far (newest first) -}
push : ∀ {Σ Δ j} → Env Σ Δ → List (Val Σ Any) → Vec (Atm Σ Δ Any) j → List (Val Σ Any)
push φ vs [] = vs
push φ vs (a ∷ as) = push φ (atom φ a ∷ vs) as

rev-push : ∀ {Σ Δ j} (φ : Env Σ Δ) vs (as : Vec (Atm Σ Δ Any) j)
  → reverse (push φ vs as) ≡ reverse vs ++ toList (map (atom φ) as)
rev-push φ vs [] = sym (++-identityʳ _)
rev-push φ vs (a ∷ as) =
  trans (rev-push φ (atom φ a ∷ vs) as)
    (trans (cong (_++ _) (unfold-reverse (atom φ a) vs)) (++-assoc (reverse vs) _ _))

{- the tuple of the values of atoms -}
collected-push : ∀ {Σ Δ n} (φ : Env Σ Δ) (as : Vec (Atm Σ Δ Any) n) (e : length (push φ [] as) + 0 ≡ n)
  → collected (push φ [] as) e ≡ map (atom φ) as
collected-push φ as e =
  trans (sym (cast-is-id refl _)) (toList-injective refl _ _ (trans (toList-collected (push φ [] as) e) (rev-push φ [] as)))

module _ {Σ : List ℕ} (ds : All (Code Σ) Σ) (M₀ : Tm Σ [] Any) where

  private L = sem (program ds M₀)

  atm-step : ∀ {Δ A} {φ : Env Σ Δ} {κ} (a : Atm Σ Δ A) → step ds (eval ⌜ a ⌝ᵃ φ κ) ≡ next (ret (atom φ a) κ)
  atm-step (var x) = refl
  atm-step (lit B c) = refl
  atm-step (ref f) = refl

  tuple-atoms : ∀ {Δ j n} {φ : Env Σ Δ} {κ} vs (as : Vec (Atm Σ Δ Any) j) (e : length vs + j ≡ n)
    → Σ[ e' ∈ length (push φ vs as) + 0 ≡ n ] Star L (tuple-next vs ⌜ as ⌝ᵛ φ e κ) (ret (tup (collected (push φ vs as) e')) κ)
  tuple-atoms vs [] e = e , ε
  tuple-atoms {φ = φ} vs (a ∷ as) e with tuple-atoms (atom φ a ∷ vs) as (more {v = atom φ a} vs e)
  ... | e' , σ = e' , (atm-step a ◅ (refl ◅ σ))

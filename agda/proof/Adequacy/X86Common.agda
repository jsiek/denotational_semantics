{-

  Definitions shared by the soundness and adequacy proofs for the X86ᵀ
  machine (see proof/Adequacy/X86.agda): runs of the machine of the
  definitions ds from any state, and the state that a call of code c
  starts in (start), on any stack, and how the open closure is related
  to its slot (OpR).

-}

open import Data.List using (List)
open import Data.List.Relation.Unary.All using (All)
open import Data.Nat using (ℕ)
open import Language.Typed.X86

module proof.Adequacy.X86Common {Σ : List ℕ} (ds : All (λ m → Body Σ (called m)) Σ) where

open import Language.Typed.Type hiding (_≟_; _∋_)
open import Semantics.CEK.Typed.X86
open import proof.Semantics.CEK.Smallstep using (next)
open import Framework.Lookup using (_!_)
open import Framework.Membership using (_∋_)
open import proof.Framework.Runs using (module Runs)

open import Data.List.Relation.Unary.All using ([])
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open Runs (step ds) public

{- running code c on the environment e and the argument a -}
start : ∀ {η} → Val Σ (code η) → Val Σ ⟪ tup η ⟫ → Val Σ Any → Stack Σ → State Σ
start {η} (code f) e a σ = run (Body.start (ds ! f)) (Body.blocks (ds ! f)) σ η ⟨ rv tt e a , [] , tt , tt ⟩

enter-start : ∀ {η} (c : Val Σ (code η)) {e a σ} → enter ds c e a σ ≡ next (start c e a σ)
enter-start (code f) = refl

{- the open closure x has the code and environment that the machine keeps -}
OpR : ∀ {Δ η} (O : Maybe (Δ ∋ ⟪ fun ⟫)) → Frame Σ Δ → Opened Σ η O → Set
OpR (just x) φ o = pack (proj₁ o) (proj₂ o) ≡ φ ! x
OpR nothing φ o = ⊤

pack-eta : (v : Val Σ ⟪ fun ⟫) → pack (code-of v) (env-of v) ≡ v
pack-eta (pack c e) = refl

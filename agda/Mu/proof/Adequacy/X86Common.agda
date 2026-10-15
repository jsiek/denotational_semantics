{-

  Definitions shared by the soundness and adequacy proofs for the X86μ
  machine (see Mu/proof/Adequacy/X86.agda), as for X86ᵀ
  (proof/Adequacy/X86Common.agda): runs of the machine of the
  definitions ds from any state, the state that a call of code c starts
  in (start), on any stack of its result type, and how the open
  closure is related to its slot (OpR): the machine keeps the types η
  of its environment and the environment, which are those of the
  closure in the slot.

-}

open import Data.List using (List)
open import Mu.Language.X86
open import Mu.Framework.AllUtil using (All)

module Mu.proof.Adequacy.X86Common {Σ : List DSig} (ds : All (λ s → Body Σ (DSig.cod s) (called s)) Σ) where

open import Mu.Language.Type
open import Mu.Semantics.CEK.X86
open import proof.Semantics.CEK.Smallstep using (next)
open import proof.Framework.Runs using (module Runs)
open import Mu.Framework.AllUtil using (lookup; [])

open import Data.Maybe using (Maybe; just; nothing)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open Runs (step ds) public

{- running code c on the environment e and the argument a -}
start : ∀ {η A B} → Val Σ (code η A B) → Val Σ (tup η) → Val Σ A → Stack Σ B → State Σ
start {η} (code f) e a σ =
  run (Body.start (lookup ds f)) (Body.blocks (lookup ds f)) σ η ⟨ rv tt e a , [] , tt , tt ⟩

enter-start : ∀ {η A B} (c : Val Σ (code η A B)) {e a σ} → enter ds c e a σ ≡ next (start c e a σ)
enter-start (code f) = refl

{- the open closure is that of its slot: η and the environment are its own -}
data OpR {Δ} (φ : Frame Σ Δ) : (O : Maybe (Open Δ)) (η : Ctx) → Opened Σ η O → Set where
  none : ∀ {η} → OpR φ nothing η tt
  agree : ∀ {A B} {x : Δ ∋ A ⇒ B} → OpR φ (just (opened x)) (size (lookup φ x)) (env-of (lookup φ x))

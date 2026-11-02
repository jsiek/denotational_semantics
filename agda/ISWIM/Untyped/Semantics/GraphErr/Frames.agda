module Untyped.Semantics.GraphErr.Frames where
{-

 Tables of global definitions and stores of frame slots in the graph
 model with errors, which the semantics of X86 (Untyped/Semantics/GraphErr/X86.agda)
 uses, and which the semantics of the preserved untyped Imp and CFG
 (agda/Untyped/) share with it; as in Untyped/Semantics/Graph/Frames.agda, with
 the errors of the machines: reading a slot beyond the frame errors
 (init, {ω}); assigning one errs once the value assigned has been
 computed (frameᵐ: ω if the value is anything, ∅ if it diverges). A
 reference to no definition is code whose call errs (errcode).

-}

open import Framework.Primitives using (Int)
open import Framework.GraphModel.SetsAsPredicates
open import Framework.GraphModel.Domain
open import Framework.GraphModel.OpsBase using (ℬ)
open import Framework.GraphModel.ErrorMonad

open import Data.Integer using (+_)
open import Data.Nat using (ℕ; _≟_; _<?_)
open import Data.List using (List; []; _∷_; length)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Relation.Nullary using (yes; no)

{- the meanings of the global definitions, by their references -}
Table : Set₁
Table = ℕ → 𝒫 Value

Store : Set₁
Store = ℕ → 𝒫 Value

init : 𝒫 Value
init = ⌈ ω ⌉

{- slot x of a frame of n slots -}
read : ℕ → Store → ℕ → 𝒫 Value
read n σ x with x <? n
... | yes _ = σ x
... | no _ = init

_[_↦_] : Store → ℕ → 𝒫 Value → Store
(σ [ x ↦ D ]) y with y ≟ x
... | yes _ = D
... | no _ = σ y

{- E, if slot x is within a frame of n slots; otherwise an error, once
   the value D to assign has been computed -}
frameᵐ : ℕ → ℕ → 𝒫 Value → 𝒫 Value → 𝒫 Value
frameᵐ n x D E with x <? n
... | yes _ = E
... | no _ = D ≫= λ _ → ⌈ ω ⌉

{- the slots of a fresh frame -}
zeros : Store
zeros _ = ℬ Int (+ 0) ptt

{- the table of a list of definitions, newest first, given the code of a
   definition -}
tables : ∀ {B : Set} → (Table → B → 𝒫 Value) → List B → Table
tables code [] k = errcode
tables code (b ∷ bs) k with k ≟ length bs
... | yes _ = code (tables code bs) b
... | no _ = tables code bs k

module Untyped.Semantics.Graph.Frames where
{-

 Tables of global definitions and stores of frame slots in the graph
 model, which the semantics of X86 (Untyped/Semantics/Graph/X86.agda) uses, and
 which the semantics of the preserved untyped Clos5, Imp and CFG
 (agda/Untyped/) share with it.

 A table T gives the meaning of each global definition, by its
 reference. A store σ gives each slot of the frame a meaning, a set of
 values. Reading a slot beyond a frame of n slots gives init, the error
 value; assigning one errors, so the construct means ∅ (checked). The
 slots of a fresh frame hold 0 (zeros).

-}

open import Framework.GraphModel.SetsAsPredicates
open import Framework.GraphModel.Domain
open import Framework.GraphModel.OpsBase using (ℬ)
open import Framework.Primitives using (Int)

open import Data.Integer using (+_)
open import Data.Nat using (ℕ; _≟_; _<?_)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Relation.Nullary using (yes; no)

{- the meanings of the global definitions, by their references -}
Table : Set₁
Table = ℕ → 𝒫 Value

init : 𝒫 Value
init = ⌈ ω ⌉

Store : Set₁
Store = ℕ → 𝒫 Value

{- slot x of a frame of n slots -}
read : ℕ → Store → ℕ → 𝒫 Value
read n σ x with x <? n
... | yes _ = σ x
... | no _ = init

_[_↦_] : Store → ℕ → 𝒫 Value → Store
(σ [ x ↦ D ]) y with y ≟ x
... | yes _ = D
... | no _ = σ y

{- D, if slot x is within a frame of n slots -}
checked : ℕ → ℕ → 𝒫 Value → 𝒫 Value
checked n x D with x <? n
... | yes _ = D
... | no _ = ∅

{- the slots of a fresh frame -}
zeros : Store
zeros _ = ℬ Int (+ 0) ptt

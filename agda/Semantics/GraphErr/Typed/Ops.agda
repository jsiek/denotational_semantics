{-

  The operators of the typed languages (Language/Typed/) in the graph
  model with errors: the graph model's operators (Framework/GraphModel/Ops)
  under the binds of the error monad (Framework/GraphModel/ErrorMonad),
  in the machines' order, with no check of the kind of an operand: a
  typed operand has the kind its operator needs. An operand may still
  hold ω, from a failed project, which the binds propagate.

  * A value of type Any is a value of the graph model, tagged by its kind
    (kind, in ErrorMonad), so inject is the identity, and project G
    checks that kind: it is the only operator that adds ω.
  * let x = M in N is the bind of N.

-}

module Semantics.GraphErr.Typed.Ops where

open import Framework.Primitives using (Int)
open import Framework.GraphModel.SetsAsPredicates
open import Framework.GraphModel.DOpSig
open import Framework.GraphModel.Domain
open import Framework.GraphModel.Ops using (⋆; proj; 𝒞)
open import Framework.GraphModel.ErrorMonad
open import Semantics.Graph.Prim using (primD)
open import Language.Prim using (Prim)
open import Language.Typed.Type using (Flat; base; tup; sum; fun)

open import Data.Fin using (Fin)
open import Data.Product using () renaming (_,_ to ⟨_,_⟩)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)

{- the kind of the values of a flat type -}
kindᶠ : Flat → Kind
kindᶠ (base B) = base B
kindᶠ (tup n) = tup n
kindᶠ sum = inj
kindᶠ fun = fun

projectᵗ : Flat → 𝒫 Value → 𝒫 Value
projectᵗ G D = D ≫= λ X → checked (kindᶠ G) X X

appᵗ : 𝒫 Value → 𝒫 Value → 𝒫 Value
appᵗ D E = D ≫= λ F → E ≫= λ X → ⋆ ⟨ F , ⟨ X , ptt ⟩ ⟩

getᵗ : ∀ {n} → Fin n → 𝒫 Value → 𝒫 Value
getᵗ i D = D ≫= λ X → proj i ⟨ X , ptt ⟩

caseᵗ : 𝒫 Value → (𝒫 Value → 𝒫 Value) → (𝒫 Value → 𝒫 Value) → 𝒫 Value
caseᵗ D F G = D ≫= λ X → 𝒞 ⟨ X ⇂ ValPayload , ⟨ F , ⟨ G , ptt ⟩ ⟩ ⟩

primᵗ : Prim → 𝒫 Value → 𝒫 Value → 𝒫 Value
primᵗ p D E = D ≫= λ X → E ≫= λ Y → primD p ⟨ X , ⟨ Y , ptt ⟩ ⟩

{- a variable not in scope: never, in a typed term -}
init : 𝒫 Value
init = ⌈ ω ⌉

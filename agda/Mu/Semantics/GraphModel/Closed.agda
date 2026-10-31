{-

  The environment of a closed FPC program in the graph model.

  Environments are total (Env Value = Var → 𝒫 Value) and nonempty-env
  asks every position to be nonempty, so the positions a closed program
  never reads still need a nonempty, self-consistent set. In the typed
  development that filler is {⟨⟩}; the dynamically typed variant's ρ₀
  (proof/Framework/GraphModel/Domain.agda) uses {ω}, its error element.

-}

module Mu.Semantics.GraphModel.Closed where

open import Framework.GraphModel.Prelude

{- the environment of a closed program: every variable denotes {⟨⟩} -}
ρ₀ : Env Value
ρ₀ = λ _ → ⌈ ⟨⟩ ⌉

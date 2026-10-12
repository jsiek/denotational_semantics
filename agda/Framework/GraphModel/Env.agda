open import Framework.GraphModel.SetsAsPredicates using (𝒫)
open import Framework.abt.Var

module Framework.GraphModel.Env where

{- ================ Set-valued environments ================================ -}

Env : (A : Set) → Set₁
Env A = Var → 𝒫 A

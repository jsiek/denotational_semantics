{-

  The Scott-domain meaning of this compiler's primitive operations
  (Language.Prim): the value of a primitive's result, and primD p d e,
  which applies p to the integers d and e, and is ⊥ unless both are
  integers. The rest of the domain and its operators are language
  independent (Framework/Scott/).

-}

open import MLTT.Spartan hiding (inl; inr; cases)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons

open import Framework.Primitives using (Int)
open import Language.Prim using (Prim; Out; int; bool; δ)
open import Data.Bool using (true; false)
open import Data.Integer using (ℤ)

module Semantics.Scott.Prim
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : propext 𝓤₀)
       where

open import Framework.Scott.Base pt fe
open import Framework.Scott.Functor pt fe pe
open import Framework.Scott.Domain pt fe pe
open import Framework.Scott.Ops pt fe pe

{- the empty tuple -}
unit : ⟨ 𝔻 ⟩
unit = tuple 0 · (λ ())

{- the value of the result of a primitive: eq returns left ⟨⟩ for true
   and right ⟨⟩ for false -}
out : Out → ⟨ 𝔻 ⟩
out (int n) = const Int n
out (bool true) = inl · unit
out (bool false) = inr · unit

primD : Prim → DCPO[ 𝔻 , 𝔻 ⟹₁ 𝔻 ]
primD p = case (𝔻 ⟹𝔻) h₁
 where
  h₂ : ℤ → (t : Tag) → DCPO[ obj (Payload t) 𝔻 , 𝔻 ]
  h₂ n (con Int m) = const₁ 𝟙ᵈ 𝔻 (out (δ p n m))
  h₂ n t = const₁ (obj (Payload t) 𝔻) 𝔻 ⊥𝔻
  h₁ : (t : Tag) → DCPO[ obj (Payload t) 𝔻 , 𝔻 ⟹₁ 𝔻 ]
  h₁ (con Int n) = const₁ 𝟙ᵈ (𝔻 ⟹₁ 𝔻) (case 𝔻⊥ (h₂ n))
  h₁ t = const₁ (obj (Payload t) 𝔻) (𝔻 ⟹₁ 𝔻) (const₁ 𝔻 𝔻 ⊥𝔻)

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

{- the value of the result of a primitive: eq returns left ⟨⟩ for true
   and right ⟨⟩ for false -}
out : Out → ⟨ 𝔻 ⟩
out (int n) = const Int n
out (bool true) = inl · unit
out (bool false) = inr · unit

{- the branches: on the second operand, and on the first -}
prim-br₂ : Prim → ℤ → (t : Tag) → DCPO[ obj (Payload t) 𝔻 , 𝔻 ]
prim-br₂ p n (con Int m) = const₁ 𝟙ᵈ 𝔻 (out (δ p n m))
prim-br₂ p n t = const₁ (obj (Payload t) 𝔻) 𝔻 ⊥𝔻

prim-br₁ : Prim → (t : Tag) → DCPO[ obj (Payload t) 𝔻 , 𝔻 ⟹₁ 𝔻 ]
prim-br₁ p (con Int n) = const₁ 𝟙ᵈ (𝔻 ⟹₁ 𝔻) (case 𝔻⊥ (prim-br₂ p n))
prim-br₁ p t = const₁ (obj (Payload t) 𝔻) (𝔻 ⟹₁ 𝔻) (const₁ 𝔻 𝔻 ⊥𝔻)

primD : Prim → DCPO[ 𝔻 , 𝔻 ⟹₁ 𝔻 ]
primD p = case (𝔻 ⟹𝔻) (prim-br₁ p)

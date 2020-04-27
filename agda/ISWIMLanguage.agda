{-

  Collects everything regarding the ISWIM language
  into one convenient module.

-}

module ISWIMLanguage where

open import ValueConst public
open import EvalISWIM public
open import ISWIM public
open ISWIM.ASTMod public
open import ValueConst public
open import ValueStructAux value_struct public
open import OrderingAux value_struct ordering public
open import Consistency public
open import ConsistentAux value_struct ordering consistent public
open import CurryConst public
open import PrimConst public
open import ModelCurryConst public
open import ModelCallByValue
   value_struct ordering consistent ℱ model_curry public
open import CurryApplyAux
   value_struct ordering consistent _●_ ℱ model_curry_apply public
open import ISWIMDenot
   value_struct ordering _●_ ℱ (λ {P} k v → ℘ {P} k v) public
open import Compositionality public
open ISWIMDenotAux
   value_struct ordering _●_ ℱ consistent model_curry_apply
   (λ {P} k v → ℘ {P} k v) public
open import SoundnessISWIM public
open import AdequacyISWIM public



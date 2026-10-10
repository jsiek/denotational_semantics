open import Primitives
open import Values
open import ISWIM

module ModelISWIM where

open import ValueConst public
open import ValueStructAux value_struct public
open import OrderingAux value_struct ordering public
open import Consistency public
open import CurryConst public
open import ModelCurryConst public

open import ModelCallByValue value_struct ordering consistent ℱ model_curry
     public


{-

  The values of the Clos5 machine (Semantics/CEK/Clos5.agda), which the machines
  of Imp, CFG and X86 share: code pointers, pairs, constants, tuples and
  injections, their observations, and the primitives on them. As in
  Clos4, code pointers and pairs (closures) are observed as functions
  (o-fun).

-}

module Semantics.CEK.Values where

open import Framework.Primitives using (Base; base-rep; Int)
open import Language.Prim using (Prim; Out; int; bool)
open import Semantics.Observation

open import Data.List using (List; []; _∷_)
open import Data.Bool using (true; false)
open import Data.Maybe using (Maybe; map)
open import Data.Nat using (ℕ)

data Val : Set where
  code : ℕ → Val                        {- a reference to a global definition -}
  pair : Val → Val → Val
  const : (B : Base) → base-rep B → Val
  tup : List Val → Val
  inl : Val → Val
  inr : Val → Val

obs : Val → Obs
obs-list : List Val → List Obs
obs (code k) = o-fun
obs (pair v w) = o-fun
obs (const B k) = o-const B k
obs (tup vs) = o-tuple (obs-list vs)
obs (inl v) = o-inl (obs v)
obs (inr v) = o-inr (obs v)
obs-list [] = []
obs-list (v ∷ vs) = obs v ∷ obs-list vs

{- the value of a primitive's result -}
out : Out → Val
out (int n) = const Int n
out (bool true) = inl (tup [])
out (bool false) = inr (tup [])

{- a primitive on two values, if they are integers -}
prim? : Prim → Val → Val → Maybe Val
prim? p v w = map out (δ? p (obs v) (obs w))

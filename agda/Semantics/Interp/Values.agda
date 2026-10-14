{-

  The values of the X86 interpreter (Semantics/Interp/X86.agda), which
  the interpreters of the preserved untyped Clos5, Imp and CFG
  (agda/Untyped/) share: code pointers, pairs (closures), constants,
  tuples and injections, their observations, the primitives on them and
  the projections, and frames of slots.

-}

module Semantics.Interp.Values where

open import Framework.Primitives using (Base; base-rep; Int)
open import Language.Prim using (Prim; Out; int; bool)
open import Semantics.Observation
open import Framework.ListUtil using (proj)
open import Semantics.Interp.Clock

open import Data.Bool using (true; false)
open import Data.Fin using (Fin)
open import Data.Integer using (+_)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing; map)
open import Data.Nat using (ℕ; zero; suc)

data Val : Set where
  code : ℕ → Val                        {- a reference to a global definition -}
  pair : Val → Val → Val
  const : (B : Base) → base-rep B → Val
  tup : List Val → Val
  inl : Val → Val
  inr : Val → Val

Env : Set
Env = List Val

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

{- the value of a primitive's result; eq gives inl ⟨⟩ or inr ⟨⟩ -}
out : Out → Val
out (int n) = const Int n
out (bool true) = inl (tup [])
out (bool false) = inr (tup [])

prim? : Prim → Val → Val → Maybe Val
prim? p v w = map out (δ? p (obs v) (obs w))

project : ∀ {n} → Fin n → Val → Result Val
project i (tup vs) = from-maybe (proj i vs)
project i _ = error

first second : Val → Result Val
first (pair v w) = ret v
first _ = error
second (pair v w) = ret w
second _ = error

Frame : Set
Frame = List Val

{- the initial value of a slot -}
zero-val : Val
zero-val = const Int (+ 0)

{- the frame with slot x assigned v, if it has slot x -}
_[_]≔_ : Frame → ℕ → Val → Maybe Frame
[] [ x ]≔ v = nothing
(u ∷ φ) [ zero ]≔ v = just (v ∷ φ)
(u ∷ φ) [ suc x ]≔ v = map (u ∷_) (φ [ x ]≔ v)

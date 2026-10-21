module proof.Framework.VecUtil where

open import Framework.VecUtil using (_<><_)

open import Data.Vec using (Vec)
open import Data.Vec.Relation.Binary.Pointwise.Inductive using (Pointwise; []; _∷_)

{- related vectors, reversed in front of related vectors, are related -}
_<><₂_ : ∀ {A B : Set} {R : A → B → Set} {m n} {xs : Vec A m} {ys : Vec B m} {xs' : Vec A n} {ys' : Vec B n}
  → Pointwise R xs ys → Pointwise R xs' ys' → Pointwise R (xs <>< xs') (ys <>< ys')
[] <><₂ rs' = rs'
(r ∷ rs) <><₂ rs' = rs <><₂ (r ∷ rs')

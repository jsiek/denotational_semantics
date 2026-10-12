{-

  List operations shared by the machines: looking up a variable in an
  environment, projecting from a tuple of a given size, and listing the
  subterms of a tuple. (Lemmas about them are in
  proof/Framework/ListUtil.agda.)

-}

module Framework.ListUtil where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_; replicate)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Framework.abt.Sig using (■)
open import Framework.abt.AbstractBindingTree using (ABT; Args)
open import Framework.Syntax.SyntaxUtil using (_,,_)

private variable
  A : Set

{- the x-th element, if there is one -}
_‼_ : List A → ℕ → Maybe A
[] ‼ x = nothing
(v ∷ vs) ‼ zero = just v
(v ∷ vs) ‼ suc x = vs ‼ x

has-length : ℕ → List A → Bool
has-length zero [] = true
has-length (suc n) (_ ∷ vs) = has-length n vs
has-length _ _ = false

{- component i of a tuple, if the tuple has n components -}
proj : ∀ {n} → Fin n → List A → Maybe A
proj {n = suc n} zero (v ∷ vs) = if has-length n vs then just v else nothing
proj (suc i) (v ∷ vs) = proj i vs
proj _ [] = nothing

{- the subterms of a tuple or of a closure's free variables -}
args→list : ∀ {Op sig n} → Args Op sig (replicate n ■) → List (ABT Op sig)
args→list {n = zero} Nil = []
args→list {n = suc n} (M ,, args) = M ∷ args→list args

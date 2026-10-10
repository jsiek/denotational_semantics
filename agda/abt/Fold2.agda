{-# OPTIONS --without-K --safe #-}
{- Extracted from the abt library (github.com/jsiek/abstract-binding-trees,
   commit 1387c40): just the fold, without the fusion lemmas. -}
open import Agda.Primitive using (Level)
open import Data.List using (List; []; _∷_)
open import Data.Product using () renaming (_,_ to ⟨_,_⟩ )
open import Data.Unit.Polymorphic using (tt)
open import abt.ScopedTuple using (Tuple)
open import abt.Sig
open import abt.Var
open import abt.GSubst

module abt.Fold2 (Op : Set) (sig : Op → List Sig) where

open import abt.AbstractBindingTree Op sig

private
  variable
    ℓ : Level
    V : Set ℓ

{-------------------------------------------------------------------------------
 Folding over an abstract binding tree

 fold f v₀ σ M

 Applies f at every operator node in M to the results of
 recursively folding its subexpressions.
 Applies σ to every variable node in M.
 When going under a "clear", σ is replaced with the default environment
 that maps every variable to v₀.
 ------------------------------------------------------------------------------}

fold : ((op : Op) → Tuple (sig op) (Result V) → V)
   → V → GSubst V → ABT → V
fold-arg : ((op : Op) → Tuple (sig op) (Result V) → V)
   → V → GSubst V → {b : Sig} → Arg b → Result V b
fold-args : ((op : Op) → Tuple (sig op) (Result V) → V)
   → V → GSubst V → {bs : List Sig} → Args bs → Tuple bs (Result V)

fold f v₀ σ (` x) = σ x
fold f v₀ σ (op ⦅ args ⦆) = f op (fold-args f v₀ σ {sig op} args)

fold-arg f v₀ σ (ast M) = (fold f v₀ σ M)
fold-arg f v₀ σ (bind arg) v = fold-arg f v₀ (v • σ) arg
fold-arg f v₀ σ (clear arg) = fold-arg f v₀ (λ x → v₀) arg

fold-args f v₀ σ {[]} nil = tt
fold-args f v₀ σ {b ∷ bs} (cons arg args) =
  ⟨ fold-arg f v₀ σ arg , fold-args f v₀ σ args ⟩

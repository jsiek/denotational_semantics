module NewSyntaxUtil where

  open import Data.Nat using (ℕ; zero; suc)

  open import abt.AbstractBindingTree
  open import NewSigUtil

  infixr 7  _,,_
  pattern _,,_ M Ns = cons (ast M) Ns
  pattern Nil = nil
  pattern ⟩_,,_ M Ns = cons (bind (ast M)) Ns
  pattern !_,,_ M Ns = cons M Ns

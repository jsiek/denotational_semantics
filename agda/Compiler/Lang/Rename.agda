open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List)
open import abt.Sig using (Sig)
open import abt.Var using (Var)

{-
  Renaming the variables of a term. A cleared argument (∁) cannot see the
  variables around it, so renaming leaves it unchanged.
-}
module Compiler.Lang.Rename (Op : Set) (sig : Op → List Sig) where

open import abt.AbstractBindingTree Op sig
  renaming (ABT to AST)

{- the renaming for the body of a binder -}
ext : (Var → Var) → Var → Var
ext r zero = zero
ext r (suc x) = suc (r x)

rename : (Var → Var) → AST → AST
rename-arg : ∀ {b} → (Var → Var) → Arg b → Arg b
rename-args : ∀ {bs} → (Var → Var) → Args bs → Args bs

rename r (` x) = ` (r x)
rename r (op ⦅ args ⦆) = op ⦅ rename-args r args ⦆

rename-arg r (ast M) = ast (rename r M)
rename-arg r (bind a) = bind (rename-arg (ext r) a)
rename-arg r (clear a) = clear a

rename-args r nil = nil
rename-args r (cons a args) = cons (rename-arg r a) (rename-args r args)

{- shift every variable up by one, to put a term under one more binder -}
shift : AST → AST
shift = rename suc

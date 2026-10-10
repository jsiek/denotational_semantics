{-# OPTIONS --safe #-}
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; replicate)

open import NewSyntaxUtil
open import NewSigUtil

module Compiler.Compile.Enclose where
  {-
   The enclose pass (Clos1 → Clos2): the body of each closure is closed
   off (∁) and bound under its free variables, so it can no longer see the
   surrounding environment.

   The body itself is unchanged. This is right when the closure lists the
   first n surrounding variables as its free variables, in the order
   ` (n - 1) , ... , ` 0, as the annotate pass does: the free variable
   bound last is then variable 1 of the body, which was variable 0 of the
   surrounding environment, and so on.
  -}
  open import Compiler.Lang.Clos1 as Source
  open import Compiler.Lang.Clos2 as Target
    renaming (clear to clear'; bind to bind'; ast to ast';
              AST to AST'; Arg to Arg'; Args to Args'; `_ to #_;
              _⦅_⦆ to _⦅_⦆')
  open import Compiler.Compile.Optimize using (bind-n-ast)

  {- the free variables that annotate gives a closure: ` (n - 1) , ... , ` 0 -}
  fv-vars : ∀ n → Args (replicate n ■)
  fv-vars zero = Nil
  fv-vars (suc n) = (` n) ,, fv-vars n

  enclose : AST → AST'
  enc-args : ∀ {n} → Args (replicate n ■) → Args' (replicate n ■)

  enclose (` x) = # x
  enclose (clos-op n ⦅ ! bind (ast N) ,, fvs ⦆) =
    clos-op n ⦅ ! clear' (bind-n-ast n (enclose N)) ,, enc-args fvs ⦆'
  enclose (app ⦅ L ,, M ,, Nil ⦆) = app ⦅ enclose L ,, enclose M ,, Nil ⦆'
  enclose (lit B k ⦅ Nil ⦆) = lit B k ⦅ Nil ⦆'
  enclose (tuple n ⦅ args ⦆) = tuple n ⦅ enc-args args ⦆'
  enclose (get i ⦅ M ,, Nil ⦆) = get i ⦅ enclose M ,, Nil ⦆'
  enclose (inl-op ⦅ M ,, Nil ⦆) = inl-op ⦅ enclose M ,, Nil ⦆'
  enclose (inr-op ⦅ M ,, Nil ⦆) = inr-op ⦅ enclose M ,, Nil ⦆'
  enclose (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) =
    case-op ⦅ enclose L ,, ⟩ enclose M ,, ⟩ enclose N ,, Nil ⦆'

  enc-args {zero} Nil = Nil
  enc-args {suc n} (M ,, args) = enclose M ,, enc-args args

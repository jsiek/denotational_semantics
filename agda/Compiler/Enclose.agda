open import Data.Nat using (ℕ; zero; suc; _∸_)
open import Data.List using (List; replicate)

open import Framework.Syntax.SyntaxUtil
open import Framework.Syntax.SigUtil

module Compiler.Enclose where
  {-
   The enclose pass (ISWIM → Clos2): each function becomes a closure whose
   body is closed off (∁) and bound under its free variables, so it can no
   longer see the surrounding environment.

   The free variables are the first m surrounding variables,
   ` (m - 1) , ... , ` 0, where m is the least number that covers every
   surrounding variable the body uses. The body itself is unchanged: the
   free variable bound last is variable 1 of the body, which was variable 0
   of the surrounding environment, and so on.
  -}
  open import Language.ISWIM as Source
  open import Language.Clos2 as Target
    renaming (clear to clear'; bind to bind'; ast to ast';
              AST to AST'; Arg to Arg'; Args to Args'; `_ to #_;
              _⦅_⦆ to _⦅_⦆')
  open import Compiler.Optimize using (bind-n-ast)

  {- one more than the largest variable a term uses, or 0 if it uses none -}
  open import Framework.Syntax.Uses Source.Op Source.sig using (bound; bound-arg; bound-args)

  {- the free variables of a closure: ` (n - 1) , ... , ` 0 -}
  fv-vars : ∀ n → Args' (replicate n ■)
  fv-vars zero = Nil
  fv-vars (suc n) = (# n) ,, fv-vars n

  enclose : AST → AST'
  enc-args : ∀ {n} → Args (replicate n ■) → Args' (replicate n ■)

  enclose (` x) = # x
  enclose (lam ⦅ ⟩ N ,, Nil ⦆) =
    clos-op m ⦅ ! clear' (bind-n-ast m (enclose N)) ,, fv-vars m ⦆'
    where
    {- the body's variable 0 is the argument, so the surrounding variable k
       is the body's variable suc k -}
    m = bound N ∸ 1
  enclose (app ⦅ L ,, M ,, Nil ⦆) = app ⦅ enclose L ,, enclose M ,, Nil ⦆'
  enclose (lit B k ⦅ Nil ⦆) = lit B k ⦅ Nil ⦆'
  enclose (tuple n ⦅ args ⦆) = tuple n ⦅ enc-args args ⦆'
  enclose (get i ⦅ M ,, Nil ⦆) = get i ⦅ enclose M ,, Nil ⦆'
  enclose (inl-op ⦅ M ,, Nil ⦆) = inl-op ⦅ enclose M ,, Nil ⦆'
  enclose (inr-op ⦅ M ,, Nil ⦆) = inr-op ⦅ enclose M ,, Nil ⦆'
  enclose (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) =
    case-op ⦅ enclose L ,, ⟩ enclose M ,, ⟩ enclose N ,, Nil ⦆'
  enclose (prim p ⦅ L ,, M ,, Nil ⦆) = prim p ⦅ enclose L ,, enclose M ,, Nil ⦆'

  enc-args {zero} Nil = Nil
  enc-args {suc n} (M ,, args) = enclose M ,, enc-args args

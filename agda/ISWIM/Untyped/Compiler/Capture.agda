open import Data.Nat using (ℕ; zero; suc; _∸_)
open import Data.List using (List; replicate)

open import Framework.Syntax.SyntaxUtil
open import Framework.Syntax.SigUtil

module Untyped.Compiler.Capture where
  {-
   The capture pass (ISWIM → Clos2): each function becomes a closure whose
   body is closed off (∁) and bound under its free variables, so it can no
   longer see the surrounding environment.

   The free variables are the first m surrounding variables,
   ` (m - 1) , ... , ` 0, where m is the least number that covers every
   surrounding variable the body uses. The body itself is unchanged: the
   free variable bound last is variable 1 of the body, which was variable 0
   of the surrounding environment, and so on.
  -}
  open import Language.ISWIM as Source
  open import Untyped.Language.Clos2 as Target
    renaming (clear to clear'; bind to bind'; ast to ast';
              AST to AST'; Arg to Arg'; Args to Args'; `_ to #_;
              _⦅_⦆ to _⦅_⦆')
  open import Untyped.Compiler.Prune using (bind-n-ast)

  {- one more than the largest variable a term uses, or 0 if it uses none -}
  open import Framework.Syntax.Uses Source.Op Source.sig using (bound; bound-arg; bound-args)

  {- the free variables of a closure: ` (n - 1) , ... , ` 0 -}
  fv-vars : ∀ n → Args' (replicate n ■)
  fv-vars zero = Nil
  fv-vars (suc n) = (# n) ,, fv-vars n

  capture : AST → AST'
  enc-args : ∀ {n} → Args (replicate n ■) → Args' (replicate n ■)

  capture (` x) = # x
  capture (lam ⦅ ⟩ N ,, Nil ⦆) =
    clos-op m ⦅ ! clear' (bind-n-ast m (capture N)) ,, fv-vars m ⦆'
    where
    {- the body's variable 0 is the argument, so the surrounding variable k
       is the body's variable suc k -}
    m = bound N ∸ 1
  capture (app ⦅ L ,, M ,, Nil ⦆) = app ⦅ capture L ,, capture M ,, Nil ⦆'
  capture (lit B k ⦅ Nil ⦆) = lit B k ⦅ Nil ⦆'
  capture (tuple n ⦅ args ⦆) = tuple n ⦅ enc-args args ⦆'
  capture (get i ⦅ M ,, Nil ⦆) = get i ⦅ capture M ,, Nil ⦆'
  capture (inl-op ⦅ M ,, Nil ⦆) = inl-op ⦅ capture M ,, Nil ⦆'
  capture (inr-op ⦅ M ,, Nil ⦆) = inr-op ⦅ capture M ,, Nil ⦆'
  capture (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) =
    case-op ⦅ capture L ,, ⟩ capture M ,, ⟩ capture N ,, Nil ⦆'
  capture (prim p ⦅ L ,, M ,, Nil ⦆) = prim p ⦅ capture L ,, capture M ,, Nil ⦆'
  capture (let-op ⦅ M ,, ⟩ N ,, Nil ⦆) = let-op ⦅ capture M ,, ⟩ capture N ,, Nil ⦆'

  enc-args {zero} Nil = Nil
  enc-args {suc n} (M ,, args) = capture M ,, enc-args args

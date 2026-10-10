open import Data.Nat using (ℕ; zero; suc; _∸_; _⊔_)
open import Data.List using (List; replicate)

open import NewSyntaxUtil
open import NewSigUtil

module Compiler.Compile.Annotate where
  {-
   The annotate pass (ISWIM → Clos1): each function becomes a closure that
   lists, as its free variables, the surrounding variables its body may
   use. These are the first m surrounding variables, ` (m - 1) , ... , ` 0,
   where m is the least number that covers every surrounding variable the
   body uses. The body itself is unchanged.
  -}
  open import Compiler.Lang.ISWIM as Source
  open import Compiler.Lang.Clos1 as Target
    renaming (clear to clear'; bind to bind'; ast to ast';
              AST to AST'; Arg to Arg'; Args to Args'; `_ to #_;
              _⦅_⦆ to _⦅_⦆')
  open import Compiler.Compile.Enclose using (fv-vars)

  {- one more than the largest variable a term uses, or 0 if it uses none -}
  bound : AST' → ℕ
  bound-arg : ∀ {b} → Arg' b → ℕ
  bound-args : ∀ {bs} → Args' bs → ℕ

  bound (# x) = suc x
  bound (op ⦅ args ⦆') = bound-args args

  bound-arg (ast' M) = bound M
  bound-arg (bind' a) = bound-arg a ∸ 1
  bound-arg (clear' a) = 0

  bound-args nil = 0
  bound-args (cons a args) = bound-arg a ⊔ bound-args args

  annotate : AST → AST'
  ann-args : ∀ {n} → Args (replicate n ■) → Args' (replicate n ■)

  annotate (` x) = # x
  annotate (lam ⦅ ⟩ N ,, Nil ⦆) = clos-op m ⦅ ⟩ N' ,, fv-vars m ⦆'
    where
    N' = annotate N
    {- the body's variable 0 is the argument, so the surrounding variable k
       is the body's variable suc k -}
    m = bound N' ∸ 1
  annotate (app ⦅ L ,, M ,, Nil ⦆) = app ⦅ annotate L ,, annotate M ,, Nil ⦆'
  annotate (lit B k ⦅ Nil ⦆) = lit B k ⦅ Nil ⦆'
  annotate (tuple n ⦅ args ⦆) = tuple n ⦅ ann-args args ⦆'
  annotate (get i ⦅ M ,, Nil ⦆) = get i ⦅ annotate M ,, Nil ⦆'
  annotate (inl-op ⦅ M ,, Nil ⦆) = inl-op ⦅ annotate M ,, Nil ⦆'
  annotate (inr-op ⦅ M ,, Nil ⦆) = inr-op ⦅ annotate M ,, Nil ⦆'
  annotate (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) =
    case-op ⦅ annotate L ,, ⟩ annotate M ,, ⟩ annotate N ,, Nil ⦆'

  ann-args {zero} Nil = Nil
  ann-args {suc n} (M ,, args) = annotate M ,, ann-args args

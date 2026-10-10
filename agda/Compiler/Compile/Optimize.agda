{-# OPTIONS --safe #-}
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; replicate)
open import Relation.Nullary using (Dec; yes; no)

open import NewSyntaxUtil
open import NewSigUtil

module Compiler.Compile.Optimize where
  {-
   The optimize pass (Clos2 → Clos2): a closure stops capturing the free
   variables that its code does not use.

   Closures are strict, so dropping a free variable is only safe when it
   cannot be empty. We drop it when its expression is a variable (which
   is what the earlier passes produce); in a nonempty environment a
   variable is never empty.

   Inside a closure's code, variable 0 is the argument and variable
   (suc j) is the free variable bound last but j. Dropping free variables
   renumbers these, so the pass carries a renaming of variables.
  -}
  open import Compiler.Lang.Clos2
  open import Compiler.Lang.Uses Op sig public
  open import Compiler.Compile.Concretize using (unbind-n)

  {- the renaming for the body of a binder -}
  ext-var : (Var → Var) → Var → Var
  ext-var r zero = zero
  ext-var r (suc x) = suc (r x)

  {- the code of a closure, under its n + 1 binders -}
  bind-n-ast : ∀ n → AST → Arg (ν-n n (ν ■))
  bind-n-ast zero N = bind (ast N)
  bind-n-ast (suc n) N = bind (bind-n-ast n N)

  {- the free variables that a closure keeps; index renumbers the
     positions of its old free variables (and of the variables past them)
     as positions of the new ones -}
  record Pruned : Set where
    constructor pruned
    field
      count : ℕ
      kept : Args (replicate count ■)
      index : ℕ → ℕ
  open Pruned public

  keep : AST → Pruned → Pruned
  keep M (pruned m fvs idx) = pruned (suc m) (M ,, fvs) idx

  {- the positions past the free variables, after keeping or dropping the
     outermost free variable -}
  keep-base : (ℕ → ℕ) → ℕ → ℕ
  keep-base b zero = zero
  keep-base b (suc k) = suc (b k)

  drop-base : (ℕ → ℕ) → ℕ → ℕ
  drop-base b zero = zero
  drop-base b (suc k) = b k

  optimize : (Var → Var) → AST → AST
  opt-args : ∀ {n} → (Var → Var) → Args (replicate n ■) → Args (replicate n ■)
  opt-body : (Var → Var) → ∀ k → Arg (ν-n k (ν ■)) → AST
  {- U j says whether the code uses the free variable at position j -}
  prune : ∀ n (r : Var → Var) {U : ℕ → Set} → (∀ j → Dec (U j))
    → Args (replicate n ■) → (ℕ → ℕ) → Pruned

  optimize r (` x) = ` (r x)
  optimize r (clos-op n ⦅ ! clear a ,, fvs ⦆) =
    clos-op (count P) ⦅ ! clear (bind-n-ast (count P) (opt-body (ext-var (index P)) n a))
                      ,, kept P ⦆
    where
    P = prune n r (λ j → uses? (suc j) (unbind-n n a)) fvs (λ k → k)
  optimize r (app ⦅ L ,, M ,, Nil ⦆) = app ⦅ optimize r L ,, optimize r M ,, Nil ⦆
  optimize r (lit B k ⦅ Nil ⦆) = lit B k ⦅ Nil ⦆
  optimize r (tuple n ⦅ args ⦆) = tuple n ⦅ opt-args r args ⦆
  optimize r (get i ⦅ M ,, Nil ⦆) = get i ⦅ optimize r M ,, Nil ⦆
  optimize r (inl-op ⦅ M ,, Nil ⦆) = inl-op ⦅ optimize r M ,, Nil ⦆
  optimize r (inr-op ⦅ M ,, Nil ⦆) = inr-op ⦅ optimize r M ,, Nil ⦆
  optimize r (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) =
    case-op ⦅ optimize r L ,, ⟩ optimize (ext-var r) M ,, ⟩ optimize (ext-var r) N ,, Nil ⦆

  opt-args {zero} r Nil = Nil
  opt-args {suc n} r (M ,, args) = optimize r M ,, opt-args r args

  {- opt-body r k a is optimize r (unbind-n k a) -}
  opt-body r zero (bind (ast N)) = optimize r N
  opt-body r (suc k) (bind a) = opt-body r k a

  {- the outermost free variable is at position n -}
  prune zero r dec Nil b = pruned 0 Nil b
  prune (suc n) r dec ((` y) ,, fvs) b with dec n
  ... | yes _ = keep (` (r y)) (prune n r dec fvs (keep-base b))
  ... | no _ = prune n r dec fvs (drop-base b)
  prune (suc n) r dec ((op ⦅ args ⦆) ,, fvs) b =
    keep (optimize r (op ⦅ args ⦆)) (prune n r dec fvs (keep-base b))

  {- the pass, for a whole program -}
  optimize-program : AST → AST
  optimize-program = optimize (λ x → x)

{-# OPTIONS --safe #-}
open import Data.Nat using (ℕ; zero; suc; _<_; _<?_)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; replicate)
open import Relation.Nullary using (yes; no)

open import NewSyntaxUtil
open import NewSigUtil

module Compiler.Compile.Concretize where
  {-
   The concretize pass: each closure stores its free variables in a
   single tuple, and inside the closure's code each free variable becomes
   a projection from that tuple.

   In Clos2 the code of a closure with n free variables binds them one at
   a time and then binds the argument, so in the body variable 0 is the
   argument and variable (suc k), for k < n, is the free variable that was
   bound last but k. In Clos3 the code binds the tuple of free variables
   (variable 1) and the argument (variable 0).
  -}
  open import Compiler.Lang.Clos2 as Source
  open import Compiler.Lang.Clos3 as Target
    renaming (clear to clear'; bind to bind'; ast to ast';
              AST to AST'; Arg to Arg'; Args to Args'; `_ to #_;
              _⦅_⦆ to _⦅_⦆')

  {- where a Clos2 variable lives in Clos3: in a variable, or in a
     component of a tuple held in a variable -}
  data Ref : Set where
    var : Var → Ref
    prj : ∀ {n} → Fin n → Var → Ref

  ref-ast : Ref → AST'
  ref-ast (var x) = # x
  ref-ast (prj i x) = get i ⦅ # x ,, Nil ⦆'

  shift-ref : Ref → Ref
  shift-ref (var x) = var (suc x)
  shift-ref (prj i x) = prj i (suc x)

  {- the map for the body of a binder -}
  ext-ref : (Var → Ref) → Var → Ref
  ext-ref φ zero = var zero
  ext-ref φ (suc x) = shift-ref (φ x)

  {- the position in the tuple of the free variable bound last but k -}
  fv-index : ∀ n k → k < n → Fin n
  fv-index (suc n) k k<sn with k <? n
  ... | yes k<n = suc (fv-index n k k<n)
  ... | no _ = zero

  {- the map for the code of a closure with n free variables; variables
     past the free variables refer to the initial environment, which in
     Clos3 starts at variable 2 -}
  fv-ref : ℕ → Var → Ref
  fv-ref n zero = var zero
  fv-ref n (suc k) with k <? n
  ... | yes k<n = prj (fv-index n k k<n) 1
  ... | no _ = var 2

  {- the body of a closure's code, under its n + 1 binders -}
  unbind-n : ∀ k → Arg (ν-n k (ν ■)) → AST
  unbind-n zero (bind (ast N)) = N
  unbind-n (suc k) (bind a) = unbind-n k a

  concretize : (Var → Ref) → AST → AST'
  conc-body : ℕ → ∀ k → Arg (ν-n k (ν ■)) → AST'
  conc-args : ∀ {n} → (Var → Ref) → Args (replicate n ■) → Args' (replicate n ■)

  concretize φ (` x) = ref-ast (φ x)
  concretize φ (clos-op n ⦅ ! clear a ,, fvs ⦆) =
    clos-op n ⦅ ! clear' (bind' (bind' (ast' (conc-body n n a)))) ,, conc-args φ fvs ⦆'
  concretize φ (app ⦅ L ,, M ,, Nil ⦆) = app ⦅ concretize φ L ,, concretize φ M ,, Nil ⦆'
  concretize φ (lit B k ⦅ Nil ⦆) = lit B k ⦅ Nil ⦆'
  concretize φ (tuple n ⦅ args ⦆) = tuple n ⦅ conc-args φ args ⦆'
  concretize φ (get i ⦅ M ,, Nil ⦆) = get i ⦅ concretize φ M ,, Nil ⦆'
  concretize φ (inl-op ⦅ M ,, Nil ⦆) = inl-op ⦅ concretize φ M ,, Nil ⦆'
  concretize φ (inr-op ⦅ M ,, Nil ⦆) = inr-op ⦅ concretize φ M ,, Nil ⦆'
  concretize φ (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) =
    case-op ⦅ concretize φ L ,, ⟩ concretize (ext-ref φ) M ,, ⟩ concretize (ext-ref φ) N ,, Nil ⦆'

  {- conc-body n k a is concretize (fv-ref n) (unbind-n k a) -}
  conc-body n zero (bind (ast N)) = concretize (fv-ref n) N
  conc-body n (suc k) (bind a) = conc-body n k a

  conc-args {zero} φ Nil = Nil
  conc-args {suc n} φ (M ,, args) = concretize φ M ,, conc-args φ args

  {- the pass, for a whole program -}
  concretize-program : AST → AST'
  concretize-program = concretize var

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; replicate)
open import Framework.abt.Sig using (Sig; ■)
open import Framework.abt.Var using (Var)

{-
  Substituting terms for the variables of a term, for any signature
  (lemmas in proof/Framework/Syntax/Subst.agda). A substitution maps each
  variable to a term; under a binder, variable 0 stays and the others are
  shifted (exts). A cleared argument (∁) cannot see the variables around
  it, so substitution leaves it unchanged, as renaming does.
-}
module Framework.Syntax.Subst (Op : Set) (sig : Op → List Sig) where

open import Framework.abt.AbstractBindingTree Op sig
  renaming (ABT to AST)
open import Framework.Syntax.Rename Op sig using (rename)
open import Framework.abt.GSubst using (_•_) public

Subst : Set
Subst = Var → AST

{- the identity substitution -}
ids : Subst
ids = `_

{- the substitution for the body of a binder -}
exts : Subst → Subst
exts σ zero = ` zero
exts σ (suc x) = rename suc (σ x)

sub : Subst → AST → AST
sub-arg : ∀ {b} → Subst → Arg b → Arg b
sub-args : ∀ {bs} → Subst → Args bs → Args bs

sub σ (` x) = σ x
sub σ (op ⦅ args ⦆) = op ⦅ sub-args σ args ⦆

sub-arg σ (ast M) = ast (sub σ M)
sub-arg σ (bind a) = bind (sub-arg (exts σ) a)
sub-arg σ (clear a) = clear a

sub-args σ nil = nil
sub-args σ (cons a args) = cons (sub-arg σ a) (sub-args σ args)

{- σ extended by the operands Ms, bound in order: the last one is
   variable 0 -}
extend : ∀ {n} → Args (replicate n ■) → Subst → Subst
extend {zero} nil σ = σ
extend {suc n} (cons (ast M) Ms) σ = extend Ms (M • σ)

{- substituting M for variable 0 of the body N of a binder -}
_[_] : AST → AST → AST
N [ M ] = sub (M • ids) N

module Language.Mon where
{-

 Monadic normal form, a sublanguage of Clos5: the output of the
 remove-complex-operands pass (Compiler/RCO.agda).

 An atom is a variable, a literal, or a reference to a global
 definition. In monadic normal form, the operands of app, pair, fst,
 snd, tuple, get, inl, inr and prim and the scrutinee of case are atoms;
 the right-hand side and body of let and the branches of case may be
 complex, but are in monadic normal form themselves.

-}

open import Language.Clos5
open import Framework.Syntax.Rename Op sig using (rename; rename-args; ext)
open import Framework.Syntax.SyntaxUtil using (_,,_; ⟩_,,_; Nil)

open import Data.Fin using (Fin)
open import Data.Nat using (zero)
open import Data.List using (replicate)
open import Data.List.Relation.Unary.All using (All)
open import Data.Product using (_×_)

data Atom : AST → Set where
  var : ∀ x → Atom (` x)
  lit : ∀ B k → Atom (lit B k ⦅ nil ⦆)
  ref : ∀ k → Atom (fun-ref k ⦅ nil ⦆)

{- n operands, all atoms -}
data Atoms : ∀ {n} → Args (replicate n ■) → Set where
  [] : Atoms {zero} nil
  _∷_ : ∀ {n M} {Ms : Args (replicate n ■)} → Atom M → Atoms Ms → Atoms (M ,, Ms)

data Mon : AST → Set where
  atom : ∀ {M} → Atom M → Mon M
  app : ∀ {As} → Atoms {3} As → Mon (app ⦅ As ⦆)
  pair : ∀ {As} → Atoms {2} As → Mon (pair-op ⦅ As ⦆)
  fst : ∀ {As} → Atoms {1} As → Mon (fst-op ⦅ As ⦆)
  snd : ∀ {As} → Atoms {1} As → Mon (snd-op ⦅ As ⦆)
  tuple : ∀ {n} {As : Args (replicate n ■)} → Atoms As → Mon (tuple n ⦅ As ⦆)
  get : ∀ {n} {i : Fin n} {As} → Atoms {1} As → Mon (get i ⦅ As ⦆)
  inl : ∀ {As} → Atoms {1} As → Mon (inl-op ⦅ As ⦆)
  inr : ∀ {As} → Atoms {1} As → Mon (inr-op ⦅ As ⦆)
  case : ∀ {A M N} → Atom A → Mon M → Mon N → Mon (case-op ⦅ A ,, ⟩ M ,, ⟩ N ,, Nil ⦆)
  prim : ∀ {p As} → Atoms {2} As → Mon (prim p ⦅ As ⦆)
  let′ : ∀ {M N} → Mon M → Mon N → Mon (let-op ⦅ M ,, ⟩ N ,, Nil ⦆)

{- a monadic program: every global definition and main -}
MonProgram : Program → Set
MonProgram (program ds M) = All Mon ds × Mon M

{- renaming variables preserves monadic normal form -}
atom-rename : ∀ r {M} → Atom M → Atom (rename r M)
atom-rename r (var x) = var (r x)
atom-rename r (lit B k) = lit B k
atom-rename r (ref k) = ref k

atoms-rename : ∀ r {n} {Ms : Args (replicate n ■)} → Atoms Ms
  → Atoms (rename-args r Ms)
atoms-rename r [] = []
atoms-rename r (a ∷ as) = atom-rename r a ∷ atoms-rename r as

mon-rename : ∀ r {M} → Mon M → Mon (rename r M)
mon-rename r (atom a) = atom (atom-rename r a)
mon-rename r (app as) = app (atoms-rename r as)
mon-rename r (pair as) = pair (atoms-rename r as)
mon-rename r (fst as) = fst (atoms-rename r as)
mon-rename r (snd as) = snd (atoms-rename r as)
mon-rename r (tuple as) = tuple (atoms-rename r as)
mon-rename r (get as) = get (atoms-rename r as)
mon-rename r (inl as) = inl (atoms-rename r as)
mon-rename r (inr as) = inr (atoms-rename r as)
mon-rename r (case a m n) = case (atom-rename r a) (mon-rename (ext r) m) (mon-rename (ext r) n)
mon-rename r (prim as) = prim (atoms-rename r as)
mon-rename r (let′ m n) = let′ (mon-rename r m) (mon-rename (ext r) n)

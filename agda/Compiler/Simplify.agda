{-

  The simplify pass (ISWIM → ISWIM), a simplified version of the source
  optimizer cp0 of Chez Scheme. It runs before enclose (but is not yet
  part of compile, Compiler/Pipeline.agda).

  In one recursive pass, simp carries what it knows about each variable
  (Facts): the term that replaces it, and a value that it is known to be,
  if any (Info). It does

  1. constant folding: a primitive whose operands are known integers
     becomes its result (eq gives inl ⟨⟩ or inr ⟨⟩, as the semantics do);
  2. case of a known injection: case L of x. M | y. N, where L is known to
     be inl V, becomes M with V for x (likewise inr);
  3. projection from a known tuple: get i L, where L is known to be a
     tuple of values, becomes its component i;
  4. β on a value: app (lam N) M, where M becomes a value V, becomes N
     with V for its variable, which gives copy propagation and the
     elimination of dead bindings.

  It only duplicates or discards values, and never reorders evaluation:
  a known value comes from evaluating a term that has no effect, so
  replacing that term by the value drops only that evaluation.

  Substitution policy: only small values are duplicated: variables,
  literals, ⟨⟩, and an injection of one of them (small). Any other value
  (a function, a tuple, a nested injection) keeps its binding: the
  redex stays, as the let app (lam N') V', and the bound variable is
  known to be V', so that a projection from it, or a case on it, can
  still be folded.

  Not yet: inlining a known function at a call. Info records functions
  as known values (lam), so that inlining can look them up; it would
  re-simplify the function's body, under fuel, and inline when the
  result is small enough.

-}

module Compiler.Simplify where

open import Language.ISWIM
open import Language.Prim using (Prim; Out; int; bool; δ)
open import Framework.Primitives using (Int)
open import Framework.Syntax.SyntaxUtil using (_,,_; Nil; ⟩_,,_)
open import Framework.Syntax.Rename Op sig using (shift)
open import Framework.ListUtil using (proj; args→list)

open import Data.Bool using (Bool; true; false; _∧_; if_then_else_)
open import Data.Fin using (Fin)
open import Data.Integer using (ℤ)
open import Data.List using (replicate)
open import Data.Maybe using (Maybe; just; nothing; map)
open import Data.Nat using (zero; suc)
open import Data.Product using (_×_; _,_)

{- What is known -------------------------------------------------------------}

{- what simplify knows of a variable or a term: the term that replaces it,
   and a value it is known to be, if any -}
infix 4 _∣_
record Info : Set where
  constructor _∣_
  field
    term : AST
    known : Maybe AST
open Info public

{- what simplify knows of each variable -}
Facts : Set
Facts = Var → Info

{- a value, which is known to be itself -}
self : AST → Info
self V = V ∣ just V

{- under one more binder -}
shift-info : Info → Info
shift-info (M ∣ k) = shift M ∣ map shift k

{- under a binder that stays, whose variable is unknown -}
under : Facts → Facts
under E = self (` 0) • (λ x → shift-info (E x))

{- Values --------------------------------------------------------------------}

{- values (syntactically: a variable stands for a value) -}
value : AST → Bool
values : ∀ {n} → Args (replicate n ■) → Bool
value (` x) = true
value (lam ⦅ _ ⦆) = true
value (lit B k ⦅ _ ⦆) = true
value (tuple n ⦅ as ⦆) = values as
value (inl-op ⦅ M ,, Nil ⦆) = value M
value (inr-op ⦅ M ,, Nil ⦆) = value M
value _ = false
values {zero} Nil = true
values {suc n} (M ,, as) = value M ∧ values as

{- a term that is known to be itself if it is a value -}
info : AST → Info
info M = M ∣ (if value M then just M else nothing)

{- the values that may be duplicated: variables, literals, ⟨⟩, and an
   injection of one of them -}
atom : AST → Bool
atom (` x) = true
atom (lit B k ⦅ _ ⦆) = true
atom (tuple zero ⦅ _ ⦆) = true
atom _ = false

small : AST → Bool
small (inl-op ⦅ M ,, Nil ⦆) = atom M
small (inr-op ⦅ M ,, Nil ⦆) = atom M
small M = atom M

{- Known values ---------------------------------------------------------------}

{- the integer that a term is known to be -}
int-of : Maybe AST → Maybe ℤ
int-of (just (lit Int n ⦅ Nil ⦆)) = just n
int-of _ = nothing

{- component i of a tuple that a term is known to be -}
component : ∀ {n} → Fin n → Maybe AST → Maybe AST
component i (just (tuple m ⦅ Ks ⦆)) = proj i (args→list Ks)
component i _ = nothing

{- the branch (true for inl) that a case on a term known to be an
   injection takes, and the value it binds, if that value is small -}
branch : Maybe AST → Maybe (Bool × AST)
branch (just (inl-op ⦅ K ,, Nil ⦆)) = if small K then just (true , K) else nothing
branch (just (inr-op ⦅ K ,, Nil ⦆)) = if small K then just (false , K) else nothing
branch _ = nothing

{- the term of a primitive's result -}
prim-term : Out → AST
prim-term (int n) = lit Int n ⦅ Nil ⦆
prim-term (bool true) = inl-op ⦅ tuple 0 ⦅ Nil ⦆ ,, Nil ⦆
prim-term (bool false) = inr-op ⦅ tuple 0 ⦅ Nil ⦆ ,, Nil ⦆

{- The pass -------------------------------------------------------------------}

simp : Facts → AST → Info
simp-args : ∀ {n} → Facts → Args (replicate n ■) → Args (replicate n ■)
simp-app : Facts → AST → Info → Info
simp-let : Facts → AST → Info → Info
simp-get : ∀ {n} → Fin n → Info → Info
simp-case : Facts → Info → AST → AST → Info
simp-prim : Prim → Info → Info → Info

simp E (` x) = E x
simp E (lam ⦅ ⟩ N ,, Nil ⦆) = self (lam ⦅ ⟩ term (simp (under E) N) ,, Nil ⦆)
simp E (app ⦅ L ,, M ,, Nil ⦆) = simp-app E L (simp E M)
simp E (lit B k ⦅ Nil ⦆) = self (lit B k ⦅ Nil ⦆)
simp E (tuple n ⦅ as ⦆) = info (tuple n ⦅ simp-args E as ⦆)
simp E (get i ⦅ L ,, Nil ⦆) = simp-get i (simp E L)
simp E (inl-op ⦅ M ,, Nil ⦆) = info (inl-op ⦅ term (simp E M) ,, Nil ⦆)
simp E (inr-op ⦅ M ,, Nil ⦆) = info (inr-op ⦅ term (simp E M) ,, Nil ⦆)
simp E (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) = simp-case E (simp E L) M N
simp E (prim p ⦅ L ,, M ,, Nil ⦆) = simp-prim p (simp E L) (simp E M)

simp-args {zero} E Nil = Nil
simp-args {suc n} E (M ,, as) = term (simp E M) ,, simp-args E as

{- an application: β, if the operator is a function -}
simp-app E (lam ⦅ ⟩ N ,, Nil ⦆) I = simp-let E N I
simp-app E L I = app ⦅ term (simp E L) ,, term I ,, Nil ⦆ ∣ nothing

{- the body N of a function, applied to the operand I: a small value is
   substituted; another value stays bound, and known; anything else
   stays bound -}
simp-let E N I with small (term I) | value (term I)
... | true | _ = simp (self (term I) • E) N
... | false | true =
  app ⦅ lam ⦅ ⟩ term (simp (((` 0) ∣ just (shift (term I))) • (λ x → shift-info (E x))) N) ,, Nil ⦆
      ,, term I ,, Nil ⦆ ∣ nothing
... | false | false = app ⦅ lam ⦅ ⟩ term (simp (under E) N) ,, Nil ⦆ ,, term I ,, Nil ⦆ ∣ nothing

{- a projection from a known tuple: the component, if it is small, and
   otherwise the projection, known to be the component -}
simp-get i I with component i (known I)
... | just K = if small K then self K else (get i ⦅ term I ,, Nil ⦆ ∣ just K)
... | nothing = get i ⦅ term I ,, Nil ⦆ ∣ nothing

{- a case on a known injection: the branch it takes -}
simp-case E I M N with branch (known I)
... | just (true , K) = simp (self K • E) M
... | just (false , K) = simp (self K • E) N
... | nothing =
  case-op ⦅ term I ,, ⟩ term (simp (under E) M) ,, ⟩ term (simp (under E) N) ,, Nil ⦆ ∣ nothing

{- a primitive on known integers: its result -}
simp-prim p I J with int-of (known I)
... | nothing = prim p ⦅ term I ,, term J ,, Nil ⦆ ∣ nothing
... | just n with int-of (known J)
...   | nothing = prim p ⦅ term I ,, term J ,, Nil ⦆ ∣ nothing
...   | just m = self (prim-term (δ p n m))

{- the pass, for a whole program: every variable is itself, and unknown -}
simplify : AST → AST
simplify M = term (simp (λ x → self (` x)) M)

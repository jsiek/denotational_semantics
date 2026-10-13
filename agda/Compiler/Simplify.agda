{-

  The simplify pass (ISWIM → ISWIM), a simplified version of the source
  optimizer cp0 of Chez Scheme, the first pass of compile
  (Compiler/Pipeline.agda).

  In one recursive pass, simp carries what it knows about each variable
  (Facts): the term that replaces it, and what it is known to be, if
  anything (Info): a value, or a function λ N, kept as its body N before
  simplification together with the Facts where it was defined (Known).
  It does

  1. constant folding: a primitive whose operands are known integers
     becomes its result (eq gives inl ⟨⟩ or inr ⟨⟩, as the semantics do);
  2. case of a known injection: case L of x. M | y. N, where L is known to
     be inl V, becomes M with V for x (likewise inr);
  3. projection from a known tuple: get i L, where L is known to be a
     tuple of values, becomes its component i;
  4. β on a value: app (lam N) M, where M becomes a value V, becomes N
     with V for its variable, which gives copy propagation and the
     elimination of dead bindings;
  5. inlining: app L M, where L is known to be a function λ N, becomes
     N's body, simplified at the call with its variable bound to M as in
     4 (simp-let), if the result is small enough (inline-size). The body
     is simplified again under the Facts of its definition and what is
     known of M, as in cp0; fuel (inline-fuel) bounds how deeply calls
     are inlined within inlined bodies, so the pass is structurally
     recursive.

  It only duplicates or discards values, and never reorders evaluation:
  a known value comes from evaluating a term that has no effect, so
  replacing that term by the value drops only that evaluation. In
  inlining, the operator L, known, is dropped, and the operand M stays
  bound, as cp0 does: a call f M becomes the let app (lam N') M', which
  evaluates M' once, before the body, and keeps it even if N' does not
  use it, unless M' is a value (4).

  Substitution policy: only small values are duplicated: variables,
  literals, ⟨⟩, and an injection of one of them (small). A small value
  substituted for a variable keeps what is known of it (a copy of a
  known function is known). Any other value (a function, a tuple, a
  nested injection) keeps its binding: the redex stays, as the let
  app (lam N') V', and the bound variable is known as V' is, so that a
  projection from it, or a case on it, can still be folded, and a call
  of it inlined.

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
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤ᵇ_)
open import Data.Product using (_×_; _,_)

{- What is known -------------------------------------------------------------}

{- what simplify knows of a variable or a term: the term that replaces it,
   and what it is known to be, if anything (Known) -}
infix 4 _∣_
record Info : Set
data Known : Set

{- what simplify knows of each variable -}
Facts : Set
Facts = Var → Info

{- a value (val), or a function λ N, its body N not yet simplified, with
   what was known of its variables where it was defined (fun) -}
data Known where
  val : AST → Known
  fun : AST → Facts → Known

record Info where
  inductive
  constructor _∣_
  field
    term : AST
    known : Maybe Known
open Info public

{- a value, which is known to be itself -}
self : AST → Info
self V = V ∣ just (val V)

{- under one more binder -}
shift-info : Info → Info
shift-known : Known → Known
shift-mk : Maybe Known → Maybe Known
shift-info I = shift (term I) ∣ shift-mk (known I)
shift-mk nothing = nothing
shift-mk (just K) = just (shift-known K)
shift-known (val V) = val (shift V)
shift-known (fun N E) = fun N (λ x → shift-info (E x))

{- under a binder that stays, whose variable is unknown -}
under : Facts → Facts
under E = self (` 0) • (λ x → shift-info (E x))

{- under a binder that stays, whose variable is known as I is -}
known-as : Info → Facts → Facts
known-as I E = ((` 0) ∣ known (shift-info I)) • (λ x → shift-info (E x))

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
info M = M ∣ (if value M then just (val M) else nothing)

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
int-of : Maybe Known → Maybe ℤ
int-of (just (val (lit Int n ⦅ Nil ⦆))) = just n
int-of _ = nothing

{- component i of a tuple that a term is known to be -}
component : ∀ {n} → Fin n → Maybe Known → Maybe AST
component i (just (val (tuple m ⦅ Ks ⦆))) = proj i (args→list Ks)
component i _ = nothing

{- the branch (true for inl) that a case on a term known to be an
   injection takes, and the value it binds, if that value is small -}
branch : Maybe Known → Maybe (Bool × AST)
branch (just (val (inl-op ⦅ K ,, Nil ⦆))) = if small K then just (true , K) else nothing
branch (just (val (inr-op ⦅ K ,, Nil ⦆))) = if small K then just (false , K) else nothing
branch _ = nothing

{- the term of a primitive's result -}
prim-term : Out → AST
prim-term (int n) = lit Int n ⦅ Nil ⦆
prim-term (bool true) = inl-op ⦅ tuple 0 ⦅ Nil ⦆ ,, Nil ⦆
prim-term (bool false) = inr-op ⦅ tuple 0 ⦅ Nil ⦆ ,, Nil ⦆

{- the size of a term -}
size : AST → ℕ
size-arg : ∀ {b} → Arg b → ℕ
size-args : ∀ {bs} → Args bs → ℕ
size (` x) = 1
size (op ⦅ as ⦆) = suc (size-args as)
size-arg (ast M) = size M
size-arg (bind a) = size-arg a
size-arg (clear a) = size-arg a
size-args nil = 0
size-args (cons a as) = size-arg a + size-args as

{- inlining: the depth of nested inlining (fuel), and the size up to which
   a function's body, simplified at the call, is inlined -}
inline-fuel inline-size : ℕ
inline-fuel = 4
inline-size = 24

{- whether a term is a function -}
data Lam? : AST → Set where
  is-lam : ∀ N → Lam? (lam ⦅ ⟩ N ,, Nil ⦆)
  other : ∀ {L} → Lam? L

lam? : ∀ L → Lam? L
lam? (lam ⦅ ⟩ N ,, Nil ⦆) = is-lam N
lam? L = other

{- The pass -------------------------------------------------------------------}

simp : ℕ → Facts → AST → Info
simp-args : ∀ {n} → ℕ → Facts → Args (replicate n ■) → Args (replicate n ■)
simp-app : ℕ → Facts → AST → Info → Info
simp-call : ℕ → Info → Info → Info
simp-let : ℕ → Facts → AST → Info → Info
simp-get : ∀ {n} → Fin n → Info → Info
simp-case : ℕ → Facts → Info → AST → AST → Info
simp-prim : Prim → Info → Info → Info

simp f E (` x) = E x
simp f E (lam ⦅ ⟩ N ,, Nil ⦆) = lam ⦅ ⟩ term (simp f (under E) N) ,, Nil ⦆ ∣ just (fun N E)
simp f E (app ⦅ L ,, M ,, Nil ⦆) = simp-app f E L (simp f E M)
simp f E (lit B k ⦅ Nil ⦆) = self (lit B k ⦅ Nil ⦆)
simp f E (tuple n ⦅ as ⦆) = info (tuple n ⦅ simp-args f E as ⦆)
simp f E (get i ⦅ L ,, Nil ⦆) = simp-get i (simp f E L)
simp f E (inl-op ⦅ M ,, Nil ⦆) = info (inl-op ⦅ term (simp f E M) ,, Nil ⦆)
simp f E (inr-op ⦅ M ,, Nil ⦆) = info (inr-op ⦅ term (simp f E M) ,, Nil ⦆)
simp f E (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) = simp-case f E (simp f E L) M N
simp f E (prim p ⦅ L ,, M ,, Nil ⦆) = simp-prim p (simp f E L) (simp f E M)

simp-args {zero} f E Nil = Nil
simp-args {suc n} f E (M ,, as) = term (simp f E M) ,, simp-args f E as

{- an application: β, if the operator is a function, and otherwise a call -}
simp-app f E L I with lam? L
... | is-lam N = simp-let f E N I
... | other = simp-call f (simp f E L) I

{- a call of a known function λ N, with fuel: its body is simplified at
   the call, with the operand bound (simp-let), and inlined if the result
   is small enough. The operator, known, has no effect, and is dropped -}
simp-call (suc f) (T ∣ just (fun N E)) I with size (term (simp-let f E N I)) ≤ᵇ inline-size
... | true = simp-let f E N I
... | false = app ⦅ T ,, term I ,, Nil ⦆ ∣ nothing
simp-call f J I = app ⦅ term J ,, term I ,, Nil ⦆ ∣ nothing

{- the body N of a function, applied to the operand I (a let): a small
   value is substituted, and known as I is; another value stays bound, and
   known; anything else stays bound -}
simp-let f E N I with small (term I) | value (term I)
... | true | _ = simp f (I • E) N
... | false | true = app ⦅ lam ⦅ ⟩ term (simp f (known-as I E) N) ,, Nil ⦆ ,, term I ,, Nil ⦆ ∣ nothing
... | false | false = app ⦅ lam ⦅ ⟩ term (simp f (under E) N) ,, Nil ⦆ ,, term I ,, Nil ⦆ ∣ nothing

{- a projection from a known tuple: the component, if it is small, and
   otherwise the projection, known to be the component -}
simp-get i I with component i (known I)
... | just K = if small K then self K else (get i ⦅ term I ,, Nil ⦆ ∣ just (val K))
... | nothing = get i ⦅ term I ,, Nil ⦆ ∣ nothing

{- a case on a known injection: the branch it takes -}
simp-case f E I M N with branch (known I)
... | just (true , K) = simp f (self K • E) M
... | just (false , K) = simp f (self K • E) N
... | nothing =
  case-op ⦅ term I ,, ⟩ term (simp f (under E) M) ,, ⟩ term (simp f (under E) N) ,, Nil ⦆ ∣ nothing

{- a primitive on known integers: its result -}
simp-prim p I J with int-of (known I)
... | nothing = prim p ⦅ term I ,, term J ,, Nil ⦆ ∣ nothing
... | just n with int-of (known J)
...   | nothing = prim p ⦅ term I ,, term J ,, Nil ⦆ ∣ nothing
...   | just m = self (prim-term (δ p n m))

{- the pass, for a whole program: every variable is itself, and unknown -}
simplify : AST → AST
simplify M = term (simp inline-fuel (λ x → self (` x)) M)

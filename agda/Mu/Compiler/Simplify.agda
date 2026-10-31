{-

  The simplify pass (FPC → FPC), a simplified version of the
  source optimizer cp0 of Chez Scheme, the first pass of compile
  (Mu/Compiler/Pipeline.agda): the untyped simplify
  (Compiler/Simplify.agda), intrinsically typed, with the same design,
  rules and policy, and one more known-value rule, for unfold.

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
  4. unfold of a known fold: unfold L, where L is known to be fold V,
     becomes V, as a projection (3) does (the rule that μ adds);
  5. β on a value: app (lam N) M, and likewise let x = M in N, where M
     becomes a value V, becomes N with V for its variable, which gives
     copy propagation and the elimination of dead bindings;
  6. inlining: app L M, where L is known to be a function λ N, becomes
     N's body, simplified at the call with its variable bound to M as in
     5 (simp-let), if the result is small enough (inline-size). The body
     is simplified again under the Facts of its definition and what is
     known of M, as in cp0; fuel (inline-fuel) bounds how deeply calls
     are inlined within inlined bodies, so the pass is structurally
     recursive.

  It only duplicates or discards values, and never reorders evaluation:
  a known value comes from evaluating a term that has no effect, so
  replacing that term by the value drops only that evaluation. In
  inlining, the operator L, known, is dropped, and the operand M stays
  bound, as cp0 does: a call f M becomes let x = M' in N', which
  evaluates M' once, before the body, and keeps it even if N' does not
  use it, unless M' is a value (5).

  Substitution policy: only small values are duplicated: variables,
  literals, ⟨⟩, and an injection of one of them (small). A small value
  substituted for a variable keeps what is known of it (a copy of a
  known function is known). Any other value (a function, a tuple, a
  nested injection, a fold) keeps its binding, as let x = V' in N', and
  the bound variable is known as V' is, so that a projection from it, a
  case on it or an unfold of it can still be folded, and a call of it
  inlined.

  What typing changes: Facts map the variables of the source's context
  Δ to Info in the target's Γ, and Info and Known are indexed by a
  context and a type, so the pass preserves types by construction. A
  known component, branch or unfolding is found by a test (component,
  branch, unfolded) that takes the operand's type generically, with an
  equation to the expected one, since a term cannot be split at a
  concrete type (unfold's type A [ μ A ] does not unify with one; the
  design note's green slime); for the same reason lam? recognizes a
  function at any type. Typed tuples need no test of their length.
  Renaming is the kit's (Mu/Language/FPCSubst.agda), which the
  reduction semantics shares.

-}

module Mu.Compiler.Simplify where

open import Framework.Primitives using (Int)
open import Language.Prim using (Prim; sub; eq)
open import Mu.Language.Type
open import Mu.Language.FPC
open import Mu.Language.FPCSubst using (ren)
open import Mu.Framework.AllUtil using (All; []; _∷_; lookup)

open import Data.Bool using (Bool; true; false; _∧_; if_then_else_)
open import Data.Integer using (ℤ; _-_; _≟_)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤ᵇ_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (does)

{- What is known -------------------------------------------------------------}

{- what simplify knows of a variable or a term of type A in Γ: the term
   that replaces it, and what it is known to be, if anything (Known) -}
infix 4 _∣_
record Info (Γ : Ctx) (A : Type) : Set
data Known (Γ : Ctx) : Type → Set

{- what simplify knows of each variable of Δ, in Γ -}
Facts : Ctx → Ctx → Set
Facts Δ Γ = ∀ {A} → Δ ∋ A → Info Γ A

{- a value (val), or a function λ N, its body N not yet simplified, with
   what was known of its variables where it was defined (fun) -}
data Known Γ where
  val : ∀ {A} → Tm Γ A → Known Γ A
  fun : ∀ {Δ A B} → Tm (A ∷ Δ) B → Facts Δ Γ → Known Γ (A ⇒ B)

record Info Γ A where
  inductive
  constructor _∣_
  field
    term : Tm Γ A
    known : Maybe (Known Γ A)
open Info public

{- a value, which is known to be itself -}
self : ∀ {Γ A} → Tm Γ A → Info Γ A
self V = V ∣ just (val V)

{- under one more binder -}
shift-info : ∀ {Γ A B} → Info Γ A → Info (B ∷ Γ) A
shift-known : ∀ {Γ A B} → Known Γ A → Known (B ∷ Γ) A
shift-mk : ∀ {Γ A B} → Maybe (Known Γ A) → Maybe (Known (B ∷ Γ) A)
shift-info I = ren S (term I) ∣ shift-mk (known I)
shift-mk nothing = nothing
shift-mk (just K) = just (shift-known K)
shift-known (val V) = val (ren S V)
shift-known (fun N E) = fun N (λ x → shift-info (E x))

{- variable 0 known as I is, and the rest as E says -}
infixr 5 _•_
_•_ : ∀ {Δ Γ B} → Info Γ B → Facts Δ Γ → Facts (B ∷ Δ) Γ
(I • E) Z = I
(I • E) (S x) = E x

{- under a binder that stays, whose variable is unknown -}
under : ∀ {Δ Γ B} → Facts Δ Γ → Facts (B ∷ Δ) (B ∷ Γ)
under E = self (` Z) • (λ x → shift-info (E x))

{- under a binder that stays, whose variable is known as I is -}
known-as : ∀ {Δ Γ B} → Info Γ B → Facts Δ Γ → Facts (B ∷ Δ) (B ∷ Γ)
known-as I E = ((` Z) ∣ known (shift-info I)) • (λ x → shift-info (E x))

{- Values --------------------------------------------------------------------}

{- values (syntactically: a variable stands for a value) -}
value : ∀ {Γ A} → Tm Γ A → Bool
values : ∀ {Γ Δ} → All (Tm Γ) Δ → Bool
value (` x) = true
value (lam _) = true
value (lit B c) = true
value (tuple Ms) = values Ms
value (inl M) = value M
value (inr M) = value M
value (fold M) = value M
value _ = false
values [] = true
values (M ∷ Ms) = value M ∧ values Ms

{- a term that is known to be itself if it is a value -}
info : ∀ {Γ A} → Tm Γ A → Info Γ A
info M = M ∣ (if value M then just (val M) else nothing)

{- the values that may be duplicated: variables, literals, ⟨⟩, and an
   injection of one of them -}
atom : ∀ {Γ A} → Tm Γ A → Bool
atom (` x) = true
atom (lit B c) = true
atom (tuple []) = true
atom _ = false

small : ∀ {Γ A} → Tm Γ A → Bool
small (inl M) = atom M
small (inr M) = atom M
small M = atom M

{- Known values ---------------------------------------------------------------}

{- the integer that a term is known to be -}
int-of : ∀ {Γ A} → Maybe (Known Γ A) → Maybe ℤ
int-of (just (val (lit Int n))) = just n
int-of _ = nothing

{- component i of a tuple that a term of type C = tup Δ is known to be -}
component : ∀ {Γ C Δ A} → Δ ∋ A → Maybe (Known Γ C) → C ≡ tup Δ → Maybe (Tm Γ A)
component i (just (val (tuple Ks))) refl = just (lookup Ks i)
component i _ _ = nothing

{- the branch that a case on a term of type C = A ⊹ B known to be an
   injection takes, and the value it binds, if that value is small -}
branch : ∀ {Γ C A B} → Maybe (Known Γ C) → C ≡ A ⊹ B → Maybe (Tm Γ A ⊎ Tm Γ B)
branch (just (val (inl K))) refl = if small K then just (inj₁ K) else nothing
branch (just (val (inr K))) refl = if small K then just (inj₂ K) else nothing
branch _ _ = nothing

{- the value under a fold that a term of type C = μ A is known to be -}
unfolded : ∀ {Γ C A} → Maybe (Known Γ C) → C ≡ μ A → Maybe (Tm Γ (unroll A))
unfolded (just (val (fold K))) refl = just K
unfolded _ _ = nothing

{- the term of a primitive's result -}
prim-term : ∀ {Γ} p → ℤ → ℤ → Tm Γ (out-ty p)
prim-term sub n m = lit Int (n - m)
prim-term eq n m = if does (n ≟ m) then inl (tuple []) else inr (tuple [])

{- the size of a term -}
size : ∀ {Γ A} → Tm Γ A → ℕ
sizes : ∀ {Γ Δ} → All (Tm Γ) Δ → ℕ
size (` x) = 1
size (lam N) = suc (size N)
size (app L M) = suc (size L + size M)
size (lit B c) = 1
size (tuple Ms) = suc (sizes Ms)
size (get i M) = suc (size M)
size (inl M) = suc (size M)
size (inr M) = suc (size M)
size (case L M N) = suc (size L + (size M + size N))
size (prim p L M) = suc (size L + size M)
size (let′ M N) = suc (size M + size N)
size (fold M) = suc (size M)
size (unfold M) = suc (size M)
sizes [] = 0
sizes (M ∷ Ms) = size M + sizes Ms

{- inlining: the depth of nested inlining (fuel), and the size up to which
   a function's body, simplified at the call, is inlined -}
inline-fuel inline-size : ℕ
inline-fuel = 4
inline-size = 24

{- whether a term is a function (at any type) -}
data Lam? {Γ} : ∀ {C} → Tm Γ C → Set where
  is-lam : ∀ {A B} (N : Tm (A ∷ Γ) B) → Lam? (lam N)
  other : ∀ {C} {L : Tm Γ C} → Lam? L

lam? : ∀ {Γ C} (L : Tm Γ C) → Lam? L
lam? (lam N) = is-lam N
lam? L = other

{- The pass -------------------------------------------------------------------}

simp : ∀ {Δ Γ A} → ℕ → Facts Δ Γ → Tm Δ A → Info Γ A
simps : ∀ {Δ Γ Δ'} → ℕ → Facts Δ Γ → All (Tm Δ) Δ' → All (Tm Γ) Δ'
simp-app : ∀ {Δ Γ A B} → ℕ → Facts Δ Γ → Tm Δ (A ⇒ B) → Info Γ A → Info Γ B
simp-call : ∀ {Γ A B} → ℕ → Info Γ (A ⇒ B) → Info Γ A → Info Γ B
simp-let : ∀ {Δ Γ A B} → ℕ → Facts Δ Γ → Tm (A ∷ Δ) B → Info Γ A → Info Γ B
simp-get : ∀ {Γ Δ A} → Δ ∋ A → Info Γ (tup Δ) → Info Γ A
simp-case : ∀ {Δ Γ A B C} → ℕ → Facts Δ Γ → Info Γ (A ⊹ B) → Tm (A ∷ Δ) C → Tm (B ∷ Δ) C → Info Γ C
simp-prim : ∀ {Γ} p → Info Γ (base Int) → Info Γ (base Int) → Info Γ (out-ty p)
simp-unfold : ∀ {Γ A} → Info Γ (μ A) → Info Γ (unroll A)

simp f E (` x) = E x
simp f E (lam N) = lam (term (simp f (under E) N)) ∣ just (fun N E)
simp f E (app L M) = simp-app f E L (simp f E M)
simp f E (lit B c) = self (lit B c)
simp f E (tuple Ms) = info (tuple (simps f E Ms))
simp f E (get i L) = simp-get i (simp f E L)
simp f E (inl M) = info (inl (term (simp f E M)))
simp f E (inr M) = info (inr (term (simp f E M)))
simp f E (case L M N) = simp-case f E (simp f E L) M N
simp f E (prim p L M) = simp-prim p (simp f E L) (simp f E M)
simp f E (let′ M N) = simp-let f E N (simp f E M)
simp f E (fold M) = info (fold (term (simp f E M)))
simp f E (unfold L) = simp-unfold (simp f E L)

simps f E [] = []
simps f E (M ∷ Ms) = term (simp f E M) ∷ simps f E Ms

{- an application: β, if the operator is a function, and otherwise a call -}
simp-app f E L I with lam? L
... | is-lam N = simp-let f E N I
... | other = simp-call f (simp f E L) I

{- a call of a known function λ N, with fuel: its body is simplified at
   the call, with the operand bound (simp-let), and inlined if the result
   is small enough. The operator, known, has no effect, and is dropped -}
simp-call (suc f) (T ∣ just (fun N E)) I with size (term (simp-let f E N I)) ≤ᵇ inline-size
... | true = simp-let f E N I
... | false = app T (term I) ∣ nothing
simp-call f J I = app (term J) (term I) ∣ nothing

{- the body N of a function, applied to the operand I, or of a let that
   binds I: a small value is substituted, and known as I is; another value
   stays bound by a let, and known; anything else stays bound by a let -}
simp-let f E N I with small (term I) | value (term I)
... | true | _ = simp f (I • E) N
... | false | true = let′ (term I) (term (simp f (known-as I E) N)) ∣ nothing
... | false | false = let′ (term I) (term (simp f (under E) N)) ∣ nothing

{- a projection from a known tuple: the component, if it is small, and
   otherwise the projection, known to be the component -}
simp-get i I with component i (known I) refl
... | just K = if small K then self K else (get i (term I) ∣ just (val K))
... | nothing = get i (term I) ∣ nothing

{- a case on a known injection: the branch it takes -}
simp-case f E I M N with branch (known I) refl
... | just (inj₁ K) = simp f (self K • E) M
... | just (inj₂ K) = simp f (self K • E) N
... | nothing = case (term I) (term (simp f (under E) M)) (term (simp f (under E) N)) ∣ nothing

{- a primitive on known integers: its result -}
simp-prim p I J with int-of (known I)
... | nothing = prim p (term I) (term J) ∣ nothing
... | just n with int-of (known J)
...   | nothing = prim p (term I) (term J) ∣ nothing
...   | just m = self (prim-term p n m)

{- an unfold of a known fold: the value under it, if it is small, and
   otherwise the unfold, known to be that value (as simp-get) -}
simp-unfold I with unfolded (known I) refl
... | just K = if small K then self K else (unfold (term I) ∣ just (val K))
... | nothing = unfold (term I) ∣ nothing

{- the pass, for a whole program: every variable is itself, and unknown -}
simplify : ∀ {A} → Tm [] A → Tm [] A
simplify M = term (simp inline-fuel (λ x → self (` x)) M)

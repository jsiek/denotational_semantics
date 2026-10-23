{-

  Correctness of the simplify pass (ISWIMμ → ISWIMμ) by a forward
  simulation of the target's machine by the source's, as for the untyped
  simplify (proof/Correctness/CEK/SimplifySim.agda; see the design note
  in Semantics/CEK/Smallstep.agda); Equivalent is symmetric.

  The target does less work than the source: the reductions simplify did
  ahead of time (β of a small value, an inlined call, a case on a known
  injection, a projection from a known tuple, an unfold of a known
  fold, a primitive on known integers) are steps of the source only,
  which it takes when the target takes the corresponding one. But the
  target does more work in one place: it evaluates a small value (inl 3,
  say) where the source looks up a variable, and it evaluates the value
  of a let that simplify kept, where the source has run ahead. There the
  target stutters: a match is indexed by the number of target steps
  until a state related to the current source state (match).

  Values are related (_≈_) when they agree, except that a target closure
  is the simplified body of a source closure, under Facts that are true
  of the two environments (Ok): the term that replaces each variable
  denotes, in the target's environment, a value related to the source's
  (Strong), and what it is known to be describes it (KDen): a known
  value the same way, up to functions (Den), and a known function λ N
  as a source closure of N, under Facts true of its environment. States
  and continuations are related frame by frame, the code by simp.

  The source's run ahead is by run: if the term that simp E M returns is
  a value, or M has a known value (Ask), the source runs M to a value it
  describes. β and an inlined call share one lemma each (let-run,
  let-sim), from the source's run to the operand:
  for an inlined call, the source first runs the operator to the known
  function's closure. Typed states have no unbound variable and no
  value of the wrong kind, so no step of either machine stops with an
  error, and the theorem holds for every closed program.

-}

module Mu.proof.Correctness.AbstractMachines.SimplifySim where

open import Framework.Primitives using (Int)
open import Language.Prim using (Prim)
import Language.Prim as Pr
open import Mu.Language.Type
open import Mu.Language.ISWIM
open import Mu.Language.ISWIMSubst using (ren; travs; varK)
open import Mu.Framework.AllUtil using (All; []; _∷_; lookup; _<><_; _<><ᵃ_; All₂; lookup₂; _<><₂_)
open import Mu.proof.Compiler.SimplifyFacts as P
  using (Info; _∣_; term; known; Known; Facts; self; info; under; known-as; shift-info; shift-known; simp; simps;
         lam?; is-lam; other; simp-call; size; inline-size; inline-fuel;
         simp-app; simp-let; simp-get; simp-case; simp-prim; simp-unfold; simplify; small; atom; value; values;
         component; branch; unfolded; int-of; prim-term; value-sv; small-sv; comp-inv; int-inv; branch-inl; branch-inr;
         unfold-inv)
open import Semantics.Observation
open import proof.Semantics.CEK.Smallstep
open import proof.Semantics.CEK.Simulation
import Mu.Semantics.AbstractMachines.ISWIM as S

open import Data.Bool using (Bool; true; false; _∧_; if_then_else_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Integer using (_≟_)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _≤ᵇ_)
open import Data.Product using (_×_; Σ-syntax; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Function using (flip)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)
open import Relation.Nullary using (does)

{- The relation ------------------------------------------------------------------}

infix 4 _≈_ _≈k_ _~_

data _≈_ : ∀ {A} → S.Val A → S.Val A → Set
{- v is related to a value that the value term T denotes in ρ' (Strong);
   or the same, but a function describes any value (Den) -}
Desc : Bool → ∀ {Γ A} → S.Val A → Tm Γ A → S.Env Γ → Set
Descs : Bool → ∀ {Γ Δ} → All S.Val Δ → All (Tm Γ) Δ → S.Env Γ → Set
Strong Den : ∀ {Γ A} → S.Val A → Tm Γ A → S.Env Γ → Set
Strong = Desc true
Den = Desc false

{- what simp knows of each variable is true of the source's environment ρ
   and the target's ρ' -}
record Ok {Δ Γ} (E : Facts Δ Γ) (ρ : S.Env Δ) (ρ' : S.Env Γ) : Set
{- what simp knows a term is describes v: a value, or a function λ N closed
   in a source environment ρ of which its Facts are true (KDen) -}
KDen : ∀ {Γ A} → S.Val A → Known Γ A → S.Env Γ → Set
Kn : ∀ {Γ A} → S.Val A → Info Γ A → S.Env Γ → Set
Kn v I ρ' = ∀ {K} → known I ≡ just K → KDen v K ρ'

record Ok {Δ} E ρ ρ' where
  inductive
  constructor mk-ok
  field
    trm : ∀ {A} (x : Δ ∋ A) → Strong (lookup ρ x) (term (E x)) ρ'
    knw : ∀ {A} (x : Δ ∋ A) → Kn (lookup ρ x) (E x) ρ'
    sml : ∀ {A} (x : Δ ∋ A) → small (term (E x)) ≡ true

{- the source's value on the left -}
data _≈_ where
  clo≈ : ∀ {fl Δ Γ A B} {E : Facts Δ Γ} {N : Tm (A ∷ Δ) B} {ρ ρ'} → Ok E ρ ρ'
    → S.clo N ρ ≈ S.clo (term (simp fl (under E) N)) ρ'
  const≈ : ∀ {B c} → S.const {B} c ≈ S.const c
  tup≈ : ∀ {Δ} {vs ws : All S.Val Δ} → All₂ _≈_ vs ws → S.tup vs ≈ S.tup ws
  inl≈ : ∀ {A B v w} → v ≈ w → S.inl {A} {B} v ≈ S.inl w
  inr≈ : ∀ {A B v w} → v ≈ w → S.inr {A} {B} v ≈ S.inr w
  fold≈ : ∀ {A v w} → v ≈ w → S.fold {A} v ≈ S.fold w

Desc b v (` y) ρ' = v ≈ lookup ρ' y
Desc true v (lam N) ρ' = v ≈ S.clo N ρ'
Desc false v (lam N) ρ' = ⊤
Desc b v (lit B c) ρ' = v ≡ S.const c
Desc b v (tuple Ms) ρ' = Σ[ vs ∈ All S.Val _ ] v ≡ S.tup vs × Descs b vs Ms ρ'
Desc b v (inl M) ρ' = Σ[ v₀ ∈ S.Val _ ] v ≡ S.inl v₀ × Desc b v₀ M ρ'
Desc b v (inr M) ρ' = Σ[ v₀ ∈ S.Val _ ] v ≡ S.inr v₀ × Desc b v₀ M ρ'
Desc b v (fold M) ρ' = Σ[ v₀ ∈ S.Val _ ] v ≡ S.fold v₀ × Desc b v₀ M ρ'
Desc b v _ ρ' = ⊥
Descs b [] [] ρ' = ⊤
Descs b (v ∷ vs) (M ∷ Ms) ρ' = Desc b v M ρ' × Descs b vs Ms ρ'

KDen v (P.val K) ρ' = Den v K ρ'
KDen v (P.fun {Δ} N E) ρ' = Σ[ ρ ∈ S.Env Δ ] v ≡ S.clo N ρ × Ok E ρ ρ'

Strongs Dens : ∀ {Γ Δ} → All S.Val Δ → All (Tm Γ) Δ → S.Env Γ → Set
Strongs = Descs true
Dens = Descs false

open Ok

{- the source frames that bind the variable of a body N in ρ: the call of
   a closure (β, an inlined call), and a let -}
data Binds {Δ A B} (N : Tm (A ∷ Δ) B) (ρ : S.Env Δ) : (S.Cont B → S.Cont A) → Set where
  by-app : Binds N ρ (S.appR (S.clo N ρ))
  by-let : Binds N ρ (S.letK N ρ)

bind-step : ∀ {Δ A B} {N : Tm (A ∷ Δ) B} {ρ G v κ} → Binds N ρ G → S.step (S.ret v (G κ)) ≡ next (S.eval N (v ∷ ρ) κ)
bind-step by-app = refl
bind-step by-let = refl

data _≈k_ : ∀ {A} → S.Cont A → S.Cont A → Set where
  halt : ∀ {A} → S.halt {A} ≈k S.halt
  appL : ∀ {fl Δ Γ A B} {E : Facts Δ Γ} {M : Tm Δ A} {ρ ρ'} {κ κ' : S.Cont B} → Ok E ρ ρ' → κ ≈k κ'
    → S.appL M ρ κ ≈k S.appL (term (simp fl E M)) ρ' κ'
  appR : ∀ {A B} {v v' : S.Val (A ⇒ B)} {κ κ'} → v ≈ v' → κ ≈k κ' → S.appR v κ ≈k S.appR v' κ'
  tupK : ∀ {fl Δ Γ Δ' A Δ''} {E : Facts Δ Γ} {vs vs' : All S.Val Δ'} {Ms : All (Tm Δ) Δ''} {ρ ρ'}
    {κ κ' : S.Cont (tup (Δ' <>< (A ∷ Δ'')))} → All₂ _≈_ vs vs' → Ok E ρ ρ' → κ ≈k κ'
    → S.tupK vs Ms ρ κ ≈k S.tupK vs' (simps fl E Ms) ρ' κ'
  getK : ∀ {Δ A} {i : Δ ∋ A} {κ κ'} → κ ≈k κ' → S.getK i κ ≈k S.getK i κ'
  inlK : ∀ {A B} {κ κ' : S.Cont (A ⊹ B)} → κ ≈k κ' → S.inlK κ ≈k S.inlK κ'
  inrK : ∀ {A B} {κ κ' : S.Cont (A ⊹ B)} → κ ≈k κ' → S.inrK κ ≈k S.inrK κ'
  caseK : ∀ {fl Δ Γ A B C} {E : Facts Δ Γ} {M : Tm (A ∷ Δ) C} {N : Tm (B ∷ Δ) C} {ρ ρ' κ κ'} → Ok E ρ ρ' → κ ≈k κ'
    → S.caseK M N ρ κ ≈k S.caseK (term (simp fl (under E) M)) (term (simp fl (under E) N)) ρ' κ'
  primL : ∀ {p fl Δ Γ} {E : Facts Δ Γ} {M : Tm Δ (base Int)} {ρ ρ' κ κ'} → Ok E ρ ρ' → κ ≈k κ'
    → S.primL p M ρ κ ≈k S.primL p (term (simp fl E M)) ρ' κ'
  primR : ∀ {p n κ κ'} → κ ≈k κ' → S.primR p n κ ≈k S.primR p n κ'
  {- a let that simplify kept, of a source β, inlined call or let -}
  letK : ∀ {fl Δ Γ A B} {E : Facts Δ Γ} {N : Tm (A ∷ Δ) B} {ρ ρ' G κ κ'} → Binds N ρ G → Ok E ρ ρ' → κ ≈k κ'
    → G κ ≈k S.letK (term (simp fl (under E) N)) ρ' κ'
  foldK : ∀ {A} {κ κ' : S.Cont (μ A)} → κ ≈k κ' → S.foldK {A} κ ≈k S.foldK κ'
  unfoldK : ∀ {A} {κ κ' : S.Cont (unroll A)} → κ ≈k κ' → S.unfoldK {A} κ ≈k S.unfoldK κ'

data _~_ : S.State → S.State → Set where
  eval~ : ∀ {fl Δ Γ A} {E : Facts Δ Γ} {M : Tm Δ A} {ρ ρ' κ κ'} → Ok E ρ ρ' → κ ≈k κ'
    → S.eval M ρ κ ~ S.eval (term (simp fl E M)) ρ' κ'
  ret~ : ∀ {A} {v v' : S.Val A} {κ κ'} → v ≈ v' → κ ≈k κ' → S.ret v κ ~ S.ret v' κ'

{- Related values are observed alike -------------------------------------------}

obs≈ : ∀ {A} {v w : S.Val A} → v ≈ w → S.obs v ≡ S.obs w
obs≈* : ∀ {Δ} {vs ws : All S.Val Δ} → All₂ _≈_ vs ws → S.obs-all vs ≡ S.obs-all ws
obs≈ (clo≈ _) = refl
obs≈ const≈ = refl
obs≈ (tup≈ rs) = cong o-tuple (obs≈* rs)
obs≈ (inl≈ r) = cong o-inl (obs≈ r)
obs≈ (inr≈ r) = cong o-inr (obs≈ r)
obs≈ (fold≈ r) = obs≈ r
obs≈* [] = refl
obs≈* (r ∷ rs) = cong₂ _∷_ (obs≈ r) (obs≈* rs)

δ≈ : ∀ p n m → S.δᵀ p n m ≈ S.δᵀ p n m
δ≈ Pr.sub n m = const≈
δ≈ Pr.eq n m with does (n ≟ m)
... | true = inl≈ (tup≈ [])
... | false = inr≈ (tup≈ [])

{- Describing values --------------------------------------------------------------}

strong-den : ∀ {Γ A} (T : Tm Γ A) {ρ' v} → Strong v T ρ' → Den v T ρ'
strongs-den : ∀ {Γ Δ} (Ms : All (Tm Γ) Δ) {ρ' vs} → Strongs vs Ms ρ' → Dens vs Ms ρ'
strong-den (` y) d = d
strong-den (lam N) d = tt
strong-den (lit B c) d = d
strong-den (tuple Ms) (vs , e , ds) = vs , e , strongs-den Ms ds
strong-den (inl M) (v , e , d) = v , e , strong-den M d
strong-den (inr M) (v , e , d) = v , e , strong-den M d
strong-den (fold M) (v , e , d) = v , e , strong-den M d
strongs-den [] {vs = []} d = tt
strongs-den (M ∷ Ms) {vs = v ∷ vs} (d , ds) = strong-den M d , strongs-den Ms ds

{- a small value has no functions -}
atom-strong : ∀ {Γ A} (T : Tm Γ A) {ρ' v} → atom T ≡ true → Den v T ρ' → Strong v T ρ'
atom-strong (` y) _ d = d
atom-strong (lit B c) _ d = d
atom-strong (tuple []) _ ([] , e , _) = [] , e , tt

small-strong : ∀ {Γ A} (T : Tm Γ A) {ρ' v} → small T ≡ true → Den v T ρ' → Strong v T ρ'
small-strong (inl M) s (v , e , d) = v , e , atom-strong M s d
small-strong (inr M) s (v , e , d) = v , e , atom-strong M s d
small-strong (` y) s d = d
small-strong (lit B c) s d = d
small-strong (tuple []) s ([] , e , _) = [] , e , tt

atom-shift : ∀ {Γ A B} (T : Tm Γ A) → atom T ≡ true → atom (ren (S {b = B}) T) ≡ true
atom-shift (` y) s = refl
atom-shift (lit B c) s = refl
atom-shift (tuple []) s = refl

small-shift : ∀ {Γ A B} (T : Tm Γ A) → small T ≡ true → small (ren (S {b = B}) T) ≡ true
small-shift (inl M) s = atom-shift M s
small-shift (inr M) s = atom-shift M s
small-shift (` y) s = refl
small-shift (lit B c) s = refl
small-shift (tuple []) s = refl

den-shift : ∀ {Γ A B} (K : Tm Γ A) {ρ' v} {w : S.Val B} → Den v K ρ' → Den v (ren S K) (w ∷ ρ')
dens-shift : ∀ {Γ Δ B} (Ms : All (Tm Γ) Δ) {ρ' vs} {w : S.Val B} → Dens vs Ms ρ' → Dens vs (travs varK S Ms) (w ∷ ρ')
den-shift (` y) d = d
den-shift (lam N) d = tt
den-shift (lit B c) d = d
den-shift (tuple Ms) (vs , e , ds) = vs , e , dens-shift Ms ds
den-shift (inl M) (v , e , d) = v , e , den-shift M d
den-shift (inr M) (v , e , d) = v , e , den-shift M d
den-shift (fold M) (v , e , d) = v , e , den-shift M d
dens-shift [] {vs = []} d = tt
dens-shift (M ∷ Ms) {vs = v ∷ vs} (d , ds) = den-shift M d , dens-shift Ms ds

{- under one more variable, in the target -}
strong-shift : ∀ {Γ A B} (T : Tm Γ A) {ρ' v} {w : S.Val B} → small T ≡ true → Strong v T ρ' → Strong v (ren S T) (w ∷ ρ')
strong-shift T s d = small-strong (ren S T) (small-shift T s) (den-shift T (strong-den T d))

{- the result of a primitive -}
prim-strong : ∀ {Γ} p n m {ρ' : S.Env Γ} → Strong (S.δᵀ p n m) (prim-term p n m) ρ'
prim-strong Pr.sub n m = refl
prim-strong Pr.eq n m with does (n ≟ m)
... | true = S.tup [] , refl , [] , refl , tt
... | false = S.tup [] , refl , [] , refl , tt

{- a component of a described tuple -}
dens-lookup : ∀ {Γ Δ A} {Ks : All (Tm Γ) Δ} {ρ' vs} → Dens vs Ks ρ' → (i : Δ ∋ A) → Den (lookup vs i) (lookup Ks i) ρ'
dens-lookup {Ks = K ∷ Ks} {vs = v ∷ vs} (d , ds) Z = d
dens-lookup {Ks = K ∷ Ks} {vs = v ∷ vs} (d , ds) (S i) = dens-lookup ds i

{- Facts --------------------------------------------------------------------------}

{- under one more variable, in the target only -}
kden-shift : ∀ {Γ A B} (K : Known Γ A) {ρ' v} {w : S.Val B} → KDen v K ρ' → KDen v (shift-known K) (w ∷ ρ')
kn-shift : ∀ {Γ A B} (I : Info Γ A) {ρ' v} {w : S.Val B} → Kn v I ρ' → Kn v (shift-info I) (w ∷ ρ')
ok-weak : ∀ {Δ Γ B} {E : Facts Δ Γ} {ρ ρ'} {w : S.Val B} → Ok E ρ ρ' → Ok (λ x → shift-info (E x)) ρ (w ∷ ρ')
kden-shift (P.val K) d = den-shift K d
kden-shift (P.fun N E) (ρ , refl , ok) = ρ , refl , ok-weak ok
kn-shift (T ∣ just K) h refl = kden-shift K (h refl)
ok-weak {E = E} ok = mk-ok (λ x → strong-shift (term (E x)) (sml ok x) (trm ok x)) (λ x → kn-shift (E x) (knw ok x))
                           (λ x → small-shift (term (E x)) (sml ok x))

{- variable 0 known as I is, in the source only -}
ok-cons : ∀ {Δ Γ A} {E : Facts Δ Γ} {ρ ρ'} {I : Info Γ A} {v} → Ok E ρ ρ' → Strong v (term I) ρ' → Kn v I ρ'
  → small (term I) ≡ true → Ok (I P.• E) (v ∷ ρ) ρ'
ok-cons ok d k s = mk-ok (λ { Z → d ; (S x) → trm ok x }) (λ { Z → k ; (S x) → knw ok x })
                         (λ { Z → s ; (S x) → sml ok x })

ok-self : ∀ {Δ Γ A} {E : Facts Δ Γ} {ρ ρ'} {T : Tm Γ A} {v} → Ok E ρ ρ' → small T ≡ true → Strong v T ρ'
  → Ok (self T P.• E) (v ∷ ρ) ρ'
ok-self {T = T} ok s d = ok-cons ok d (λ { refl → strong-den T d }) s

{- under a binder that stays -}
ok-under : ∀ {Δ Γ A} {E : Facts Δ Γ} {ρ ρ'} {v v' : S.Val A} → Ok E ρ ρ' → v ≈ v' → Ok (under E) (v ∷ ρ) (v' ∷ ρ')
ok-under ok r = ok-cons (ok-weak ok) r (λ { refl → r }) refl

{- a value known as I is, that stays bound to variable 0 -}
ok-let : ∀ {Δ Γ A} {E : Facts Δ Γ} {ρ ρ'} {I : Info Γ A} {v w} → Ok E ρ ρ' → v ≈ w → Kn v I ρ'
  → Ok (known-as I E) (v ∷ ρ) (w ∷ ρ')
ok-let {I = I} ok r k = ok-cons (ok-weak ok) r (kn-shift I k) refl

{- What is asked of what simp returns, I: that its term is a value, which
   then describes the source's value (Strong); or that it is known as K,
   which then describes it (KDen) -}
data Ask {Γ A} : Set where
  is-val : Ask
  is-known : Known Γ A → Ask

Holds : ∀ {Γ A} → Ask {Γ} {A} → Info Γ A → Set
Holds is-val I = value (term I) ≡ true
Holds (is-known K) I = known I ≡ just K

Gives : ∀ {Γ A} → Ask {Γ} {A} → Info Γ A → S.Val A → S.Env Γ → Set
Gives is-val I v ρ' = Strong v (term I) ρ'
Gives (is-known K) I v ρ' = KDen v K ρ'

absurd : ∀ {X : Set} → true ≡ false → X
absurd ()

{- nothing is asked of an unknown term that is not a value -}
no-ask : ∀ {Γ A} q {T : Tm Γ A} {X : Set} → value T ≡ false → Holds q (T ∣ nothing) → X
no-ask is-val nv e = absurd (trans (sym e) nv)
no-ask (is-known K) nv ()

{- a value term known to be itself -}
self-gives : ∀ {Γ A} q (T : Tm Γ A) {v ρ'} → Holds q (self T) → Strong v T ρ' → Gives q (self T) v ρ'
self-gives is-val T e d = d
self-gives (is-known K) T refl d = strong-den T d

{- The simulation, for any target program P' and source program P -------------}

module _ {T₀ : Type} (P P' : Tm [] T₀) where

  {- the target's machine (L₁) is simulated by the source's (L₂) -}
  L₁ = S.sem P'
  L₂ = S.sem P

  {- the target is i steps from a state related to the source's -}
  match = Lag L₁ (flip _~_)

  {- a run of the source from an evaluation to a return has a step -}
  run-plus : ∀ {Γ A} {M : Tm Γ A} {ρ κ v} → Star L₂ (S.eval M ρ κ) (S.ret v κ) → Plus L₂ (S.eval M ρ κ) (S.ret v κ)
  run-plus (st ◅ σ) = plus st σ

  Run : ∀ {Γ A} → Tm Γ A → S.Env Γ → S.Val A → Set
  Run M ρ v = ∀ κ → Star L₂ (S.eval M ρ κ) (S.ret v κ)

  Run′ : ∀ {Γ A} → Tm Γ A → S.Env Γ → S.Val A → Set
  Run′ M ρ v = ∀ κ → Star L₁ (S.eval M ρ κ) (S.ret v κ)

  {- The target evaluates value terms -}

  trun : ∀ {Γ A} (T : Tm Γ A) {ρ' v} → Strong v T ρ' → Σ[ w ∈ S.Val A ] Run′ T ρ' w × v ≈ w
  truns : ∀ {Γ Δ} (Ms : All (Tm Γ) Δ) {ρ' vs} → Strongs vs Ms ρ'
    → ∀ {Δ'} {acc acc' : All S.Val Δ'} → All₂ _≈_ acc acc'
    → Σ[ ws ∈ All S.Val Δ ] (∀ κ → Star L₁ (S.tuple-next acc' Ms ρ' κ) (S.ret (S.tup (acc' <><ᵃ ws)) κ))
        × All₂ _≈_ (acc <><ᵃ vs) (acc' <><ᵃ ws)
  trun (` y) r = _ , (λ κ → refl ◅ ε) , r
  trun (lam N) r = _ , (λ κ → refl ◅ ε) , r
  trun (lit B c) refl = _ , (λ κ → refl ◅ ε) , const≈
  trun (tuple Ms) (vs , refl , ds) with truns Ms ds {acc = []} {[]} []
  ... | ws , σ , rs = S.tup ws , (λ κ → refl ◅ σ κ) , tup≈ rs
  trun (inl M) (v , refl , d) with trun M d
  ... | w , σ , r = S.inl w , (λ κ → refl ◅ (σ (S.inlK κ) ◅◅ (refl ◅ ε))) , inl≈ r
  trun (inr M) (v , refl , d) with trun M d
  ... | w , σ , r = S.inr w , (λ κ → refl ◅ (σ (S.inrK κ) ◅◅ (refl ◅ ε))) , inr≈ r
  trun (fold M) (v , refl , d) with trun M d
  ... | w , σ , r = S.fold w , (λ κ → refl ◅ (σ (S.foldK κ) ◅◅ (refl ◅ ε))) , fold≈ r
  truns [] {vs = []} tt rs = [] , (λ κ → ε) , rs <><₂ []
  truns (M ∷ Ms) {ρ'} {vs = v ∷ vs} (d , ds) {acc' = acc'} rs with trun M d
  ... | w , σ , r with truns Ms ds (r ∷ rs)
  ...   | ws , τ , rs' = w ∷ ws , (λ κ → σ (S.tupK acc' Ms ρ' κ) ◅◅ (refl ◅ τ κ)) , rs'

  {- Answers whose target takes a step -}
  record Step-ans (s s' : S.State) : Set where
    constructor ans
    field
      {t} : S.State
      t-step : S.step s' ≡ next t
      {j} : ℕ
      {s₁} : S.State
      s-plus : Plus L₂ s s₁
      t-match : match j t s₁

  prefix : ∀ {s s' s₀} → Star L₂ s s₀ → Step-ans s₀ s' → Step-ans s s'
  prefix σ (ans e π m) = ans e (star-plus σ π) m

  {- a value term against a run of the source to a value it describes -}
  value-ans : ∀ {Γ Δ A} (T : Tm Γ A) {M : Tm Δ A} {ρ ρ' v κ κ'} → Strong v T ρ' → Run M ρ v → κ ≈k κ'
    → Step-ans (S.eval M ρ κ) (S.eval T ρ' κ')
  value-ans T d σ k with trun T d
  ... | w , τ , r with τ _
  ...   | st ◅ τ' with lag-star τ' (ret~ r k)
  ...     | j , m = ans st (run-plus (σ _)) m

  {- the source runs to one value -}
  run-unique : ∀ {A s} {v w : S.Val A} → Star L₂ s (S.ret v S.halt) → Star L₂ s (S.ret w S.halt) → v ≡ w
  run-unique ε ε = refl
  run-unique ε (() ◅ _)
  run-unique (() ◅ _) ε
  run-unique {s = s} (st ◅ σ) (st' ◅ τ) with step-det {L = L₂} {s} st st'
  ... | refl = run-unique σ τ

  {- The source runs ahead: run -}

  {- if what simp returns, I, has what is asked, the source runs M in ρ to
     a value that I describes -}
  Ans : ∀ {Δ Γ A} → Ask {Γ} {A} → Tm Δ A → S.Env Δ → Info Γ A → S.Env Γ → Set
  Ans q M ρ I ρ' = Holds q I → Σ[ v ∈ S.Val _ ] Run M ρ v × Gives q I v ρ'

  {- what simp knows of an operand I is true of the source's M, if I is a
     value; and of an operator J of the source's L -}
  Opd : ∀ {Δ Γ A} → Tm Δ A → S.Env Δ → Info Γ A → S.Env Γ → Set
  Opd M ρ I ρ' = value (term I) ≡ true → Σ[ v ∈ S.Val _ ] Run M ρ v × Strong v (term I) ρ' × Kn v I ρ'
  Fn : ∀ {Δ Γ A} → Tm Δ A → S.Env Δ → Info Γ A → S.Env Γ → Set
  Fn L ρ J ρ' = ∀ {K} → Ans (is-known K) L ρ J ρ'

  {- a term known to be itself if it is a value (info) -}
  info-known : ∀ {Δ Γ A} (T : Tm Γ A) {M : Tm Δ A} {ρ ρ' K} → Ans is-val M ρ (info T) ρ' → Ans (is-known K) M ρ (info T) ρ'
  info-known T r k with value T
  info-known T r refl | true with r refl
  ... | v , σ , d = v , σ , strong-den T d

  {- a known component or unfolding K: itself if it is small, and
     otherwise the term T, known as K -}
  small-run : ∀ {Δ Γ A} q (K : Tm Γ A) {T : Tm Γ A} {M : Tm Δ A} {ρ ρ'} → value T ≡ false
    → Σ[ v ∈ S.Val A ] Run M ρ v × Den v K ρ' → Ans q M ρ (if small K then self K else (T ∣ just (P.val K))) ρ'
  small-run q K nv r e with small K in s
  small-run is-val K nv (v , σ , d) e | true = v , σ , small-strong K s d
  small-run is-val K nv r e | false = absurd (trans (sym e) nv)
  small-run (is-known _) K nv r refl | true = r
  small-run (is-known _) K nv r refl | false = r

  {- under a frame F that wraps the value: inl, inr or fold (c) -}
  wrap : ∀ {Δ Γ A B} {W : Tm Δ B} {M : Tm Δ A} {T : Tm Γ A} {ρ ρ'} {c : S.Val A → S.Val B} {F : S.Cont B → S.Cont A}
    → (∀ {κ} → S.step (S.eval W ρ κ) ≡ next (S.eval M ρ (F κ))) → (∀ {v κ} → S.step (S.ret v (F κ)) ≡ next (S.ret (c v) κ))
    → Σ[ v ∈ S.Val A ] Run M ρ v × Strong v T ρ' → Σ[ w ∈ S.Val B ] Run W ρ w × Σ[ v ∈ S.Val A ] w ≡ c v × Strong v T ρ'
  wrap st st' (v , σ , d) = _ , (λ κ → st ◅ (σ _ ◅◅ (st' ◅ ε))) , v , refl , d

  run : ∀ {Δ Γ A} q fl (M : Tm Δ A) {E : Facts Δ Γ} {ρ ρ'} → Ok E ρ ρ' → Ans q M ρ (simp fl E M) ρ'
  run-tuple : ∀ {Δ Γ Δ'} fl (Ms : All (Tm Δ) Δ') {E : Facts Δ Γ} {ρ ρ'} → Ok E ρ ρ' → Ans is-val (tuple Ms) ρ (simp fl E (tuple Ms)) ρ'
  run-terms : ∀ {Δ Γ Δ''} fl (Ms : All (Tm Δ) Δ'') {E : Facts Δ Γ} {ρ ρ'} → Ok E ρ ρ' → values (simps fl E Ms) ≡ true
    → ∀ {Δ'} {acc : All S.Val Δ'} → Σ[ vs ∈ All S.Val Δ'' ] (∀ κ → Star L₂ (S.tuple-next acc Ms ρ κ) (S.ret (S.tup (acc <><ᵃ vs)) κ))
        × Strongs vs (simps fl E Ms) ρ'
  {- a component of a known tuple -}
  run-get : ∀ {Δ Γ Δ' A} fl (i : Δ' ∋ A) (L : Tm Δ (tup Δ')) {E : Facts Δ Γ} {ρ ρ' K} → Ok E ρ ρ'
    → component i (known (simp fl E L)) refl ≡ just K → Σ[ v ∈ S.Val A ] Run (get i L) ρ v × Den v K ρ'
  {- the value under a known fold -}
  run-unf : ∀ {Δ Γ A} fl (L : Tm Δ (μ A)) {E : Facts Δ Γ} {ρ ρ' K} → Ok E ρ ρ'
    → unfolded (known (simp fl E L)) refl ≡ just K → Σ[ v ∈ S.Val _ ] Run (unfold L) ρ v × Den v K ρ'
  {- the branch of a case on a known injection -}
  run-inl : ∀ {Δ Γ A B} fl (L : Tm Δ (A ⊹ B)) {E : Facts Δ Γ} {ρ ρ' K} → Ok E ρ ρ'
    → branch (known (simp fl E L)) refl ≡ just (inj₁ K)
    → Σ[ v ∈ S.Val A ] (∀ {C} (M : Tm (A ∷ Δ) C) N κ → Star L₂ (S.eval L ρ (S.caseK M N ρ κ)) (S.eval M (v ∷ ρ) κ)) × Strong v K ρ'
  run-inr : ∀ {Δ Γ A B} fl (L : Tm Δ (A ⊹ B)) {E : Facts Δ Γ} {ρ ρ' K} → Ok E ρ ρ'
    → branch (known (simp fl E L)) refl ≡ just (inj₂ K)
    → Σ[ v ∈ S.Val B ] (∀ {C} (M : Tm (A ∷ Δ) C) N κ → Star L₂ (S.eval L ρ (S.caseK M N ρ κ)) (S.eval N (v ∷ ρ) κ)) × Strong v K ρ'
  {- a primitive on known integers -}
  run-int : ∀ {Δ Γ} fl (L : Tm Δ (base Int)) {E : Facts Δ Γ} {ρ ρ' n} → Ok E ρ ρ' → int-of (known (simp fl E L)) ≡ just n
    → Run L ρ (S.const n)

  {- an operand that becomes a value: the source runs it to a value that
     it describes, and that what simp knows of it describes -}
  arg-run : ∀ {Δ Γ A} fl (M : Tm Δ A) {E : Facts Δ Γ} {ρ ρ'} → Ok E ρ ρ' → Opd M ρ (simp fl E M) ρ'
  {- the body N of a function λ N closed in ρf, bound to the operand I,
     when the source runs some term S to the operand M, with a frame G
     that binds it (Q) -}
  let-run : ∀ {Δf Δ Γ A B} q fl (N : Tm (A ∷ Δf) B) I (M : Tm Δ A) {E' : Facts Δf Γ} {ρf ρ ρ'} {Sm : Tm Δ B} {G}
    → Ok E' ρf ρ' → Opd M ρ I ρ' → Binds N ρf G → (∀ κ → Star L₂ (S.eval Sm ρ κ) (S.eval M ρ (G κ)))
    → Ans q Sm ρ (simp-let fl E' N I) ρ'
  {- a call of the operator L, of which simp knows J -}
  call-run : ∀ {Δ Γ A B} q fl (J : Info Γ (A ⇒ B)) I (L : Tm Δ (A ⇒ B)) M {ρ ρ'} → Fn L ρ J ρ' → Opd M ρ I ρ'
    → Ans q (app L M) ρ (simp-call fl J I) ρ'

  run is-val fl (` x) {ρ = ρ} ok e = lookup ρ x , (λ κ → refl ◅ ε) , trm ok x
  run (is-known K) fl (` x) {ρ = ρ} ok k = lookup ρ x , (λ κ → refl ◅ ε) , knw ok x k
  run is-val fl (lam N) ok e = _ , (λ κ → refl ◅ ε) , clo≈ ok
  run (is-known K) fl (lam N) {ρ = ρ} ok refl = _ , (λ κ → refl ◅ ε) , ρ , refl , ok
  run q fl (app L M) ok e with lam? L
  ... | is-lam N = let-run q fl N _ M ok (arg-run fl M ok) by-app (λ κ → refl ◅ refl ◅ refl ◅ ε) e
  ... | other = call-run q fl _ _ L M (run (is-known _) fl L ok) (arg-run fl M ok) e
  run q fl (lit B c) ok e = _ , (λ κ → refl ◅ ε) , self-gives q (lit B c) e refl
  run is-val fl (tuple Ms) ok = run-tuple fl Ms ok
  run (is-known K) fl (tuple Ms) {E} ok = info-known (tuple (simps fl E Ms)) (run-tuple fl Ms ok)
  run q fl (get i L) {E} ok e with component i (known (simp fl E L)) refl in c
  ... | just K = small-run q K refl (run-get fl i L ok c) e
  ... | nothing = no-ask q refl e
  run is-val fl (inl M) ok e = wrap refl refl (run is-val fl M ok e)
  run (is-known K) fl (inl M) {E} ok = info-known (inl (term (simp fl E M))) λ e → wrap refl refl (run is-val fl M ok e)
  run is-val fl (inr M) ok e = wrap refl refl (run is-val fl M ok e)
  run (is-known K) fl (inr M) {E} ok = info-known (inr (term (simp fl E M))) λ e → wrap refl refl (run is-val fl M ok e)
  run q fl (case L M N) {E} ok e with branch (known (simp fl E L)) refl in b
  ... | nothing = no-ask q refl e
  ... | just (inj₁ K) with run-inl fl L ok b
  ...   | v , σ , d with run q fl M (ok-self ok (proj₂ (branch-inl (known (simp fl E L)) refl b)) d) e
  ...     | w , τ , d' = w , (λ κ → refl ◅ (σ _ _ κ ◅◅ τ κ)) , d'
  run q fl (case L M N) {E} ok e | just (inj₂ K) with run-inr fl L ok b
  ...   | v , σ , d with run q fl N (ok-self ok (proj₂ (branch-inr (known (simp fl E L)) refl b)) d) e
  ...     | w , τ , d' = w , (λ κ → refl ◅ (σ _ _ κ ◅◅ τ κ)) , d'
  run q fl (prim p L M) {E} {ρ = ρ} ok e with int-of (known (simp fl E L)) in e₁
  ... | nothing = no-ask q refl e
  ... | just n with int-of (known (simp fl E M)) in e₂
  ...   | nothing = no-ask q refl e
  ...   | just m =
    S.δᵀ p n m
    , (λ κ → refl ◅ (run-int fl L ok e₁ (S.primL p M ρ κ) ◅◅ (refl ◅ (run-int fl M ok e₂ (S.primR p n κ) ◅◅ (refl ◅ ε)))))
    , self-gives q (prim-term p n m) e (prim-strong p n m)
  run q fl (let′ M N) ok e = let-run q fl N _ M ok (arg-run fl M ok) by-let (λ κ → refl ◅ ε) e
  run is-val fl (fold M) ok e = wrap refl refl (run is-val fl M ok e)
  run (is-known K) fl (fold M) {E} ok = info-known (fold (term (simp fl E M))) λ e → wrap refl refl (run is-val fl M ok e)
  run q fl (unfold L) {E} ok e with unfolded (known (simp fl E L)) refl in u
  ... | just K = small-run q K refl (run-unf fl L ok u) e
  ... | nothing = no-ask q refl e

  run-tuple fl Ms ok e with run-terms fl Ms ok e {acc = []}
  ... | vs , σ , ds = S.tup vs , (λ κ → refl ◅ σ κ) , vs , refl , ds

  run-terms fl [] ok _ {acc = acc} = [] , (λ κ → ε) , tt
  run-terms fl (M ∷ Ms) {E} {ρ = ρ} ok e {acc = acc} with P.∧-true {value (term (simp fl E M))} e
  ... | e₁ , e₂ with run is-val fl M ok e₁
  ...   | v , σ , d with run-terms fl Ms ok e₂ {acc = v ∷ acc}
  ...     | vs , τ , ds = v ∷ vs , (λ κ → σ (S.tupK acc Ms ρ κ) ◅◅ (refl ◅ τ κ)) , d , ds

  run-get fl i L {E} ok c with comp-inv i (known (simp fl E L)) refl c
  ... | Ks , k , refl with run (is-known _) fl L ok k
  ...   | .(S.tup vs) , σ , (vs , refl , ds) =
    lookup vs i , (λ κ → refl ◅ (σ (S.getK i κ) ◅◅ (refl ◅ ε))) , dens-lookup ds i

  run-unf fl L {E} ok u with run (is-known _) fl L ok (unfold-inv (known (simp fl E L)) refl u)
  ... | .(S.fold v₀) , σ , (v₀ , refl , d) = v₀ , (λ κ → refl ◅ (σ (S.unfoldK κ) ◅◅ (refl ◅ ε))) , d

  run-inl fl L {E} {ρ = ρ} ok b with branch-inl (known (simp fl E L)) refl b
  ... | k , s with run (is-known _) fl L ok k
  ...   | .(S.inl v₀) , σ , (v₀ , refl , d) = v₀ , (λ M N κ → σ (S.caseK M N ρ κ) ◅◅ (refl ◅ ε)) , small-strong _ s d

  run-inr fl L {E} {ρ = ρ} ok b with branch-inr (known (simp fl E L)) refl b
  ... | k , s with run (is-known _) fl L ok k
  ...   | .(S.inr v₀) , σ , (v₀ , refl , d) = v₀ , (λ M N κ → σ (S.caseK M N ρ κ) ◅◅ (refl ◅ ε)) , small-strong _ s d

  run-int fl L {E} ok e with int-inv (known (simp fl E L)) e
  ... | refl , k with run (is-known _) fl L ok k
  ...   | .(S.const _) , σ , refl = σ

  arg-run fl M {E} {ρ} {ρ'} ok e with run is-val fl M ok e
  ... | v , σ , d = v , σ , d , λ {K} k → same {K} (run (is-known K) fl M ok k)
    where same : ∀ {K} → Σ[ v' ∈ S.Val _ ] Run M ρ v' × KDen v' K ρ' → KDen v K ρ'
          same {K} (v' , σ' , d') with run-unique (σ' S.halt) (σ S.halt)
          ... | refl = d'

  let-run q fl N I M okf A bd Q e with small (term I) in s
  ... | true with A (P.small-value (term I) s)
  ...   | v , σ , d , k with run q fl N (ok-cons okf d k s) e
  ...     | w , τ , d' = w , (λ κ → Q κ ◅◅ (σ _ ◅◅ (bind-step bd ◅ τ κ))) , d'
  let-run q fl N I M okf A bd Q e | false with value (term I)
  ... | true = no-ask q refl e
  ... | false = no-ask q refl e

  call-run q (suc fl) (T ∣ just (P.fun N E')) I L M jk A e with size (term (simp-let fl E' N I)) ≤ᵇ inline-size | jk refl
  ... | true | v , σ , ρf , refl , okf = let-run q fl N I M okf A by-app (λ κ → refl ◅ (σ _ ◅◅ (refl ◅ ε))) e
  ... | false | _ = no-ask q refl e
  call-run q zero J I L M jk A e = no-ask q refl e
  call-run q (suc fl) (T ∣ nothing) I L M jk A e = no-ask q refl e
  call-run q (suc fl) (T ∣ just (P.val K)) I L M jk A e = no-ask q refl e

  {- The source's answer to a target evaluation ----------------------------------}

  tuple-next~ : ∀ {fl Δ Γ Δ' Δ''} {E : Facts Δ Γ} {vs vs' : All S.Val Δ'} {Ms : All (Tm Δ) Δ''} {ρ ρ'}
    {κ κ' : S.Cont (tup (Δ' <>< Δ''))} → All₂ _≈_ vs vs' → Ok E ρ ρ' → κ ≈k κ'
    → S.tuple-next vs Ms ρ κ ~ S.tuple-next vs' (simps fl E Ms) ρ' κ'
  tuple-next~ {Ms = []} rs ok k = ret~ (tup≈ (rs <><₂ [])) k
  tuple-next~ {Ms = M ∷ Ms} rs ok k = eval~ ok (tupK rs ok k)

  {- the target and the source take one step each -}
  lock : ∀ {s s' t t'} → S.step s' ≡ next t' → S.step s ≡ next t → t ~ t' → Step-ans s s'
  lock e e' r = ans e (step⁺ e') (lag₀ r)

  eval-sim : ∀ {Δ Γ A} fl (M : Tm Δ A) {E : Facts Δ Γ} {ρ ρ' κ κ'} → Ok E ρ ρ' → κ ≈k κ'
    → Step-ans (S.eval M ρ κ) (S.eval (term (simp fl E M)) ρ' κ')
  structural : ∀ {Δ Γ A} fl (M : Tm Δ A) {E : Facts Δ Γ} {ρ ρ' κ κ'} → Ok E ρ ρ' → κ ≈k κ' → value (term (simp fl E M)) ≡ false
    → Step-ans (S.eval M ρ κ) (S.eval (term (simp fl E M)) ρ' κ')

  {- the body N of a function λ N closed in ρf, bound to the operand M,
     when the source runs to the evaluation of M (Q) -}
  let-sim : ∀ {Δf Δ Γ A B} fl (N : Tm (A ∷ Δf) B) fl₀ (M : Tm Δ A) {E' : Facts Δf Γ} {E : Facts Δ Γ} {ρf ρ ρ' s G κ κ'}
    → Ok E' ρf ρ' → Ok E ρ ρ' → Binds N ρf G → κ ≈k κ' → Plus L₂ s (S.eval M ρ (G κ))
    → Step-ans s (S.eval (term (simp-let fl E' N (simp fl₀ E M))) ρ' κ')
  {- a call of the operator L, of which the source knows J -}
  call-sim : ∀ {Δ Γ A B} fl (J : Info Γ (A ⇒ B)) (L : Tm Δ (A ⇒ B)) M {E : Facts Δ Γ} {ρ ρ' κ κ'}
    → (∀ {κ κ'} → κ ≈k κ' → S.eval L ρ κ ~ S.eval (term J) ρ' κ') → Fn L ρ J ρ' → Ok E ρ ρ' → κ ≈k κ'
    → Step-ans (S.eval (app L M) ρ κ) (S.eval (term (simp-call fl J (simp fl E M))) ρ' κ')

  eval-sim fl M {E} ok k with value (term (simp fl E M)) in isv
  ... | true with run is-val fl M ok isv
  ...   | v , σ , d = value-ans (term (simp fl E M)) d σ k
  eval-sim fl M ok k | false = structural fl M ok k isv

  structural fl (lam N) ok k ()
  structural fl (lit B c) ok k ()
  structural fl (` x) {E} ok k isv = absurd (trans (sym (P.small-value (term (E x)) (sml ok x))) isv)
  structural fl (app L M) {E} ok k isv with lam? L
  ... | is-lam N = let-sim fl N fl M ok ok by-app k (plus refl (refl ◅ refl ◅ ε))
  ... | other = call-sim fl (simp fl E L) L M (eval~ ok) (run (is-known _) fl L ok) ok k
  structural fl (tuple Ms) ok k isv = lock refl refl (tuple-next~ [] ok k)
  structural fl (get i L) {E} ok k isv with component i (known (simp fl E L)) refl
  ... | nothing = lock refl refl (eval~ ok (getK k))
  ... | just K with small K in s
  ...   | true = absurd (trans (sym (P.small-value K s)) isv)
  ...   | false = lock refl refl (eval~ ok (getK k))
  structural fl (inl M) ok k isv = lock refl refl (eval~ ok (inlK k))
  structural fl (inr M) ok k isv = lock refl refl (eval~ ok (inrK k))
  structural fl (case L M N) {E} ok k isv with branch (known (simp fl E L)) refl in b
  ... | nothing = lock refl refl (eval~ ok (caseK ok k))
  ... | just (inj₁ K) with run-inl fl L ok b
  ...   | v , σ , d = prefix (refl ◅ σ _ _ _) (eval-sim fl M (ok-self ok (proj₂ (branch-inl (known (simp fl E L)) refl b)) d) k)
  structural fl (case L M N) {E} ok k isv | just (inj₂ K) with run-inr fl L ok b
  ...   | v , σ , d = prefix (refl ◅ σ _ _ _) (eval-sim fl N (ok-self ok (proj₂ (branch-inr (known (simp fl E L)) refl b)) d) k)
  structural fl (prim p L M) {E} ok k isv with int-of (known (simp fl E L))
  ... | nothing = lock refl refl (eval~ ok (primL ok k))
  ... | just n with int-of (known (simp fl E M))
  ...   | nothing = lock refl refl (eval~ ok (primL ok k))
  ...   | just m = absurd (trans (sym (P.sv-value (P.prim-term-sv p n m))) isv)
  structural fl (let′ M N) ok k isv = let-sim fl N fl M ok ok by-let k (plus refl ε)
  structural fl (fold M) ok k isv = lock refl refl (eval~ ok (foldK k))
  structural fl (unfold L) {E} ok k isv with unfolded (known (simp fl E L)) refl
  ... | nothing = lock refl refl (eval~ ok (unfoldK k))
  ... | just K with small K in s
  ...   | true = absurd (trans (sym (P.small-value K s)) isv)
  ...   | false = lock refl refl (eval~ ok (unfoldK k))

  let-sim fl N fl₀ M {E'} {E} {ρ' = ρ'} {κ' = κ'} okf ok bd k Q with small (term (simp fl₀ E M)) in s | value (term (simp fl₀ E M)) in isv
  ... | true | _ with arg-run fl₀ M ok (P.small-value (term (simp fl₀ E M)) s)
  ...   | v , σ , d , kn = prefix (plus→star Q ◅◅ (σ _ ◅◅ (bind-step bd ◅ ε))) (eval-sim fl N (ok-cons okf d kn s) k)
  let-sim fl N fl₀ M {E'} {E} {ρ' = ρ'} {κ' = κ'} okf ok bd k Q | false | true with arg-run fl₀ M ok isv
  ...   | v , σ , d , kn with trun (term (simp fl₀ E M)) d
  ...     | w' , τ , r with lag-star (τ (S.letK N' ρ' κ') ◅◅ (refl ◅ ε)) (eval~ (ok-let {I = simp fl₀ E M} okf r kn) k)
    where N' = term (simp fl (known-as (simp fl₀ E M) E') N)
  ...       | j , m = ans refl (plus-star Q (σ _ ◅◅ (bind-step bd ◅ ε))) m
  let-sim fl N fl₀ M okf ok bd k Q | false | false = ans refl Q (lag₀ (eval~ ok (letK bd okf k)))

  call-sim (suc fl) (T ∣ just (P.fun N E')) L M {E} jt jk ok k
    with size (term (simp-let fl E' N (simp (suc fl) E M))) ≤ᵇ inline-size | jk refl
  ... | true | v , σ , ρf , refl , okf = let-sim fl N (suc fl) M okf ok by-app k (plus refl (σ _ ◅◅ (refl ◅ ε)))
  ... | false | _ = lock refl refl (jt (appL ok k))
  call-sim zero J L M jt jk ok k = lock refl refl (jt (appL ok k))
  call-sim (suc fl) (T ∣ nothing) L M jt jk ok k = lock refl refl (jt (appL ok k))
  call-sim (suc fl) (T ∣ just (P.val K)) L M jt jk ok k = lock refl refl (jt (appL ok k))

  {- The simulation ------------------------------------------------------------}

  next~ : ∀ {i s t t'} → S.step s ≡ next t → t ~ t' → Answers≺ L₂ match i (next t') s
  next~ e r = steps₁≺ e (lag₀ r)

  base-sim : ∀ {i s s'} → s ~ s' → Answers≺ L₂ match i (S.step s') s
  base-sim (eval~ {fl = fl} {M = M} ok k) with eval-sim fl M ok k
  ... | ans e π m rewrite e = steps π m
  base-sim (ret~ r halt) = stops (cong stop (obs≈ r))
  base-sim (ret~ r (appL ok k)) = next~ refl (eval~ ok (appR r k))
  base-sim (ret~ r (appR (clo≈ ok) k)) = next~ refl (eval~ (ok-under ok r) k)
  base-sim (ret~ r (tupK rs ok k)) = next~ refl (tuple-next~ (r ∷ rs) ok k)
  base-sim (ret~ (tup≈ rs) (getK {i = i} k)) = next~ refl (ret~ (lookup₂ rs i) k)
  base-sim (ret~ r (inlK k)) = next~ refl (ret~ (inl≈ r) k)
  base-sim (ret~ r (inrK k)) = next~ refl (ret~ (inr≈ r) k)
  base-sim (ret~ (inl≈ r) (caseK ok k)) = next~ refl (eval~ (ok-under ok r) k)
  base-sim (ret~ (inr≈ r) (caseK ok k)) = next~ refl (eval~ (ok-under ok r) k)
  base-sim (ret~ const≈ (primL ok k)) = next~ refl (eval~ ok (primR k))
  base-sim (ret~ (const≈ {c = m}) (primR {p} {n} k)) = next~ refl (ret~ (δ≈ p n m) k)
  base-sim (ret~ r (letK bd ok k)) = next~ (bind-step bd) (eval~ (ok-under ok r) k)
  base-sim (ret~ r (foldK k)) = next~ refl (ret~ (fold≈ r) k)
  base-sim (ret~ (fold≈ r) (unfoldK k)) = next~ refl (ret~ r k)

{- The end theorem: for every closed program ----------------------------------------}

ok₀ : Ok (λ x → self (` x)) [] []
ok₀ = mk-ok (λ ()) (λ ()) (λ ())

simplify-correct : ∀ {A} (M : Tm [] A) → Equivalent (S.sem M) (S.sem (simplify M))
simplify-correct M = equiv-sym (equivalent
  (lag-fsim (lag-now (eval~ {fl = inline-fuel} ok₀ halt)) (base-sim M (simplify M))))

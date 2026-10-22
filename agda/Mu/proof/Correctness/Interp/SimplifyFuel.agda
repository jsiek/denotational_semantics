{-

  Correctness of the simplify pass (ISWIMμ → ISWIMμ) for the clocked
  interpreters, as for the untyped simplify
  (proof/Correctness/Interp/SimplifyFuel.agda; see the design note in
  Semantics/Interp/Clock.agda).

  Not clock for clock: the clock ticks at each call, and simplify removes
  calls (β of a small value, inlining), so the target needs no more clock
  than the source, and the source may need more than the target. The theorem has
  the shape of the others (Equivalent), from two lemmas (clocked-back,
  proof/Framework/Clocked.agda):

  * forward, at the same clock: the source's result, if it does not
    time out, is the target's, related (LeResult);
  * backward: if the target does not time out at a clock, then the
    source has a related result at every large enough clock (Stable);

  and the interpreter's monotonicity in the clock (mono). One induction
  (sim) proves both directions at each clock (Sim).

  Values are related as in the CEK proof (SimplifySim): the source's on
  the left, a source closure to the simplified body of it, a target
  closure, under Facts that are true of the two environments (Ok); a
  known function is a source closure (KDen). When simp E M returns a
  value term, or M has a known value, the source runs M to a value it
  describes, at every large enough clock (run, both at once: Opd). A
  call, β or an inlined known function (whose body the source reaches
  by running the operator), is one lemma for each (run-let, let-sim).
  The interpreters never err, and the theorem holds for every closed
  program.

-}

module Mu.proof.Correctness.Interp.SimplifyFuel where

open import Framework.Primitives using (Int)
import Language.Prim as Pr
open import Mu.Language.Type
open import Mu.Language.ISWIM
open import Mu.Language.ISWIMSubst using (ren; travs; varK)
open import Mu.Framework.AllUtil using (All; []; _∷_; lookup; All₂; lookup₂)
open import Mu.proof.Compiler.SimplifyFacts as P
  using (Info; _∣_; term; known; Known; Facts; self; info; under; known-as; shift-info; shift-known; simp; simps;
         simp-app; simp-call; simp-let; lam?; is-lam; other; size; inline-size; inline-fuel; simp-get; simp-case;
         simp-prim; simp-unfold; simplify; small; atom; value; values; component; branch; unfolded; int-of; prim-term;
         value-sv; small-sv; comp-inv; int-inv; branch-inl; branch-inr; unfold-inv)
open import Semantics.Observation
open import proof.Semantics.Interp.Clock
import Mu.Semantics.Interp.ISWIM as S

open import Data.Bool using (Bool; true; false; _∧_; if_then_else_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Integer using (_≟_)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; zero; suc; _≤_; s≤s; _≤ᵇ_)
open import Data.Nat.Properties using (n≤1+n; ≤-refl)
open import Data.Product using (_×_; Σ-syntax; _,_; proj₁; proj₂; map₁; map₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary using (does)

{- a closure, of the code N and the environment ρ -}
clo : ∀ {Δ A B} → Tm (A ∷ Δ) B → S.Env Δ → S.Val (A ⇒ B)
clo N ρ = S.pack (S.code N) (S.tup ρ)

{- The relation ------------------------------------------------------------------}

infix 4 _≈_

data _≈_ : ∀ {A} → S.Val A → S.Val A → Set
{- the value term T denotes, in ρ', a value that v is related to (Strong);
   or the same, but a function describes any value (Den) -}
Desc : Bool → ∀ {Γ A} → S.Val A → Tm Γ A → S.Env Γ → Set
Descs : Bool → ∀ {Γ Δ} → All S.Val Δ → All (Tm Γ) Δ → S.Env Γ → Set
Strong Den : ∀ {Γ A} → S.Val A → Tm Γ A → S.Env Γ → Set
Strong = Desc true
Den = Desc false

{- what a value is known to be is true of it: a value that describes it,
   or a function λ N that is a source closure of N, under Facts true of
   the closure's environment and the target's -}
KDen : ∀ {Γ A} → S.Val A → Known Γ A → S.Env Γ → Set
Kn : ∀ {Γ A} → S.Val A → Info Γ A → S.Env Γ → Set
Kn v I ρ' = ∀ {K} → known I ≡ just K → KDen v K ρ'

{- what simp knows of each variable is true of the source's environment ρ
   and the target's ρ' -}
record Ok {Δ Γ} (E : Facts Δ Γ) (ρ : S.Env Δ) (ρ' : S.Env Γ) : Set where
  inductive
  constructor mk-ok
  field
    trm : ∀ {A} (x : Δ ∋ A) → Strong (lookup ρ x) (term (E x)) ρ'
    knw : ∀ {A} (x : Δ ∋ A) → Kn (lookup ρ x) (E x) ρ'
    sml : ∀ {A} (x : Δ ∋ A) → small (term (E x)) ≡ true

{- the source's value on the left -}
data _≈_ where
  clo≈ : ∀ {fl Δ Γ A B} {E : Facts Δ Γ} {N : Tm (A ∷ Δ) B} {ρ ρ'} → Ok E ρ ρ'
    → clo N ρ ≈ clo (term (simp fl (under E) N)) ρ'
  const≈ : ∀ {B c} → S.const {B} c ≈ S.const c
  tup≈ : ∀ {Δ} {vs ws : All S.Val Δ} → All₂ _≈_ vs ws → S.tup vs ≈ S.tup ws
  inl≈ : ∀ {A B v w} → v ≈ w → S.inl {A} {B} v ≈ S.inl w
  inr≈ : ∀ {A B v w} → v ≈ w → S.inr {A} {B} v ≈ S.inr w
  fold≈ : ∀ {A v w} → v ≈ w → S.fold {A} v ≈ S.fold w

Desc b v (` y) ρ' = v ≈ lookup ρ' y
Desc true v (lam N) ρ' = v ≈ clo N ρ'
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
KDen v (P.fun {Δ} N E) ρ' = Σ[ ρ ∈ S.Env Δ ] v ≡ clo N ρ × Ok E ρ ρ'

Strongs Dens : ∀ {Γ Δ} → All S.Val Δ → All (Tm Γ) Δ → S.Env Γ → Set
Strongs = Descs true
Dens = Descs false

open Ok

{- Related values are observed alike, and operations on them agree ----------}

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

δ≈ : ∀ p {v₁ v₂ w₁ w₂} → v₁ ≈ w₁ → v₂ ≈ w₂ → S.δ p v₁ v₂ ≈ S.δ p w₁ w₂
δ≈ Pr.sub const≈ const≈ = const≈
δ≈ Pr.eq (const≈ {c = n}) (const≈ {c = m}) with does (n ≟ m)
... | true = inl≈ (tup≈ [])
... | false = inr≈ (tup≈ [])

nth≈ : ∀ {Δ A} (i : Δ ∋ A) {v w} → v ≈ w → S.nth i v ≈ S.nth i w
nth≈ i (tup≈ rs) = lookup₂ rs i

unfold≈ : ∀ {A} {v w : S.Val (μ A)} → v ≈ w → S.unfold-v v ≈ S.unfold-v w
unfold≈ (fold≈ r) = r

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
prim-strong : ∀ {Γ} p n m {ρ' : S.Env Γ} → Strong (S.δ p (S.const n) (S.const m)) (prim-term p n m) ρ'
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

{- a small value I for variable 0, in the source only -}
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

{- a value that stays bound to variable 0, known as I is -}
ok-let : ∀ {Δ Γ A} {E : Facts Δ Γ} {ρ ρ'} {I : Info Γ A} {v w} → Ok E ρ ρ' → v ≈ w → Kn v I ρ'
  → Ok (known-as I E) (v ∷ ρ) (w ∷ ρ')
ok-let {I = I} ok r k = ok-cons (ok-weak ok) r (kn-shift I k) refl

{- The interpreter is monotone in the clock --------------------------------------}

mono : ∀ {ck ck'} → ck ≤ ck' → ∀ {Γ A} (ρ : S.Env Γ) (M : Tm Γ A) → S.eval ck ρ M ⊑ᵣ S.eval ck' ρ M
monos : ∀ {ck ck'} → ck ≤ ck' → ∀ {Γ Δ} (ρ : S.Env Γ) (Ms : All (Tm Γ) Δ) → S.evals ck ρ Ms ⊑ᵣ S.evals ck' ρ Ms
mono-call : ∀ {ck ck'} → ck ≤ ck' → ∀ {A B} (f : S.Val (A ⇒ B)) w → S.call ck f w ⊑ᵣ S.call ck' f w
mono le ρ (` x) = same
mono le ρ (lam N) = same
mono le ρ (app L M) = ⊑-bind (mono le ρ L) (λ f → ⊑-bind (mono le ρ M) (λ w → mono-call le f w))
mono le ρ (lit B c) = same
mono le ρ (tuple Ms) = ⊑-bind (monos le ρ Ms) (λ _ → same)
mono le ρ (get i M) = ⊑-bind (mono le ρ M) (λ _ → same)
mono le ρ (inl M) = ⊑-bind (mono le ρ M) (λ _ → same)
mono le ρ (inr M) = ⊑-bind (mono le ρ M) (λ _ → same)
mono le ρ (case L M N) = ⊑-bind (mono le ρ L) λ { (S.inl v) → mono le (v ∷ ρ) M ; (S.inr v) → mono le (v ∷ ρ) N }
mono le ρ (prim p L M) = ⊑-bind (mono le ρ L) (λ v → ⊑-bind (mono le ρ M) (λ w → same))
mono le ρ (let′ M N) = ⊑-bind (mono le ρ M) (λ v → mono le (v ∷ ρ) N)
mono le ρ (fold M) = ⊑-bind (mono le ρ M) (λ _ → same)
mono le ρ (unfold M) = ⊑-bind (mono le ρ M) (λ _ → same)
monos le ρ [] = same
monos le ρ (M ∷ Ms) = ⊑-bind (mono le ρ M) (λ v → ⊑-bind (monos le ρ Ms) (λ vs → same))
mono-call {zero} le f w = timeout
mono-call {suc ck} {suc ck'} (s≤s le) (S.pack (S.code N) (S.tup ρ)) w = mono le (w ∷ ρ) N

mono-at : ∀ {Γ A} (ρ : S.Env Γ) (M : Tm Γ A) → Mono (λ ck → S.eval ck ρ M)
mono-at ρ M le = mono le ρ M

{- Stable results of the source ------------------------------------------------}

st-call : ∀ {Δ A B} {N : Tm (A ∷ Δ) B} {ρ w r} → Stable (λ ck → S.eval ck (w ∷ ρ) N) r → Stable (λ ck → S.call ck (clo N ρ) w) r
st-call (c , e) = suc c , λ { (suc ck) (s≤s le) → e ck le }

Run : ∀ {Γ A} → Tm Γ A → S.Env Γ → S.Val A → Set
Run M ρ v = Stable (λ ck → S.eval ck ρ M) (ret v)

{- the source evaluates M, then the body N with its value bound: by a call
   of a closure of N in ρf (true, which ticks), or a let (false) -}
Body : ∀ {Δ A B} → Bool → ℕ → Tm (A ∷ Δ) B → S.Env Δ → S.Val A → Result (S.Val B)
Body true ck N ρ v = S.call ck (clo N ρ) v
Body false ck N ρ v = S.eval ck (v ∷ ρ) N

Bound : ∀ {Δf Δ A B} → Bool → Tm Δ A → Tm (A ∷ Δf) B → S.Env Δf → S.Env Δ → ℕ → Result (S.Val B)
Bound t M N ρf ρ ck = S.eval ck ρ M >>= Body t ck N ρf

st-body : ∀ {Δ A B} t {N : Tm (A ∷ Δ) B} {ρ v r} → Stable (λ ck → S.eval ck (v ∷ ρ) N) r → Stable (λ ck → Body t ck N ρ v) r
st-body true = st-call
st-body false σ = σ

{- The target evaluates value terms, at any clock ---------------------------------}

teval : ∀ {Γ A} (T : Tm Γ A) {ρ' v} → Strong v T ρ' → Σ[ w ∈ S.Val A ] (∀ ck → S.eval ck ρ' T ≡ ret w) × v ≈ w
tevals : ∀ {Γ Δ} (Ms : All (Tm Γ) Δ) {ρ' vs} → Strongs vs Ms ρ'
  → Σ[ ws ∈ All S.Val Δ ] (∀ ck → S.evals ck ρ' Ms ≡ ret ws) × All₂ _≈_ vs ws
teval (` y) r = _ , (λ ck → refl) , r
teval (lam N) r = _ , (λ ck → refl) , r
teval (lit B c) refl = _ , (λ ck → refl) , const≈
teval (tuple Ms) (vs , refl , ds) with tevals Ms ds
... | ws , e , rs = S.tup ws , (λ ck → cong (_>>= _) (e ck)) , tup≈ rs
teval (inl M) (v , refl , d) with teval M d
... | w , e , r = S.inl w , (λ ck → cong (_>>= _) (e ck)) , inl≈ r
teval (inr M) (v , refl , d) with teval M d
... | w , e , r = S.inr w , (λ ck → cong (_>>= _) (e ck)) , inr≈ r
teval (fold M) (v , refl , d) with teval M d
... | w , e , r = S.fold w , (λ ck → cong (_>>= _) (e ck)) , fold≈ r
tevals [] {vs = []} tt = [] , (λ ck → refl) , []
tevals (M ∷ Ms) {vs = v ∷ vs} (d , ds) with teval M d | tevals Ms ds
... | w , e , r | ws , es , rs = w ∷ ws , (λ ck → bind≡ (e ck) λ _ → cong (_>>= _) (es ck)) , r ∷ rs

{- The source runs ahead ------------------------------------------------------------}

{- what the source does (f) with a term whose simplification is I: it runs
   to the value that I's value term, or its known value, describes -}
record Opd {Γ A} (f : ℕ → Result (S.Val A)) (I : Info Γ A) (ρ' : S.Env Γ) : Set where
  constructor opd
  field
    o-term : value (term I) ≡ true → Σ[ v ∈ S.Val A ] Stable f (ret v) × Strong v (term I) ρ'
    o-known : ∀ {K} → known I ≡ just K → Σ[ v ∈ S.Val A ] Stable f (ret v) × KDen v K ρ'
open Opd

{- what a value that f reaches at some clock is known to be -}
opd-kn : ∀ {Γ A} {f : ℕ → Result (S.Val A)} {I : Info Γ A} {ρ' v} → Mono f → Opd f I ρ' → Σ[ c ∈ ℕ ] f c ≡ ret v → Kn v I ρ'
opd-kn m o (c , e) k with o-known o k
... | v' , σ' , d' with refl ← stable-ret m σ' e = d'

{- the value of a value term, described by it and by what it is known to be -}
opd-val : ∀ {Γ A} {f : ℕ → Result (S.Val A)} {I : Info Γ A} {ρ'} → Mono f → Opd f I ρ' → value (term I) ≡ true
  → Σ[ v ∈ S.Val A ] Stable f (ret v) × Strong v (term I) ρ' × Kn v I ρ'
opd-val m o e with o-term o e
... | v , σ@(c , e') , d = v , σ , d , opd-kn m o (c , e' c ≤-refl)

{- the same values, reached by g -}
opd-map : ∀ {Γ A} {f g : ℕ → Result (S.Val A)} {I : Info Γ A} {ρ'} → (∀ {v} → Stable f (ret v) → Stable g (ret v))
  → Opd f I ρ' → Opd g I ρ'
opd-map h (opd t k) = opd (λ e → map₂ (map₁ h) (t e)) (λ e → map₂ (map₁ h) (k e))

{- a value term T that describes the value v the source reaches -}
opd-self : ∀ {Γ A} {f : ℕ → Result (S.Val A)} {v} (T : Tm Γ A) {ρ'} → Stable f (ret v) → Strong v T ρ' → Opd f (self T) ρ'
opd-self T σ d = opd (λ _ → _ , σ , d) λ { refl → _ , σ , strong-den T d }

{- a term T that is known to be itself if it is a value -}
opd-info : ∀ {Γ A} {f : ℕ → Result (S.Val A)} (T : Tm Γ A) {ρ'}
  → (value T ≡ true → Σ[ v ∈ S.Val A ] Stable f (ret v) × Strong v T ρ') → Opd f (T ∣ (if value T then just (P.val T) else nothing)) ρ'
opd-info T h with value T in isv
... | true = opd (λ _ → h refl) λ { refl → map₂ (map₂ (strong-den T)) (h refl) }
... | false = opd (λ e → h (trans (sym isv) e)) λ ()

run : ∀ {Δ Γ A} fl (M : Tm Δ A) {E : Facts Δ Γ} {ρ ρ'} → Ok E ρ ρ' → Opd (λ ck → S.eval ck ρ M) (simp fl E M) ρ'
run-terms : ∀ {Δ Γ Δ'} fl (Ms : All (Tm Δ) Δ') {E : Facts Δ Γ} {ρ ρ'} → Ok E ρ ρ' → values (simps fl E Ms) ≡ true
  → Σ[ vs ∈ All S.Val Δ' ] Stable (λ ck → S.evals ck ρ Ms) (ret vs) × Strongs vs (simps fl E Ms) ρ'
run-get : ∀ {Δ Γ Δ' A} fl (i : Δ' ∋ A) (L : Tm Δ (tup Δ')) {E : Facts Δ Γ} {ρ ρ' K} → Ok E ρ ρ'
  → component i (known (simp fl E L)) refl ≡ just K → Σ[ v ∈ S.Val A ] Run (get i L) ρ v × Den v K ρ'
run-unf : ∀ {Δ Γ A} fl (L : Tm Δ (μ A)) {E : Facts Δ Γ} {ρ ρ' K} → Ok E ρ ρ'
  → unfolded (known (simp fl E L)) refl ≡ just K → Σ[ v ∈ S.Val _ ] Run (unfold L) ρ v × Den v K ρ'
{- a known branch: L runs to an injection of v, which K describes, for the branch's variable -}
run-inl : ∀ {Δ Γ A B} fl (L : Tm Δ (A ⊹ B)) {E : Facts Δ Γ} {ρ ρ' K} → Ok E ρ ρ'
  → branch (known (simp fl E L)) refl ≡ just (inj₁ K) → Σ[ v ∈ S.Val A ] Run L ρ (S.inl v) × Ok (self K P.• E) (v ∷ ρ) ρ'
run-inr : ∀ {Δ Γ A B} fl (L : Tm Δ (A ⊹ B)) {E : Facts Δ Γ} {ρ ρ' K} → Ok E ρ ρ'
  → branch (known (simp fl E L)) refl ≡ just (inj₂ K) → Σ[ v ∈ S.Val B ] Run L ρ (S.inr v) × Ok (self K P.• E) (v ∷ ρ) ρ'
run-int : ∀ {Δ Γ} fl (L : Tm Δ (base Int)) {E : Facts Δ Γ} {ρ ρ' n} → Ok E ρ ρ' → int-of (known (simp fl E L)) ≡ just n
  → Run L ρ (S.const n)
{- a let, or a call: the source runs the operand, then N (run-let), or
   the target calls (run-call) -}
run-let : ∀ {Δf Δ Γ A B} t fl (N : Tm (A ∷ Δf) B) {Ef : Facts Δf Γ} {ρf ρ' I} {M : Tm Δ A} {ρ} → Ok Ef ρf ρ'
  → Opd (λ ck → S.eval ck ρ M) I ρ' → Opd (Bound t M N ρf ρ) (simp-let fl Ef N I) ρ'
run-call : ∀ {Δ Γ A B} fl (J : Info Γ (A ⇒ B)) I {L : Tm Δ (A ⇒ B)} {M ρ' ρ} → Opd (λ ck → S.eval ck ρ L) J ρ'
  → Opd (λ ck → S.eval ck ρ M) I ρ' → Opd (λ ck → S.eval ck ρ (app L M)) (simp-call fl J I) ρ'

{- a primitive on known integers -}
run-prim : ∀ {Δ Γ} fl p (L M : Tm Δ (base Int)) {E : Facts Δ Γ} {ρ ρ' n m} → Ok E ρ ρ'
  → int-of (known (simp fl E L)) ≡ just n → int-of (known (simp fl E M)) ≡ just m
  → Run (prim p L M) ρ (S.δ p (S.const n) (S.const m))
run-prim fl p L M ok e₁ e₂ = st-bind (run-int fl L ok e₁) (st-bind (run-int fl M ok e₂) (st-now (λ _ → refl)))

run fl (` x) {ρ = ρ} ok = opd (λ _ → _ , st-now (λ _ → refl) , trm ok x) λ k → _ , st-now (λ _ → refl) , knw ok x k
run fl (lam N) ok = opd (λ _ → _ , st-now (λ _ → refl) , clo≈ ok) λ { refl → _ , st-now (λ _ → refl) , _ , refl , ok }
run fl (app L M) {E} {ρ = ρ} ok with lam? L
... | is-lam N = run-let true fl N {ρf = ρ} {M = M} ok (run fl M ok)
... | other = run-call fl (simp fl E L) _ {L = L} {M} (run fl L ok) (run fl M ok)
run fl (lit B c) ok = opd-self (lit B c) (st-now (λ _ → refl)) refl
run fl (tuple Ms) {E} ok = opd-info (tuple (simps fl E Ms)) λ e →
  let vs , σ , ds = run-terms fl Ms ok e in S.tup vs , st-bind σ (st-now (λ _ → refl)) , vs , refl , ds
run fl (get i L) {E} ok with component i (known (simp fl E L)) refl in c
... | nothing = opd (λ ()) (λ ())
... | just K with small K in s | run-get fl i L ok c
...   | true | v , σ , d = opd-self K σ (small-strong K s d)
...   | false | r = opd (λ ()) λ { refl → r }
run fl (inl M) {E} ok = opd-info (inl (term (simp fl E M))) λ e →
  let v , σ , d = o-term (run fl M ok) e in S.inl v , st-bind σ (st-now (λ _ → refl)) , v , refl , d
run fl (inr M) {E} ok = opd-info (inr (term (simp fl E M))) λ e →
  let v , σ , d = o-term (run fl M ok) e in S.inr v , st-bind σ (st-now (λ _ → refl)) , v , refl , d
run fl (case L M N) {E} ok with branch (known (simp fl E L)) refl in b
... | nothing = opd (λ ()) (λ ())
... | just (inj₁ K) with run-inl fl L ok b
...   | v , σ , ok' = opd-map (st-bind σ) (run fl M ok')
run fl (case L M N) {E} ok | just (inj₂ K) with run-inr fl L ok b
...   | v , σ , ok' = opd-map (st-bind σ) (run fl N ok')
run fl (prim p L M) {E} ok with int-of (known (simp fl E L)) in e₁
... | nothing = opd (λ ()) (λ ())
... | just n with int-of (known (simp fl E M)) in e₂
...   | nothing = opd (λ ()) (λ ())
...   | just m = opd-self (prim-term p n m) (run-prim fl p L M ok e₁ e₂) (prim-strong p n m)
run fl (let′ M N) ok = run-let false fl N {M = M} ok (run fl M ok)
run fl (fold M) {E} ok = opd-info (fold (term (simp fl E M))) λ e →
  let v , σ , d = o-term (run fl M ok) e in S.fold v , st-bind σ (st-now (λ _ → refl)) , v , refl , d
run fl (unfold L) {E} ok with unfolded (known (simp fl E L)) refl in u
... | nothing = opd (λ ()) (λ ())
... | just K with small K in s | run-unf fl L ok u
...   | true | v , σ , d = opd-self K σ (small-strong K s d)
...   | false | r = opd (λ ()) λ { refl → r }

run-terms fl [] ok _ = [] , st-now (λ _ → refl) , tt
run-terms fl (M ∷ Ms) {E} ok e with P.∧-true {value (term (simp fl E M))} e
... | e₁ , e₂ with o-term (run fl M ok) e₁ | run-terms fl Ms ok e₂
...   | v , σ , d | vs , τ , ds = v ∷ vs , st-bind σ (st-bind τ (st-now (λ _ → refl))) , d , ds

run-get fl i L {E} ok c with comp-inv i (known (simp fl E L)) refl c
... | Ks , k , refl with o-known (run fl L ok) k
...   | .(S.tup vs) , σ , (vs , refl , ds) = lookup vs i , st-bind σ (st-now (λ _ → refl)) , dens-lookup ds i

run-unf fl L {E} ok u with o-known (run fl L ok) (unfold-inv (known (simp fl E L)) refl u)
... | .(S.fold v₀) , σ , (v₀ , refl , d) = v₀ , st-bind σ (st-now (λ _ → refl)) , d

run-inl fl L {E} ok b with branch-inl (known (simp fl E L)) refl b
... | k , s with o-known (run fl L ok) k
...   | .(S.inl v₀) , σ , (v₀ , refl , d) = v₀ , σ , ok-self ok s (small-strong _ s d)

run-inr fl L {E} ok b with branch-inr (known (simp fl E L)) refl b
... | k , s with o-known (run fl L ok) k
...   | .(S.inr v₀) , σ , (v₀ , refl , d) = v₀ , σ , ok-self ok s (small-strong _ s d)

run-int fl L {E} ok e with int-inv (known (simp fl E L)) e
... | refl , k with o-known (run fl L ok) k
...   | .(S.const _) , σ , refl = σ

run-let t fl N {I = I} {M = M} {ρ} okf o with small (term I) in s | value (term I)
... | true | _ with opd-val (mono-at ρ M) o (P.small-value (term I) s)
...   | v , σ , d , h = opd-map (λ τ → st-bind σ (st-body t τ)) (run fl N (ok-cons okf d h s))
run-let t fl N okf o | false | true = opd (λ ()) (λ ())
run-let t fl N okf o | false | false = opd (λ ()) (λ ())

run-call (suc fl) (T ∣ just (P.fun N Ef)) I {M = M} hJ o with size (term (simp-let fl Ef N I)) ≤ᵇ inline-size
... | true with o-known hJ refl
...   | _ , σL , (ρf , refl , okf) = opd-map (st-bind σL) (run-let true fl N {M = M} okf o)
run-call (suc fl) (T ∣ just (P.fun N Ef)) I hJ o | false = opd (λ ()) (λ ())
run-call zero J I hJ o = opd (λ ()) (λ ())
run-call (suc fl) (T ∣ nothing) I hJ o = opd (λ ()) (λ ())
run-call (suc fl) (T ∣ just (P.val K)) I hJ o = opd (λ ()) (λ ())

{- Both directions, at each clock ---------------------------------------------------}

{- at clock ck, the source's result is the target's, related, or a timeout
   (forward), and if the target's is not a timeout, the source has a related
   result from some clock on (backward) -}
record Sim {X Y : Set} (R : X → Y → Set) (f : ℕ → Result X) (r : Result Y) (ck : ℕ) : Set where
  constructor both
  field
    fwd : LeResult R (f ck) r
    bwd : Back R f r
open Sim

sim-ret : ∀ {X Y : Set} {R : X → Y → Set} {v w ck} → R v w → Sim R (λ _ → ret v) (ret w) ck
sim-ret r = both (ret r) λ _ → _ , st-now (λ _ → refl) , ret r

{- the continuations are given a value that the source reaches at some clock -}
sim-bind : ∀ {X Y X' Y' : Set} {R : X → Y → Set} {R' : X' → Y' → Set} {f : ℕ → Result X} {g : Result Y}
  {h : ℕ → X → Result X'} {k : Y → Result Y'} {ck} → Sim R f g ck
  → (∀ {v w} → Σ[ c ∈ ℕ ] f c ≡ ret v → R v w → Sim R' (λ c → h c v) (k w) ck)
  → Sim R' (λ c → f c >>= h c) (g >>= k) ck
sim-bind (both le bk) K = both (bind-le le λ e r → fwd (K (_ , e) r)) (back-bind bk λ { (c , e) r → bwd (K (c , e c ≤-refl) r) })

{- the source runs f, which returns v from some clock on, then h -}
sim-run : ∀ {X Y Z : Set} {R : Y → Z → Set} {f : ℕ → Result X} {h : ℕ → X → Result Y} {g v ck}
  → Mono f → Stable f (ret v) → Sim R (λ c → h c v) g ck → Sim R (λ c → f c >>= h c) g ck
sim-run m σ (both le bk) = both (le-stable _ m σ le) (back-run σ bk)

{- the source runs M to a value that the target's value term T describes -}
sim-known : ∀ {Δ Γ A} ck (M : Tm Δ A) ρ {v} {T : Tm Γ A} {ρ'} → Run M ρ v → Strong v T ρ'
  → Sim _≈_ (λ c → S.eval c ρ M) (S.eval ck ρ' T) ck
sim-known ck M ρ σ d with teval _ d
... | w , et , r rewrite et ck =
  both (subst (λ x → LeResult _≈_ x _) (bind-ret (S.eval ck ρ M)) (le-stable ck (mono-at ρ M) σ (ret r))) λ _ → _ , σ , ret r

back-call : ∀ {Δ A B} {N : Tm (A ∷ Δ) B} {ρ w} {r : Result (S.Val B)} → Back _≈_ (λ ck → S.eval ck (w ∷ ρ) N) r
  → Back _≈_ (λ ck → S.call ck (clo N ρ) w) r
back-call bk nt with bk nt
... | r , st , rr = r , st-call st , rr

sim : ∀ ck fl {Δ Γ A} (M : Tm Δ A) {E : Facts Δ Γ} {ρ ρ'} → Ok E ρ ρ'
  → Sim _≈_ (λ c → S.eval c ρ M) (S.eval ck ρ' (term (simp fl E M))) ck
sims : ∀ ck fl {Δ Γ Δ'} (Ms : All (Tm Δ) Δ') {E : Facts Δ Γ} {ρ ρ'} → Ok E ρ ρ'
  → Sim (All₂ _≈_) (λ c → S.evals c ρ Ms) (S.evals ck ρ' (simps fl E Ms)) ck
sim-call : ∀ ck {A B} {f f' : S.Val (A ⇒ B)} {w w'} → f ≈ f' → w ≈ w' → Sim _≈_ (λ c → S.call c f w) (S.call ck f' w') ck
sim-call zero r s = both timeout λ nt → ⊥-elim (nt refl)
sim-call (suc ck) (clo≈ {fl} {N = N} ok) s with sim ck fl N (ok-under ok s)
... | both le bk = both le (back-call bk)
{- a let or a call, as in run-let and run-call -}
body-sim : ∀ {Δ Γ A B} t ck fl (N : Tm (A ∷ Δ) B) {E : Facts (A ∷ Δ) Γ} {ρ v ρ'} → Ok E (v ∷ ρ) ρ'
  → Sim _≈_ (λ c → Body t c N ρ v) (S.eval ck ρ' (term (simp fl E N))) ck
let-sim : ∀ {Δf Δ Γ A B} t ck fl (N : Tm (A ∷ Δf) B) {Ef : Facts Δf Γ} {ρf ρ' I} {M : Tm Δ A} {ρ} → Ok Ef ρf ρ' → Opd (λ ck → S.eval ck ρ M) I ρ'
  → Sim _≈_ (λ c → S.eval c ρ M) (S.eval ck ρ' (term I)) ck
  → Sim _≈_ (Bound t M N ρf ρ) (S.eval ck ρ' (term (simp-let fl Ef N I))) ck
call-sim : ∀ {Δ Γ A B} ck fl (J : Info Γ (A ⇒ B)) I {L : Tm Δ (A ⇒ B)} {M ρ' ρ} → Opd (λ ck → S.eval ck ρ L) J ρ'
  → Sim _≈_ (λ c → S.eval c ρ L) (S.eval ck ρ' (term J)) ck → Opd (λ ck → S.eval ck ρ M) I ρ'
  → Sim _≈_ (λ c → S.eval c ρ M) (S.eval ck ρ' (term I)) ck
  → Sim _≈_ (λ c → S.eval c ρ (app L M)) (S.eval ck ρ' (term (simp-call fl J I))) ck

sims ck fl [] ok = sim-ret []
sims ck fl (M ∷ Ms) ok = sim-bind (sim ck fl M ok) λ _ r → sim-bind (sims ck fl Ms ok) λ _ rs → sim-ret (r ∷ rs)

body-sim true zero fl N ok = both timeout (back-call (bwd (sim zero fl N ok)))
body-sim true (suc ck) fl N {E} {ρ' = ρ'} ok =
  both (le-⊑ (fwd (sim ck fl N ok)) (mono (n≤1+n ck) ρ' (term (simp fl E N)))) (back-call (bwd (sim (suc ck) fl N ok)))
body-sim false ck fl N ok = sim ck fl N ok

let-sim t ck fl N {I = I} {M} {ρ} okf o hM with small (term I) in s | value (term I) in isv
... | true | _ with opd-val (mono-at ρ M) o (P.small-value (term I) s)
...   | v , σ , d , h = sim-run (mono-at ρ M) σ (body-sim t ck fl N (ok-cons okf d h s))
let-sim t ck fl N {I = I} {M} {ρ} okf o hM | false | true =
  sim-bind hM λ e r → body-sim t ck fl N (ok-let {I = I} okf r (opd-kn (mono-at ρ M) o e))
let-sim t ck fl N okf o hM | false | false = sim-bind hM λ _ r → body-sim t ck fl N (ok-under okf r)

call-sim ck (suc fl) (T ∣ just (P.fun N Ef)) I {L} {M} hJ hL o hM with size (term (simp-let fl Ef N I)) ≤ᵇ inline-size
... | true with o-known hJ refl
...   | _ , σL , (ρf , refl , okf) = sim-run (mono-at _ L) σL (let-sim true ck fl N {M = M} okf o hM)
call-sim ck (suc fl) (T ∣ just (P.fun N Ef)) I {L} hJ hL o hM | false = sim-bind hL λ _ r → sim-bind hM λ _ s → sim-call ck r s
call-sim ck zero J I hJ hL o hM = sim-bind hL λ _ r → sim-bind hM λ _ s → sim-call ck r s
call-sim ck (suc fl) (T ∣ nothing) I hJ hL o hM = sim-bind hL λ _ r → sim-bind hM λ _ s → sim-call ck r s
call-sim ck (suc fl) (T ∣ just (P.val K)) I hJ hL o hM = sim-bind hL λ _ r → sim-bind hM λ _ s → sim-call ck r s

sim ck fl (` x) {ρ = ρ} ok = sim-known ck (` x) ρ (st-now (λ _ → refl)) (trm ok x)
sim ck fl (lam N) ok = sim-ret (clo≈ ok)
sim ck fl (app L M) {E} ok with lam? L
... | is-lam N = let-sim true ck fl N {M = M} ok (run fl M ok) (sim ck fl M ok)
... | other = call-sim ck fl (simp fl E L) _ {L = L} {M} (run fl L ok) (sim ck fl L ok) (run fl M ok) (sim ck fl M ok)
sim ck fl (lit B c) ok = sim-ret const≈
sim ck fl (tuple Ms) ok = sim-bind (sims ck fl Ms ok) λ _ rs → sim-ret (tup≈ rs)
sim ck fl (get i L) {E} ok with component i (known (simp fl E L)) refl in c
... | nothing = sim-bind (sim ck fl L ok) λ _ r → sim-ret (nth≈ i r)
... | just K with small K in s | run-get fl i L ok c
...   | true | v , σ , d = sim-known ck (get i L) _ σ (small-strong K s d)
...   | false | _ = sim-bind (sim ck fl L ok) λ _ r → sim-ret (nth≈ i r)
sim ck fl (inl M) ok = sim-bind (sim ck fl M ok) λ _ r → sim-ret (inl≈ r)
sim ck fl (inr M) ok = sim-bind (sim ck fl M ok) λ _ r → sim-ret (inr≈ r)
sim ck fl (case L M N) {E} ok with branch (known (simp fl E L)) refl in b
... | nothing = sim-bind (sim ck fl L ok) λ { _ (inl≈ r) → sim ck fl M (ok-under ok r) ; _ (inr≈ r) → sim ck fl N (ok-under ok r) }
... | just (inj₁ K) with run-inl fl L ok b
...   | v , σ , ok' = sim-run (mono-at _ L) σ (sim ck fl M ok')
sim ck fl (case L M N) {E} ok | just (inj₂ K) with run-inr fl L ok b
...   | v , σ , ok' = sim-run (mono-at _ L) σ (sim ck fl N ok')
sim ck fl (prim p L M) {E} ok with int-of (known (simp fl E L)) in e₁
... | nothing = sim-bind (sim ck fl L ok) λ _ r → sim-bind (sim ck fl M ok) λ _ s → sim-ret (δ≈ p r s)
... | just n with int-of (known (simp fl E M)) in e₂
...   | nothing = sim-bind (sim ck fl L ok) λ _ r → sim-bind (sim ck fl M ok) λ _ s → sim-ret (δ≈ p r s)
...   | just m = sim-known ck (prim p L M) _ (run-prim fl p L M ok e₁ e₂) (prim-strong p n m)
sim ck fl (let′ M N) ok = let-sim false ck fl N {M = M} ok (run fl M ok) (sim ck fl M ok)
sim ck fl (fold M) ok = sim-bind (sim ck fl M ok) λ _ r → sim-ret (fold≈ r)
sim ck fl (unfold L) {E} ok with unfolded (known (simp fl E L)) refl in u
... | nothing = sim-bind (sim ck fl L ok) λ _ r → sim-ret (unfold≈ r)
... | just K with small K in s | run-unf fl L ok u
...   | true | v , σ , d = sim-known ck (unfold L) _ σ (small-strong K s d)
...   | false | _ = sim-bind (sim ck fl L ok) λ _ r → sim-ret (unfold≈ r)

{- The end theorem: for every closed program ----------------------------------------}

ok₀ : Ok (λ x → self (` x)) [] []
ok₀ = mk-ok (λ ()) (λ ()) (λ ())

simplify-correct : ∀ {A} (M : Tm [] A) → Equivalent (S.sem M) (S.sem (simplify M))
simplify-correct M =
  clocked-back _≈_ obs≈ (mono-at [] (simplify M)) (λ ck → fwd (sim ck inline-fuel M ok₀)) (λ ck → bwd (sim ck inline-fuel M ok₀))

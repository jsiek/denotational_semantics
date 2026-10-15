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

  * forward, at the same clock (run≈): the source's result, if it does
    not time out, is the target's, related (LeResult);
  * backward (back): if the target does not time out at a clock, then
    the source has a related result at every large enough clock (Stable);

  and the interpreter's monotonicity in the clock (mono).

  Values are related as in the CEK proof (SimplifySim): the source's on
  the left, a source closure to the simplified body of it, a target
  closure, under Facts that are true of the two environments (Ok); a
  known function is a source closure (KDen). When simp E M returns a
  value term, or M has a known value, the source runs M to a value it
  describes, at every large enough clock (run-term, run-known). A call,
  β or an inlined known function (whose body the source reaches by
  running the operator), is one lemma per direction (run-let, let≈,
  back-let). The interpreters never err, and the theorem holds for every
  closed program.

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

open import Data.Bool using (Bool; true; false; _∧_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Integer using (_≟_)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; zero; suc; _≤_; s≤s; _≤ᵇ_)
open import Data.Nat.Properties using (n≤1+n)
open import Data.Product using (_×_; Σ-syntax; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong; cong₂; subst)
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
  fold≈ : ∀ {A c v w} → v ≈ w → S.fold {A} {c} v ≈ S.fold w

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

unfold≈ : ∀ {A c} {v w : S.Val (μ A {c})} → v ≈ w → S.unfold-v v ≈ S.unfold-v w
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

{- an application whose operator runs to a closure of N -}
via : ∀ {Δf Δ A B} {L : Tm Δ (A ⇒ B)} {M} {N : Tm (A ∷ Δf) B} {ρf ρ} {Q : S.Val B → Set} → Run L ρ (clo N ρf)
  → Σ[ v ∈ S.Val B ] Stable (Bound true M N ρf ρ) (ret v) × Q v → Σ[ v ∈ S.Val B ] Run (app L M) ρ v × Q v
via σL (v , τ , d) = v , st-bind σL τ , d

{- The target evaluates value terms, at any clock ---------------------------------}

teval : ∀ {Γ A} (T : Tm Γ A) {ρ' v} → Strong v T ρ' → Σ[ w ∈ S.Val A ] (∀ ck → S.eval ck ρ' T ≡ ret w) × v ≈ w
tevals : ∀ {Γ Δ} (Ms : All (Tm Γ) Δ) {ρ' vs} → Strongs vs Ms ρ'
  → Σ[ ws ∈ All S.Val Δ ] (∀ ck → S.evals ck ρ' Ms ≡ ret ws) × All₂ _≈_ vs ws
teval (` y) r = _ , (λ ck → refl) , r
teval (lam N) r = _ , (λ ck → refl) , r
teval (lit B c) refl = _ , (λ ck → refl) , const≈
teval (tuple Ms) {ρ'} (vs , refl , ds) with tevals Ms ds
... | ws , e , rs = S.tup ws , ev , tup≈ rs
  where ev : ∀ ck → S.eval ck ρ' (tuple Ms) ≡ ret (S.tup ws)
        ev ck rewrite e ck = refl
teval (inl M) {ρ'} (v , refl , d) with teval M d
... | w , e , r = S.inl w , ev , inl≈ r
  where ev : ∀ ck → S.eval ck ρ' (inl M) ≡ ret (S.inl w)
        ev ck rewrite e ck = refl
teval (inr M) {ρ'} (v , refl , d) with teval M d
... | w , e , r = S.inr w , ev , inr≈ r
  where ev : ∀ ck → S.eval ck ρ' (inr M) ≡ ret (S.inr w)
        ev ck rewrite e ck = refl
teval (fold {A = A} {c} M) {ρ'} (v , refl , d) with teval M d
... | w , e , r = S.fold w , ev , fold≈ r
  where ev : ∀ ck → S.eval ck ρ' (fold {A = A} {c} M) ≡ ret (S.fold {A} {c} w)
        ev ck rewrite e ck = refl
tevals [] {vs = []} tt = [] , (λ ck → refl) , []
tevals (M ∷ Ms) {ρ'} {vs = v ∷ vs} (d , ds) with teval M d | tevals Ms ds
... | w , e , r | ws , es , rs = w ∷ ws , ev , r ∷ rs
  where ev : ∀ ck → S.evals ck ρ' (M ∷ Ms) ≡ ret (w ∷ ws)
        ev ck rewrite e ck | es ck = refl

{- The source runs ahead: run-term and run-known --------------------------------}

{- what the source does with the operand M of a call, whose simplification
   is I: it runs M to the value that I's value term, or its known value,
   describes -}
record Opd {Δ Γ A} (M : Tm Δ A) (ρ : S.Env Δ) (I : Info Γ A) (ρ' : S.Env Γ) : Set where
  constructor opd
  field
    o-term : value (term I) ≡ true → Σ[ v ∈ S.Val A ] Run M ρ v × Strong v (term I) ρ'
    o-known : ∀ {K} → known I ≡ just K → Σ[ v ∈ S.Val A ] Run M ρ v × KDen v K ρ'
open Opd

{- the value of a value operand, described by its term and what it is known to be -}
opd-val : ∀ {Δ Γ A} {I : Info Γ A} {M : Tm Δ A} {ρ' ρ} → Opd M ρ I ρ' → value (term I) ≡ true
  → Σ[ v ∈ S.Val A ] Run M ρ v × Strong v (term I) ρ' × Kn v I ρ'
opd-val {I = I} {M} {ρ'} {ρ} o e with o-term o e
... | v , σ , d = v , σ , d , λ {K} k → G {K} (o-known o k)
  where G : ∀ {K} → Σ[ v' ∈ S.Val _ ] Run M ρ v' × KDen v' K ρ' → KDen v K ρ'
        G (v' , σ' , d') with stable-unique σ' σ
        ... | refl = d'

Fn : ∀ {Δ Γ A} → Tm Δ A → S.Env Δ → Info Γ A → S.Env Γ → Set
Fn L ρ J ρ' = ∀ {K} → known J ≡ just K → Σ[ v ∈ S.Val _ ] Run L ρ v × KDen v K ρ'

run-term : ∀ {Δ Γ A} fl (M : Tm Δ A) {E : Facts Δ Γ} {ρ ρ'} → Ok E ρ ρ' → value (term (simp fl E M)) ≡ true
  → Σ[ v ∈ S.Val A ] Run M ρ v × Strong v (term (simp fl E M)) ρ'
run-known : ∀ {Δ Γ A} fl (M : Tm Δ A) {E : Facts Δ Γ} {ρ ρ' K} → Ok E ρ ρ' → known (simp fl E M) ≡ just K
  → Σ[ v ∈ S.Val A ] Run M ρ v × KDen v K ρ'
run-terms : ∀ {Δ Γ Δ'} fl (Ms : All (Tm Δ) Δ') {E : Facts Δ Γ} {ρ ρ'} → Ok E ρ ρ' → values (simps fl E Ms) ≡ true
  → Σ[ vs ∈ All S.Val Δ' ] Stable (λ ck → S.evals ck ρ Ms) (ret vs) × Strongs vs (simps fl E Ms) ρ'
run-get : ∀ {Δ Γ Δ' A} fl (i : Δ' ∋ A) (L : Tm Δ (tup Δ')) {E : Facts Δ Γ} {ρ ρ' K} → Ok E ρ ρ'
  → component i (known (simp fl E L)) refl ≡ just K → Σ[ v ∈ S.Val A ] Run (get i L) ρ v × Den v K ρ'
run-unf : ∀ {Δ Γ A c} fl (L : Tm Δ (μ A {c})) {E : Facts Δ Γ} {ρ ρ' K} → Ok E ρ ρ'
  → unfolded (known (simp fl E L)) refl ≡ just K → Σ[ v ∈ S.Val _ ] Run (unfold L) ρ v × Den v K ρ'
run-inl : ∀ {Δ Γ A B} fl (L : Tm Δ (A ⊹ B)) {E : Facts Δ Γ} {ρ ρ' K} → Ok E ρ ρ'
  → branch (known (simp fl E L)) refl ≡ just (inj₁ K) → Σ[ v ∈ S.Val A ] Run L ρ (S.inl v) × Strong v K ρ'
run-inr : ∀ {Δ Γ A B} fl (L : Tm Δ (A ⊹ B)) {E : Facts Δ Γ} {ρ ρ' K} → Ok E ρ ρ'
  → branch (known (simp fl E L)) refl ≡ just (inj₂ K) → Σ[ v ∈ S.Val B ] Run L ρ (S.inr v) × Strong v K ρ'
run-int : ∀ {Δ Γ} fl (L : Tm Δ (base Int)) {E : Facts Δ Γ} {ρ ρ' n} → Ok E ρ ρ' → int-of (known (simp fl E L)) ≡ just n
  → Run L ρ (S.const n)
{- a let, or a call: the source runs the operand, then N (run-let), or
   the target calls (run-call) -}
run-let : ∀ {Δf Δ Γ A B} t fl (N : Tm (A ∷ Δf) B) {Ef : Facts Δf Γ} {ρf ρ' I} {M : Tm Δ A} {ρ} → Ok Ef ρf ρ' → Opd M ρ I ρ'
  → value (term (simp-let fl Ef N I)) ≡ true
  → Σ[ v ∈ S.Val B ] Stable (Bound t M N ρf ρ) (ret v) × Strong v (term (simp-let fl Ef N I)) ρ'
known-let : ∀ {Δf Δ Γ A B} t fl (N : Tm (A ∷ Δf) B) {Ef : Facts Δf Γ} {ρf ρ' I} {M : Tm Δ A} {ρ K} → Ok Ef ρf ρ' → Opd M ρ I ρ'
  → known (simp-let fl Ef N I) ≡ just K → Σ[ v ∈ S.Val B ] Stable (Bound t M N ρf ρ) (ret v) × KDen v K ρ'
run-call : ∀ {Δ Γ A B} fl (J : Info Γ (A ⇒ B)) I {L : Tm Δ (A ⇒ B)} {M ρ' ρ} → Fn L ρ J ρ' → Opd M ρ I ρ'
  → value (term (simp-call fl J I)) ≡ true
  → Σ[ v ∈ S.Val B ] Run (app L M) ρ v × Strong v (term (simp-call fl J I)) ρ'
known-call : ∀ {Δ Γ A B} fl (J : Info Γ (A ⇒ B)) I {L : Tm Δ (A ⇒ B)} {M ρ' ρ K} → Fn L ρ J ρ' → Opd M ρ I ρ'
  → known (simp-call fl J I) ≡ just K → Σ[ v ∈ S.Val B ] Run (app L M) ρ v × KDen v K ρ'

run-opd : ∀ {Δ Γ A} fl (M : Tm Δ A) {E : Facts Δ Γ} {ρ ρ'} → Ok E ρ ρ' → Opd M ρ (simp fl E M) ρ'
run-opd fl M ok = opd (run-term fl M ok) (run-known fl M ok)

{- a primitive on known integers -}
run-prim : ∀ {Δ Γ} fl p (L M : Tm Δ (base Int)) {E : Facts Δ Γ} {ρ ρ' n m} → Ok E ρ ρ'
  → int-of (known (simp fl E L)) ≡ just n → int-of (known (simp fl E M)) ≡ just m
  → Run (prim p L M) ρ (S.δ p (S.const n) (S.const m))
run-prim fl p L M ok e₁ e₂ = st-bind (run-int fl L ok e₁) (st-bind (run-int fl M ok e₂) (st-now (λ _ → refl)))

run-term fl (` x) {ρ = ρ} ok e = lookup ρ x , st-now (λ ck → refl) , trm ok x
run-term fl (lam N) ok e = _ , st-now (λ _ → refl) , clo≈ ok
run-term fl (app L M) {E} {ρ = ρ} ok e with lam? L
... | is-lam N = run-let true fl N {ρf = ρ} {M = M} ok (run-opd fl M ok) e
... | other = run-call fl (simp fl E L) _ {L = L} (run-known fl L ok) (run-opd fl M ok) e
run-term fl (lit B c) ok e = _ , st-now (λ _ → refl) , refl
run-term fl (tuple Ms) ok e with run-terms fl Ms ok e
... | vs , σ , ds = S.tup vs , st-bind σ (st-now (λ _ → refl)) , vs , refl , ds
run-term fl (get i L) {E} ok e with component i (known (simp fl E L)) refl in c
... | just K with small K in s
...   | true with run-get fl i L ok c
...     | v , σ , d = v , σ , small-strong K s d
run-term fl (inl M) ok e with run-term fl M ok e
... | v , σ , d = S.inl v , st-bind σ (st-now (λ _ → refl)) , v , refl , d
run-term fl (inr M) ok e with run-term fl M ok e
... | v , σ , d = S.inr v , st-bind σ (st-now (λ _ → refl)) , v , refl , d
run-term fl (case L M N) {E} ok e with branch (known (simp fl E L)) refl in b
... | just (inj₁ K) with run-inl fl L ok b
...   | v , σ , d with run-term fl M (ok-self ok (proj₂ (branch-inl (known (simp fl E L)) refl b)) d) e
...     | w , τ , d' = w , st-bind σ τ , d'
run-term fl (case L M N) {E} ok e | just (inj₂ K) with run-inr fl L ok b
...   | v , σ , d with run-term fl N (ok-self ok (proj₂ (branch-inr (known (simp fl E L)) refl b)) d) e
...     | w , τ , d' = w , st-bind σ τ , d'
run-term fl (prim p L M) {E} ok e with int-of (known (simp fl E L)) in e₁
... | just n with int-of (known (simp fl E M)) in e₂
...   | just m = _ , run-prim fl p L M ok e₁ e₂ , prim-strong p n m
run-term fl (let′ M N) ok e = run-let false fl N ok (run-opd fl M ok) e
run-term fl (fold M) ok e with run-term fl M ok e
... | v , σ , d = S.fold v , st-bind σ (st-now (λ _ → refl)) , v , refl , d
run-term fl (unfold L) {E} ok e with unfolded (known (simp fl E L)) refl in u
... | just K with small K in s
...   | true with run-unf fl L ok u
...     | v , σ , d = v , σ , small-strong K s d

run-terms fl [] ok _ = [] , st-now (λ _ → refl) , tt
run-terms fl (M ∷ Ms) {E} ok e with P.∧-true {value (term (simp fl E M))} e
... | e₁ , e₂ with run-term fl M ok e₁ | run-terms fl Ms ok e₂
...   | v , σ , d | vs , τ , ds = v ∷ vs , st-bind σ (st-bind τ (st-now (λ _ → refl))) , d , ds

run-get fl i L {E} ok c with comp-inv i (known (simp fl E L)) refl c
... | Ks , k , refl with run-known fl L ok k
...   | .(S.tup vs) , σ , (vs , refl , ds) = lookup vs i , st-bind σ (st-now (λ _ → refl)) , dens-lookup ds i

run-unf fl L {E} ok u with run-known fl L ok (unfold-inv (known (simp fl E L)) refl u)
... | .(S.fold v₀) , σ , (v₀ , refl , d) = v₀ , st-bind σ (st-now (λ _ → refl)) , d

run-inl fl L {E} ok b with branch-inl (known (simp fl E L)) refl b
... | k , s with run-known fl L ok k
...   | .(S.inl v₀) , σ , (v₀ , refl , d) = v₀ , σ , small-strong _ s d

run-inr fl L {E} ok b with branch-inr (known (simp fl E L)) refl b
... | k , s with run-known fl L ok k
...   | .(S.inr v₀) , σ , (v₀ , refl , d) = v₀ , σ , small-strong _ s d

run-int fl L {E} ok e with int-inv (known (simp fl E L)) e
... | refl , k with run-known fl L ok k
...   | .(S.const _) , σ , refl = σ

run-known fl (` x) {ρ = ρ} ok k = lookup ρ x , st-now (λ ck → refl) , knw ok x k
run-known fl (lam N) {ρ = ρ} ok refl = _ , st-now (λ _ → refl) , ρ , refl , ok
run-known fl (app L M) {E} {ρ = ρ} ok k with lam? L
... | is-lam N = known-let true fl N {ρf = ρ} {M = M} ok (run-opd fl M ok) k
... | other = known-call fl (simp fl E L) _ {L = L} (run-known fl L ok) (run-opd fl M ok) k
run-known fl (lit B c) ok refl = _ , st-now (λ _ → refl) , refl
run-known fl (tuple Ms) {E} ok k with value (tuple (simps fl E Ms)) in isv
run-known fl (tuple Ms) {E} ok refl | true with run-term fl (tuple Ms) ok isv
... | v , σ , d = v , σ , strong-den (tuple (simps fl E Ms)) d
run-known fl (get i L) {E} ok k with component i (known (simp fl E L)) refl in c
... | just K with small K
run-known fl (get i L) {E} ok refl | just K | true = run-get fl i L ok c
run-known fl (get i L) {E} ok refl | just K | false = run-get fl i L ok c
run-known fl (inl M) {E} ok k with value (term (simp fl E M)) in isv
run-known fl (inl M) {E} ok refl | true with run-term fl (inl M) ok isv
... | v , σ , d = v , σ , strong-den (inl (term (simp fl E M))) d
run-known fl (inr M) {E} ok k with value (term (simp fl E M)) in isv
run-known fl (inr M) {E} ok refl | true with run-term fl (inr M) ok isv
... | v , σ , d = v , σ , strong-den (inr (term (simp fl E M))) d
run-known fl (case L M N) {E} ok k with branch (known (simp fl E L)) refl in b
... | just (inj₁ K) with run-inl fl L ok b
...   | v , σ , d with run-known fl M (ok-self ok (proj₂ (branch-inl (known (simp fl E L)) refl b)) d) k
...     | w , τ , d' = w , st-bind σ τ , d'
run-known fl (case L M N) {E} ok k | just (inj₂ K) with run-inr fl L ok b
...   | v , σ , d with run-known fl N (ok-self ok (proj₂ (branch-inr (known (simp fl E L)) refl b)) d) k
...     | w , τ , d' = w , st-bind σ τ , d'
run-known fl (prim p L M) {E} ok k with int-of (known (simp fl E L)) in e₁
... | just n with int-of (known (simp fl E M)) in e₂
run-known fl (prim p L M) {E} ok refl | just n | just m =
  _ , run-prim fl p L M ok e₁ e₂ , strong-den (prim-term p n m) (prim-strong p n m)
run-known fl (let′ M N) ok k = known-let false fl N ok (run-opd fl M ok) k
run-known fl (fold M) {E} ok k with value (term (simp fl E M)) in isv
run-known fl (fold M) {E} ok refl | true with run-term fl (fold M) ok isv
... | v , σ , d = v , σ , strong-den (fold (term (simp fl E M))) d
run-known fl (unfold L) {E} ok k with unfolded (known (simp fl E L)) refl in u
... | just K with small K
run-known fl (unfold L) {E} ok refl | just K | true = run-unf fl L ok u
run-known fl (unfold L) {E} ok refl | just K | false = run-unf fl L ok u

run-let t fl N {I = I} okf o e with small (term I) in s | value (term I) in isv
... | true | _ with opd-val o (P.small-value (term I) s)
...   | v , σ , d , h with run-term fl N (ok-cons okf d h s) e
...     | w , τ , d' = w , st-bind σ (st-body t τ) , d'
run-let t fl N {I = I} okf o () | false | true
run-let t fl N {I = I} okf o () | false | false

known-let t fl N {I = I} okf o k with small (term I) in s | value (term I) in isv
... | true | _ with opd-val o (P.small-value (term I) s)
...   | v , σ , d , h with run-known fl N (ok-cons okf d h s) k
...     | w , τ , d' = w , st-bind σ (st-body t τ) , d'
known-let t fl N {I = I} okf o () | false | true
known-let t fl N {I = I} okf o () | false | false

run-call (suc fl) (T ∣ just (P.fun N Ef)) I {L} {M} hJ o e with size (term (simp-let fl Ef N I)) ≤ᵇ inline-size
... | true with hJ refl
...   | _ , σL , (ρf , refl , okf) = via {L = L} {M} σL (run-let true fl N {M = M} okf o e)
run-call (suc fl) (T ∣ just (P.fun N Ef)) I {L} {M} hJ o () | false
run-call zero J I hJ o ()
run-call (suc fl) (T ∣ nothing) I hJ o ()
run-call (suc fl) (T ∣ just (P.val K)) I hJ o ()

known-call (suc fl) (T ∣ just (P.fun N Ef)) I {L} {M} hJ o k with size (term (simp-let fl Ef N I)) ≤ᵇ inline-size
... | true with hJ refl
...   | _ , σL , (ρf , refl , okf) = via {L = L} {M} σL (known-let true fl N {M = M} okf o k)
known-call (suc fl) (T ∣ just (P.fun N Ef)) I {L} {M} hJ o () | false
known-call zero J I hJ o ()
known-call (suc fl) (T ∣ nothing) I hJ o ()
known-call (suc fl) (T ∣ just (P.val K)) I hJ o ()

{- Forward, at the same clock ------------------------------------------------------}

{- the source runs M to a value that the target's value term T describes -}
known-le : ∀ {Δ Γ A} ck (M : Tm Δ A) ρ {v} {T : Tm Γ A} {ρ'} → Run M ρ v → Strong v T ρ' → LeResult _≈_ (S.eval ck ρ M) (S.eval ck ρ' T)
known-le ck M ρ σ d with teval _ d
... | w , et , r rewrite et ck = subst (λ x → LeResult _≈_ x _) (bind-ret (S.eval ck ρ M)) (le-stable ck (mono-at ρ M) σ (ret r))

run≈ : ∀ ck fl {Δ Γ A} (M : Tm Δ A) {E : Facts Δ Γ} {ρ ρ'} → Ok E ρ ρ' → LeResult _≈_ (S.eval ck ρ M) (S.eval ck ρ' (term (simp fl E M)))
runs≈ : ∀ ck fl {Δ Γ Δ'} (Ms : All (Tm Δ) Δ') {E : Facts Δ Γ} {ρ ρ'} → Ok E ρ ρ'
  → LeResult (All₂ _≈_) (S.evals ck ρ Ms) (S.evals ck ρ' (simps fl E Ms))
call≈ : ∀ ck {A B} {f f' : S.Val (A ⇒ B)} {w w'} → f ≈ f' → w ≈ w' → LeResult _≈_ (S.call ck f w) (S.call ck f' w')
call≈ zero r s = timeout
call≈ (suc ck) (clo≈ {fl} {N = N} ok) s = run≈ ck fl N (ok-under ok s)
{- a let or a call, as in run-let and run-call -}
body-le : ∀ {Δ Γ A B} t ck fl (N : Tm (A ∷ Δ) B) {E : Facts (A ∷ Δ) Γ} {ρ v ρ'} → Ok E (v ∷ ρ) ρ'
  → LeResult _≈_ (Body t ck N ρ v) (S.eval ck ρ' (term (simp fl E N)))
let≈ : ∀ {Δf Δ Γ A B} t ck fl (N : Tm (A ∷ Δf) B) {Ef : Facts Δf Γ} {ρf ρ' I} {M : Tm Δ A} {ρ} → Ok Ef ρf ρ' → Opd M ρ I ρ'
  → LeResult _≈_ (S.eval ck ρ M) (S.eval ck ρ' (term I))
  → LeResult _≈_ (Bound t M N ρf ρ ck) (S.eval ck ρ' (term (simp-let fl Ef N I)))
call-le : ∀ {Δ Γ A B} ck fl (J : Info Γ (A ⇒ B)) I {L : Tm Δ (A ⇒ B)} {M ρ' ρ} → Fn L ρ J ρ'
  → LeResult _≈_ (S.eval ck ρ L) (S.eval ck ρ' (term J)) → Opd M ρ I ρ' → LeResult _≈_ (S.eval ck ρ M) (S.eval ck ρ' (term I))
  → LeResult _≈_ (S.eval ck ρ (app L M)) (S.eval ck ρ' (term (simp-call fl J I)))

runs≈ ck fl [] ok = ret []
runs≈ ck fl (M ∷ Ms) ok = bind-le (run≈ ck fl M ok) (λ _ r → bind-le (runs≈ ck fl Ms ok) (λ _ rs → ret (r ∷ rs)))

body-le true zero fl N ok = timeout
body-le true (suc ck) fl N {E} {ρ' = ρ'} ok = le-⊑ (run≈ ck fl N ok) (mono (n≤1+n ck) ρ' (term (simp fl E N)))
body-le false ck fl N ok = run≈ ck fl N ok

let≈ t ck fl N {I = I} {M} {ρ} okf o hM with small (term I) in s | value (term I) in isv
... | true | _ with opd-val o (P.small-value (term I) s)
...   | v , σ , d , h = le-stable ck (mono-at ρ M) σ (body-le t ck fl N (ok-cons okf d h s))
let≈ t ck fl N {Ef} {ρf} {ρ'} {I} {M} {ρ} okf o hM | false | true with opd-val o isv
... | v₀ , σ , d , h = bind-le hM λ e r → G (stable-ret (mono-at ρ M) σ e) r
  where
  G : ∀ {v w} → v ≡ v₀ → v ≈ w → LeResult _≈_ (Body t ck N ρf v) (S.eval ck (w ∷ ρ') (term (simp fl (known-as I Ef) N)))
  G refl r = body-le t ck fl N (ok-let {I = I} okf r h)
let≈ t ck fl N okf o hM | false | false = bind-le hM λ _ r → body-le t ck fl N (ok-under okf r)

call-le ck (suc fl) (T ∣ just (P.fun N Ef)) I {L} hJ hL o hM with size (term (simp-let fl Ef N I)) ≤ᵇ inline-size
... | true with hJ refl
...   | _ , σL , (ρf , refl , okf) = le-stable ck (mono-at _ L) σL (let≈ true ck fl N okf o hM)
call-le ck (suc fl) (T ∣ just (P.fun N Ef)) I {L} hJ hL o hM | false = bind-le hL (λ _ r → bind-le hM (λ _ s → call≈ ck r s))
call-le ck zero J I hJ hL o hM = bind-le hL (λ _ r → bind-le hM (λ _ s → call≈ ck r s))
call-le ck (suc fl) (T ∣ nothing) I hJ hL o hM = bind-le hL (λ _ r → bind-le hM (λ _ s → call≈ ck r s))
call-le ck (suc fl) (T ∣ just (P.val K)) I hJ hL o hM = bind-le hL (λ _ r → bind-le hM (λ _ s → call≈ ck r s))

run≈ ck fl (` x) {ρ = ρ} ok = known-le ck (` x) ρ (st-now (λ ck → refl)) (trm ok x)
run≈ ck fl (lam N) ok = ret (clo≈ ok)
run≈ ck fl (app L M) {E} ok with lam? L
... | is-lam N = let≈ true ck fl N ok (run-opd fl M ok) (run≈ ck fl M ok)
... | other = call-le ck fl (simp fl E L) _ {L = L} (run-known fl L ok) (run≈ ck fl L ok) (run-opd fl M ok) (run≈ ck fl M ok)
run≈ ck fl (lit B c) ok = ret const≈
run≈ ck fl (tuple Ms) ok = bind-le (runs≈ ck fl Ms ok) (λ _ rs → ret (tup≈ rs))
run≈ ck fl (get i L) {E} ok with component i (known (simp fl E L)) refl in c
... | nothing = bind-le (run≈ ck fl L ok) (λ _ r → ret (nth≈ i r))
... | just K with small K in s
...   | true with run-get fl i L ok c
...     | v , σ , d = known-le ck (get i L) _ σ (small-strong K s d)
run≈ ck fl (get i L) {E} ok | just K | false = bind-le (run≈ ck fl L ok) (λ _ r → ret (nth≈ i r))
run≈ ck fl (inl M) ok = bind-le (run≈ ck fl M ok) (λ _ r → ret (inl≈ r))
run≈ ck fl (inr M) ok = bind-le (run≈ ck fl M ok) (λ _ r → ret (inr≈ r))
run≈ ck fl (case L M N) {E} ok with branch (known (simp fl E L)) refl in b
... | nothing = bind-le (run≈ ck fl L ok) λ { _ (inl≈ r) → run≈ ck fl M (ok-under ok r) ; _ (inr≈ r) → run≈ ck fl N (ok-under ok r) }
... | just (inj₁ K) with run-inl fl L ok b
...   | v , σ , d = le-stable ck (mono-at _ L) σ (run≈ ck fl M (ok-self ok (proj₂ (branch-inl (known (simp fl E L)) refl b)) d))
run≈ ck fl (case L M N) {E} ok | just (inj₂ K) with run-inr fl L ok b
...   | v , σ , d = le-stable ck (mono-at _ L) σ (run≈ ck fl N (ok-self ok (proj₂ (branch-inr (known (simp fl E L)) refl b)) d))
run≈ ck fl (prim p L M) {E} ok with int-of (known (simp fl E L)) in e₁
... | nothing = bind-le (run≈ ck fl L ok) (λ _ r → bind-le (run≈ ck fl M ok) (λ _ s → ret (δ≈ p r s)))
... | just n with int-of (known (simp fl E M)) in e₂
...   | nothing = bind-le (run≈ ck fl L ok) (λ _ r → bind-le (run≈ ck fl M ok) (λ _ s → ret (δ≈ p r s)))
...   | just m = known-le ck (prim p L M) _ (run-prim fl p L M ok e₁ e₂) (prim-strong p n m)
run≈ ck fl (let′ M N) ok = let≈ false ck fl N ok (run-opd fl M ok) (run≈ ck fl M ok)
run≈ ck fl (fold M) ok = bind-le (run≈ ck fl M ok) (λ _ r → ret (fold≈ r))
run≈ ck fl (unfold L) {E} ok with unfolded (known (simp fl E L)) refl in u
... | nothing = bind-le (run≈ ck fl L ok) (λ _ r → ret (unfold≈ r))
... | just K with small K in s
...   | true with run-unf fl L ok u
...     | v , σ , d = known-le ck (unfold L) _ σ (small-strong K s d)
run≈ ck fl (unfold L) {E} ok | just K | false = bind-le (run≈ ck fl L ok) (λ _ r → ret (unfold≈ r))

{- Backward: the source catches up -------------------------------------------------}

{- the source runs M to a value that the target's value term T describes -}
known-back : ∀ {Δ Γ A} ck (M : Tm Δ A) ρ {v} {T : Tm Γ A} {ρ'} → Run M ρ v → Strong v T ρ' → Back _≈_ (λ ck → S.eval ck ρ M) (S.eval ck ρ' T)
known-back ck M ρ σ d _ with teval _ d
... | w , et , r rewrite et ck = _ , σ , ret r

{- a value of the source, against the target's -}
now : ∀ {X Y : Set} {R : X → Y → Set} {f : ℕ → Result X} {v w} {r₂ : Result Y} → (∀ ck → f ck ≡ ret v) → r₂ ≡ ret w → R v w → Back R f r₂
now e refl r _ = _ , st-now e , ret r

back : ∀ ck fl {Δ Γ A} (M : Tm Δ A) {E : Facts Δ Γ} {ρ ρ'} → Ok E ρ ρ' → Back _≈_ (λ ck → S.eval ck ρ M) (S.eval ck ρ' (term (simp fl E M)))
backs : ∀ ck fl {Δ Γ Δ'} (Ms : All (Tm Δ) Δ') {E : Facts Δ Γ} {ρ ρ'} → Ok E ρ ρ'
  → Back (All₂ _≈_) (λ ck → S.evals ck ρ Ms) (S.evals ck ρ' (simps fl E Ms))
call-back : ∀ ck {A B} {f f' : S.Val (A ⇒ B)} {w w'} → f ≈ f' → w ≈ w' → Back _≈_ (λ ck → S.call ck f w) (S.call ck f' w')
call-back zero r s nt = ⊥-elim (nt refl)
call-back (suc ck) (clo≈ {fl} {N = N} ok) s nt with back ck fl N (ok-under ok s) nt
... | r , st , rr = r , st-call st , rr
{- a let or a call, as in run-let and run-call -}
body-back : ∀ {Δ Γ A B} t ck fl (N : Tm (A ∷ Δ) B) {E : Facts (A ∷ Δ) Γ} {ρ v ρ'} → Ok E (v ∷ ρ) ρ'
  → Back _≈_ (λ ck → Body t ck N ρ v) (S.eval ck ρ' (term (simp fl E N)))
back-let : ∀ {Δf Δ Γ A B} t ck fl (N : Tm (A ∷ Δf) B) {Ef : Facts Δf Γ} {ρf ρ' I} {M : Tm Δ A} {ρ} → Ok Ef ρf ρ' → Opd M ρ I ρ'
  → Back _≈_ (λ ck → S.eval ck ρ M) (S.eval ck ρ' (term I))
  → Back _≈_ (Bound t M N ρf ρ) (S.eval ck ρ' (term (simp-let fl Ef N I)))
back-call' : ∀ {Δ Γ A B} ck fl (J : Info Γ (A ⇒ B)) I {L : Tm Δ (A ⇒ B)} {M ρ' ρ} → Fn L ρ J ρ'
  → Back _≈_ (λ ck → S.eval ck ρ L) (S.eval ck ρ' (term J)) → Opd M ρ I ρ' → Back _≈_ (λ ck → S.eval ck ρ M) (S.eval ck ρ' (term I))
  → Back _≈_ (λ ck → S.eval ck ρ (app L M)) (S.eval ck ρ' (term (simp-call fl J I)))

backs ck fl [] ok = now (λ _ → refl) refl []
backs ck fl (M ∷ Ms) ok =
  back-bind (back ck fl M ok) (λ _ r → back-bind (backs ck fl Ms ok) (λ _ rs → now (λ _ → refl) refl (r ∷ rs)))

body-back true ck fl N ok nt with back ck fl N ok nt
... | r , st , rr = r , st-call st , rr
body-back false ck fl N ok = back ck fl N ok

back-let t ck fl N {ρf = ρf} {I = I} {M} okf o hM with small (term I) in s | value (term I) in isv
... | true | _ with opd-val o (P.small-value (term I) s)
...   | v , σ , d , h = back-run {g = λ c v → Body t c N ρf v} σ (body-back t ck fl N (ok-cons okf d h s))
back-let t ck fl N {ρ' = ρ'} {I = I} {M} {ρ} okf o hM | false | true with opd-val o isv
... | v₀ , σ , d , h = back-bind hM λ st r → body-back t ck fl N (ok-let {I = I} okf r (h' st))
  where h' : ∀ {v} → Stable (λ ck → S.eval ck ρ M) (ret v) → Kn v I ρ'
        h' st k with stable-unique st σ
        ... | refl = h k
back-let t ck fl N okf o hM | false | false = back-bind hM λ _ r → body-back t ck fl N (ok-under okf r)

back-call' ck (suc fl) (T ∣ just (P.fun N Ef)) I {L} hJ hL o hM with size (term (simp-let fl Ef N I)) ≤ᵇ inline-size
... | true with hJ refl
...   | _ , σL , (ρf , refl , okf) = back-run σL (back-let true ck fl N okf o hM)
back-call' ck (suc fl) (T ∣ just (P.fun N Ef)) I {L} hJ hL o hM | false =
  back-bind hL (λ _ r → back-bind hM (λ _ s → call-back ck r s))
back-call' ck zero J I hJ hL o hM = back-bind hL (λ _ r → back-bind hM (λ _ s → call-back ck r s))
back-call' ck (suc fl) (T ∣ nothing) I hJ hL o hM = back-bind hL (λ _ r → back-bind hM (λ _ s → call-back ck r s))
back-call' ck (suc fl) (T ∣ just (P.val K)) I hJ hL o hM = back-bind hL (λ _ r → back-bind hM (λ _ s → call-back ck r s))

back ck fl (` x) {ρ = ρ} ok = known-back ck (` x) ρ (st-now (λ ck → refl)) (trm ok x)
back ck fl (lam N) ok = now (λ _ → refl) refl (clo≈ ok)
back ck fl (app L M) {E} ok with lam? L
... | is-lam N = back-let true ck fl N ok (run-opd fl M ok) (back ck fl M ok)
... | other = back-call' ck fl (simp fl E L) _ {L = L} (run-known fl L ok) (back ck fl L ok) (run-opd fl M ok) (back ck fl M ok)
back ck fl (lit B c) ok = now (λ _ → refl) refl const≈
back ck fl (tuple Ms) ok = back-bind (backs ck fl Ms ok) (λ _ rs → now (λ _ → refl) refl (tup≈ rs))
back ck fl (get i L) {E} ok with component i (known (simp fl E L)) refl in c
... | nothing = back-bind (back ck fl L ok) (λ _ r → now (λ _ → refl) refl (nth≈ i r))
... | just K with small K in s
...   | true with run-get fl i L ok c
...     | v , σ , d = known-back ck (get i L) _ σ (small-strong K s d)
back ck fl (get i L) {E} ok | just K | false = back-bind (back ck fl L ok) (λ _ r → now (λ _ → refl) refl (nth≈ i r))
back ck fl (inl M) ok = back-bind (back ck fl M ok) (λ _ r → now (λ _ → refl) refl (inl≈ r))
back ck fl (inr M) ok = back-bind (back ck fl M ok) (λ _ r → now (λ _ → refl) refl (inr≈ r))
back ck fl (case L M N) {E} ok with branch (known (simp fl E L)) refl in b
... | nothing = back-bind (back ck fl L ok) λ { _ (inl≈ r) → back ck fl M (ok-under ok r) ; _ (inr≈ r) → back ck fl N (ok-under ok r) }
... | just (inj₁ K) with run-inl fl L ok b
...   | v , σ , d =
  back-run {g = λ c u → S.either u (λ v → S.eval c (v ∷ _) M) (λ v → S.eval c (v ∷ _) N)} σ
    (back ck fl M (ok-self ok (proj₂ (branch-inl (known (simp fl E L)) refl b)) d))
back ck fl (case L M N) {E} ok | just (inj₂ K) with run-inr fl L ok b
...   | v , σ , d =
  back-run {g = λ c u → S.either u (λ v → S.eval c (v ∷ _) M) (λ v → S.eval c (v ∷ _) N)} σ
    (back ck fl N (ok-self ok (proj₂ (branch-inr (known (simp fl E L)) refl b)) d))
back ck fl (prim p L M) {E} ok with int-of (known (simp fl E L)) in e₁
... | nothing = back-bind (back ck fl L ok) (λ _ r → back-bind (back ck fl M ok) (λ _ s → now (λ _ → refl) refl (δ≈ p r s)))
... | just n with int-of (known (simp fl E M)) in e₂
...   | nothing = back-bind (back ck fl L ok) (λ _ r → back-bind (back ck fl M ok) (λ _ s → now (λ _ → refl) refl (δ≈ p r s)))
...   | just m = known-back ck (prim p L M) _ (run-prim fl p L M ok e₁ e₂) (prim-strong p n m)
back ck fl (let′ M N) ok = back-let false ck fl N ok (run-opd fl M ok) (back ck fl M ok)
back ck fl (fold M) ok = back-bind (back ck fl M ok) (λ _ r → now (λ _ → refl) refl (fold≈ r))
back ck fl (unfold L) {E} ok with unfolded (known (simp fl E L)) refl in u
... | nothing = back-bind (back ck fl L ok) (λ _ r → now (λ _ → refl) refl (unfold≈ r))
... | just K with small K in s
...   | true with run-unf fl L ok u
...     | v , σ , d = known-back ck (unfold L) _ σ (small-strong K s d)
back ck fl (unfold L) {E} ok | just K | false = back-bind (back ck fl L ok) (λ _ r → now (λ _ → refl) refl (unfold≈ r))

{- The end theorem: for every closed program ----------------------------------------}

ok₀ : Ok (λ x → self (` x)) [] []
ok₀ = mk-ok (λ ()) (λ ()) (λ ())

simplify-correct : ∀ {A} (M : Tm [] A) → Equivalent (S.sem M) (S.sem (simplify M))
simplify-correct M =
  clocked-back _≈_ obs≈ (mono-at [] (simplify M)) (λ ck → run≈ ck inline-fuel M ok₀) (λ ck → back ck inline-fuel M ok₀)

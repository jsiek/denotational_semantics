{-

  Correctness of the simplify pass (ISWIM → ISWIM) for the clocked
  interpreters (see the design note in Clock.agda).

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
  back-let). The end theorem is for closed programs.

-}

module proof.Correctness.Interp.SimplifyFuel where

open import Framework.Primitives using (Int)
open import Framework.Syntax.SyntaxUtil using (_,,_; Nil; ⟩_,,_)
open import Language.ISWIM
open import Language.Prim using (int; bool; δ)
open import proof.Compiler.SimplifyFacts as P
  using (Info; _∣_; term; known; Known; val; fun; Facts; self; info; under; known-as; shift-info; shift-known;
         simp; simp-args; simp-app; simp-call; simp-let; lam?; is-lam; other; size; inline-size; inline-fuel; simp-get; simp-case; simp-prim; simplify; small; atom; value; values;
         component; branch; int-of; prim-term; value-sv; small-sv; comp-inv; int-inv; branch-inl; branch-inr)
open import Compiler.CaptureScope using (Closed)
open import proof.Compiler.SimplifyScope using (closed-ws)
open import Framework.Syntax.Rename Op sig using (rename; rename-args; shift)
open import Framework.Syntax.Scope Op sig using (WS; WS-args)
open import Semantics.Observation
open import proof.Semantics.Interp.Clock
open import proof.Framework.ListUtil
import Semantics.Interp.ISWIM as S

open import Data.Bool using (Bool; true; false; _∧_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; length; map; replicate; reverse; reverseAcc)
open import Data.List.Properties using (reverse-involutive)
open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_; reverse⁺)
open import Data.Maybe using (just; nothing)
import Data.Maybe.Relation.Binary.Pointwise as M
open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; s≤s; _≤ᵇ_)
open import Data.Nat.Properties using (n≤1+n)
open import Data.Product using (_×_; Σ-syntax; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong; cong₂; subst)

{- The relation ------------------------------------------------------------------}

infix 4 _≈_

data _≈_ : S.Val → S.Val → Set
{- the value term T denotes, in ρ', a value that v is related to (Strong);
   or the same, but a function describes any value (Den) -}
Desc : Bool → S.Val → AST → S.Env → Set
Descs : Bool → ∀ {n} → List S.Val → Args (replicate n ■) → S.Env → Set
Strong Den : S.Val → AST → S.Env → Set
Strong = Desc true
Den = Desc false

{- what a value is known to be is true of it: a value that describes it,
   or a function λ N that is a source closure of N, under Facts true of
   the closure's environment and the target's -}
KDen : S.Val → Known → S.Env → Set

{- what simp knows of each variable is true of the source's environment ρ
   and the target's ρ' -}
record Ok (E : Facts) (ρ ρ' : S.Env) : Set where
  inductive
  constructor mk-ok
  field
    trm : ∀ x {v} → ρ ‼ x ≡ just v → Strong v (term (E x)) ρ'
    knw : ∀ x {v K} → ρ ‼ x ≡ just v → known (E x) ≡ just K → KDen v K ρ'
    sml : ∀ x → small (term (E x)) ≡ true

{- the source's value on the left -}
data _≈_ where
  clo≈ : ∀ {fl E N ρ' ρ} → Ok E ρ ρ' → WS (suc (length ρ)) N → S.clo N ρ ≈ S.clo (term (simp fl (under E) N)) ρ'
  const≈ : ∀ {B k} → S.const B k ≈ S.const B k
  tup≈ : ∀ {vs ws} → Pointwise _≈_ vs ws → S.tup vs ≈ S.tup ws
  inl≈ : ∀ {v w} → v ≈ w → S.inl v ≈ S.inl w
  inr≈ : ∀ {v w} → v ≈ w → S.inr v ≈ S.inr w

Desc b v (` y) ρ' = Σ[ w ∈ S.Val ] ρ' ‼ y ≡ just w × v ≈ w
Desc true v (lam ⦅ ⟩ N ,, Nil ⦆) ρ' = v ≈ S.clo N ρ'
Desc false v (lam ⦅ ⟩ N ,, Nil ⦆) ρ' = ⊤
Desc b v (lit B k ⦅ Nil ⦆) ρ' = v ≡ S.const B k
Desc b v (tuple n ⦅ as ⦆) ρ' = Σ[ vs ∈ List S.Val ] v ≡ S.tup vs × Descs b vs as ρ'
Desc b v (inl-op ⦅ M ,, Nil ⦆) ρ' = Σ[ v₀ ∈ S.Val ] v ≡ S.inl v₀ × Desc b v₀ M ρ'
Desc b v (inr-op ⦅ M ,, Nil ⦆) ρ' = Σ[ v₀ ∈ S.Val ] v ≡ S.inr v₀ × Desc b v₀ M ρ'
Desc b v _ ρ' = ⊥
Descs b {zero} vs Nil ρ' = vs ≡ []
Descs b {suc n} vs (M ,, as) ρ' = Σ[ v ∈ S.Val ] Σ[ vs' ∈ List S.Val ] vs ≡ v ∷ vs' × Desc b v M ρ' × Descs b vs' as ρ'

KDen v (val K) ρ' = Den v K ρ'
KDen v (fun N E) ρ' = Σ[ ρ ∈ S.Env ] v ≡ S.clo N ρ × Ok E ρ ρ' × WS (suc (length ρ)) N

Strongs Dens : ∀ {n} → List S.Val → Args (replicate n ■) → S.Env → Set
Strongs = Descs true
Dens = Descs false

open Ok

{- Related values are observed alike -------------------------------------------}

obs≈ : ∀ {v w} → v ≈ w → S.obs v ≡ S.obs w
obs≈-list : ∀ {vs ws} → Pointwise _≈_ vs ws → S.obs-list vs ≡ S.obs-list ws
obs≈ (clo≈ _ _) = refl
obs≈ const≈ = refl
obs≈ (tup≈ rs) = cong o-tuple (obs≈-list rs)
obs≈ (inl≈ r) = cong o-inl (obs≈ r)
obs≈ (inr≈ r) = cong o-inr (obs≈ r)
obs≈-list [] = refl
obs≈-list (r ∷ rs) = cong₂ _∷_ (obs≈ r) (obs≈-list rs)

prim≈ : ∀ p {v₁ v₂ w₁ w₂} → v₁ ≈ w₁ → v₂ ≈ w₂ → M.Pointwise _≈_ (S.prim? p v₁ v₂) (S.prim? p w₁ w₂)
prim≈ p {w₁ = w₁} {w₂ = w₂} r s rewrite obs≈ r | obs≈ s with δ? p (S.obs w₁) (S.obs w₂)
... | nothing = M.nothing
... | just (int n) = M.just const≈
... | just (bool true) = M.just (inl≈ (tup≈ []))
... | just (bool false) = M.just (inr≈ (tup≈ []))

{- Describing values --------------------------------------------------------------}

strong-den : ∀ T {ρ' v} → Strong v T ρ' → Den v T ρ'
strongs-den : ∀ {n} (as : Args (replicate n ■)) {ρ' vs} → Strongs vs as ρ' → Dens vs as ρ'
strong-den (` y) d = d
strong-den (lam ⦅ ⟩ N ,, Nil ⦆) d = tt
strong-den (lit B k ⦅ Nil ⦆) d = d
strong-den (tuple n ⦅ as ⦆) (vs , e , ds) = vs , e , strongs-den as ds
strong-den (inl-op ⦅ M ,, Nil ⦆) (v , e , d) = v , e , strong-den M d
strong-den (inr-op ⦅ M ,, Nil ⦆) (v , e , d) = v , e , strong-den M d
strongs-den {zero} Nil e = e
strongs-den {suc n} (M ,, as) (v , vs , e , d , ds) = v , vs , e , strong-den M d , strongs-den as ds

{- a small value has no functions -}
atom-strong : ∀ T {ρ' v} → atom T ≡ true → Den v T ρ' → Strong v T ρ'
atom-strong (` y) _ d = d
atom-strong (lit B k ⦅ Nil ⦆) _ d = d
atom-strong (tuple zero ⦅ Nil ⦆) _ d = d

small-strong : ∀ T {ρ' v} → small T ≡ true → Den v T ρ' → Strong v T ρ'
small-strong (inl-op ⦅ M ,, Nil ⦆) s (v , e , d) = v , e , atom-strong M s d
small-strong (inr-op ⦅ M ,, Nil ⦆) s (v , e , d) = v , e , atom-strong M s d
small-strong (` y) s d = d
small-strong (lit B k ⦅ Nil ⦆) s d = d
small-strong (tuple zero ⦅ Nil ⦆) s d = d

atom-shift : ∀ T → atom T ≡ true → atom (shift T) ≡ true
atom-shift (` y) s = refl
atom-shift (lit B k ⦅ Nil ⦆) s = refl
atom-shift (tuple zero ⦅ Nil ⦆) s = refl

small-shift : ∀ T → small T ≡ true → small (shift T) ≡ true
small-shift (inl-op ⦅ M ,, Nil ⦆) s = atom-shift M s
small-shift (inr-op ⦅ M ,, Nil ⦆) s = atom-shift M s
small-shift (` y) s = refl
small-shift (lit B k ⦅ Nil ⦆) s = refl
small-shift (tuple zero ⦅ Nil ⦆) s = refl

den-shift : ∀ K {ρ' v w} → Den v K ρ' → Den v (shift K) (w ∷ ρ')
dens-shift : ∀ {n} (as : Args (replicate n ■)) {ρ' vs w} → Dens vs as ρ' → Dens vs (rename-args suc as) (w ∷ ρ')
den-shift (` y) d = d
den-shift (lam ⦅ ⟩ N ,, Nil ⦆) d = tt
den-shift (lit B k ⦅ Nil ⦆) d = d
den-shift (tuple n ⦅ as ⦆) (vs , e , ds) = vs , e , dens-shift as ds
den-shift (inl-op ⦅ M ,, Nil ⦆) (v , e , d) = v , e , den-shift M d
den-shift (inr-op ⦅ M ,, Nil ⦆) (v , e , d) = v , e , den-shift M d
dens-shift {zero} Nil e = e
dens-shift {suc n} (M ,, as) (v , vs , e , d , ds) = v , vs , e , den-shift M d , dens-shift as ds

{- under one more variable, in the target -}
strong-shift : ∀ T {ρ' v w} → small T ≡ true → Strong v T ρ' → Strong v (shift T) (w ∷ ρ')
strong-shift T s d = small-strong (shift T) (small-shift T s) (den-shift T (strong-den T d))

{- the result of a primitive -}
prim-strong : ∀ o {ρ'} → Strong (S.out o) (prim-term o) ρ'
prim-strong (int n) = refl
prim-strong (bool true) = S.tup [] , refl , [] , refl , refl
prim-strong (bool false) = S.tup [] , refl , [] , refl , refl

{- a component of a described tuple -}
dens-pw : ∀ {n} (Ks : Args (replicate n ■)) {ρ' vs} → Dens vs Ks ρ' → Pointwise (λ v K → Den v K ρ') vs (args→list Ks)
dens-pw {zero} Nil refl = []
dens-pw {suc n} (K ,, Ks) (v , vs , refl , d , ds) = d ∷ dens-pw Ks ds

dens-proj : ∀ {n m} (i : Fin n) (Ks : Args (replicate m ■)) {ρ' vs K} → Dens vs Ks ρ' → proj i (args→list Ks) ≡ just K
  → Σ[ v ∈ S.Val ] proj i vs ≡ just v × Den v K ρ'
dens-proj i Ks {vs = vs} ds p with proj-pw i (dens-pw Ks ds)
... | pw rewrite p with proj i vs | pw
...   | just v | M.just d = v , refl , d

{- Facts --------------------------------------------------------------------------}

lookup-ws : ∀ {x} (ρ : S.Env) → x < length ρ → Σ[ v ∈ S.Val ] ρ ‼ x ≡ just v
lookup-ws ρ x< = ‼-< ρ _ x<

{- under one more variable, in the target only -}
ok-weak : ∀ {E ρ ρ' w} → Ok E ρ ρ' → Ok (λ x → shift-info (E x)) ρ (w ∷ ρ')
kden-shift : ∀ K {ρ' v w} → KDen v K ρ' → KDen v (shift-known K) (w ∷ ρ')
knw-shift : ∀ I {ρ' v w} → (∀ {K} → known I ≡ just K → KDen v K ρ')
  → ∀ {K} → known (shift-info I) ≡ just K → KDen v K (w ∷ ρ')
ok-weak {E} ok = mk-ok (λ x e → strong-shift (term (E x)) (sml ok x) (trm ok x e)) (λ x e → knw-shift (E x) (knw ok x e))
  (λ x → small-shift (term (E x)) (sml ok x))
kden-shift (val K) d = den-shift K d
kden-shift (fun N E) (ρ , refl , ok , w) = ρ , refl , ok-weak ok , w
knw-shift (T ∣ just K) h refl = kden-shift K (h refl)
knw-shift (T ∣ nothing) h ()

{- variable 0 bound in both environments, known by k -}
ok-bind : ∀ {E ρ ρ' w v k} → Ok E ρ ρ' → v ≈ w → (∀ {K} → k ≡ just K → KDen v K (w ∷ ρ'))
  → Ok (((` 0) ∣ k) • (λ x → shift-info (E x))) (v ∷ ρ) (w ∷ ρ')
ok-bind ok r d = mk-ok (λ { zero refl → _ , refl , r ; (suc x) e → trm ok' x e })
  (λ { zero refl k → d k ; (suc x) e k → knw ok' x e k }) (λ { zero → refl ; (suc x) → sml ok' x })
  where ok' = ok-weak ok

{- under a binder that stays -}
ok-under : ∀ {E ρ ρ' v' v} → Ok E ρ ρ' → v ≈ v' → Ok (under E) (v ∷ ρ) (v' ∷ ρ')
ok-under ok r = ok-bind ok r (λ { refl → _ , refl , r })

{- a value that stays bound to variable 0, known as I is -}
ok-let : ∀ {E ρ ρ' I w v} → Ok E ρ ρ' → v ≈ w → (∀ {K} → known I ≡ just K → KDen v K ρ')
  → Ok (known-as I E) (v ∷ ρ) (w ∷ ρ')
ok-let {I = I} ok r h = ok-bind ok r (knw-shift I h)

{- a small value I for variable 0, in the source only -}
ok-cons : ∀ {E ρ ρ' I v} → Ok E ρ ρ' → small (term I) ≡ true → Strong v (term I) ρ'
  → (∀ {K} → known I ≡ just K → KDen v K ρ') → Ok (I • E) (v ∷ ρ) ρ'
ok-cons ok s d h = mk-ok (λ { zero refl → d ; (suc x) e → trm ok x e })
  (λ { zero refl k → h k ; (suc x) e k → knw ok x e k }) (λ { zero → s ; (suc x) → sml ok x })

ok-self : ∀ {E ρ ρ' T v} → Ok E ρ ρ' → small T ≡ true → Strong v T ρ' → Ok (self T • E) (v ∷ ρ) ρ'
ok-self {T = T} ok s d = ok-cons ok s d (λ { refl → strong-den T d })


{- The interpreter is monotone in the clock --------------------------------------}

mono : ∀ {ck ck'} → ck ≤ ck' → ∀ ρ M → S.eval ck ρ M ⊑ᵣ S.eval ck' ρ M
mono-args : ∀ {ck ck' n} → ck ≤ ck' → ∀ ρ vs (as : Args (replicate n ■)) → S.eval-args ck ρ vs as ⊑ᵣ S.eval-args ck' ρ vs as
mono-apply : ∀ {ck ck'} → ck ≤ ck' → ∀ ρ M v → S.apply ck ρ M v ⊑ᵣ S.apply ck' ρ M v
mono-call : ∀ {ck ck'} → ck ≤ ck' → ∀ N ρ → S.call ck N ρ ⊑ᵣ S.call ck' N ρ
mono-branch : ∀ {ck ck'} → ck ≤ ck' → ∀ ρ M N v → S.branch ck ρ M N v ⊑ᵣ S.branch ck' ρ M N v
mono le ρ (` x) = same
mono le ρ (lam ⦅ ⟩ N ,, Nil ⦆) = same
mono le ρ (app ⦅ L ,, M ,, Nil ⦆) = ⊑-bind (mono le ρ L) (mono-apply le ρ M)
mono le ρ (lit B k ⦅ Nil ⦆) = same
mono le ρ (tuple n ⦅ as ⦆) = ⊑-bind (mono-args le ρ [] as) (λ _ → same)
mono le ρ (get i ⦅ M ,, Nil ⦆) = ⊑-bind (mono le ρ M) (λ _ → same)
mono le ρ (inl-op ⦅ M ,, Nil ⦆) = ⊑-bind (mono le ρ M) (λ _ → same)
mono le ρ (inr-op ⦅ M ,, Nil ⦆) = ⊑-bind (mono le ρ M) (λ _ → same)
mono le ρ (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) = ⊑-bind (mono le ρ L) (mono-branch le ρ M N)
mono le ρ (prim p ⦅ L ,, M ,, Nil ⦆) = ⊑-bind (mono le ρ L) (λ v → ⊑-bind (mono le ρ M) (λ w → same))
mono le ρ (let-op ⦅ M ,, ⟩ N ,, Nil ⦆) = ⊑-bind (mono le ρ M) (λ v → mono le (v ∷ ρ) N)
mono-args {n = zero} le ρ vs Nil = same
mono-args {n = suc n} le ρ vs (M ,, as) = ⊑-bind (mono le ρ M) (λ v → mono-args le ρ (v ∷ vs) as)
mono-apply le ρ M (S.clo N ρ') = ⊑-bind (mono le ρ M) (λ w → mono-call le N (w ∷ ρ'))
mono-apply le ρ M (S.const B k) = same
mono-apply le ρ M (S.tup vs) = same
mono-apply le ρ M (S.inl v) = same
mono-apply le ρ M (S.inr v) = same
mono-call {zero} le N ρ = timeout
mono-call {suc ck} {suc ck'} (s≤s le) N ρ = mono le ρ N
mono-branch le ρ M N (S.inl v) = mono le (v ∷ ρ) M
mono-branch le ρ M N (S.inr v) = mono le (v ∷ ρ) N
mono-branch le ρ M N (S.clo _ _) = same
mono-branch le ρ M N (S.const B k) = same
mono-branch le ρ M N (S.tup vs) = same

mono-at : ∀ ρ M → Mono (λ ck → S.eval ck ρ M)
mono-at ρ M le = mono le ρ M

{- Stable results of the source ------------------------------------------------}

st-call : ∀ {N ρ r} → Stable (λ ck → S.eval ck ρ N) r → Stable (λ ck → S.call ck N ρ) r
st-call (c , e) = suc c , λ { (suc ck) (s≤s le) → e ck le }

Run : AST → S.Env → S.Val → Set
Run M ρ v = Stable (λ ck → S.eval ck ρ M) (ret v)

{- the source evaluates M, then the body N with its value bound: by a call
   of a closure of N in ρf (true, which ticks), or a let (false) -}
Body : Bool → ℕ → AST → S.Env → Result S.Val
Body true ck N ρ = S.call ck N ρ
Body false ck N ρ = S.eval ck ρ N

Bound : Bool → AST → AST → S.Env → S.Env → ℕ → Result S.Val
Bound t M N ρf ρ ck = S.eval ck ρ M >>= λ v → Body t ck N (v ∷ ρf)

st-body : ∀ t {N ρ r} → Stable (λ ck → S.eval ck ρ N) r → Stable (λ ck → Body t ck N ρ) r
st-body true = st-call
st-body false σ = σ

{- an application whose operator runs to a closure of N -}
via : ∀ {L M N ρf ρ} {P : S.Val → Set} → Run L ρ (S.clo N ρf)
  → Σ[ v ∈ S.Val ] Stable (Bound true M N ρf ρ) (ret v) × P v → Σ[ v ∈ S.Val ] Run (app ⦅ L ,, M ,, Nil ⦆) ρ v × P v
via σL (v , τ , d) = v , st-bind σL τ , d

{- The target evaluates value terms, at any clock ---------------------------------}

teval : ∀ T {ρ' v} → Strong v T ρ' → Σ[ w ∈ S.Val ] (∀ ck → S.eval ck ρ' T ≡ ret w) × v ≈ w
tevals : ∀ {n} (as : Args (replicate n ■)) {ρ' vs} → Strongs vs as ρ'
  → Σ[ ws ∈ List S.Val ] (∀ ck acc → S.eval-args ck ρ' acc as ≡ ret (reverseAcc acc ws)) × Pointwise _≈_ vs ws
teval (` y) (w , e , r) = w , (λ ck → cong from-maybe e) , r
teval (lam ⦅ ⟩ N ,, Nil ⦆) r = _ , (λ ck → refl) , r
teval (lit B k ⦅ Nil ⦆) refl = _ , (λ ck → refl) , const≈
teval (tuple n ⦅ as ⦆) {ρ'} (vs , refl , ds) with tevals as ds
... | ws , e , rs = S.tup ws , ev , tup≈ rs
  where ev : ∀ ck → S.eval ck ρ' (tuple n ⦅ as ⦆) ≡ ret (S.tup ws)
        ev ck rewrite e ck [] | reverse-involutive ws = refl
teval (inl-op ⦅ M ,, Nil ⦆) {ρ'} (v , refl , d) with teval M d
... | w , e , r = S.inl w , ev , inl≈ r
  where ev : ∀ ck → S.eval ck ρ' (inl-op ⦅ M ,, Nil ⦆) ≡ ret (S.inl w)
        ev ck rewrite e ck = refl
teval (inr-op ⦅ M ,, Nil ⦆) {ρ'} (v , refl , d) with teval M d
... | w , e , r = S.inr w , ev , inr≈ r
  where ev : ∀ ck → S.eval ck ρ' (inr-op ⦅ M ,, Nil ⦆) ≡ ret (S.inr w)
        ev ck rewrite e ck = refl
tevals {zero} Nil refl = [] , (λ ck acc → refl) , []
tevals {suc n} (M ,, as) {ρ'} (v , vs , refl , d , ds) with teval M d | tevals as ds
... | w , e , r | ws , es , rs = w ∷ ws , ev , r ∷ rs
  where ev : ∀ ck acc → S.eval-args ck ρ' acc (M ,, as) ≡ ret (reverseAcc acc (w ∷ ws))
        ev ck acc rewrite e ck = es ck (w ∷ acc)

{- The source runs ahead: run-term and run-known --------------------------------}

{- what the source does with the operand M of a call, whose simplification
   is I: it runs M to the value that I's value term, or its known value,
   describes -}
record Opd (M : AST) (ρ : S.Env) (I : Info) (ρ' : S.Env) : Set where
  constructor opd
  field
    o-term : value (term I) ≡ true → Σ[ v ∈ S.Val ] Run M ρ v × Strong v (term I) ρ'
    o-known : ∀ {K} → known I ≡ just K → Σ[ v ∈ S.Val ] Run M ρ v × KDen v K ρ'
open Opd

{- the value of a value operand, described by its term and what it is known to be -}
opd-val : ∀ {I M ρ' ρ} → Opd M ρ I ρ' → value (term I) ≡ true
  → Σ[ v ∈ S.Val ] Run M ρ v × Strong v (term I) ρ' × (∀ {K} → known I ≡ just K → KDen v K ρ')
opd-val {I} {M} {ρ'} {ρ} o e with o-term o e
... | v , σ , d = v , σ , d , λ {K} k → G {K} (o-known o k)
  where G : ∀ {K} → Σ[ v' ∈ S.Val ] Run M ρ v' × KDen v' K ρ' → KDen v K ρ'
        G (v' , σ' , d') with stable-unique σ' σ
        ... | refl = d'

run-term : ∀ fl M {E ρ ρ'} → Ok E ρ ρ' → WS (length ρ) M → value (term (simp fl E M)) ≡ true
  → Σ[ v ∈ S.Val ] Run M ρ v × Strong v (term (simp fl E M)) ρ'
run-known : ∀ fl M {E ρ ρ' K} → Ok E ρ ρ' → WS (length ρ) M → known (simp fl E M) ≡ just K
  → Σ[ v ∈ S.Val ] Run M ρ v × KDen v K ρ'
run-terms : ∀ fl {n} (as : Args (replicate n ■)) {E ρ ρ'} → Ok E ρ ρ' → WS-args (length ρ) as
  → values (simp-args fl E as) ≡ true
  → Σ[ vs ∈ List S.Val ] (∀ acc → Stable (λ ck → S.eval-args ck ρ acc as) (ret (reverseAcc acc vs)))
      × Strongs vs (simp-args fl E as) ρ'
run-get : ∀ fl {n} (i : Fin n) L {E ρ ρ' K} → Ok E ρ ρ' → WS (length ρ) L → component i (known (simp fl E L)) ≡ just K
  → Σ[ v ∈ S.Val ] Run (get i ⦅ L ,, Nil ⦆) ρ v × Den v K ρ'
run-inl : ∀ fl L {E ρ ρ' K} → Ok E ρ ρ' → WS (length ρ) L → branch (known (simp fl E L)) ≡ just (true , K)
  → Σ[ v ∈ S.Val ] Run L ρ (S.inl v) × Strong v K ρ'
run-inr : ∀ fl L {E ρ ρ' K} → Ok E ρ ρ' → WS (length ρ) L → branch (known (simp fl E L)) ≡ just (false , K)
  → Σ[ v ∈ S.Val ] Run L ρ (S.inr v) × Strong v K ρ'
run-int : ∀ fl L {E ρ ρ' n} → Ok E ρ ρ' → WS (length ρ) L → int-of (known (simp fl E L)) ≡ just n → Run L ρ (S.const Int n)
{- a let, or a call: the source runs the operand, then N (run-let), or
   the target calls (run-call) -}
run-let : ∀ t fl N {Ef ρf ρ' I M ρ} → Ok Ef ρf ρ' → WS (suc (length ρf)) N → Opd M ρ I ρ'
  → value (term (simp-let fl Ef N I)) ≡ true
  → Σ[ v ∈ S.Val ] Stable (Bound t M N ρf ρ) (ret v) × Strong v (term (simp-let fl Ef N I)) ρ'
known-let : ∀ t fl N {Ef ρf ρ' I M ρ K} → Ok Ef ρf ρ' → WS (suc (length ρf)) N → Opd M ρ I ρ'
  → known (simp-let fl Ef N I) ≡ just K → Σ[ v ∈ S.Val ] Stable (Bound t M N ρf ρ) (ret v) × KDen v K ρ'
run-call : ∀ fl J I {L M ρ' ρ} → (∀ {K} → known J ≡ just K → Σ[ v ∈ S.Val ] Run L ρ v × KDen v K ρ') → Opd M ρ I ρ'
  → value (term (simp-call fl J I)) ≡ true
  → Σ[ v ∈ S.Val ] Run (app ⦅ L ,, M ,, Nil ⦆) ρ v × Strong v (term (simp-call fl J I)) ρ'
known-call : ∀ fl J I {L M ρ' ρ K} → (∀ {K} → known J ≡ just K → Σ[ v ∈ S.Val ] Run L ρ v × KDen v K ρ') → Opd M ρ I ρ'
  → known (simp-call fl J I) ≡ just K → Σ[ v ∈ S.Val ] Run (app ⦅ L ,, M ,, Nil ⦆) ρ v × KDen v K ρ'

run-opd : ∀ fl M {E ρ ρ'} → Ok E ρ ρ' → WS (length ρ) M → Opd M ρ (simp fl E M) ρ'
run-opd fl M ok w = opd (run-term fl M ok w) (run-known fl M ok w)

{- a primitive on known integers -}
run-prim : ∀ fl p L M {E ρ ρ' n m} → Ok E ρ ρ' → WS (length ρ) L → WS (length ρ) M
  → int-of (known (simp fl E L)) ≡ just n → int-of (known (simp fl E M)) ≡ just m
  → Run (prim p ⦅ L ,, M ,, Nil ⦆) ρ (S.out (δ p n m))
run-prim fl p L M ok wL wM e₁ e₂ = st-bind (run-int fl L ok wL e₁) (st-bind (run-int fl M ok wM e₂) (st-now (λ _ → refl)))

run-term fl (` x) {ρ = ρ} ok w e with lookup-ws ρ w
... | v , l = v , st-now (λ ck → cong from-maybe l) , trm ok x l
run-term fl (lam ⦅ ⟩ N ,, Nil ⦆) ok (w , _) e = _ , st-now (λ _ → refl) , clo≈ ok w
run-term fl (app ⦅ L ,, M ,, Nil ⦆) {E} {ρ = ρ} ok (wL , wM , _) e with lam? L
... | is-lam N = run-let true fl N {ρf = ρ} {M = M} ok (proj₁ wL) (run-opd fl M ok wM) e
... | other = run-call fl (simp fl E L) _ {L = L} (run-known fl L ok wL) (run-opd fl M ok wM) e
run-term fl (lit B k ⦅ Nil ⦆) ok w e = _ , st-now (λ _ → refl) , refl
run-term fl (tuple n ⦅ as ⦆) {E} {ρ = ρ} ok w e with run-terms fl as ok w e
... | vs , σ , ds = S.tup vs , st-bind (σ []) (st-now (λ _ → cong (λ x → ret (S.tup x)) (reverse-involutive vs))) , vs , refl , ds
run-term fl (get i ⦅ L ,, Nil ⦆) {E} ok (w , _) e with component i (known (simp fl E L)) in c
... | just K with small K in s
...   | true with run-get fl i L ok w c
...     | v , σ , d = v , σ , small-strong K s d
run-term fl (inl-op ⦅ M ,, Nil ⦆) ok (w , _) e with run-term fl M ok w e
... | v , σ , d = S.inl v , st-bind σ (st-now (λ _ → refl)) , v , refl , d
run-term fl (inr-op ⦅ M ,, Nil ⦆) ok (w , _) e with run-term fl M ok w e
... | v , σ , d = S.inr v , st-bind σ (st-now (λ _ → refl)) , v , refl , d
run-term fl (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) {E} ok (wL , (wM , wN , _)) e with branch (known (simp fl E L)) in b
... | just (true , K) with run-inl fl L ok wL b
...   | v , σ , d with run-term fl M (ok-self ok (proj₂ (branch-inl (known (simp fl E L)) b)) d) wM e
...     | w , τ , d' = w , st-bind σ τ , d'
run-term fl (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) {E} ok (wL , (wM , wN , _)) e | just (false , K) with run-inr fl L ok wL b
...   | v , σ , d with run-term fl N (ok-self ok (proj₂ (branch-inr (known (simp fl E L)) b)) d) wN e
...     | w , τ , d' = w , st-bind σ τ , d'
run-term fl (prim p ⦅ L ,, M ,, Nil ⦆) {E} ok (wL , wM , _) e with int-of (known (simp fl E L)) in e₁
... | just n with int-of (known (simp fl E M)) in e₂
...   | just m = S.out (δ p n m) , run-prim fl p L M ok wL wM e₁ e₂ , prim-strong (δ p n m)
run-term fl (let-op ⦅ M ,, ⟩ N ,, Nil ⦆) ok (wM , wN , _) e = run-let false fl N ok wN (run-opd fl M ok wM) e

run-terms fl {zero} Nil ok _ _ = [] , (λ acc → st-now (λ _ → refl)) , refl
run-terms fl {suc n} (M ,, as) {E} ok (w , ws) e with P.∧-true {value (term (simp fl E M))} e
... | e₁ , e₂ with run-term fl M ok w e₁ | run-terms fl as ok ws e₂
...   | v , σ , d | vs , τ , ds = v ∷ vs , (λ acc → st-bind σ (τ (v ∷ acc))) , v , vs , refl , d , ds

run-get fl i L {E} ok w c with comp-inv i (known (simp fl E L)) c
... | m , Ks , k , p with run-known fl L ok w k
...   | .(S.tup vs) , σ , (vs , refl , ds) with dens-proj i Ks ds p
...     | v , q , d = v , st-bind σ (st-now (λ _ → cong from-maybe q)) , d

run-inl fl L {E} ok w b with branch-inl (known (simp fl E L)) b
... | k , s with run-known fl L ok w k
...   | .(S.inl v₀) , σ , (v₀ , refl , d) = v₀ , σ , small-strong _ s d

run-inr fl L {E} ok w b with branch-inr (known (simp fl E L)) b
... | k , s with run-known fl L ok w k
...   | .(S.inr v₀) , σ , (v₀ , refl , d) = v₀ , σ , small-strong _ s d

run-int fl L {E} ok w e with run-known fl L ok w (int-inv (known (simp fl E L)) e)
... | .(S.const Int _) , σ , refl = σ

run-known fl (` x) {ρ = ρ} ok w k with lookup-ws ρ w
... | v , l = v , st-now (λ ck → cong from-maybe l) , knw ok x l k
run-known fl (lam ⦅ ⟩ N ,, Nil ⦆) {ρ = ρ} ok (w , _) refl = _ , st-now (λ _ → refl) , ρ , refl , ok , w
run-known fl (app ⦅ L ,, M ,, Nil ⦆) {E} {ρ = ρ} ok (wL , wM , _) k with lam? L
... | is-lam N = known-let true fl N {ρf = ρ} {M = M} ok (proj₁ wL) (run-opd fl M ok wM) k
... | other = known-call fl (simp fl E L) _ {L = L} (run-known fl L ok wL) (run-opd fl M ok wM) k
run-known fl (lit B k ⦅ Nil ⦆) ok w refl = _ , st-now (λ _ → refl) , refl
run-known fl (tuple n ⦅ as ⦆) {E} ok w k with value (tuple n ⦅ simp-args fl E as ⦆) in isv
run-known fl (tuple n ⦅ as ⦆) {E} ok w refl | true with run-term fl (tuple n ⦅ as ⦆) ok w isv
... | v , σ , d = v , σ , strong-den (tuple n ⦅ simp-args fl E as ⦆) d
run-known fl (get i ⦅ L ,, Nil ⦆) {E} ok (w , _) k with component i (known (simp fl E L)) in c
... | just K with small K
run-known fl (get i ⦅ L ,, Nil ⦆) {E} ok (w , _) refl | just K | true = run-get fl i L ok w c
run-known fl (get i ⦅ L ,, Nil ⦆) {E} ok (w , _) refl | just K | false = run-get fl i L ok w c
run-known fl (inl-op ⦅ M ,, Nil ⦆) {E} ok w k with value (term (simp fl E M)) in isv
run-known fl (inl-op ⦅ M ,, Nil ⦆) {E} ok w refl | true with run-term fl (inl-op ⦅ M ,, Nil ⦆) ok w isv
... | v , σ , d = v , σ , strong-den (inl-op ⦅ term (simp fl E M) ,, Nil ⦆) d
run-known fl (inr-op ⦅ M ,, Nil ⦆) {E} ok w k with value (term (simp fl E M)) in isv
run-known fl (inr-op ⦅ M ,, Nil ⦆) {E} ok w refl | true with run-term fl (inr-op ⦅ M ,, Nil ⦆) ok w isv
... | v , σ , d = v , σ , strong-den (inr-op ⦅ term (simp fl E M) ,, Nil ⦆) d
run-known fl (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) {E} ok (wL , (wM , wN , _)) k with branch (known (simp fl E L)) in b
... | just (true , K) with run-inl fl L ok wL b
...   | v , σ , d with run-known fl M (ok-self ok (proj₂ (branch-inl (known (simp fl E L)) b)) d) wM k
...     | w , τ , d' = w , st-bind σ τ , d'
run-known fl (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) {E} ok (wL , (wM , wN , _)) k | just (false , K) with run-inr fl L ok wL b
...   | v , σ , d with run-known fl N (ok-self ok (proj₂ (branch-inr (known (simp fl E L)) b)) d) wN k
...     | w , τ , d' = w , st-bind σ τ , d'
run-known fl (prim p ⦅ L ,, M ,, Nil ⦆) {E} ok (wL , wM , _) k with int-of (known (simp fl E L)) in e₁
... | just n with int-of (known (simp fl E M)) in e₂
run-known fl (prim p ⦅ L ,, M ,, Nil ⦆) {E} ok (wL , wM , _) refl | just n | just m =
  S.out (δ p n m) , run-prim fl p L M ok wL wM e₁ e₂ , strong-den (prim-term (δ p n m)) (prim-strong (δ p n m))
run-known fl (let-op ⦅ M ,, ⟩ N ,, Nil ⦆) ok (wM , wN , _) k = known-let false fl N ok wN (run-opd fl M ok wM) k

run-let t fl N {I = I} okf wN o e with small (term I) in s | value (term I) in isv
... | true | _ with opd-val o (P.small-value (term I) s)
...   | v , σ , d , h with run-term fl N (ok-cons okf s d h) wN e
...     | w , τ , d' = w , st-bind σ (st-body t τ) , d'
run-let t fl N {I = I} okf wN o () | false | true
run-let t fl N {I = I} okf wN o () | false | false

known-let t fl N {I = I} okf wN o k with small (term I) in s | value (term I) in isv
... | true | _ with opd-val o (P.small-value (term I) s)
...   | v , σ , d , h with run-known fl N (ok-cons okf s d h) wN k
...     | w , τ , d' = w , st-bind σ (st-body t τ) , d'
known-let t fl N {I = I} okf wN o () | false | true
known-let t fl N {I = I} okf wN o () | false | false

run-call (suc fl) (T ∣ just (fun N Ef)) I {L} hJ o e with size (term (simp-let fl Ef N I)) ≤ᵇ inline-size
... | true with hJ refl
...   | _ , σL , (ρf , refl , okf , wN) = via {L} σL (run-let true fl N okf wN o e)
run-call (suc fl) (T ∣ just (fun N Ef)) I {L} hJ o () | false
run-call zero J I hJ o ()
run-call (suc fl) (T ∣ nothing) I hJ o ()
run-call (suc fl) (T ∣ just (val K)) I hJ o ()

known-call (suc fl) (T ∣ just (fun N Ef)) I {L} hJ o k with size (term (simp-let fl Ef N I)) ≤ᵇ inline-size
... | true with hJ refl
...   | _ , σL , (ρf , refl , okf , wN) = via {L} σL (known-let true fl N okf wN o k)
known-call (suc fl) (T ∣ just (fun N Ef)) I {L} hJ o () | false
known-call zero J I hJ o ()
known-call (suc fl) (T ∣ nothing) I hJ o ()
known-call (suc fl) (T ∣ just (val K)) I hJ o ()

{- Forward, at the same clock ------------------------------------------------------}

{- the source runs M to a value that the target's value term T describes -}
known-le : ∀ ck M ρ {v T ρ'} → Run M ρ v → Strong v T ρ' → LeResult _≈_ (S.eval ck ρ M) (S.eval ck ρ' T)
known-le ck M ρ σ d with teval _ d
... | w , et , r rewrite et ck = subst (λ x → LeResult _≈_ x _) (bind-ret (S.eval ck ρ M)) (le-stable ck (mono-at ρ M) σ (ret r))

run≈ : ∀ ck fl M {E ρ ρ'} → Ok E ρ ρ' → WS (length ρ) M → LeResult _≈_ (S.eval ck ρ M) (S.eval ck ρ' (term (simp fl E M)))
args≈ : ∀ ck fl {n} (as : Args (replicate n ■)) {E ρ ρ' acc acc'} → Ok E ρ ρ' → WS-args (length ρ) as → Pointwise _≈_ acc acc'
  → LeResult (Pointwise _≈_) (S.eval-args ck ρ acc as) (S.eval-args ck ρ' acc' (simp-args fl E as))
apply≈ : ∀ ck {M M' ρ ρ' v v'} → LeResult _≈_ (S.eval ck ρ M) (S.eval ck ρ' M') → v ≈ v'
  → LeResult _≈_ (S.apply ck ρ M v) (S.apply ck ρ' M' v')
call≈ : ∀ ck fl N {E ρ ρ'} → Ok E ρ ρ' → WS (length ρ) N → LeResult _≈_ (S.call ck N ρ) (S.call ck (term (simp fl E N)) ρ')
call≈ zero fl N ok w = timeout
call≈ (suc ck) fl N ok w = run≈ ck fl N ok w
branch≈ : ∀ ck fl M N {E ρ ρ' v v'} → Ok E ρ ρ' → WS (suc (length ρ)) M → WS (suc (length ρ)) N → v ≈ v'
  → LeResult _≈_ (S.branch ck ρ M N v) (S.branch ck ρ' (term (simp fl (under E) M)) (term (simp fl (under E) N)) v')
branch≈ ck fl M N ok wM wN (inl≈ r) = run≈ ck fl M (ok-under ok r) wM
branch≈ ck fl M N ok wM wN (inr≈ r) = run≈ ck fl N (ok-under ok r) wN
branch≈ ck fl M N ok wM wN (clo≈ _ _) = error
branch≈ ck fl M N ok wM wN const≈ = error
branch≈ ck fl M N ok wM wN (tup≈ _) = error
project≈ : ∀ {n} (i : Fin n) {v v'} → v ≈ v' → LeResult _≈_ (S.project i v) (S.project i v')
project≈ i (tup≈ rs) = from-maybe-le (proj-pw i rs)
project≈ i (clo≈ _ _) = error
project≈ i const≈ = error
project≈ i (inl≈ _) = error
project≈ i (inr≈ _) = error
{- a let or a call, as in run-let and run-call -}
body-le : ∀ t ck fl N {E ρ ρ'} → Ok E ρ ρ' → WS (length ρ) N → LeResult _≈_ (Body t ck N ρ) (S.eval ck ρ' (term (simp fl E N)))
let≈ : ∀ t ck fl N {Ef ρf ρ' I M ρ} → Ok Ef ρf ρ' → WS (suc (length ρf)) N → Opd M ρ I ρ'
  → LeResult _≈_ (S.eval ck ρ M) (S.eval ck ρ' (term I))
  → LeResult _≈_ (Bound t M N ρf ρ ck) (S.eval ck ρ' (term (simp-let fl Ef N I)))
call-le : ∀ ck fl J I {L M ρ' ρ} → (∀ {K} → known J ≡ just K → Σ[ v ∈ S.Val ] Run L ρ v × KDen v K ρ')
  → LeResult _≈_ (S.eval ck ρ L) (S.eval ck ρ' (term J)) → Opd M ρ I ρ' → LeResult _≈_ (S.eval ck ρ M) (S.eval ck ρ' (term I))
  → LeResult _≈_ (S.eval ck ρ (app ⦅ L ,, M ,, Nil ⦆)) (S.eval ck ρ' (term (simp-call fl J I)))

apply≈ ck hM (clo≈ {fl} {N = N} ok₁ w₁) = bind-le hM (λ _ r → call≈ ck fl N (ok-under ok₁ r) w₁)
apply≈ ck hM const≈ = error
apply≈ ck hM (tup≈ _) = error
apply≈ ck hM (inl≈ _) = error
apply≈ ck hM (inr≈ _) = error

args≈ ck fl {zero} Nil ok _ rs = ret rs
args≈ ck fl {suc n} (M ,, as) ok (w , ws) rs = bind-le (run≈ ck fl M ok w) (λ _ r → args≈ ck fl as ok ws (r ∷ rs))

body-le true zero fl N ok w = timeout
body-le true (suc ck) fl N {E} {ρ' = ρ'} ok w = le-⊑ (run≈ ck fl N ok w) (mono (n≤1+n ck) ρ' (term (simp fl E N)))
body-le false ck fl N ok w = run≈ ck fl N ok w

let≈ t ck fl N {I = I} {M} {ρ} okf wN o hM with small (term I) in s | value (term I) in isv
... | true | _ with opd-val o (P.small-value (term I) s)
...   | v , σ , d , h = le-stable ck (mono-at ρ M) σ (body-le t ck fl N (ok-cons okf s d h) wN)
let≈ t ck fl N {Ef} {ρf} {ρ'} {I} {M} {ρ} okf wN o hM | false | true with opd-val o isv
... | v₀ , σ , d , h = bind-le hM λ e r → G (stable-ret (mono-at ρ M) σ e) r
  where
  G : ∀ {v w} → v ≡ v₀ → v ≈ w → LeResult _≈_ (Body t ck N (v ∷ ρf)) (S.eval ck (w ∷ ρ') (term (simp fl (known-as I Ef) N)))
  G refl r = body-le t ck fl N (ok-let {I = I} okf r h) wN
let≈ t ck fl N okf wN o hM | false | false = bind-le hM λ _ r → body-le t ck fl N (ok-under okf r) wN

call-le ck (suc fl) (T ∣ just (fun N Ef)) I {L} hJ hL o hM with size (term (simp-let fl Ef N I)) ≤ᵇ inline-size
... | true with hJ refl
...   | _ , σL , (ρf , refl , okf , wN) = le-stable ck (mono-at _ L) σL (let≈ true ck fl N okf wN o hM)
call-le ck (suc fl) (T ∣ just (fun N Ef)) I {L} hJ hL o hM | false = bind-le hL (λ _ r → apply≈ ck hM r)
call-le ck zero J I hJ hL o hM = bind-le hL (λ _ r → apply≈ ck hM r)
call-le ck (suc fl) (T ∣ nothing) I hJ hL o hM = bind-le hL (λ _ r → apply≈ ck hM r)
call-le ck (suc fl) (T ∣ just (val K)) I hJ hL o hM = bind-le hL (λ _ r → apply≈ ck hM r)

run≈ ck fl (` x) {ρ = ρ} ok w with lookup-ws ρ w
... | v , l = known-le ck (` x) ρ (st-now (λ ck → cong from-maybe l)) (trm ok x l)
run≈ ck fl (lam ⦅ ⟩ N ,, Nil ⦆) ok (w , _) = ret (clo≈ ok w)
run≈ ck fl (app ⦅ L ,, M ,, Nil ⦆) {E} ok (wL , wM , _) with lam? L
... | is-lam N = let≈ true ck fl N ok (proj₁ wL) (run-opd fl M ok wM) (run≈ ck fl M ok wM)
... | other = call-le ck fl (simp fl E L) _ {L = L} (run-known fl L ok wL) (run≈ ck fl L ok wL) (run-opd fl M ok wM) (run≈ ck fl M ok wM)
run≈ ck fl (lit B k ⦅ Nil ⦆) ok w = ret const≈
run≈ ck fl (tuple n ⦅ as ⦆) ok w = bind-le (args≈ ck fl as ok w []) (λ _ rs → ret (tup≈ (reverse⁺ rs)))
run≈ ck fl (get i ⦅ L ,, Nil ⦆) {E} ok (w , _) with component i (known (simp fl E L)) in c
... | nothing = bind-le (run≈ ck fl L ok w) (λ _ r → project≈ i r)
... | just K with small K in s
...   | true with run-get fl i L ok w c
...     | v , σ , d = known-le ck (get i ⦅ L ,, Nil ⦆) _ σ (small-strong K s d)
run≈ ck fl (get i ⦅ L ,, Nil ⦆) {E} ok (w , _) | just K | false = bind-le (run≈ ck fl L ok w) (λ _ r → project≈ i r)
run≈ ck fl (inl-op ⦅ M ,, Nil ⦆) ok (w , _) = bind-le (run≈ ck fl M ok w) (λ _ r → ret (inl≈ r))
run≈ ck fl (inr-op ⦅ M ,, Nil ⦆) ok (w , _) = bind-le (run≈ ck fl M ok w) (λ _ r → ret (inr≈ r))
run≈ ck fl (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) {E} ok (wL , (wM , wN , _)) with branch (known (simp fl E L)) in b
... | nothing = bind-le (run≈ ck fl L ok wL) (λ _ r → branch≈ ck fl M N ok wM wN r)
... | just (true , K) with run-inl fl L ok wL b
...   | v , σ , d = le-stable ck (mono-at _ L) σ (run≈ ck fl M (ok-self ok (proj₂ (branch-inl (known (simp fl E L)) b)) d) wM)
run≈ ck fl (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) {E} ok (wL , (wM , wN , _)) | just (false , K) with run-inr fl L ok wL b
...   | v , σ , d = le-stable ck (mono-at _ L) σ (run≈ ck fl N (ok-self ok (proj₂ (branch-inr (known (simp fl E L)) b)) d) wN)
run≈ ck fl (prim p ⦅ L ,, M ,, Nil ⦆) {E} ok (wL , wM , _) with int-of (known (simp fl E L)) in e₁
... | nothing = bind-le (run≈ ck fl L ok wL) (λ _ r → bind-le (run≈ ck fl M ok wM) (λ _ s → from-maybe-le (prim≈ p r s)))
... | just n with int-of (known (simp fl E M)) in e₂
...   | nothing = bind-le (run≈ ck fl L ok wL) (λ _ r → bind-le (run≈ ck fl M ok wM) (λ _ s → from-maybe-le (prim≈ p r s)))
...   | just m = known-le ck (prim p ⦅ L ,, M ,, Nil ⦆) _ (run-prim fl p L M ok wL wM e₁ e₂) (prim-strong (δ p n m))
run≈ ck fl (let-op ⦅ M ,, ⟩ N ,, Nil ⦆) ok (wM , wN , _) = let≈ false ck fl N ok wN (run-opd fl M ok wM) (run≈ ck fl M ok wM)

{- Backward: the source catches up -------------------------------------------------}

{- the source runs M to a value that the target's value term T describes -}
known-back : ∀ ck M ρ {v T ρ'} → Run M ρ v → Strong v T ρ' → Back _≈_ (λ ck → S.eval ck ρ M) (S.eval ck ρ' T)
known-back ck M ρ σ d _ with teval _ d
... | w , et , r rewrite et ck = _ , σ , ret r

back : ∀ ck fl M {E ρ ρ'} → Ok E ρ ρ' → WS (length ρ) M → Back _≈_ (λ ck → S.eval ck ρ M) (S.eval ck ρ' (term (simp fl E M)))
back-args : ∀ ck fl {n} (as : Args (replicate n ■)) {E ρ ρ' acc acc'} → Ok E ρ ρ' → WS-args (length ρ) as → Pointwise _≈_ acc acc'
  → Back (Pointwise _≈_) (λ ck → S.eval-args ck ρ acc as) (S.eval-args ck ρ' acc' (simp-args fl E as))
back-apply : ∀ ck {M M' ρ ρ' v v'} → Back _≈_ (λ ck → S.eval ck ρ M) (S.eval ck ρ' M') → v ≈ v'
  → Back _≈_ (λ ck → S.apply ck ρ M v) (S.apply ck ρ' M' v')
back-call : ∀ ck fl N {E ρ ρ' N'} → N' ≡ term (simp fl E N) → Ok E ρ ρ' → WS (length ρ) N
  → Back _≈_ (λ ck → S.call ck N ρ) (S.call ck N' ρ')
back-call zero fl N e ok w nt = ⊥-elim (nt refl)
back-call (suc ck) fl N refl ok w nt with back ck fl N ok w nt
... | r , st , rr = r , st-call st , rr
back-branch : ∀ ck fl M N {E ρ ρ' v v'} → Ok E ρ ρ' → WS (suc (length ρ)) M → WS (suc (length ρ)) N → v ≈ v'
  → Back _≈_ (λ ck → S.branch ck ρ M N v) (S.branch ck ρ' (term (simp fl (under E) M)) (term (simp fl (under E) N)) v')
back-branch ck fl M N ok wM wN (inl≈ r) = back ck fl M (ok-under ok r) wM
back-branch ck fl M N ok wM wN (inr≈ r) = back ck fl N (ok-under ok r) wN
back-branch ck fl M N ok wM wN (clo≈ _ _) = back-error (λ _ → refl)
back-branch ck fl M N ok wM wN const≈ = back-error (λ _ → refl)
back-branch ck fl M N ok wM wN (tup≈ _) = back-error (λ _ → refl)
back-project : ∀ {n} (i : Fin n) {v v'} → v ≈ v' → Back _≈_ (λ _ → S.project i v) (S.project i v')
back-project i (tup≈ rs) = back-maybe (proj-pw i rs)
back-project i (clo≈ _ _) = back-error (λ _ → refl)
back-project i const≈ = back-error (λ _ → refl)
back-project i (inl≈ _) = back-error (λ _ → refl)
back-project i (inr≈ _) = back-error (λ _ → refl)
{- a let or a call, as in run-let and run-call -}
body-back : ∀ t ck fl N {E ρ ρ'} → Ok E ρ ρ' → WS (length ρ) N → Back _≈_ (λ ck → Body t ck N ρ) (S.eval ck ρ' (term (simp fl E N)))
back-let : ∀ t ck fl N {Ef ρf ρ' I M ρ} → Ok Ef ρf ρ' → WS (suc (length ρf)) N → Opd M ρ I ρ'
  → Back _≈_ (λ ck → S.eval ck ρ M) (S.eval ck ρ' (term I))
  → Back _≈_ (Bound t M N ρf ρ) (S.eval ck ρ' (term (simp-let fl Ef N I)))
back-call' : ∀ ck fl J I {L M ρ' ρ} → (∀ {K} → known J ≡ just K → Σ[ v ∈ S.Val ] Run L ρ v × KDen v K ρ')
  → Back _≈_ (λ ck → S.eval ck ρ L) (S.eval ck ρ' (term J)) → Opd M ρ I ρ' → Back _≈_ (λ ck → S.eval ck ρ M) (S.eval ck ρ' (term I))
  → Back _≈_ (λ ck → S.eval ck ρ (app ⦅ L ,, M ,, Nil ⦆)) (S.eval ck ρ' (term (simp-call fl J I)))

back-apply ck hM (clo≈ {fl} {N = N} ok₁ w₁) = back-bind hM (λ _ r → back-call ck fl N refl (ok-under ok₁ r) w₁)
back-apply ck hM const≈ = back-error (λ _ → refl)
back-apply ck hM (tup≈ _) = back-error (λ _ → refl)
back-apply ck hM (inl≈ _) = back-error (λ _ → refl)
back-apply ck hM (inr≈ _) = back-error (λ _ → refl)

back-args ck fl {zero} Nil ok _ rs _ = _ , st-now (λ _ → refl) , ret rs
back-args ck fl {suc n} (M ,, as) ok (w , ws) rs = back-bind (back ck fl M ok w) (λ _ r → back-args ck fl as ok ws (r ∷ rs))

body-back true ck fl N ok w nt with back ck fl N ok w nt
... | r , st , rr = r , st-call st , rr
body-back false ck fl N ok w = back ck fl N ok w

back-let t ck fl N {ρf = ρf} {I = I} {M} okf wN o hM with small (term I) in s | value (term I) in isv
... | true | _ with opd-val o (P.small-value (term I) s)
...   | v , σ , d , h = back-run {g = λ c v → Body t c N (v ∷ ρf)} σ (body-back t ck fl N (ok-cons okf s d h) wN)
back-let t ck fl N {ρ' = ρ'} {I = I} {M} {ρ} okf wN o hM | false | true with opd-val o isv
... | v₀ , σ , d , h = back-bind hM λ st r → body-back t ck fl N (ok-let {I = I} okf r (h' st)) wN
  where h' : ∀ {v} → Stable (λ ck → S.eval ck ρ M) (ret v) → ∀ {K} → known I ≡ just K → KDen v K ρ'
        h' st k with stable-unique st σ
        ... | refl = h k
back-let t ck fl N okf wN o hM | false | false = back-bind hM λ _ r → body-back t ck fl N (ok-under okf r) wN

back-call' ck (suc fl) (T ∣ just (fun N Ef)) I {L} hJ hL o hM with size (term (simp-let fl Ef N I)) ≤ᵇ inline-size
... | true with hJ refl
...   | _ , σL , (ρf , refl , okf , wN) = back-run σL (back-let true ck fl N okf wN o hM)
back-call' ck (suc fl) (T ∣ just (fun N Ef)) I {L} hJ hL o hM | false = back-bind hL (λ _ r → back-apply ck hM r)
back-call' ck zero J I hJ hL o hM = back-bind hL (λ _ r → back-apply ck hM r)
back-call' ck (suc fl) (T ∣ nothing) I hJ hL o hM = back-bind hL (λ _ r → back-apply ck hM r)
back-call' ck (suc fl) (T ∣ just (val K)) I hJ hL o hM = back-bind hL (λ _ r → back-apply ck hM r)

back ck fl (` x) {ρ = ρ} ok w with lookup-ws ρ w
... | v , l = known-back ck (` x) ρ (st-now (λ ck → cong from-maybe l)) (trm ok x l)
back ck fl (lam ⦅ ⟩ N ,, Nil ⦆) ok (w , _) _ = _ , st-now (λ _ → refl) , ret (clo≈ ok w)
back ck fl (app ⦅ L ,, M ,, Nil ⦆) {E} ok (wL , wM , _) with lam? L
... | is-lam N = back-let true ck fl N ok (proj₁ wL) (run-opd fl M ok wM) (back ck fl M ok wM)
... | other = back-call' ck fl (simp fl E L) _ {L = L} (run-known fl L ok wL) (back ck fl L ok wL) (run-opd fl M ok wM) (back ck fl M ok wM)
back ck fl (lit B k ⦅ Nil ⦆) ok w _ = _ , st-now (λ _ → refl) , ret const≈
back ck fl (tuple n ⦅ as ⦆) ok w =
  back-bind (back-args ck fl as ok w []) (λ _ rs _ → _ , st-now (λ _ → refl) , ret (tup≈ (reverse⁺ rs)))
back ck fl (get i ⦅ L ,, Nil ⦆) {E} ok (w , _) with component i (known (simp fl E L)) in c
... | nothing = back-bind (back ck fl L ok w) (λ _ r → back-project i r)
... | just K with small K in s
...   | true with run-get fl i L ok w c
...     | v , σ , d = known-back ck (get i ⦅ L ,, Nil ⦆) _ σ (small-strong K s d)
back ck fl (get i ⦅ L ,, Nil ⦆) {E} ok (w , _) | just K | false = back-bind (back ck fl L ok w) (λ _ r → back-project i r)
back ck fl (inl-op ⦅ M ,, Nil ⦆) ok (w , _) = back-bind (back ck fl M ok w) (λ _ r _ → _ , st-now (λ _ → refl) , ret (inl≈ r))
back ck fl (inr-op ⦅ M ,, Nil ⦆) ok (w , _) = back-bind (back ck fl M ok w) (λ _ r _ → _ , st-now (λ _ → refl) , ret (inr≈ r))
back ck fl (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) {E} ok (wL , (wM , wN , _)) with branch (known (simp fl E L)) in b
... | nothing = back-bind (back ck fl L ok wL) (λ _ r → back-branch ck fl M N ok wM wN r)
... | just (true , K) with run-inl fl L ok wL b
...   | v , σ , d = back-run {g = λ c → S.branch c _ M N} σ (back ck fl M (ok-self ok (proj₂ (branch-inl (known (simp fl E L)) b)) d) wM)
back ck fl (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) {E} ok (wL , (wM , wN , _)) | just (false , K) with run-inr fl L ok wL b
...   | v , σ , d = back-run {g = λ c → S.branch c _ M N} σ (back ck fl N (ok-self ok (proj₂ (branch-inr (known (simp fl E L)) b)) d) wN)
back ck fl (prim p ⦅ L ,, M ,, Nil ⦆) {E} ok (wL , wM , _) with int-of (known (simp fl E L)) in e₁
... | nothing = back-bind (back ck fl L ok wL) (λ _ r → back-bind (back ck fl M ok wM) (λ _ s → back-maybe (prim≈ p r s)))
... | just n with int-of (known (simp fl E M)) in e₂
...   | nothing = back-bind (back ck fl L ok wL) (λ _ r → back-bind (back ck fl M ok wM) (λ _ s → back-maybe (prim≈ p r s)))
...   | just m = known-back ck (prim p ⦅ L ,, M ,, Nil ⦆) _ (run-prim fl p L M ok wL wM e₁ e₂) (prim-strong (δ p n m))
back ck fl (let-op ⦅ M ,, ⟩ N ,, Nil ⦆) ok (wM , wN , _) = back-let false ck fl N ok wN (run-opd fl M ok wM) (back ck fl M ok wM)

{- The end theorem: for closed programs ------------------------------------------}

ok₀ : Ok (λ x → self (` x)) [] []
ok₀ = mk-ok (λ x ()) (λ x ()) (λ x → refl)

simplify-correct : ∀ M → Closed M → Equivalent (S.sem M) (S.sem (simplify M))
simplify-correct M c =
  clocked-back _≈_ obs≈ (mono-at [] (simplify M))
    (λ ck → run≈ ck inline-fuel M ok₀ (closed-ws {M} c)) (λ ck → back ck inline-fuel M ok₀ (closed-ws {M} c))

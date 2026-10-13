{-

  Correctness of the simplify pass (ISWIM → ISWIM) for the clocked
  interpreters (see the design note in Clock.agda).

  Not clock for clock: the clock ticks at each call, and simplify removes
  calls (β of a small value), so the target needs no more clock than the
  source, and the source may need more than the target. The theorem has
  the shape of the others (Equivalent), from two lemmas (clocked-le):

  * forward, at the same clock (run≈): the source's result, if it does
    not time out, is the target's, related (LeResult);
  * backward (back): if the target does not time out at a clock, then
    the source has a related result at every large enough clock (Stable);

  and the interpreter's monotonicity in the clock (mono).

  Values are related as in the CEK proof (SimplifySim): the target's on
  the left, a target closure being the simplified body of a source
  closure under Facts that are true of the two environments (Ok). When
  simp E M returns a value term, or M has a known value, the source runs
  M to a value it describes, at every large enough clock (run-term,
  run-known). The end theorem is for closed programs.

-}

module proof.Correctness.Interp.SimplifyFuel where

open import Framework.Primitives using (Int)
open import Framework.Syntax.SyntaxUtil using (_,,_; Nil; ⟩_,,_)
open import Language.ISWIM
open import Language.Prim using (int; bool; δ)
open import proof.Compiler.SimplifyFacts as P
  using (Info; _∣_; term; known; Facts; self; info; under; shift-info; simp; simp-args;
         simp-app; simp-let; simp-get; simp-case; simp-prim; simplify; small; atom; value; values;
         component; branch; int-of; prim-term; value-sv; small-sv; comp-inv; int-inv; branch-inl; branch-inr)
open import Compiler.EncloseScope using (Closed)
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
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe.Relation.Binary.Pointwise as M
open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; _⊔_; s≤s; z≤n)
open import Data.Nat.Properties using (m≤m⊔n; m≤n⊔m; ≤-trans; ≤-refl)
open import Data.Product using (_×_; Σ-syntax; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)

{- The relation ------------------------------------------------------------------}

infix 4 _≈_

data _≈_ : S.Val → S.Val → Set
{- the value term T denotes, in ρ', a value related to v (Strong); or the
   same, but a function describes any value (Den) -}
Desc : Bool → AST → S.Env → S.Val → Set
Descs : Bool → ∀ {n} → Args (replicate n ■) → S.Env → List S.Val → Set
Strong Den : AST → S.Env → S.Val → Set
Strong = Desc true
Den = Desc false

{- what simp knows of each variable is true of the target's environment ρ'
   and the source's ρ -}
record Ok (E : Facts) (ρ' ρ : S.Env) : Set where
  inductive
  constructor mk-ok
  field
    val : ∀ x {v} → ρ ‼ x ≡ just v → Strong (term (E x)) ρ' v
    knw : ∀ x {v K} → ρ ‼ x ≡ just v → known (E x) ≡ just K → Den K ρ' v
    sml : ∀ x → small (term (E x)) ≡ true

{- the target's value on the left -}
data _≈_ where
  clo≈ : ∀ {E N ρ' ρ} → Ok E ρ' ρ → WS (suc (length ρ)) N → S.clo (term (simp (under E) N)) ρ' ≈ S.clo N ρ
  const≈ : ∀ {B k} → S.const B k ≈ S.const B k
  tup≈ : ∀ {vs ws} → Pointwise _≈_ vs ws → S.tup vs ≈ S.tup ws
  inl≈ : ∀ {v w} → v ≈ w → S.inl v ≈ S.inl w
  inr≈ : ∀ {v w} → v ≈ w → S.inr v ≈ S.inr w

Desc b (` y) ρ' v = Σ[ w ∈ S.Val ] ρ' ‼ y ≡ just w × w ≈ v
Desc true (lam ⦅ ⟩ N ,, Nil ⦆) ρ' v = S.clo N ρ' ≈ v
Desc false (lam ⦅ ⟩ N ,, Nil ⦆) ρ' v = ⊤
Desc b (lit B k ⦅ Nil ⦆) ρ' v = v ≡ S.const B k
Desc b (tuple n ⦅ as ⦆) ρ' v = Σ[ vs ∈ List S.Val ] v ≡ S.tup vs × Descs b as ρ' vs
Desc b (inl-op ⦅ M ,, Nil ⦆) ρ' v = Σ[ v₀ ∈ S.Val ] v ≡ S.inl v₀ × Desc b M ρ' v₀
Desc b (inr-op ⦅ M ,, Nil ⦆) ρ' v = Σ[ v₀ ∈ S.Val ] v ≡ S.inr v₀ × Desc b M ρ' v₀
Desc b _ ρ' v = ⊥
Descs b {zero} Nil ρ' vs = vs ≡ []
Descs b {suc n} (M ,, as) ρ' vs = Σ[ v ∈ S.Val ] Σ[ vs' ∈ List S.Val ] vs ≡ v ∷ vs' × Desc b M ρ' v × Descs b as ρ' vs'

Strongs Dens : ∀ {n} → Args (replicate n ■) → S.Env → List S.Val → Set
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

strong-den : ∀ T {ρ' v} → Strong T ρ' v → Den T ρ' v
strongs-den : ∀ {n} (as : Args (replicate n ■)) {ρ' vs} → Strongs as ρ' vs → Dens as ρ' vs
strong-den (` y) d = d
strong-den (lam ⦅ ⟩ N ,, Nil ⦆) d = tt
strong-den (lit B k ⦅ Nil ⦆) d = d
strong-den (tuple n ⦅ as ⦆) (vs , e , ds) = vs , e , strongs-den as ds
strong-den (inl-op ⦅ M ,, Nil ⦆) (v , e , d) = v , e , strong-den M d
strong-den (inr-op ⦅ M ,, Nil ⦆) (v , e , d) = v , e , strong-den M d
strongs-den {zero} Nil e = e
strongs-den {suc n} (M ,, as) (v , vs , e , d , ds) = v , vs , e , strong-den M d , strongs-den as ds

{- a small value has no functions -}
atom-strong : ∀ T {ρ' v} → atom T ≡ true → Den T ρ' v → Strong T ρ' v
atom-strong (` y) _ d = d
atom-strong (lit B k ⦅ Nil ⦆) _ d = d
atom-strong (tuple zero ⦅ Nil ⦆) _ d = d

small-strong : ∀ T {ρ' v} → small T ≡ true → Den T ρ' v → Strong T ρ' v
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

den-shift : ∀ K {ρ' v w} → Den K ρ' v → Den (shift K) (w ∷ ρ') v
dens-shift : ∀ {n} (as : Args (replicate n ■)) {ρ' vs w} → Dens as ρ' vs → Dens (rename-args suc as) (w ∷ ρ') vs
den-shift (` y) d = d
den-shift (lam ⦅ ⟩ N ,, Nil ⦆) d = tt
den-shift (lit B k ⦅ Nil ⦆) d = d
den-shift (tuple n ⦅ as ⦆) (vs , e , ds) = vs , e , dens-shift as ds
den-shift (inl-op ⦅ M ,, Nil ⦆) (v , e , d) = v , e , den-shift M d
den-shift (inr-op ⦅ M ,, Nil ⦆) (v , e , d) = v , e , den-shift M d
dens-shift {zero} Nil e = e
dens-shift {suc n} (M ,, as) (v , vs , e , d , ds) = v , vs , e , den-shift M d , dens-shift as ds

{- under one more variable, in the target -}
strong-shift : ∀ T {ρ' v w} → small T ≡ true → Strong T ρ' v → Strong (shift T) (w ∷ ρ') v
strong-shift T s d = small-strong (shift T) (small-shift T s) (den-shift T (strong-den T d))

{- the result of a primitive -}
prim-strong : ∀ o {ρ'} → Strong (prim-term o) ρ' (S.out o)
prim-strong (int n) = refl
prim-strong (bool true) = S.tup [] , refl , [] , refl , refl
prim-strong (bool false) = S.tup [] , refl , [] , refl , refl

{- a component of a described tuple -}
dens-pw : ∀ {n} (Ks : Args (replicate n ■)) {ρ' vs} → Dens Ks ρ' vs → Pointwise (λ K v → Den K ρ' v) (args→list Ks) vs
dens-pw {zero} Nil refl = []
dens-pw {suc n} (K ,, Ks) (v , vs , refl , d , ds) = d ∷ dens-pw Ks ds

dens-proj : ∀ {n m} (i : Fin n) (Ks : Args (replicate m ■)) {ρ' vs K} → Dens Ks ρ' vs → proj i (args→list Ks) ≡ just K
  → Σ[ v ∈ S.Val ] proj i vs ≡ just v × Den K ρ' v
dens-proj i Ks {vs = vs} ds p with proj-pw i (dens-pw Ks ds)
... | pw rewrite p with proj i vs | pw
...   | just v | M.just d = v , refl , d

{- Facts --------------------------------------------------------------------------}

lookup-ws : ∀ {x} (ρ : S.Env) → x < length ρ → Σ[ v ∈ S.Val ] ρ ‼ x ≡ just v
lookup-ws ρ x< = ‼-< ρ _ x<

{- variable 0 bound in both environments, known by k -}
ok-bind : ∀ {E ρ' ρ w v k} → Ok E ρ' ρ → w ≈ v → (∀ {K} → k ≡ just K → Den K (w ∷ ρ') v)
  → Ok (((` 0) ∣ k) • (λ x → shift-info (E x))) (w ∷ ρ') (v ∷ ρ)
ok-bind {E} ok r d = mk-ok val' knw' sml'
  where
  val' : _
  val' zero refl = _ , refl , r
  val' (suc x) e = strong-shift (term (E x)) (sml ok x) (val ok x e)
  knw' : _
  knw' zero refl k = d k
  knw' (suc x) {K = K} e k with known (E x) in k₀
  knw' (suc x) {K = .(shift K₀)} e refl | just K₀ = den-shift K₀ (knw ok x e k₀)
  sml' : _
  sml' zero = refl
  sml' (suc x) = small-shift (term (E x)) (sml ok x)

{- under a binder that stays -}
ok-under : ∀ {E ρ' ρ v' v} → Ok E ρ' ρ → v' ≈ v → Ok (under E) (v' ∷ ρ') (v ∷ ρ)
ok-under ok r = ok-bind ok r (λ { refl → _ , refl , r })

{- a small value for variable 0, in the source only -}
ok-self : ∀ {E ρ' ρ T v} → Ok E ρ' ρ → small T ≡ true → Strong T ρ' v → Ok (self T • E) ρ' (v ∷ ρ)
ok-self {T = T} ok s d = mk-ok val' knw' sml'
  where
  val' : _
  val' zero refl = d
  val' (suc x) e = val ok x e
  knw' : _
  knw' zero refl refl = strong-den T d
  knw' (suc x) e k = knw ok x e k
  sml' : _
  sml' zero = s
  sml' (suc x) = sml ok x

{- a value V that stays bound to variable 0, and known -}
ok-let : ∀ {E ρ' ρ V w v} → Ok E ρ' ρ → w ≈ v → Strong V ρ' v
  → Ok (((` 0) ∣ just (shift V)) • (λ x → shift-info (E x))) (w ∷ ρ') (v ∷ ρ)
ok-let {V = V} ok r d = ok-bind ok r (λ { refl → den-shift V (strong-den V d) })


{- The interpreter is monotone in the clock --------------------------------------}

⊑-bind : ∀ {A B : Set} {r₁ r₂ : Result A} {f g : A → Result B}
  → r₁ ⊑ᵣ r₂ → (∀ v → f v ⊑ᵣ g v) → (r₁ >>= f) ⊑ᵣ (r₂ >>= g)
⊑-bind timeout k = timeout
⊑-bind {r₁ = timeout} same k = timeout
⊑-bind {r₁ = wrong} same k = same
⊑-bind {r₁ = ret v} same k = k v

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

⊑-eq : ∀ {A : Set} {r r' : Result A} → r ⊑ᵣ r' → ¬ r ≡ timeout → r' ≡ r
⊑-eq timeout t = ⊥-elim (t refl)
⊑-eq same t = refl

{- Results that are the same from some clock on ---------------------------------}

Stable : ∀ {A : Set} → (ℕ → Result A) → Result A → Set
Stable f r = Σ[ c ∈ ℕ ] (∀ ck → c ≤ ck → f ck ≡ r)

st-now : ∀ {A : Set} {f : ℕ → Result A} {r} → (∀ ck → f ck ≡ r) → Stable f r
st-now e = 0 , λ ck _ → e ck

st-bind : ∀ {A B : Set} {f : ℕ → Result A} {g : ℕ → A → Result B} {v r}
  → Stable f (ret v) → Stable (λ ck → g ck v) r → Stable (λ ck → f ck >>= g ck) r
st-bind {g = g} (c₁ , e₁) (c₂ , e₂) =
  c₁ ⊔ c₂ , λ ck le → trans (cong (λ r → r >>= g ck) (e₁ ck (≤-trans (m≤m⊔n c₁ c₂) le))) (e₂ ck (≤-trans (m≤n⊔m c₁ c₂) le))

st-wrong : ∀ {A B : Set} {f : ℕ → Result A} {g : ℕ → A → Result B}
  → Stable f wrong → Stable (λ ck → f ck >>= g ck) wrong
st-wrong {g = g} (c , e) = c , λ ck le → cong (λ r → r >>= g ck) (e ck le)

st-call : ∀ {N ρ r} → Stable (λ ck → S.eval ck ρ N) r → Stable (λ ck → S.call ck N ρ) r
st-call (c , e) = suc c , λ { (suc ck) (s≤s le) → e ck le }

{- a result that is stable from some clock on is the result at every clock
   at which there is one -}
stable-now : ∀ {ρ M r ck} → Stable (λ ck → S.eval ck ρ M) r → ¬ S.eval ck ρ M ≡ timeout → S.eval ck ρ M ≡ r
stable-now {ρ} {M} {ck = ck} (c , e) t =
  trans (sym (⊑-eq (mono (m≤m⊔n ck c) ρ M) t)) (e (ck ⊔ c) (m≤n⊔m ck c))

Run : AST → S.Env → S.Val → Set
Run M ρ v = Stable (λ ck → S.eval ck ρ M) (ret v)

{- The target evaluates value terms, at any clock ---------------------------------}

teval : ∀ T {ρ' v} → Strong T ρ' v → Σ[ w ∈ S.Val ] (∀ ck → S.eval ck ρ' T ≡ ret w) × w ≈ v
tevals : ∀ {n} (as : Args (replicate n ■)) {ρ' vs} → Strongs as ρ' vs
  → Σ[ ws ∈ List S.Val ] (∀ ck acc → S.eval-args ck ρ' acc as ≡ ret (reverseAcc acc ws)) × Pointwise _≈_ ws vs
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

run-term : ∀ M {E ρ' ρ} → Ok E ρ' ρ → WS (length ρ) M → value (term (simp E M)) ≡ true
  → Σ[ v ∈ S.Val ] Run M ρ v × Strong (term (simp E M)) ρ' v
run-known : ∀ M {E ρ' ρ K} → Ok E ρ' ρ → WS (length ρ) M → known (simp E M) ≡ just K
  → Σ[ v ∈ S.Val ] Run M ρ v × Den K ρ' v
run-terms : ∀ {n} (as : Args (replicate n ■)) {E ρ' ρ} → Ok E ρ' ρ → WS-args (length ρ) as
  → values (simp-args E as) ≡ true
  → Σ[ vs ∈ List S.Val ] (∀ acc → Stable (λ ck → S.eval-args ck ρ acc as) (ret (reverseAcc acc vs)))
      × Strongs (simp-args E as) ρ' vs
run-get : ∀ {n} (i : Fin n) L {E ρ' ρ K} → Ok E ρ' ρ → WS (length ρ) L → component i (known (simp E L)) ≡ just K
  → Σ[ v ∈ S.Val ] Run (get i ⦅ L ,, Nil ⦆) ρ v × Den K ρ' v
run-inl : ∀ L {E ρ' ρ K} → Ok E ρ' ρ → WS (length ρ) L → branch (known (simp E L)) ≡ just (true , K)
  → Σ[ v ∈ S.Val ] Run L ρ (S.inl v) × Strong K ρ' v
run-inr : ∀ L {E ρ' ρ K} → Ok E ρ' ρ → WS (length ρ) L → branch (known (simp E L)) ≡ just (false , K)
  → Σ[ v ∈ S.Val ] Run L ρ (S.inr v) × Strong K ρ' v
run-int : ∀ L {E ρ' ρ n} → Ok E ρ' ρ → WS (length ρ) L → int-of (known (simp E L)) ≡ just n → Run L ρ (S.const Int n)
{- a primitive on known integers -}
run-prim : ∀ p L M {E ρ' ρ n m} → Ok E ρ' ρ → WS (length ρ) L → WS (length ρ) M
  → int-of (known (simp E L)) ≡ just n → int-of (known (simp E M)) ≡ just m
  → Run (prim p ⦅ L ,, M ,, Nil ⦆) ρ (S.out (δ p n m))
run-prim p L M ok wL wM e₁ e₂ = st-bind (run-int L ok wL e₁) (st-bind (run-int M ok wM e₂) (st-now (λ _ → refl)))

run-term (` x) {ρ = ρ} ok w e with lookup-ws ρ w
... | v , l = v , st-now (λ ck → cong from-maybe l) , val ok x l
run-term (lam ⦅ ⟩ N ,, Nil ⦆) ok (w , _) e = _ , st-now (λ _ → refl) , clo≈ ok w
run-term (app ⦅ lam ⦅ ⟩ N ,, Nil ⦆ ,, M ,, Nil ⦆) {E} {ρ' = ρ'} {ρ} ok ((wN , _) , wM , _) e
  with small (term (simp E M)) in s | value (term (simp E M)) in isv
... | true | _ with run-term M ok wM (P.small-value (term (simp E M)) s)
...   | v , σ , d with run-term N (ok-self ok s d) wN e
...     | w , τ , d' = w , st-bind σ (st-call τ) , d'
run-term (app ⦅ lam ⦅ ⟩ N ,, Nil ⦆ ,, M ,, Nil ⦆) {E} ok ((wN , _) , wM , _) () | false | true
run-term (app ⦅ lam ⦅ ⟩ N ,, Nil ⦆ ,, M ,, Nil ⦆) {E} ok ((wN , _) , wM , _) () | false | false
run-term (lit B k ⦅ Nil ⦆) ok w e = _ , st-now (λ _ → refl) , refl
run-term (tuple n ⦅ as ⦆) {E} {ρ = ρ} ok w e with run-terms as ok w e
... | vs , σ , ds = S.tup vs , st-bind (σ []) (st-now (λ _ → cong (λ x → ret (S.tup x)) (reverse-involutive vs))) , vs , refl , ds
run-term (get i ⦅ L ,, Nil ⦆) {E} ok (w , _) e with component i (known (simp E L)) in c
... | just K with small K in s
...   | true with run-get i L ok w c
...     | v , σ , d = v , σ , small-strong K s d
run-term (inl-op ⦅ M ,, Nil ⦆) ok (w , _) e with run-term M ok w e
... | v , σ , d = S.inl v , st-bind σ (st-now (λ _ → refl)) , v , refl , d
run-term (inr-op ⦅ M ,, Nil ⦆) ok (w , _) e with run-term M ok w e
... | v , σ , d = S.inr v , st-bind σ (st-now (λ _ → refl)) , v , refl , d
run-term (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) {E} ok (wL , (wM , wN , _)) e with branch (known (simp E L)) in b
... | just (true , K) with run-inl L ok wL b
...   | v , σ , d with run-term M (ok-self ok (proj₂ (branch-inl (known (simp E L)) b)) d) wM e
...     | w , τ , d' = w , st-bind σ τ , d'
run-term (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) {E} ok (wL , (wM , wN , _)) e | just (false , K) with run-inr L ok wL b
...   | v , σ , d with run-term N (ok-self ok (proj₂ (branch-inr (known (simp E L)) b)) d) wN e
...     | w , τ , d' = w , st-bind σ τ , d'
run-term (prim p ⦅ L ,, M ,, Nil ⦆) {E} ok (wL , wM , _) e with int-of (known (simp E L)) in e₁
... | just n with int-of (known (simp E M)) in e₂
...   | just m = S.out (δ p n m) , run-prim p L M ok wL wM e₁ e₂ , prim-strong (δ p n m)

run-terms {zero} Nil ok _ _ = [] , (λ acc → st-now (λ _ → refl)) , refl
run-terms {suc n} (M ,, as) {E} ok (w , ws) e with P.∧-true {value (term (simp E M))} e
... | e₁ , e₂ with run-term M ok w e₁ | run-terms as ok ws e₂
...   | v , σ , d | vs , τ , ds = v ∷ vs , (λ acc → st-bind σ (τ (v ∷ acc))) , v , vs , refl , d , ds

run-get i L {E} ok w c with comp-inv i (known (simp E L)) c
... | m , Ks , k , p with run-known L ok w k
...   | .(S.tup vs) , σ , (vs , refl , ds) with dens-proj i Ks ds p
...     | v , q , d = v , st-bind σ (st-now (λ _ → cong from-maybe q)) , d

run-inl L {E} ok w b with branch-inl (known (simp E L)) b
... | k , s with run-known L ok w k
...   | .(S.inl v₀) , σ , (v₀ , refl , d) = v₀ , σ , small-strong _ s d

run-inr L {E} ok w b with branch-inr (known (simp E L)) b
... | k , s with run-known L ok w k
...   | .(S.inr v₀) , σ , (v₀ , refl , d) = v₀ , σ , small-strong _ s d

run-int L {E} ok w e with run-known L ok w (int-inv (known (simp E L)) e)
... | .(S.const Int _) , σ , refl = σ

run-known (` x) {ρ = ρ} ok w k with lookup-ws ρ w
... | v , l = v , st-now (λ ck → cong from-maybe l) , knw ok x l k
run-known (lam ⦅ ⟩ N ,, Nil ⦆) ok w refl = _ , st-now (λ _ → refl) , tt
run-known (app ⦅ lam ⦅ ⟩ N ,, Nil ⦆ ,, M ,, Nil ⦆) {E} {ρ = ρ} ok ((wN , _) , wM , _) k
  with small (term (simp E M)) in s | value (term (simp E M)) in isv
... | true | _ with run-term M ok wM (P.small-value (term (simp E M)) s)
...   | v , σ , d with run-known N (ok-self ok s d) wN k
...     | w , τ , d' = w , st-bind σ (st-call τ) , d'
run-known (app ⦅ lam ⦅ ⟩ N ,, Nil ⦆ ,, M ,, Nil ⦆) {E} ok ((wN , _) , wM , _) () | false | true
run-known (app ⦅ lam ⦅ ⟩ N ,, Nil ⦆ ,, M ,, Nil ⦆) {E} ok ((wN , _) , wM , _) () | false | false
run-known (lit B k ⦅ Nil ⦆) ok w refl = _ , st-now (λ _ → refl) , refl
run-known (tuple n ⦅ as ⦆) {E} ok w k with value (tuple n ⦅ simp-args E as ⦆) in isv
run-known (tuple n ⦅ as ⦆) {E} ok w refl | true with run-term (tuple n ⦅ as ⦆) ok w isv
... | v , σ , d = v , σ , strong-den (tuple n ⦅ simp-args E as ⦆) d
run-known (get i ⦅ L ,, Nil ⦆) {E} ok (w , _) k with component i (known (simp E L)) in c
... | just K with small K
run-known (get i ⦅ L ,, Nil ⦆) {E} ok (w , _) refl | just K | true = run-get i L ok w c
run-known (get i ⦅ L ,, Nil ⦆) {E} ok (w , _) refl | just K | false = run-get i L ok w c
run-known (inl-op ⦅ M ,, Nil ⦆) {E} ok w k with value (term (simp E M)) in isv
run-known (inl-op ⦅ M ,, Nil ⦆) {E} ok w refl | true with run-term (inl-op ⦅ M ,, Nil ⦆) ok w isv
... | v , σ , d = v , σ , strong-den (inl-op ⦅ term (simp E M) ,, Nil ⦆) d
run-known (inr-op ⦅ M ,, Nil ⦆) {E} ok w k with value (term (simp E M)) in isv
run-known (inr-op ⦅ M ,, Nil ⦆) {E} ok w refl | true with run-term (inr-op ⦅ M ,, Nil ⦆) ok w isv
... | v , σ , d = v , σ , strong-den (inr-op ⦅ term (simp E M) ,, Nil ⦆) d
run-known (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) {E} ok (wL , (wM , wN , _)) k with branch (known (simp E L)) in b
... | just (true , K) with run-inl L ok wL b
...   | v , σ , d with run-known M (ok-self ok (proj₂ (branch-inl (known (simp E L)) b)) d) wM k
...     | w , τ , d' = w , st-bind σ τ , d'
run-known (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) {E} ok (wL , (wM , wN , _)) k | just (false , K) with run-inr L ok wL b
...   | v , σ , d with run-known N (ok-self ok (proj₂ (branch-inr (known (simp E L)) b)) d) wN k
...     | w , τ , d' = w , st-bind σ τ , d'
run-known (prim p ⦅ L ,, M ,, Nil ⦆) {E} ok (wL , wM , _) k with int-of (known (simp E L)) in e₁
... | just n with int-of (known (simp E M)) in e₂
run-known (prim p ⦅ L ,, M ,, Nil ⦆) {E} ok (wL , wM , _) refl | just n | just m =
  S.out (δ p n m) , run-prim p L M ok wL wM e₁ e₂ , strong-den (prim-term (δ p n m)) (prim-strong (δ p n m))

flipM : ∀ {a b} → M.Pointwise _≈_ a b → M.Pointwise (λ v w → w ≈ v) b a
flipM (M.just r) = M.just r
flipM M.nothing = M.nothing

{- Forward, at the same clock ------------------------------------------------------}

{- the source's value on the left -}
_≽_ : S.Val → S.Val → Set
v ≽ w = w ≈ v

_≽s_ : List S.Val → List S.Val → Set
vs ≽s ws = Pointwise _≈_ ws vs

pw-flip : ∀ {ws vs} → Pointwise _≈_ ws vs → Pointwise _≽_ vs ws
pw-flip [] = []
pw-flip (r ∷ rs) = r ∷ pw-flip rs

bind-le : ∀ {A B C D : Set} {R : A → B → Set} {R' : C → D → Set} {r₁ r₂} {f : A → Result C} {g : B → Result D}
  → LeResult R r₁ r₂ → (∀ {v w} → r₁ ≡ ret v → R v w → LeResult R' (f v) (g w)) → LeResult R' (r₁ >>= f) (r₂ >>= g)
bind-le timeout k = timeout
bind-le wrong k = wrong
bind-le (ret r) k = k refl r

le-⊑ : ∀ {A B : Set} {R : A → B → Set} {r₁ r₂ r₂'} → LeResult R r₁ r₂ → r₂ ⊑ᵣ r₂' → LeResult R r₁ r₂'
le-⊑ timeout _ = timeout
le-⊑ r same = r

from-maybe-le : ∀ {A B : Set} {R : A → B → Set} {mv mw} → M.Pointwise R mv mw → LeResult R (from-maybe mv) (from-maybe mw)
from-maybe-le (M.just r) = ret r
from-maybe-le M.nothing = wrong

wrong≢ : ¬ _≡_ {A = Result S.Val} wrong timeout
wrong≢ ()

ret≢ : ∀ {v} → ¬ _≡_ {A = Result S.Val} (ret v) timeout
ret≢ ()

{- at each clock, the source times out or returns the value it runs to -}
run-at : ∀ M ρ {v} → Run M ρ v → ∀ ck → S.eval ck ρ M ≡ timeout ⊎ S.eval ck ρ M ≡ ret v
run-at M ρ σ ck with S.eval ck ρ M in e
... | timeout = inj₁ refl
... | wrong = ⊥-elim (wr (trans (sym e) (stable-now {ρ} {M} {_} {ck} σ (λ t → wrong≢ (trans (sym e) t)))))
  where wr : ∀ {v} → ¬ _≡_ {A = Result S.Val} wrong (ret v)
        wr ()
... | ret v' = inj₂ (trans (sym e) (stable-now {ρ} {M} {_} {ck} σ (λ t → ret≢ (trans (sym e) t))))

{- the source runs M to a value that the target's value term T describes -}
known-le : ∀ ck M ρ {v T ρ'} → Run M ρ v → Strong T ρ' v → LeResult _≽_ (S.eval ck ρ M) (S.eval ck ρ' T)
known-le ck M ρ σ d with teval _ d
... | w , et , r rewrite et ck with run-at M ρ σ ck
...   | inj₁ e = subst (λ x → LeResult _≽_ x _) (sym e) timeout
...   | inj₂ e = subst (λ x → LeResult _≽_ x _) (sym e) (ret r)

{- the source's operand has a known value -}
src-known : ∀ {ck} M ρ {v r₂} {g : S.Val → Result S.Val} → Run M ρ v → LeResult _≽_ (g v) r₂
  → LeResult _≽_ (S.eval ck ρ M >>= g) r₂
src-known {ck} M ρ {g = g} σ k with run-at M ρ σ ck
... | inj₁ e = subst (λ x → LeResult _≽_ (x >>= g) _) (sym e) timeout
... | inj₂ e = subst (λ x → LeResult _≽_ (x >>= g) _) (sym e) k

run≈ : ∀ ck M {E ρ' ρ} → Ok E ρ' ρ → WS (length ρ) M → LeResult _≽_ (S.eval ck ρ M) (S.eval ck ρ' (term (simp E M)))
args≈ : ∀ ck {n} (as : Args (replicate n ■)) {E ρ' ρ acc acc'} → Ok E ρ' ρ → WS-args (length ρ) as → acc ≽s acc'
  → LeResult _≽s_ (S.eval-args ck ρ acc as) (S.eval-args ck ρ' acc' (simp-args E as))
apply≈ : ∀ ck M {E ρ' ρ v v'} → Ok E ρ' ρ → WS (length ρ) M → v' ≈ v
  → LeResult _≽_ (S.apply ck ρ M v) (S.apply ck ρ' (term (simp E M)) v')
call≈ : ∀ ck N {E ρ' ρ} → Ok E ρ' ρ → WS (length ρ) N → LeResult _≽_ (S.call ck N ρ) (S.call ck (term (simp E N)) ρ')
call≈ zero N ok w = timeout
call≈ (suc ck) N ok w = run≈ ck N ok w
branch≈ : ∀ ck M N {E ρ' ρ v v'} → Ok E ρ' ρ → WS (suc (length ρ)) M → WS (suc (length ρ)) N → v' ≈ v
  → LeResult _≽_ (S.branch ck ρ M N v) (S.branch ck ρ' (term (simp (under E) M)) (term (simp (under E) N)) v')
branch≈ ck M N ok wM wN (inl≈ r) = run≈ ck M (ok-under ok r) wM
branch≈ ck M N ok wM wN (inr≈ r) = run≈ ck N (ok-under ok r) wN
branch≈ ck M N ok wM wN (clo≈ _ _) = wrong
branch≈ ck M N ok wM wN const≈ = wrong
branch≈ ck M N ok wM wN (tup≈ _) = wrong
project≈ : ∀ {n} (i : Fin n) {v v'} → v' ≈ v → LeResult _≽_ (S.project i v) (S.project i v')
project≈ i (tup≈ rs) = from-maybe-le (proj-pw i (pw-flip rs))
project≈ i (clo≈ _ _) = wrong
project≈ i const≈ = wrong
project≈ i (inl≈ _) = wrong
project≈ i (inr≈ _) = wrong

apply≈ ck M ok w (clo≈ {N = N} ok₁ w₁) = bind-le (run≈ ck M ok w) (λ _ r → call≈ ck N (ok-under ok₁ r) w₁)
apply≈ ck M ok w const≈ = wrong
apply≈ ck M ok w (tup≈ _) = wrong
apply≈ ck M ok w (inl≈ _) = wrong
apply≈ ck M ok w (inr≈ _) = wrong

args≈ ck {zero} Nil ok _ rs = ret rs
args≈ ck {suc n} (M ,, as) ok (w , ws) rs = bind-le (run≈ ck M ok w) (λ _ r → args≈ ck as ok ws (r ∷ rs))

run≈ ck (` x) {ρ = ρ} ok w with lookup-ws ρ w
... | v , l = known-le ck (` x) ρ (st-now (λ ck → cong from-maybe l)) (val ok x l)
run≈ ck (lam ⦅ ⟩ N ,, Nil ⦆) ok (w , _) = ret (clo≈ ok w)
run≈ ck (app ⦅ lam ⦅ ⟩ N ,, Nil ⦆ ,, M ,, Nil ⦆) {E} {ρ'} {ρ} ok ((wN , _) , wM , _)
  with small (term (simp E M)) in s | value (term (simp E M)) in isv
... | true | _ with run-term M ok wM (P.small-value (term (simp E M)) s)
...   | v , σ , d = src-known M ρ σ (skip ck)
  where
  skip : ∀ ck → LeResult _≽_ (S.call ck N (v ∷ ρ)) (S.eval ck ρ' (term (simp (self (term (simp E M)) • E) N)))
  skip zero = timeout
  skip (suc ck) = le-⊑ (run≈ ck N (ok-self ok s d) wN) (mono (Data.Nat.Properties.n≤1+n ck) ρ' (term (simp (self (term (simp E M)) • E) N)))
run≈ ck (app ⦅ lam ⦅ ⟩ N ,, Nil ⦆ ,, M ,, Nil ⦆) {E} ok ((wN , _) , wM , _) | false | true
  with run-term M ok wM isv
... | v₀ , σ , d = bind-le (run≈ ck M ok wM) λ {v} e r → call-let ck (stable-eq e) r
  where
  stable-eq : ∀ {v} → S.eval ck _ M ≡ ret v → v ≡ v₀
  stable-eq {v} e with trans (sym e) (stable-now {_} {M} {_} {ck} σ (λ t → case (trans (sym e) t)))
    where case : ret v ≡ timeout → ⊥
          case ()
  ... | refl = refl
  call-let : ∀ ck {v w} → v ≡ v₀ → w ≈ v
    → LeResult _≽_ (S.call ck N (v ∷ _))
                   (S.call ck (term (simp (((` 0) ∣ just (shift (term (simp E M)))) • (λ x → shift-info (E x))) N)) (w ∷ _))
  call-let zero _ _ = timeout
  call-let (suc ck) refl r = run≈ ck N (ok-let ok r d) wN
run≈ ck (app ⦅ lam ⦅ ⟩ N ,, Nil ⦆ ,, M ,, Nil ⦆) {E} ok ((wN , _) , wM , _) | false | false =
  apply≈ ck M ok wM (clo≈ ok wN)
run≈ ck (app ⦅ L@(` x) ,, M ,, Nil ⦆) ok (wL , wM , _) = bind-le (run≈ ck L ok wL) (λ _ r → apply≈ ck M ok wM r)
run≈ ck (app ⦅ L@(app ⦅ _ ⦆) ,, M ,, Nil ⦆) ok (wL , wM , _) = bind-le (run≈ ck L ok wL) (λ _ r → apply≈ ck M ok wM r)
run≈ ck (app ⦅ L@(lit B k ⦅ _ ⦆) ,, M ,, Nil ⦆) ok (wL , wM , _) = bind-le (run≈ ck L ok wL) (λ _ r → apply≈ ck M ok wM r)
run≈ ck (app ⦅ L@(tuple n ⦅ _ ⦆) ,, M ,, Nil ⦆) ok (wL , wM , _) = bind-le (run≈ ck L ok wL) (λ _ r → apply≈ ck M ok wM r)
run≈ ck (app ⦅ L@(get i ⦅ _ ⦆) ,, M ,, Nil ⦆) ok (wL , wM , _) = bind-le (run≈ ck L ok wL) (λ _ r → apply≈ ck M ok wM r)
run≈ ck (app ⦅ L@(inl-op ⦅ _ ⦆) ,, M ,, Nil ⦆) ok (wL , wM , _) = bind-le (run≈ ck L ok wL) (λ _ r → apply≈ ck M ok wM r)
run≈ ck (app ⦅ L@(inr-op ⦅ _ ⦆) ,, M ,, Nil ⦆) ok (wL , wM , _) = bind-le (run≈ ck L ok wL) (λ _ r → apply≈ ck M ok wM r)
run≈ ck (app ⦅ L@(case-op ⦅ _ ⦆) ,, M ,, Nil ⦆) ok (wL , wM , _) = bind-le (run≈ ck L ok wL) (λ _ r → apply≈ ck M ok wM r)
run≈ ck (app ⦅ L@(prim p ⦅ _ ⦆) ,, M ,, Nil ⦆) ok (wL , wM , _) = bind-le (run≈ ck L ok wL) (λ _ r → apply≈ ck M ok wM r)
run≈ ck (lit B k ⦅ Nil ⦆) ok w = ret const≈
run≈ ck (tuple n ⦅ as ⦆) ok w = bind-le (args≈ ck as ok w []) (λ _ rs → ret (tup≈ (reverse⁺ rs)))
run≈ ck (get i ⦅ L ,, Nil ⦆) {E} ok (w , _) with component i (known (simp E L)) in c
... | nothing = bind-le (run≈ ck L ok w) (λ _ r → project≈ i r)
... | just K with small K in s
...   | true with run-get i L ok w c
...     | v , σ , d = known-le ck (get i ⦅ L ,, Nil ⦆) _ σ (small-strong K s d)
run≈ ck (get i ⦅ L ,, Nil ⦆) {E} ok (w , _) | just K | false = bind-le (run≈ ck L ok w) (λ _ r → project≈ i r)
run≈ ck (inl-op ⦅ M ,, Nil ⦆) ok (w , _) = bind-le (run≈ ck M ok w) (λ _ r → ret (inl≈ r))
run≈ ck (inr-op ⦅ M ,, Nil ⦆) ok (w , _) = bind-le (run≈ ck M ok w) (λ _ r → ret (inr≈ r))
run≈ ck (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) {E} ok (wL , (wM , wN , _)) with branch (known (simp E L)) in b
... | nothing = bind-le (run≈ ck L ok wL) (λ _ r → branch≈ ck M N ok wM wN r)
... | just (true , K) with run-inl L ok wL b
...   | v , σ , d = src-known L _ σ (run≈ ck M (ok-self ok (proj₂ (branch-inl (known (simp E L)) b)) d) wM)
run≈ ck (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) {E} ok (wL , (wM , wN , _)) | just (false , K) with run-inr L ok wL b
...   | v , σ , d = src-known L _ σ (run≈ ck N (ok-self ok (proj₂ (branch-inr (known (simp E L)) b)) d) wN)
run≈ ck (prim p ⦅ L ,, M ,, Nil ⦆) {E} ok (wL , wM , _) with int-of (known (simp E L)) in e₁
... | nothing = bind-le (run≈ ck L ok wL) (λ _ r → bind-le (run≈ ck M ok wM) (λ _ s → from-maybe-le (flipM (prim≈ p r s))))
... | just n with int-of (known (simp E M)) in e₂
...   | nothing = bind-le (run≈ ck L ok wL) (λ _ r → bind-le (run≈ ck M ok wM) (λ _ s → from-maybe-le (flipM (prim≈ p r s))))
...   | just m = known-le ck (prim p ⦅ L ,, M ,, Nil ⦆) _ (run-prim p L M ok wL wM e₁ e₂) (prim-strong (δ p n m))

{- Backward: the source catches up -------------------------------------------------}

Back : ∀ {A B : Set} → (A → B → Set) → (ℕ → Result A) → Result B → Set
Back R f r₂ = ¬ r₂ ≡ timeout → Σ[ r₁ ∈ _ ] Stable f r₁ × RelResult R r₁ r₂

back-bind : ∀ {A B C D : Set} {R : A → B → Set} {R' : C → D → Set} {f : ℕ → Result A} {h : ℕ → A → Result C}
  {r₂ : Result B} {g : B → Result D}
  → Back R f r₂ → (∀ {v w} → Stable f (ret v) → R v w → Back R' (λ ck → h ck v) (g w))
  → Back R' (λ ck → f ck >>= h ck) (r₂ >>= g)
back-bind {r₂ = timeout} k₁ k₂ nt = ⊥-elim (nt refl)
back-bind {r₂ = wrong} k₁ k₂ nt with k₁ (λ ())
... | .wrong , st , wrong = wrong , st-wrong st , wrong
back-bind {r₂ = ret w} k₁ k₂ nt with k₁ (λ ())
... | .(ret _) , st , ret r with k₂ st r nt
...   | r' , st' , rr = r' , st-bind st st' , rr

back-wrong : ∀ {A B : Set} {R : A → B → Set} {f : ℕ → Result A} → (∀ ck → f ck ≡ wrong) → Back R f wrong
back-wrong e _ = wrong , st-now e , wrong

back-maybe : ∀ {A B : Set} {R : A → B → Set} {mv mw} → M.Pointwise R mv mw → Back R (λ _ → from-maybe mv) (from-maybe mw)
back-maybe (M.just r) _ = _ , st-now (λ _ → refl) , ret r
back-maybe M.nothing _ = wrong , st-now (λ _ → refl) , wrong

{- the source's operand has a known value -}
back-run : ∀ {L ρ v r₂} {g : ℕ → S.Val → Result S.Val} → Run L ρ v → Back _≽_ (λ ck → g ck v) r₂
  → Back _≽_ (λ ck → S.eval ck ρ L >>= g ck) r₂
back-run σ k nt with k nt
... | r , st , rr = r , st-bind σ st , rr

{- the source runs M to a value that the target's value term T describes -}
known-back : ∀ ck M ρ {v T ρ'} → Run M ρ v → Strong T ρ' v → Back _≽_ (λ ck → S.eval ck ρ M) (S.eval ck ρ' T)
known-back ck M ρ σ d _ with teval _ d
... | w , et , r rewrite et ck = _ , σ , ret r

stable-unique : ∀ {A : Set} {f : ℕ → Result A} {r r'} → Stable f r → Stable f r' → r ≡ r'
stable-unique (c , e) (c' , e') = trans (sym (e (c ⊔ c') (m≤m⊔n c c'))) (e' (c ⊔ c') (m≤n⊔m c c'))

back : ∀ ck M {E ρ' ρ} → Ok E ρ' ρ → WS (length ρ) M → Back _≽_ (λ ck → S.eval ck ρ M) (S.eval ck ρ' (term (simp E M)))
back-args : ∀ ck {n} (as : Args (replicate n ■)) {E ρ' ρ acc acc'} → Ok E ρ' ρ → WS-args (length ρ) as → acc ≽s acc'
  → Back _≽s_ (λ ck → S.eval-args ck ρ acc as) (S.eval-args ck ρ' acc' (simp-args E as))
back-apply : ∀ ck M {E ρ' ρ v v'} → Ok E ρ' ρ → WS (length ρ) M → v' ≈ v
  → Back _≽_ (λ ck → S.apply ck ρ M v) (S.apply ck ρ' (term (simp E M)) v')
back-call : ∀ ck N {E ρ' ρ N'} → N' ≡ term (simp E N) → Ok E ρ' ρ → WS (length ρ) N
  → Back _≽_ (λ ck → S.call ck N ρ) (S.call ck N' ρ')
back-call zero N e ok w nt = ⊥-elim (nt refl)
back-call (suc ck) N refl ok w nt with back ck N ok w nt
... | r , st , rr = r , st-call st , rr
back-branch : ∀ ck M N {E ρ' ρ v v'} → Ok E ρ' ρ → WS (suc (length ρ)) M → WS (suc (length ρ)) N → v' ≈ v
  → Back _≽_ (λ ck → S.branch ck ρ M N v) (S.branch ck ρ' (term (simp (under E) M)) (term (simp (under E) N)) v')
back-branch ck M N ok wM wN (inl≈ r) = back ck M (ok-under ok r) wM
back-branch ck M N ok wM wN (inr≈ r) = back ck N (ok-under ok r) wN
back-branch ck M N ok wM wN (clo≈ _ _) = back-wrong (λ _ → refl)
back-branch ck M N ok wM wN const≈ = back-wrong (λ _ → refl)
back-branch ck M N ok wM wN (tup≈ _) = back-wrong (λ _ → refl)
back-project : ∀ {n} (i : Fin n) {v v'} → v' ≈ v → Back _≽_ (λ _ → S.project i v) (S.project i v')
back-project i (tup≈ rs) = back-maybe (proj-pw i (pw-flip rs))
back-project i (clo≈ _ _) = back-wrong (λ _ → refl)
back-project i const≈ = back-wrong (λ _ → refl)
back-project i (inl≈ _) = back-wrong (λ _ → refl)
back-project i (inr≈ _) = back-wrong (λ _ → refl)

back-apply ck M ok w (clo≈ {N = N} ok₁ w₁) = back-bind (back ck M ok w) (λ _ r → back-call ck N refl (ok-under ok₁ r) w₁)
back-apply ck M ok w const≈ = back-wrong (λ _ → refl)
back-apply ck M ok w (tup≈ _) = back-wrong (λ _ → refl)
back-apply ck M ok w (inl≈ _) = back-wrong (λ _ → refl)
back-apply ck M ok w (inr≈ _) = back-wrong (λ _ → refl)

back-args ck {zero} Nil ok _ rs _ = _ , st-now (λ _ → refl) , ret rs
back-args ck {suc n} (M ,, as) ok (w , ws) rs = back-bind (back ck M ok w) (λ _ r → back-args ck as ok ws (r ∷ rs))

back ck (` x) {ρ = ρ} ok w with lookup-ws ρ w
... | v , l = known-back ck (` x) ρ (st-now (λ ck → cong from-maybe l)) (val ok x l)
back ck (lam ⦅ ⟩ N ,, Nil ⦆) ok (w , _) _ = _ , st-now (λ _ → refl) , ret (clo≈ ok w)
back ck (app ⦅ lam ⦅ ⟩ N ,, Nil ⦆ ,, M ,, Nil ⦆) {E} ok ((wN , _) , wM , _)
  with small (term (simp E M)) in s | value (term (simp E M)) in isv
... | true | _ with run-term M ok wM (P.small-value (term (simp E M)) s)
...   | v , σ , d = λ nt → body (back ck N (ok-self ok s d) wN nt)
  where body : _ → _
        body (r , st , rr) = r , st-bind σ (st-call st) , rr
back ck (app ⦅ lam ⦅ ⟩ N ,, Nil ⦆ ,, M ,, Nil ⦆) {E} ok ((wN , _) , wM , _) | false | true
  with run-term M ok wM isv
... | v₀ , σ , d =
  back-bind (back ck M ok wM) λ st r → back-call ck N refl (ok-let ok r (subst (Strong (term (simp E M)) _) (sym (ret-inj (stable-unique st σ))) d)) wN
  where ret-inj : ∀ {v w : S.Val} → _≡_ {A = Result S.Val} (ret v) (ret w) → v ≡ w
        ret-inj refl = refl
back ck (app ⦅ lam ⦅ ⟩ N ,, Nil ⦆ ,, M ,, Nil ⦆) {E} ok ((wN , _) , wM , _) | false | false =
  back-apply ck M ok wM (clo≈ ok wN)
back ck (app ⦅ L@(` x) ,, M ,, Nil ⦆) ok (wL , wM , _) = back-bind (back ck L ok wL) (λ _ r → back-apply ck M ok wM r)
back ck (app ⦅ L@(app ⦅ _ ⦆) ,, M ,, Nil ⦆) ok (wL , wM , _) = back-bind (back ck L ok wL) (λ _ r → back-apply ck M ok wM r)
back ck (app ⦅ L@(lit B k ⦅ _ ⦆) ,, M ,, Nil ⦆) ok (wL , wM , _) = back-bind (back ck L ok wL) (λ _ r → back-apply ck M ok wM r)
back ck (app ⦅ L@(tuple n ⦅ _ ⦆) ,, M ,, Nil ⦆) ok (wL , wM , _) = back-bind (back ck L ok wL) (λ _ r → back-apply ck M ok wM r)
back ck (app ⦅ L@(get i ⦅ _ ⦆) ,, M ,, Nil ⦆) ok (wL , wM , _) = back-bind (back ck L ok wL) (λ _ r → back-apply ck M ok wM r)
back ck (app ⦅ L@(inl-op ⦅ _ ⦆) ,, M ,, Nil ⦆) ok (wL , wM , _) = back-bind (back ck L ok wL) (λ _ r → back-apply ck M ok wM r)
back ck (app ⦅ L@(inr-op ⦅ _ ⦆) ,, M ,, Nil ⦆) ok (wL , wM , _) = back-bind (back ck L ok wL) (λ _ r → back-apply ck M ok wM r)
back ck (app ⦅ L@(case-op ⦅ _ ⦆) ,, M ,, Nil ⦆) ok (wL , wM , _) = back-bind (back ck L ok wL) (λ _ r → back-apply ck M ok wM r)
back ck (app ⦅ L@(prim p ⦅ _ ⦆) ,, M ,, Nil ⦆) ok (wL , wM , _) = back-bind (back ck L ok wL) (λ _ r → back-apply ck M ok wM r)
back ck (lit B k ⦅ Nil ⦆) ok w _ = _ , st-now (λ _ → refl) , ret const≈
back ck (tuple n ⦅ as ⦆) ok w =
  back-bind (back-args ck as ok w []) (λ _ rs _ → _ , st-now (λ _ → refl) , ret (tup≈ (reverse⁺ rs)))
back ck (get i ⦅ L ,, Nil ⦆) {E} ok (w , _) with component i (known (simp E L)) in c
... | nothing = back-bind (back ck L ok w) (λ _ r → back-project i r)
... | just K with small K in s
...   | true with run-get i L ok w c
...     | v , σ , d = known-back ck (get i ⦅ L ,, Nil ⦆) _ σ (small-strong K s d)
back ck (get i ⦅ L ,, Nil ⦆) {E} ok (w , _) | just K | false = back-bind (back ck L ok w) (λ _ r → back-project i r)
back ck (inl-op ⦅ M ,, Nil ⦆) ok (w , _) = back-bind (back ck M ok w) (λ _ r _ → _ , st-now (λ _ → refl) , ret (inl≈ r))
back ck (inr-op ⦅ M ,, Nil ⦆) ok (w , _) = back-bind (back ck M ok w) (λ _ r _ → _ , st-now (λ _ → refl) , ret (inr≈ r))
back ck (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) {E} ok (wL , (wM , wN , _)) with branch (known (simp E L)) in b
... | nothing = back-bind (back ck L ok wL) (λ _ r → back-branch ck M N ok wM wN r)
... | just (true , K) with run-inl L ok wL b
...   | v , σ , d = back-run {L} {g = λ c → S.branch c _ M N} σ (back ck M (ok-self ok (proj₂ (branch-inl (known (simp E L)) b)) d) wM)
back ck (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) {E} ok (wL , (wM , wN , _)) | just (false , K) with run-inr L ok wL b
...   | v , σ , d = back-run {L} {g = λ c → S.branch c _ M N} σ (back ck N (ok-self ok (proj₂ (branch-inr (known (simp E L)) b)) d) wN)
back ck (prim p ⦅ L ,, M ,, Nil ⦆) {E} ok (wL , wM , _) with int-of (known (simp E L)) in e₁
... | nothing = back-bind (back ck L ok wL) (λ _ r → back-bind (back ck M ok wM) (λ _ s → back-maybe (flipM (prim≈ p r s))))
... | just n with int-of (known (simp E M)) in e₂
...   | nothing = back-bind (back ck L ok wL) (λ _ r → back-bind (back ck M ok wM) (λ _ s → back-maybe (flipM (prim≈ p r s))))
...   | just m = known-back ck (prim p ⦅ L ,, M ,, Nil ⦆) _ (run-prim p L M ok wL wM e₁ e₂) (prim-strong (δ p n m))

{- The end theorem: for closed programs ------------------------------------------}

ok₀ : Ok (λ x → self (` x)) [] []
ok₀ = mk-ok (λ x ()) (λ x ()) (λ x → refl)

simplify-correct : ∀ M → Closed M → Equivalent (S.sem M) (S.sem (simplify M))
simplify-correct M c =
  clocked-le _≽_ (λ r → sym (obs≈ r)) (λ le → mono le [] (simplify M))
    (λ ck → run≈ ck M ok₀ (closed-ws {M} c))
    (λ ck nt → nt-src nt (back ck M ok₀ (closed-ws {M} c) nt))
  where
  nt-src : ∀ {r₂} → ¬ r₂ ≡ timeout → Σ[ r₁ ∈ Result S.Val ] Stable (λ ck → S.eval ck [] M) r₁ × RelResult _≽_ r₁ r₂
    → Σ[ ck' ∈ ℕ ] ¬ S.eval ck' [] M ≡ timeout
  nt-src nt (_ , _ , timeout) = ⊥-elim (nt refl)
  nt-src nt (.wrong , (c , e) , wrong) = c , λ t → wrong≢ (trans (sym (e c ≤-refl)) t)
  nt-src nt (.(ret _) , (c , e) , ret _) = c , λ t → ret≢ (trans (sym (e c ≤-refl)) t)

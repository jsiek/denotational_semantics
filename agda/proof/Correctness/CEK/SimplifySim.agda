{-

  Correctness of the simplify pass (ISWIM → ISWIM) by a forward simulation
  of the target's machine by the source's (see the design note in
  Semantics/CEK/Smallstep.agda); Equivalent is symmetric.

  The target does less work than the source: the reductions simplify did
  lag-star of time (β of a small value, an inlined call, a case on a known
  injection, a projection from a known tuple, a primitive on known
  integers) are
  steps of the source only, which it takes when the target takes the
  corresponding one. But the target does more work in one place: it
  evaluates a small value (inl 3, say) where the source looks up a
  variable, and it evaluates the value of a let that simplify kept,
  where the source has run ahead. There the target stutters: a match is
  indexed by the number of target steps until a state related to the
  current source state (match).

  Values are related (_≈_) when they agree, except that a target closure
  is the simplified body of a source closure, under Facts that are true
  of the two environments (Ok): the term that replaces each variable
  denotes, in the target's environment, a value related to the source's
  (Strong), and what it is known to be describes it (KDen): a known
  value the same way, up to functions (Den), and a known function λ N
  as a source closure of N, under Facts true of its environment. States
  and continuations are related frame by frame, the code by simp.

  The source's run-lag-star is by run-term and run-known: if the term that
  simp E M returns is a value, or M has a known value, the source runs M
  to a value it describes. β and an inlined call share one lemma each
  (let-term, let-known, let-sim), from the source's run to the operand:
  for an inlined call, the source first runs the operator to the known
  function's closure. The end theorem is for closed programs: an
  unbound variable makes the source go wrong where the target may have
  dropped it.

-}

module proof.Correctness.CEK.SimplifySim where

open import Framework.Primitives using (Int)
open import Framework.Syntax.SyntaxUtil using (_,,_; Nil; ⟩_,,_)
open import Language.ISWIM
open import Language.Prim using (int; bool; δ)
open import proof.Compiler.SimplifyFacts as P
  using (Info; _∣_; term; known; Known; Facts; self; info; under; known-as; shift-info; shift-known; simp; simp-args;
         lam?; is-lam; other; simp-call; size; inline-size; inline-fuel;
         simp-app; simp-let; simp-get; simp-case; simp-prim; simplify; small; atom; value; values;
         component; branch; int-of; prim-term; value-sv; small-sv; comp-inv; int-inv; branch-inl; branch-inr)
open import Compiler.EncloseScope using (Closed)
open import proof.Compiler.SimplifyScope using (closed-ws)
open import Framework.Syntax.Rename Op sig using (rename; rename-args; shift)
open import Framework.Syntax.Scope Op sig using (WS; WS-args)
open import Semantics.Observation
open import proof.Semantics.CEK.Smallstep
open import proof.Semantics.CEK.Simulation
open import proof.Framework.ListUtil
import Semantics.CEK.ISWIM as S

open import Data.Bool using (Bool; true; false; _∧_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; length; map; replicate; reverse; reverseAcc)
open import Data.List.Properties using (reverse-involutive)
open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_; reverse⁺)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe.Relation.Binary.Pointwise as M
open import Data.Nat using (ℕ; zero; suc; _<_; s≤s; z≤n; _≤ᵇ_)
open import Data.Nat.Properties using (n<1+n)
open import Data.Product using (_×_; Σ-syntax; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)

{- The relation ------------------------------------------------------------------}

infix 4 _≈_ _≈k_ _~_

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
record Ok (E : Facts) (ρ' ρ : S.Env) : Set
{- what simp knows a term is describes v: a value, or a function λ N closed
   in a source environment ρ of which its Facts are true (KDen) -}
KDen : Known → S.Env → S.Val → Set
Kn : Info → S.Env → S.Val → Set
Kn I ρ' v = ∀ {K} → known I ≡ just K → KDen K ρ' v

record Ok E ρ' ρ where
  inductive
  constructor mk-ok
  field
    val : ∀ x {v} → ρ ‼ x ≡ just v → Strong (term (E x)) ρ' v
    knw : ∀ x {v} → ρ ‼ x ≡ just v → Kn (E x) ρ' v
    sml : ∀ x → small (term (E x)) ≡ true

{- the target's value on the left -}
data _≈_ where
  clo≈ : ∀ {fl E N ρ' ρ} → Ok E ρ' ρ → WS (suc (length ρ)) N → S.clo (term (simp fl (under E) N)) ρ' ≈ S.clo N ρ
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

KDen (P.val K) ρ' v = Den K ρ' v
KDen (P.fun N E) ρ' v = Σ[ ρ ∈ S.Env ] v ≡ S.clo N ρ × Ok E ρ' ρ × WS (suc (length ρ)) N

Strongs Dens : ∀ {n} → Args (replicate n ■) → S.Env → List S.Val → Set
Strongs = Descs true
Dens = Descs false

open Ok

{- the subterms of a tuple, simplified -}
simps : ℕ → Facts → List AST → List AST
simps fl E = map (λ M → term (simp fl E M))

{- the source frames that bind the variable of a body N in ρ: the call of
   a closure (β, an inlined call), and a let -}
data Binds (N : AST) (ρ : S.Env) : (S.Cont → S.Cont) → Set where
  by-app : Binds N ρ (S.appR (S.clo N ρ))
  by-let : Binds N ρ (S.letK N ρ)

bind-step : ∀ {N ρ B v κ} → Binds N ρ B → S.step (S.ret v (B κ)) ≡ next (S.eval N (v ∷ ρ) κ)
bind-step by-app = refl
bind-step by-let = refl

data _≈k_ : S.Cont → S.Cont → Set where
  halt : S.halt ≈k S.halt
  appL : ∀ {fl E M ρ' ρ κ' κ} → Ok E ρ' ρ → WS (length ρ) M → κ' ≈k κ
    → S.appL (term (simp fl E M)) ρ' κ' ≈k S.appL M ρ κ
  appR : ∀ {v' v κ' κ} → v' ≈ v → κ' ≈k κ → S.appR v' κ' ≈k S.appR v κ
  tupK : ∀ {fl E vs' vs Ms ρ' ρ κ' κ} → Pointwise _≈_ vs' vs → Ok E ρ' ρ → All (WS (length ρ)) Ms → κ' ≈k κ
    → S.tupK vs' (simps fl E Ms) ρ' κ' ≈k S.tupK vs Ms ρ κ
  getK : ∀ {n} {i : Fin n} {κ' κ} → κ' ≈k κ → S.getK i κ' ≈k S.getK i κ
  inlK : ∀ {κ' κ} → κ' ≈k κ → S.inlK κ' ≈k S.inlK κ
  inrK : ∀ {κ' κ} → κ' ≈k κ → S.inrK κ' ≈k S.inrK κ
  caseK : ∀ {fl E M N ρ' ρ κ' κ} → Ok E ρ' ρ → WS (suc (length ρ)) M → WS (suc (length ρ)) N → κ' ≈k κ
    → S.caseK (term (simp fl (under E) M)) (term (simp fl (under E) N)) ρ' κ' ≈k S.caseK M N ρ κ
  primL : ∀ {p fl E M ρ' ρ κ' κ} → Ok E ρ' ρ → WS (length ρ) M → κ' ≈k κ
    → S.primL p (term (simp fl E M)) ρ' κ' ≈k S.primL p M ρ κ
  primR : ∀ {p v' v κ' κ} → v' ≈ v → κ' ≈k κ → S.primR p v' κ' ≈k S.primR p v κ
  {- a let that simplify kept, of a source β, inlined call or let -}
  letK : ∀ {fl E N ρ' ρ B κ' κ} → Binds N ρ B → Ok E ρ' ρ → WS (suc (length ρ)) N → κ' ≈k κ
    → S.letK (term (simp fl (under E) N)) ρ' κ' ≈k B κ

data _~_ : S.State → S.State → Set where
  eval~ : ∀ {fl E M ρ' ρ κ' κ} → Ok E ρ' ρ → WS (length ρ) M → κ' ≈k κ
    → S.eval (term (simp fl E M)) ρ' κ' ~ S.eval M ρ κ
  ret~ : ∀ {v' v κ' κ} → v' ≈ v → κ' ≈k κ → S.ret v' κ' ~ S.ret v κ

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

{- under one more variable, in the target only -}
kden-shift : ∀ K {ρ' v w} → KDen K ρ' v → KDen (shift-known K) (w ∷ ρ') v
kn-shift : ∀ I {ρ' v w} → Kn I ρ' v → Kn (shift-info I) (w ∷ ρ') v
ok-weak : ∀ {E ρ' ρ w} → Ok E ρ' ρ → Ok (λ x → shift-info (E x)) (w ∷ ρ') ρ
kden-shift (P.val K) d = den-shift K d
kden-shift (P.fun N E) (ρ , refl , ok , w) = ρ , refl , ok-weak ok , w
kn-shift (T ∣ just K) h refl = kden-shift K (h refl)
ok-weak {E} ok = mk-ok (λ x e → strong-shift (term (E x)) (sml ok x) (val ok x e)) (λ x e → kn-shift (E x) (knw ok x e))
                       (λ x → small-shift (term (E x)) (sml ok x))

{- variable 0 known as I is, in the source only -}
ok-cons : ∀ {E ρ' ρ I v} → Ok E ρ' ρ → Strong (term I) ρ' v → Kn I ρ' v → small (term I) ≡ true → Ok (I • E) ρ' (v ∷ ρ)
ok-cons ok d k s = mk-ok (λ { zero refl → d ; (suc x) → val ok x }) (λ { zero refl → k ; (suc x) → knw ok x })
                         (λ { zero → s ; (suc x) → sml ok x })

ok-self : ∀ {E ρ' ρ T v} → Ok E ρ' ρ → small T ≡ true → Strong T ρ' v → Ok (self T • E) ρ' (v ∷ ρ)
ok-self {T = T} ok s d = ok-cons ok d (λ { refl → strong-den T d }) s

{- under a binder that stays -}
ok-under : ∀ {E ρ' ρ v' v} → Ok E ρ' ρ → v' ≈ v → Ok (under E) (v' ∷ ρ') (v ∷ ρ)
ok-under ok r = ok-cons (ok-weak ok) (_ , refl , r) (λ { refl → _ , refl , r }) refl

{- a value known as I is, that stays bound to variable 0 -}
ok-let : ∀ {E ρ' ρ I w v} → Ok E ρ' ρ → w ≈ v → Kn I ρ' v → Ok (known-as I E) (w ∷ ρ') (v ∷ ρ)
ok-let {I = I} ok r k = ok-cons (ok-weak ok) (_ , refl , r) (kn-shift I k) refl

ws-list : ∀ {k n} (as : Args (replicate n ■)) → WS-args k as → All (WS k) (args→list as)
ws-list {n = zero} Nil _ = []
ws-list {n = suc n} (M ,, as) (w , ws) = w ∷ ws-list as ws

{- The simulation, for any target program P' and source program P -------------}

module _ (P' P : AST) where

  L₁ = S.sem P'
  L₂ = S.sem P

  {- the target is i steps from a state related to the source's -}
  match = Lag L₁ _~_

  {- a run of the source from an evaluation to a return has a step -}
  run-plus : ∀ {M ρ κ v} → Star L₂ (S.eval M ρ κ) (S.ret v κ) → Plus L₂ (S.eval M ρ κ) (S.ret v κ)
  run-plus (st ◅ σ) = plus st σ

  Run : AST → S.Env → S.Val → Set
  Run M ρ v = ∀ κ → Star L₂ (S.eval M ρ κ) (S.ret v κ)

  Run₁ : AST → S.Env → S.Val → Set
  Run₁ M ρ v = ∀ κ → Star L₁ (S.eval M ρ κ) (S.ret v κ)

  {- The target evaluates value terms -}

  trun : ∀ T {ρ' v} → Strong T ρ' v → Σ[ w ∈ S.Val ] Run₁ T ρ' w × w ≈ v
  truns : ∀ {n} (as : Args (replicate n ■)) {ρ' vs} → Strongs as ρ' vs
    → ∀ {acc' acc} → Pointwise _≈_ acc' acc
    → Σ[ ws ∈ List S.Val ] (∀ κ → Star L₁ (S.tuple-next acc' (args→list as) ρ' κ) (S.ret (S.tup (reverse ws)) κ))
        × Pointwise _≈_ ws (reverseAcc acc vs)
  trun (` y) (w , e , r) = w , (λ κ → cong (λ m → S.ret? m κ) e ◅ ε) , r
  trun (lam ⦅ ⟩ N ,, Nil ⦆) r = _ , (λ κ → refl ◅ ε) , r
  trun (lit B k ⦅ Nil ⦆) refl = _ , (λ κ → refl ◅ ε) , const≈
  trun (tuple n ⦅ as ⦆) {ρ'} (vs , refl , ds) =
    S.tup (reverse (proj₁ go)) , (λ κ → refl ◅ proj₁ (proj₂ go) κ)
    , tup≈ (subst (Pointwise _≈_ (reverse (proj₁ go))) (reverse-involutive vs) (reverse⁺ (proj₂ (proj₂ go))))
    where go = truns as ds []
  trun (inl-op ⦅ M ,, Nil ⦆) (v , refl , d) with trun M d
  ... | w , σ , r = S.inl w , (λ κ → refl ◅ (σ (S.inlK κ) ◅◅ (refl ◅ ε))) , inl≈ r
  trun (inr-op ⦅ M ,, Nil ⦆) (v , refl , d) with trun M d
  ... | w , σ , r = S.inr w , (λ κ → refl ◅ (σ (S.inrK κ) ◅◅ (refl ◅ ε))) , inr≈ r
  truns {zero} Nil {vs = []} refl {acc'} rs = acc' , (λ κ → ε) , rs
  truns {suc n} (M ,, as) (v , vs , refl , d , ds) {acc'} {acc} rs with trun M d
  ... | w , σ , r with truns as ds (r ∷ rs)
  ...   | ws , τ , rs' = ws , (λ κ → σ (S.tupK acc' (args→list as) _ κ) ◅◅ (refl ◅ τ κ)) , rs'

  {- Answers whose target takes a step -}
  record Step-ans (s' s : S.State) : Set where
    constructor ans
    field
      {t} : S.State
      t-step : S.step s' ≡ next t
      {j} : ℕ
      {s₁} : S.State
      s-plus : Plus L₂ s s₁
      t-match : match j t s₁

  prefix : ∀ {s' s s₀} → Star L₂ s s₀ → Step-ans s' s₀ → Step-ans s' s
  prefix σ (ans e π m) = ans e (star-plus σ π) m

  {- a value term against a run of the source to a value it describes -}
  value-ans : ∀ T {M ρ' ρ v κ' κ} → Strong T ρ' v → Run M ρ v → κ' ≈k κ → Step-ans (S.eval T ρ' κ') (S.eval M ρ κ)
  value-ans T d σ k with trun T d
  ... | w , τ , r with τ _
  ...   | st ◅ τ' with lag-star τ' (ret~ r k)
  ...     | j , m = ans st (run-plus (σ _)) m

  {- the source runs to one value -}
  run-unique : ∀ {s v w} → Star L₂ s (S.ret v S.halt) → Star L₂ s (S.ret w S.halt) → v ≡ w
  run-unique ε ε = refl
  run-unique ε (() ◅ _)
  run-unique (() ◅ _) ε
  run-unique {s} (st ◅ σ) (st' ◅ τ) with step-det {L = L₂} {s} st st'
  ... | refl = run-unique σ τ

  {- The source runs ahead: run-term and run-known -}

  {- what simp knows of an operand I is true of the source's M, if I is a
     value; and of an operator J of the source's L -}
  Opd : Info → AST → S.Env → S.Env → Set
  Opd I M ρ' ρ = value (term I) ≡ true → Σ[ v ∈ S.Val ] Run M ρ v × Strong (term I) ρ' v × Kn I ρ' v
  Fn : Info → AST → S.Env → S.Env → Set
  Fn J L ρ' ρ = ∀ {K} → known J ≡ just K → Σ[ v ∈ S.Val ] Run L ρ v × KDen K ρ' v

  run-term : ∀ fl M {E ρ' ρ} → Ok E ρ' ρ → WS (length ρ) M → value (term (simp fl E M)) ≡ true
    → Σ[ v ∈ S.Val ] Run M ρ v × Strong (term (simp fl E M)) ρ' v
  run-known : ∀ fl M {E ρ' ρ K} → Ok E ρ' ρ → WS (length ρ) M → known (simp fl E M) ≡ just K
    → Σ[ v ∈ S.Val ] Run M ρ v × KDen K ρ' v
  run-terms : ∀ fl {n} (as : Args (replicate n ■)) {E ρ' ρ} → Ok E ρ' ρ → WS-args (length ρ) as
    → values (simp-args fl E as) ≡ true
    → ∀ {acc} → Σ[ vs ∈ List S.Val ] (∀ κ → Star L₂ (S.tuple-next acc (args→list as) ρ κ) (S.ret (S.tup (reverse (reverseAcc acc vs))) κ))
        × Strongs (simp-args fl E as) ρ' vs
  {- a component of a known tuple -}
  run-get : ∀ fl {n} (i : Fin n) L {E ρ' ρ K} → Ok E ρ' ρ → WS (length ρ) L → component i (known (simp fl E L)) ≡ just K
    → Σ[ v ∈ S.Val ] Run (get i ⦅ L ,, Nil ⦆) ρ v × Den K ρ' v
  {- the branch of a case on a known injection -}
  run-inl : ∀ fl L {E ρ' ρ K} → Ok E ρ' ρ → WS (length ρ) L → branch (known (simp fl E L)) ≡ just (true , K)
    → Σ[ v ∈ S.Val ] (∀ M N κ → Star L₂ (S.eval L ρ (S.caseK M N ρ κ)) (S.eval M (v ∷ ρ) κ)) × Strong K ρ' v
  run-inr : ∀ fl L {E ρ' ρ K} → Ok E ρ' ρ → WS (length ρ) L → branch (known (simp fl E L)) ≡ just (false , K)
    → Σ[ v ∈ S.Val ] (∀ M N κ → Star L₂ (S.eval L ρ (S.caseK M N ρ κ)) (S.eval N (v ∷ ρ) κ)) × Strong K ρ' v
  {- a primitive on known integers -}
  run-int : ∀ fl L {E ρ' ρ n} → Ok E ρ' ρ → WS (length ρ) L → int-of (known (simp fl E L)) ≡ just n → Run L ρ (S.const Int n)

  {- an operand that becomes a value: the source runs it to a value that
     it describes, and that what simp knows of it describes -}
  arg-run : ∀ fl M {E ρ' ρ} → Ok E ρ' ρ → WS (length ρ) M → Opd (simp fl E M) M ρ' ρ
  {- the body N of a function λ N closed in ρf, bound to the operand I,
     when the source runs some term S to the operand M, with a frame B
     that binds it (P) -}
  let-term : ∀ fl N I M {E' ρ' ρf ρ S B} → Ok E' ρ' ρf → WS (suc (length ρf)) N → Opd I M ρ' ρ
    → Binds N ρf B → (∀ κ → Star L₂ (S.eval S ρ κ) (S.eval M ρ (B κ)))
    → value (term (simp-let fl E' N I)) ≡ true
    → Σ[ w ∈ S.Val ] Run S ρ w × Strong (term (simp-let fl E' N I)) ρ' w
  let-known : ∀ fl N I M {E' ρ' ρf ρ S B K} → Ok E' ρ' ρf → WS (suc (length ρf)) N → Opd I M ρ' ρ
    → Binds N ρf B → (∀ κ → Star L₂ (S.eval S ρ κ) (S.eval M ρ (B κ)))
    → known (simp-let fl E' N I) ≡ just K → Σ[ w ∈ S.Val ] Run S ρ w × KDen K ρ' w
  {- a call of the operator L, of which simp knows J -}
  call-term : ∀ fl J I L M {ρ' ρ} → Fn J L ρ' ρ → Opd I M ρ' ρ → value (term (simp-call fl J I)) ≡ true
    → Σ[ w ∈ S.Val ] Run (app ⦅ L ,, M ,, Nil ⦆) ρ w × Strong (term (simp-call fl J I)) ρ' w
  call-known : ∀ fl J I L M {ρ' ρ K} → Fn J L ρ' ρ → Opd I M ρ' ρ → known (simp-call fl J I) ≡ just K
    → Σ[ w ∈ S.Val ] Run (app ⦅ L ,, M ,, Nil ⦆) ρ w × KDen K ρ' w

  run-term fl (` x) {ρ = ρ} ok w e with lookup-ws ρ w
  ... | v , l = v , (λ κ → cong (λ m → S.ret? m κ) l ◅ ε) , val ok x l
  run-term fl (lam ⦅ ⟩ N ,, Nil ⦆) ok (w , _) e = _ , (λ κ → refl ◅ ε) , clo≈ ok w
  run-term fl (app ⦅ L ,, M ,, Nil ⦆) {E} ok (wL , wM , _) e with lam? L
  ... | is-lam N = let-term fl N _ M ok (proj₁ wL) (arg-run fl M ok wM) by-app (λ κ → refl ◅ refl ◅ refl ◅ ε) e
  ... | other = call-term fl _ _ L M (run-known fl L ok wL) (arg-run fl M ok wM) e
  run-term fl (lit B k ⦅ Nil ⦆) ok w e = _ , (λ κ → refl ◅ ε) , refl
  run-term fl (tuple n ⦅ as ⦆) {E} ok w e with run-terms fl as ok w e {[]}
  ... | vs , σ , ds =
    S.tup vs , (λ κ → refl ◅ subst (λ X → Star L₂ _ (S.ret (S.tup X) κ)) (reverse-involutive vs) (σ κ)) , vs , refl , ds
  run-term fl (get i ⦅ L ,, Nil ⦆) {E} ok (w , _) e with component i (known (simp fl E L)) in c
  ... | just K with small K in s
  ...   | true with run-get fl i L ok w c
  ...     | v , σ , d = v , σ , small-strong K s d
  run-term fl (inl-op ⦅ M ,, Nil ⦆) ok (w , _) e with run-term fl M ok w e
  ... | v , σ , d = S.inl v , (λ κ → refl ◅ (σ (S.inlK κ) ◅◅ (refl ◅ ε))) , v , refl , d
  run-term fl (inr-op ⦅ M ,, Nil ⦆) ok (w , _) e with run-term fl M ok w e
  ... | v , σ , d = S.inr v , (λ κ → refl ◅ (σ (S.inrK κ) ◅◅ (refl ◅ ε))) , v , refl , d
  run-term fl (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) {E} ok (wL , (wM , wN , _)) e with branch (known (simp fl E L)) in b
  ... | just (true , K) with run-inl fl L ok wL b
  ...   | v , σ , d with run-term fl M (ok-self ok (proj₂ (branch-inl (known (simp fl E L)) b)) d) wM e
  ...     | w , τ , d' = w , (λ κ → refl ◅ (σ _ _ κ ◅◅ τ κ)) , d'
  run-term fl (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) {E} ok (wL , (wM , wN , _)) e | just (false , K) with run-inr fl L ok wL b
  ...   | v , σ , d with run-term fl N (ok-self ok (proj₂ (branch-inr (known (simp fl E L)) b)) d) wN e
  ...     | w , τ , d' = w , (λ κ → refl ◅ (σ _ _ κ ◅◅ τ κ)) , d'
  run-term fl (prim p ⦅ L ,, M ,, Nil ⦆) {E} {ρ = ρ} ok (wL , wM , _) e with int-of (known (simp fl E L)) in e₁
  ... | just n with int-of (known (simp fl E M)) in e₂
  ...   | just m =
    S.out (δ p n m)
    , (λ κ → refl ◅ (run-int fl L ok wL e₁ (S.primL p M ρ κ) ◅◅ (refl ◅ (run-int fl M ok wM e₂ (S.primR p (S.const Int n) κ) ◅◅ (refl ◅ ε)))))
    , prim-strong (δ p n m)

  run-term fl (let-op ⦅ M ,, ⟩ N ,, Nil ⦆) ok (wM , wN , _) e =
    let-term fl N _ M ok wN (arg-run fl M ok wM) by-let (λ κ → refl ◅ ε) e

  run-terms fl {zero} Nil ok _ _ {acc} = [] , (λ κ → ε) , refl
  run-terms fl {suc n} (M ,, as) {E} {ρ = ρ} ok (w , ws) e {acc} with P.∧-true {value (term (simp fl E M))} e
  ... | e₁ , e₂ with run-term fl M ok w e₁
  ...   | v , σ , d with run-terms fl as ok ws e₂ {v ∷ acc}
  ...     | vs , τ , ds = v ∷ vs , (λ κ → σ (S.tupK acc (args→list as) ρ κ) ◅◅ (refl ◅ τ κ)) , v , vs , refl , d , ds

  run-get fl i L {E} {ρ = ρ} ok w c with comp-inv i (known (simp fl E L)) c
  ... | m , Ks , k , p with run-known fl L ok w k
  ...   | .(S.tup vs) , σ , (vs , refl , ds) with dens-proj i Ks ds p
  ...     | v , q , d = v , (λ κ → refl ◅ (σ (S.getK i κ) ◅◅ (cong (λ x → S.ret? x κ) q ◅ ε))) , d

  run-inl fl L {E} {ρ = ρ} ok w b with branch-inl (known (simp fl E L)) b
  ... | k , s with run-known fl L ok w k
  ...   | .(S.inl v₀) , σ , (v₀ , refl , d) = v₀ , (λ M N κ → σ (S.caseK M N ρ κ) ◅◅ (refl ◅ ε)) , small-strong _ s d

  run-inr fl L {E} {ρ = ρ} ok w b with branch-inr (known (simp fl E L)) b
  ... | k , s with run-known fl L ok w k
  ...   | .(S.inr v₀) , σ , (v₀ , refl , d) = v₀ , (λ M N κ → σ (S.caseK M N ρ κ) ◅◅ (refl ◅ ε)) , small-strong _ s d

  run-int fl L {E} ok w e with run-known fl L ok w (int-inv (known (simp fl E L)) e)
  ... | .(S.const Int _) , σ , refl = σ

  run-known fl (` x) {ρ = ρ} ok w k with lookup-ws ρ w
  ... | v , l = v , (λ κ → cong (λ m → S.ret? m κ) l ◅ ε) , knw ok x l k
  run-known fl (lam ⦅ ⟩ N ,, Nil ⦆) {ρ = ρ} ok (w , _) refl = _ , (λ κ → refl ◅ ε) , ρ , refl , ok , w
  run-known fl (app ⦅ L ,, M ,, Nil ⦆) {E} ok (wL , wM , _) k with lam? L
  ... | is-lam N = let-known fl N _ M ok (proj₁ wL) (arg-run fl M ok wM) by-app (λ κ → refl ◅ refl ◅ refl ◅ ε) k
  ... | other = call-known fl _ _ L M (run-known fl L ok wL) (arg-run fl M ok wM) k
  run-known fl (lit B k ⦅ Nil ⦆) ok w refl = _ , (λ κ → refl ◅ ε) , refl
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
  ...     | w , τ , d' = w , (λ κ → refl ◅ (σ _ _ κ ◅◅ τ κ)) , d'
  run-known fl (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) {E} ok (wL , (wM , wN , _)) k | just (false , K) with run-inr fl L ok wL b
  ...   | v , σ , d with run-known fl N (ok-self ok (proj₂ (branch-inr (known (simp fl E L)) b)) d) wN k
  ...     | w , τ , d' = w , (λ κ → refl ◅ (σ _ _ κ ◅◅ τ κ)) , d'
  run-known fl (prim p ⦅ L ,, M ,, Nil ⦆) {E} {ρ = ρ} ok (wL , wM , _) k with int-of (known (simp fl E L)) in e₁
  ... | just n with int-of (known (simp fl E M)) in e₂
  run-known fl (prim p ⦅ L ,, M ,, Nil ⦆) {E} {ρ = ρ} ok (wL , wM , _) refl | just n | just m =
    S.out (δ p n m)
    , (λ κ → refl ◅ (run-int fl L ok wL e₁ (S.primL p M ρ κ) ◅◅ (refl ◅ (run-int fl M ok wM e₂ (S.primR p (S.const Int n) κ) ◅◅ (refl ◅ ε)))))
    , strong-den (prim-term (δ p n m)) (prim-strong (δ p n m))

  run-known fl (let-op ⦅ M ,, ⟩ N ,, Nil ⦆) ok (wM , wN , _) k =
    let-known fl N _ M ok wN (arg-run fl M ok wM) by-let (λ κ → refl ◅ ε) k

  arg-run fl M {E} {ρ'} ok w e with run-term fl M ok w e
  ... | v , σ , d = v , σ , d , λ {K} k → same {K} (run-known fl M ok w k)
    where same : ∀ {K} → Σ[ v' ∈ S.Val ] Run M _ v' × KDen K ρ' v' → KDen K ρ' v
          same {K} (v' , σ' , d') = subst (KDen K ρ') (run-unique (σ' S.halt) (σ S.halt)) d'

  let-term fl N I M okf wN A bd P e with small (term I) in s
  ... | true with A (P.small-value (term I) s)
  ...   | v , σ , d , k with run-term fl N (ok-cons okf d k s) wN e
  ...     | w , τ , d' = w , (λ κ → P κ ◅◅ (σ _ ◅◅ (bind-step bd ◅ τ κ))) , d'
  let-term fl N I M okf wN A bd P e | false with value (term I)
  let-term fl N I M okf wN A bd P () | false | true
  let-term fl N I M okf wN A bd P () | false | false

  let-known fl N I M okf wN A bd P e with small (term I) in s
  ... | true with A (P.small-value (term I) s)
  ...   | v , σ , d , k with run-known fl N (ok-cons okf d k s) wN e
  ...     | w , τ , d' = w , (λ κ → P κ ◅◅ (σ _ ◅◅ (bind-step bd ◅ τ κ))) , d'
  let-known fl N I M okf wN A bd P e | false with value (term I)
  let-known fl N I M okf wN A bd P () | false | true
  let-known fl N I M okf wN A bd P () | false | false

  call-term (suc fl) (T ∣ just (P.fun N E')) I L M jk A e with size (term (simp-let fl E' N I)) ≤ᵇ inline-size | jk refl
  ... | true | v , σ , ρf , refl , okf , wN = let-term fl N I M okf wN A by-app (λ κ → refl ◅ (σ _ ◅◅ (refl ◅ ε))) e
  call-term (suc fl) (T ∣ just (P.fun N E')) I L M jk A () | false | _
  call-term zero J I L M jk A ()
  call-term (suc fl) (T ∣ nothing) I L M jk A ()
  call-term (suc fl) (T ∣ just (P.val K)) I L M jk A ()

  call-known (suc fl) (T ∣ just (P.fun N E')) I L M jk A e with size (term (simp-let fl E' N I)) ≤ᵇ inline-size | jk refl
  ... | true | v , σ , ρf , refl , okf , wN = let-known fl N I M okf wN A by-app (λ κ → refl ◅ (σ _ ◅◅ (refl ◅ ε))) e
  call-known (suc fl) (T ∣ just (P.fun N E')) I L M jk A () | false | _
  call-known zero J I L M jk A ()
  call-known (suc fl) (T ∣ nothing) I L M jk A ()
  call-known (suc fl) (T ∣ just (P.val K)) I L M jk A ()

  {- The source's answer to a target evaluation ----------------------------------}

  tuple-next~ : ∀ {fl E vs' vs Ms ρ' ρ κ' κ} → Pointwise _≈_ vs' vs → Ok E ρ' ρ → All (WS (length ρ)) Ms → κ' ≈k κ
    → S.tuple-next vs' (simps fl E Ms) ρ' κ' ~ S.tuple-next vs Ms ρ κ
  tuple-next~ rs ok [] k = ret~ (tup≈ (reverse⁺ rs)) k
  tuple-next~ rs ok (w ∷ ws) k = eval~ ok w (tupK rs ok ws k)

  {- the target and the source take one step each -}
  lock : ∀ {s' s t t'} → S.step s' ≡ next t' → S.step s ≡ next t → t' ~ t → Step-ans s' s
  lock e e' r = ans e (step⁺ e') (lag₀ r)

  absurd : ∀ {A : Set} → true ≡ false → A
  absurd ()

  eval-sim : ∀ fl M {E ρ' ρ κ' κ} → Ok E ρ' ρ → WS (length ρ) M → κ' ≈k κ
    → Step-ans (S.eval (term (simp fl E M)) ρ' κ') (S.eval M ρ κ)
  structural : ∀ fl M {E ρ' ρ κ' κ} → Ok E ρ' ρ → WS (length ρ) M → κ' ≈k κ → value (term (simp fl E M)) ≡ false
    → Step-ans (S.eval (term (simp fl E M)) ρ' κ') (S.eval M ρ κ)

  {- the body N of a function λ N closed in ρf, bound to the operand M,
     when the source runs to the evaluation of M (P) -}
  let-sim : ∀ fl N fl₀ M {E' E ρ' ρf ρ s B κ' κ} → Ok E' ρ' ρf → WS (suc (length ρf)) N → Ok E ρ' ρ → WS (length ρ) M
    → Binds N ρf B → κ' ≈k κ → Plus L₂ s (S.eval M ρ (B κ))
    → Step-ans (S.eval (term (simp-let fl E' N (simp fl₀ E M))) ρ' κ') s
  {- a call of the operator L, of which the source knows J -}
  call-sim : ∀ fl J L M {E ρ' ρ κ' κ} → (∀ {κ' κ} → κ' ≈k κ → S.eval (term J) ρ' κ' ~ S.eval L ρ κ)
    → (∀ {K} → known J ≡ just K → Σ[ v ∈ S.Val ] Run L ρ v × KDen K ρ' v) → Ok E ρ' ρ → WS (length ρ) M → κ' ≈k κ
    → Step-ans (S.eval (term (simp-call fl J (simp fl E M))) ρ' κ') (S.eval (app ⦅ L ,, M ,, Nil ⦆) ρ κ)

  eval-sim fl M {E} ok w k with value (term (simp fl E M)) in isv
  ... | true with run-term fl M ok w isv
  ...   | v , σ , d = value-ans (term (simp fl E M)) d σ k
  eval-sim fl M ok w k | false = structural fl M ok w k isv

  structural fl (lam ⦅ ⟩ N ,, Nil ⦆) ok w k ()
  structural fl (lit B k₀ ⦅ Nil ⦆) ok w k ()
  structural fl (` x) {E} ok w k isv = absurd (trans (sym (P.small-value (term (E x)) (sml ok x))) isv)
  structural fl (app ⦅ L ,, M ,, Nil ⦆) {E} ok (wL , wM , _) k isv with lam? L
  ... | is-lam N = let-sim fl N fl M ok (proj₁ wL) ok wM by-app k (plus refl (refl ◅ refl ◅ ε))
  ... | other = call-sim fl (simp fl E L) L M (eval~ ok wL) (run-known fl L ok wL) ok wM k
  structural fl (tuple n ⦅ as ⦆) {E} {ρ' = ρ'} {ρ} {κ'} {κ} ok w k isv =
    lock refl refl (subst (λ Ms → S.tuple-next [] Ms ρ' κ' ~ S.tuple-next [] (args→list as) ρ κ)
                          (sym (args→list-hom _ (simp-args fl E) (λ _ _ → refl) as)) (tuple-next~ [] ok (ws-list as w) k))
  structural fl (get i ⦅ L ,, Nil ⦆) {E} ok (w , _) k isv with component i (known (simp fl E L)) in c
  ... | nothing = lock refl refl (eval~ ok w (getK k))
  ... | just K with small K in s
  ...   | true = absurd (trans (sym (P.small-value K s)) isv)
  ...   | false = lock refl refl (eval~ ok w (getK k))
  structural fl (inl-op ⦅ M ,, Nil ⦆) ok (w , _) k isv = lock refl refl (eval~ ok w (inlK k))
  structural fl (inr-op ⦅ M ,, Nil ⦆) ok (w , _) k isv = lock refl refl (eval~ ok w (inrK k))
  structural fl (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) {E} ok (wL , (wM , wN , _)) k isv with branch (known (simp fl E L)) in b
  ... | nothing = lock refl refl (eval~ ok wL (caseK ok wM wN k))
  ... | just (true , K) with run-inl fl L ok wL b
  ...   | v , σ , d = prefix (refl ◅ σ _ _ _) (eval-sim fl M (ok-self ok (proj₂ (branch-inl (known (simp fl E L)) b)) d) wM k)
  structural fl (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) {E} ok (wL , (wM , wN , _)) k isv | just (false , K) with run-inr fl L ok wL b
  ...   | v , σ , d = prefix (refl ◅ σ _ _ _) (eval-sim fl N (ok-self ok (proj₂ (branch-inr (known (simp fl E L)) b)) d) wN k)
  structural fl (prim p ⦅ L ,, M ,, Nil ⦆) {E} ok (wL , wM , _) k isv with int-of (known (simp fl E L)) in e₁
  ... | nothing = lock refl refl (eval~ ok wL (primL ok wM k))
  ... | just n with int-of (known (simp fl E M)) in e₂
  ...   | nothing = lock refl refl (eval~ ok wL (primL ok wM k))
  ...   | just m = absurd (trans (sym (P.sv-value (P.prim-term-sv (δ p n m)))) isv)
  structural fl (let-op ⦅ M ,, ⟩ N ,, Nil ⦆) ok (wM , wN , _) k isv = let-sim fl N fl M ok wN ok wM by-let k (plus refl ε)

  let-sim fl N fl₀ M {E'} {E} {ρ'} {κ' = κ'} okf wN ok wM bd k P with small (term (simp fl₀ E M)) in s | value (term (simp fl₀ E M)) in isv
  ... | true | _ with arg-run fl₀ M ok wM (P.small-value (term (simp fl₀ E M)) s)
  ...   | v , σ , d , kn = prefix (plus→star P ◅◅ (σ _ ◅◅ (bind-step bd ◅ ε))) (eval-sim fl N (ok-cons okf d kn s) wN k)
  let-sim fl N fl₀ M {E'} {E} {ρ'} {κ' = κ'} okf wN ok wM bd k P | false | true with arg-run fl₀ M ok wM isv
  ...   | v , σ , d , kn with trun (term (simp fl₀ E M)) d
  ...     | w' , τ , r with lag-star (τ (S.letK N' ρ' κ') ◅◅ (refl ◅ ε)) (eval~ (ok-let {I = simp fl₀ E M} okf r kn) wN k)
    where N' = term (simp fl (known-as (simp fl₀ E M) E') N)
  ...       | j , m = ans refl (plus-star P (σ _ ◅◅ (bind-step bd ◅ ε))) m
  let-sim fl N fl₀ M okf wN ok wM bd k P | false | false = ans refl P (lag₀ (eval~ ok wM (letK bd okf wN k)))

  call-sim (suc fl) (T ∣ just (P.fun N E')) L M {E} jt jk ok wM k
    with size (term (simp-let fl E' N (simp (suc fl) E M))) ≤ᵇ inline-size | jk refl
  ... | true | v , σ , ρf , refl , okf , wN = let-sim fl N (suc fl) M okf wN ok wM by-app k (plus refl (σ _ ◅◅ (refl ◅ ε)))
  ... | false | _ = lock refl refl (jt (appL ok wM k))
  call-sim zero J L M jt jk ok wM k = lock refl refl (jt (appL ok wM k))
  call-sim (suc fl) (T ∣ nothing) L M jt jk ok wM k = lock refl refl (jt (appL ok wM k))
  call-sim (suc fl) (T ∣ just (P.val K)) L M jt jk ok wM k = lock refl refl (jt (appL ok wM k))

  {- The simulation ------------------------------------------------------------}

  next~ : ∀ {i s t' t} → S.step s ≡ next t → t' ~ t → Answers≺ L₂ match i (next t') s
  next~ e r = steps₁≺ e (lag₀ r)

  base-sim : ∀ {i s' s} → s' ~ s → Answers≺ L₂ match i (S.step s') s
  base-sim (eval~ {fl = fl} {M = M} ok w k) with eval-sim fl M ok w k
  ... | ans e π m rewrite e = steps π m
  base-sim (ret~ r halt) = stops (cong stop (sym (obs≈ r)))
  base-sim (ret~ r@(clo≈ _ _) (appL ok w k)) = next~ refl (eval~ ok w (appR r k))
  base-sim (ret~ const≈ (appL ok w k)) = stops refl
  base-sim (ret~ (tup≈ _) (appL ok w k)) = stops refl
  base-sim (ret~ (inl≈ _) (appL ok w k)) = stops refl
  base-sim (ret~ (inr≈ _) (appL ok w k)) = stops refl
  base-sim (ret~ r (appR (clo≈ ok w) k)) = next~ refl (eval~ (ok-under ok r) w k)
  base-sim (ret~ r (appR const≈ k)) = stops refl
  base-sim (ret~ r (appR (tup≈ _) k)) = stops refl
  base-sim (ret~ r (appR (inl≈ _) k)) = stops refl
  base-sim (ret~ r (appR (inr≈ _) k)) = stops refl
  base-sim (ret~ r (tupK rs ok ws k)) = next~ refl (tuple-next~ (r ∷ rs) ok ws k)
  base-sim (ret~ (tup≈ rs) (getK {i = i} k)) = answers≺ (next?-answers (proj-pw i rs) (λ r → lag₀ (ret~ r k)) refl)
  base-sim (ret~ (clo≈ _ _) (getK k)) = stops refl
  base-sim (ret~ const≈ (getK k)) = stops refl
  base-sim (ret~ (inl≈ _) (getK k)) = stops refl
  base-sim (ret~ (inr≈ _) (getK k)) = stops refl
  base-sim (ret~ r (inlK k)) = next~ refl (ret~ (inl≈ r) k)
  base-sim (ret~ r (inrK k)) = next~ refl (ret~ (inr≈ r) k)
  base-sim (ret~ (inl≈ r) (caseK ok wM wN k)) = next~ refl (eval~ (ok-under ok r) wM k)
  base-sim (ret~ (inr≈ r) (caseK ok wM wN k)) = next~ refl (eval~ (ok-under ok r) wN k)
  base-sim (ret~ (clo≈ _ _) (caseK _ _ _ k)) = stops refl
  base-sim (ret~ const≈ (caseK _ _ _ k)) = stops refl
  base-sim (ret~ (tup≈ _) (caseK _ _ _ k)) = stops refl
  base-sim (ret~ r (primL ok w k)) = next~ refl (eval~ ok w (primR r k))
  base-sim (ret~ s (primR {p} r k)) = answers≺ (next?-answers (prim≈ p r s) (λ r → lag₀ (ret~ r k)) refl)
  base-sim (ret~ r (letK bd ok w k)) = next~ (bind-step bd) (eval~ (ok-under ok r) w k)


{- The end theorem: for closed programs ------------------------------------------}

ok₀ : Ok (λ x → self (` x)) [] []
ok₀ = mk-ok (λ x ()) (λ x ()) (λ x → refl)

simplify-correct : ∀ M → Closed M → Equivalent (S.sem M) (S.sem (simplify M))
simplify-correct M c = equiv-sym (equivalent
  (lag-fsim (lag-now (eval~ {fl = inline-fuel} ok₀ (closed-ws {M} c) halt)) (base-sim (simplify M) M)))

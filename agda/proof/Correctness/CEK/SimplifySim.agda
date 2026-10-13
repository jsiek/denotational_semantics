{-

  Correctness of the simplify pass (ISWIM → ISWIM) by a forward simulation
  of the target's machine by the source's (see the design note in
  Semantics/CEK/Smallstep.agda); Equivalent is symmetric.

  The target does less work than the source: the reductions simplify did
  ahead of time (β of a small value, a case on a known injection, a
  projection from a known tuple, a primitive on known integers) are
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
  (Strong), and its known value describes it (Den: the same, up to
  functions, which are not inspected). States and continuations are
  related frame by frame, the code by simp.

  The source's run-ahead is by run-term and run-known: if the term that
  simp E M returns is a value, or M has a known value, the source runs M
  to a value it describes. The end theorem is for closed programs: an
  unbound variable makes the source go wrong where the target may have
  dropped it.

-}

module proof.Correctness.CEK.SimplifySim where

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
open import Data.Nat using (ℕ; zero; suc; _<_; s≤s; z≤n)
open import Data.Nat.Properties using (n<1+n)
open import Data.Product using (_×_; Σ-syntax; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)

{- The relation ------------------------------------------------------------------}

infix 4 _≈_ _≈k_ _~_

data _≈_ : S.Val → S.Val → Set
Strong : AST → S.Env → S.Val → Set
Strongs : ∀ {n} → Args (replicate n ■) → S.Env → List S.Val → Set
Den : AST → S.Env → S.Val → Set
Dens : ∀ {n} → Args (replicate n ■) → S.Env → List S.Val → Set

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

{- the value term T denotes, in ρ', a value related to v -}
Strong (` y) ρ' v = Σ[ w ∈ S.Val ] ρ' ‼ y ≡ just w × w ≈ v
Strong (lam ⦅ ⟩ N ,, Nil ⦆) ρ' v = S.clo N ρ' ≈ v
Strong (lit B k ⦅ Nil ⦆) ρ' v = v ≡ S.const B k
Strong (tuple n ⦅ as ⦆) ρ' v = Σ[ vs ∈ List S.Val ] v ≡ S.tup vs × Strongs as ρ' vs
Strong (inl-op ⦅ M ,, Nil ⦆) ρ' v = Σ[ v₀ ∈ S.Val ] v ≡ S.inl v₀ × Strong M ρ' v₀
Strong (inr-op ⦅ M ,, Nil ⦆) ρ' v = Σ[ v₀ ∈ S.Val ] v ≡ S.inr v₀ × Strong M ρ' v₀
Strong _ ρ' v = ⊥
Strongs {zero} Nil ρ' vs = vs ≡ []
Strongs {suc n} (M ,, as) ρ' vs = Σ[ v ∈ S.Val ] Σ[ vs' ∈ List S.Val ] vs ≡ v ∷ vs' × Strong M ρ' v × Strongs as ρ' vs'

{- the same, but a function describes any value -}
Den (` y) ρ' v = Σ[ w ∈ S.Val ] ρ' ‼ y ≡ just w × w ≈ v
Den (lam ⦅ ⟩ N ,, Nil ⦆) ρ' v = ⊤
Den (lit B k ⦅ Nil ⦆) ρ' v = v ≡ S.const B k
Den (tuple n ⦅ as ⦆) ρ' v = Σ[ vs ∈ List S.Val ] v ≡ S.tup vs × Dens as ρ' vs
Den (inl-op ⦅ M ,, Nil ⦆) ρ' v = Σ[ v₀ ∈ S.Val ] v ≡ S.inl v₀ × Den M ρ' v₀
Den (inr-op ⦅ M ,, Nil ⦆) ρ' v = Σ[ v₀ ∈ S.Val ] v ≡ S.inr v₀ × Den M ρ' v₀
Den _ ρ' v = ⊥
Dens {zero} Nil ρ' vs = vs ≡ []
Dens {suc n} (M ,, as) ρ' vs = Σ[ v ∈ S.Val ] Σ[ vs' ∈ List S.Val ] vs ≡ v ∷ vs' × Den M ρ' v × Dens as ρ' vs'

open Ok

{- the subterms of a tuple, simplified -}
simps : Facts → List AST → List AST
simps E = map (λ M → term (simp E M))

data _≈k_ : S.Cont → S.Cont → Set where
  halt : S.halt ≈k S.halt
  appL : ∀ {E M ρ' ρ κ' κ} → Ok E ρ' ρ → WS (length ρ) M → κ' ≈k κ
    → S.appL (term (simp E M)) ρ' κ' ≈k S.appL M ρ κ
  appR : ∀ {v' v κ' κ} → v' ≈ v → κ' ≈k κ → S.appR v' κ' ≈k S.appR v κ
  tupK : ∀ {E vs' vs Ms ρ' ρ κ' κ} → Pointwise _≈_ vs' vs → Ok E ρ' ρ → All (WS (length ρ)) Ms → κ' ≈k κ
    → S.tupK vs' (simps E Ms) ρ' κ' ≈k S.tupK vs Ms ρ κ
  getK : ∀ {n} {i : Fin n} {κ' κ} → κ' ≈k κ → S.getK i κ' ≈k S.getK i κ
  inlK : ∀ {κ' κ} → κ' ≈k κ → S.inlK κ' ≈k S.inlK κ
  inrK : ∀ {κ' κ} → κ' ≈k κ → S.inrK κ' ≈k S.inrK κ
  caseK : ∀ {E M N ρ' ρ κ' κ} → Ok E ρ' ρ → WS (suc (length ρ)) M → WS (suc (length ρ)) N → κ' ≈k κ
    → S.caseK (term (simp (under E) M)) (term (simp (under E) N)) ρ' κ' ≈k S.caseK M N ρ κ
  primL : ∀ {p E M ρ' ρ κ' κ} → Ok E ρ' ρ → WS (length ρ) M → κ' ≈k κ
    → S.primL p (term (simp E M)) ρ' κ' ≈k S.primL p M ρ κ
  primR : ∀ {p v' v κ' κ} → v' ≈ v → κ' ≈k κ → S.primR p v' κ' ≈k S.primR p v κ

data _~_ : S.State → S.State → Set where
  eval~ : ∀ {E M ρ' ρ κ' κ} → Ok E ρ' ρ → WS (length ρ) M → κ' ≈k κ
    → S.eval (term (simp E M)) ρ' κ' ~ S.eval M ρ κ
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

small-shift : ∀ T → small T ≡ true → small (shift T) ≡ true
small-shift (inl-op ⦅ ` y ,, Nil ⦆) s = refl
small-shift (inl-op ⦅ lit B k ⦅ Nil ⦆ ,, Nil ⦆) s = refl
small-shift (inl-op ⦅ tuple zero ⦅ Nil ⦆ ,, Nil ⦆) s = refl
small-shift (inr-op ⦅ ` y ,, Nil ⦆) s = refl
small-shift (inr-op ⦅ lit B k ⦅ Nil ⦆ ,, Nil ⦆) s = refl
small-shift (inr-op ⦅ tuple zero ⦅ Nil ⦆ ,, Nil ⦆) s = refl
small-shift (` y) s = refl
small-shift (lit B k ⦅ Nil ⦆) s = refl
small-shift (tuple zero ⦅ Nil ⦆) s = refl

{- under one more variable, in the target -}
strong-shift : ∀ T {ρ' v w} → small T ≡ true → Strong T ρ' v → Strong (shift T) (w ∷ ρ') v
strong-shift (inl-op ⦅ ` y ,, Nil ⦆) s d = d
strong-shift (inl-op ⦅ lit B k ⦅ Nil ⦆ ,, Nil ⦆) s d = d
strong-shift (inl-op ⦅ tuple zero ⦅ Nil ⦆ ,, Nil ⦆) s d = d
strong-shift (inr-op ⦅ ` y ,, Nil ⦆) s d = d
strong-shift (inr-op ⦅ lit B k ⦅ Nil ⦆ ,, Nil ⦆) s d = d
strong-shift (inr-op ⦅ tuple zero ⦅ Nil ⦆ ,, Nil ⦆) s d = d
strong-shift (` y) s d = d
strong-shift (lit B k ⦅ Nil ⦆) s d = d
strong-shift (tuple zero ⦅ Nil ⦆) s d = d

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

{- under a binder that stays -}
ok-under : ∀ {E ρ' ρ v' v} → Ok E ρ' ρ → v' ≈ v → Ok (under E) (v' ∷ ρ') (v ∷ ρ)
ok-under {E} ok r = mk-ok val' knw' sml'
  where
  val' : _
  val' zero refl = _ , refl , r
  val' (suc x) e = strong-shift (term (E x)) (sml ok x) (val ok x e)
  knw' : _
  knw' zero refl refl = _ , refl , r
  knw' (suc x) {K = K} e k with known (E x) in k₀
  knw' (suc x) {K = .(shift K₀)} e refl | just K₀ = den-shift K₀ (knw ok x e k₀)
  sml' : _
  sml' zero = refl
  sml' (suc x) = small-shift (term (E x)) (sml ok x)

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
ok-let {E} {V = V} ok r d = mk-ok val' knw' sml'
  where
  val' : _
  val' zero refl = _ , refl , r
  val' (suc x) e = strong-shift (term (E x)) (sml ok x) (val ok x e)
  knw' : _
  knw' zero refl refl = den-shift V (strong-den V d)
  knw' (suc x) {K = K} e k with known (E x) in k₀
  knw' (suc x) {K = .(shift K₀)} e refl | just K₀ = den-shift K₀ (knw ok x e k₀)
  sml' : _
  sml' zero = refl
  sml' (suc x) = small-shift (term (E x)) (sml ok x)

simps-list : ∀ E {n} (as : Args (replicate n ■)) → args→list (simp-args E as) ≡ simps E (args→list as)
simps-list E {zero} Nil = refl
simps-list E {suc n} (M ,, as) = cong (term (simp E M) ∷_) (simps-list E as)

ws-list : ∀ {k n} (as : Args (replicate n ■)) → WS-args k as → All (WS k) (args→list as)
ws-list {n = zero} Nil _ = []
ws-list {n = suc n} (M ,, as) (w , ws) = w ∷ ws-list as ws

{- The simulation, for any target program P' and source program P -------------}

module _ (P' P : AST) where

  L₁ = S.sem P'
  L₂ = S.sem P

  {- the target is i steps from a state related to the source's -}
  match : ℕ → S.State → S.State → Set
  match i s' s = Σ[ t' ∈ S.State ] Steps L₁ i s' t' × t' ~ s

  base : ∀ {s' s} → s' ~ s → match 0 s' s
  base r = _ , zero , r

  one : ∀ {s s'} → S.step s ≡ next s' → Plus L₂ s s'
  one eq = plus eq ε

  {- a run of the source from an evaluation to a return has a step -}
  run-plus : ∀ {M ρ κ v} → Star L₂ (S.eval M ρ κ) (S.ret v κ) → Plus L₂ (S.eval M ρ κ) (S.ret v κ)
  run-plus (st ◅ σ) = plus st σ

  {- the target's run of a value term, from its first step: the target
     then stutters -}
  ahead : ∀ {s' s t'} → Star L₁ s' t' → t' ~ s → Σ[ i ∈ ℕ ] match i s' s
  ahead σ r with star→steps σ
  ... | n , τ = n , _ , τ , r

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
  ...   | st ◅ τ' with ahead τ' (ret~ r k)
  ...     | j , m = ans st (run-plus (σ _)) m

  {- The source runs ahead: run-term and run-known -}

  run-term : ∀ M {E ρ' ρ} → Ok E ρ' ρ → WS (length ρ) M → value (term (simp E M)) ≡ true
    → Σ[ v ∈ S.Val ] Run M ρ v × Strong (term (simp E M)) ρ' v
  run-known : ∀ M {E ρ' ρ K} → Ok E ρ' ρ → WS (length ρ) M → known (simp E M) ≡ just K
    → Σ[ v ∈ S.Val ] Run M ρ v × Den K ρ' v
  run-terms : ∀ {n} (as : Args (replicate n ■)) {E ρ' ρ} → Ok E ρ' ρ → WS-args (length ρ) as
    → values (simp-args E as) ≡ true
    → ∀ {acc} → Σ[ vs ∈ List S.Val ] (∀ κ → Star L₂ (S.tuple-next acc (args→list as) ρ κ) (S.ret (S.tup (reverse (reverseAcc acc vs))) κ))
        × Strongs (simp-args E as) ρ' vs
  {- a component of a known tuple -}
  run-get : ∀ {n} (i : Fin n) L {E ρ' ρ K} → Ok E ρ' ρ → WS (length ρ) L → component i (known (simp E L)) ≡ just K
    → Σ[ v ∈ S.Val ] Run (get i ⦅ L ,, Nil ⦆) ρ v × Den K ρ' v
  {- the branch of a case on a known injection -}
  run-inl : ∀ L {E ρ' ρ K} → Ok E ρ' ρ → WS (length ρ) L → branch (known (simp E L)) ≡ just (true , K)
    → Σ[ v ∈ S.Val ] (∀ M N κ → Star L₂ (S.eval L ρ (S.caseK M N ρ κ)) (S.eval M (v ∷ ρ) κ)) × Strong K ρ' v
  run-inr : ∀ L {E ρ' ρ K} → Ok E ρ' ρ → WS (length ρ) L → branch (known (simp E L)) ≡ just (false , K)
    → Σ[ v ∈ S.Val ] (∀ M N κ → Star L₂ (S.eval L ρ (S.caseK M N ρ κ)) (S.eval N (v ∷ ρ) κ)) × Strong K ρ' v
  {- a primitive on known integers -}
  run-int : ∀ L {E ρ' ρ n} → Ok E ρ' ρ → WS (length ρ) L → int-of (known (simp E L)) ≡ just n → Run L ρ (S.const Int n)

  run-term (` x) {ρ = ρ} ok w e with lookup-ws ρ w
  ... | v , l = v , (λ κ → cong (λ m → S.ret? m κ) l ◅ ε) , val ok x l
  run-term (lam ⦅ ⟩ N ,, Nil ⦆) ok (w , _) e = _ , (λ κ → refl ◅ ε) , clo≈ ok w
  run-term (app ⦅ lam ⦅ ⟩ N ,, Nil ⦆ ,, M ,, Nil ⦆) {E} {ρ' = ρ'} {ρ} ok ((wN , _) , wM , _) e
    with small (term (simp E M)) in s | value (term (simp E M)) in isv
  ... | true | _ with run-term M ok wM (P.small-value (term (simp E M)) s)
  ...   | v , σ , d with run-term N (ok-self ok s d) wN e
  ...     | w , τ , d' = w , (λ κ → refl ◅ refl ◅ refl ◅ (σ (S.appR (S.clo N ρ) κ) ◅◅ (refl ◅ τ κ))) , d'
  run-term (app ⦅ lam ⦅ ⟩ N ,, Nil ⦆ ,, M ,, Nil ⦆) {E} ok ((wN , _) , wM , _) () | false | true
  run-term (app ⦅ lam ⦅ ⟩ N ,, Nil ⦆ ,, M ,, Nil ⦆) {E} ok ((wN , _) , wM , _) () | false | false
  run-term (lit B k ⦅ Nil ⦆) ok w e = _ , (λ κ → refl ◅ ε) , refl
  run-term (tuple n ⦅ as ⦆) {E} ok w e with run-terms as ok w e {[]}
  ... | vs , σ , ds =
    S.tup vs , (λ κ → refl ◅ subst (λ X → Star L₂ _ (S.ret (S.tup X) κ)) (reverse-involutive vs) (σ κ)) , vs , refl , ds
  run-term (get i ⦅ L ,, Nil ⦆) {E} ok (w , _) e with component i (known (simp E L)) in c
  ... | just K with small K in s
  ...   | true with run-get i L ok w c
  ...     | v , σ , d = v , σ , small-strong K s d
  run-term (inl-op ⦅ M ,, Nil ⦆) ok (w , _) e with run-term M ok w e
  ... | v , σ , d = S.inl v , (λ κ → refl ◅ (σ (S.inlK κ) ◅◅ (refl ◅ ε))) , v , refl , d
  run-term (inr-op ⦅ M ,, Nil ⦆) ok (w , _) e with run-term M ok w e
  ... | v , σ , d = S.inr v , (λ κ → refl ◅ (σ (S.inrK κ) ◅◅ (refl ◅ ε))) , v , refl , d
  run-term (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) {E} ok (wL , (wM , wN , _)) e with branch (known (simp E L)) in b
  ... | just (true , K) with run-inl L ok wL b
  ...   | v , σ , d with run-term M (ok-self ok (proj₂ (branch-inl (known (simp E L)) b)) d) wM e
  ...     | w , τ , d' = w , (λ κ → refl ◅ (σ _ _ κ ◅◅ τ κ)) , d'
  run-term (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) {E} ok (wL , (wM , wN , _)) e | just (false , K) with run-inr L ok wL b
  ...   | v , σ , d with run-term N (ok-self ok (proj₂ (branch-inr (known (simp E L)) b)) d) wN e
  ...     | w , τ , d' = w , (λ κ → refl ◅ (σ _ _ κ ◅◅ τ κ)) , d'
  run-term (prim p ⦅ L ,, M ,, Nil ⦆) {E} {ρ = ρ} ok (wL , wM , _) e with int-of (known (simp E L)) in e₁
  ... | just n with int-of (known (simp E M)) in e₂
  ...   | just m =
    S.out (δ p n m)
    , (λ κ → refl ◅ (run-int L ok wL e₁ (S.primL p M ρ κ) ◅◅ (refl ◅ (run-int M ok wM e₂ (S.primR p (S.const Int n) κ) ◅◅ (refl ◅ ε)))))
    , prim-strong (δ p n m)

  run-terms {zero} Nil ok _ _ {acc} = [] , (λ κ → ε) , refl
  run-terms {suc n} (M ,, as) {E} {ρ = ρ} ok (w , ws) e {acc} with P.∧-true {value (term (simp E M))} e
  ... | e₁ , e₂ with run-term M ok w e₁
  ...   | v , σ , d with run-terms as ok ws e₂ {v ∷ acc}
  ...     | vs , τ , ds = v ∷ vs , (λ κ → σ (S.tupK acc (args→list as) ρ κ) ◅◅ (refl ◅ τ κ)) , v , vs , refl , d , ds

  run-get i L {E} {ρ = ρ} ok w c with comp-inv i (known (simp E L)) c
  ... | m , Ks , k , p with run-known L ok w k
  ...   | .(S.tup vs) , σ , (vs , refl , ds) with dens-proj i Ks ds p
  ...     | v , q , d = v , (λ κ → refl ◅ (σ (S.getK i κ) ◅◅ (cong (λ x → S.ret? x κ) q ◅ ε))) , d

  run-inl L {E} {ρ = ρ} ok w b with branch-inl (known (simp E L)) b
  ... | k , s with run-known L ok w k
  ...   | .(S.inl v₀) , σ , (v₀ , refl , d) = v₀ , (λ M N κ → σ (S.caseK M N ρ κ) ◅◅ (refl ◅ ε)) , small-strong _ s d

  run-inr L {E} {ρ = ρ} ok w b with branch-inr (known (simp E L)) b
  ... | k , s with run-known L ok w k
  ...   | .(S.inr v₀) , σ , (v₀ , refl , d) = v₀ , (λ M N κ → σ (S.caseK M N ρ κ) ◅◅ (refl ◅ ε)) , small-strong _ s d

  run-int L {E} ok w e with run-known L ok w (int-inv (known (simp E L)) e)
  ... | .(S.const Int _) , σ , refl = σ

  run-known (` x) {ρ = ρ} ok w k with lookup-ws ρ w
  ... | v , l = v , (λ κ → cong (λ m → S.ret? m κ) l ◅ ε) , knw ok x l k
  run-known (lam ⦅ ⟩ N ,, Nil ⦆) ok w refl = _ , (λ κ → refl ◅ ε) , tt
  run-known (app ⦅ lam ⦅ ⟩ N ,, Nil ⦆ ,, M ,, Nil ⦆) {E} {ρ = ρ} ok ((wN , _) , wM , _) k
    with small (term (simp E M)) in s | value (term (simp E M)) in isv
  ... | true | _ with run-term M ok wM (P.small-value (term (simp E M)) s)
  ...   | v , σ , d with run-known N (ok-self ok s d) wN k
  ...     | w , τ , d' = w , (λ κ → refl ◅ refl ◅ refl ◅ (σ (S.appR (S.clo N ρ) κ) ◅◅ (refl ◅ τ κ))) , d'
  run-known (app ⦅ lam ⦅ ⟩ N ,, Nil ⦆ ,, M ,, Nil ⦆) {E} ok ((wN , _) , wM , _) () | false | true
  run-known (app ⦅ lam ⦅ ⟩ N ,, Nil ⦆ ,, M ,, Nil ⦆) {E} ok ((wN , _) , wM , _) () | false | false
  run-known (lit B k ⦅ Nil ⦆) ok w refl = _ , (λ κ → refl ◅ ε) , refl
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
  ...     | w , τ , d' = w , (λ κ → refl ◅ (σ _ _ κ ◅◅ τ κ)) , d'
  run-known (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) {E} ok (wL , (wM , wN , _)) k | just (false , K) with run-inr L ok wL b
  ...   | v , σ , d with run-known N (ok-self ok (proj₂ (branch-inr (known (simp E L)) b)) d) wN k
  ...     | w , τ , d' = w , (λ κ → refl ◅ (σ _ _ κ ◅◅ τ κ)) , d'
  run-known (prim p ⦅ L ,, M ,, Nil ⦆) {E} {ρ = ρ} ok (wL , wM , _) k with int-of (known (simp E L)) in e₁
  ... | just n with int-of (known (simp E M)) in e₂
  run-known (prim p ⦅ L ,, M ,, Nil ⦆) {E} {ρ = ρ} ok (wL , wM , _) refl | just n | just m =
    S.out (δ p n m)
    , (λ κ → refl ◅ (run-int L ok wL e₁ (S.primL p M ρ κ) ◅◅ (refl ◅ (run-int M ok wM e₂ (S.primR p (S.const Int n) κ) ◅◅ (refl ◅ ε)))))
    , strong-den (prim-term (δ p n m)) (prim-strong (δ p n m))

  {- The source's answer to a target evaluation ----------------------------------}

  tuple-next~ : ∀ {E vs' vs Ms ρ' ρ κ' κ} → Pointwise _≈_ vs' vs → Ok E ρ' ρ → All (WS (length ρ)) Ms → κ' ≈k κ
    → S.tuple-next vs' (simps E Ms) ρ' κ' ~ S.tuple-next vs Ms ρ κ
  tuple-next~ rs ok [] k = ret~ (tup≈ (reverse⁺ rs)) k
  tuple-next~ rs ok (w ∷ ws) k = eval~ ok w (tupK rs ok ws k)

  {- the target and the source take one step each -}
  lock : ∀ {s' s t t'} → S.step s' ≡ next t' → S.step s ≡ next t → t' ~ t → Step-ans s' s
  lock e e' r = ans e (one e') (base r)

  absurd : ∀ {A : Set} → true ≡ false → A
  absurd ()

  eval-sim : ∀ M {E ρ' ρ κ' κ} → Ok E ρ' ρ → WS (length ρ) M → κ' ≈k κ
    → Step-ans (S.eval (term (simp E M)) ρ' κ') (S.eval M ρ κ)
  structural : ∀ M {E ρ' ρ κ' κ} → Ok E ρ' ρ → WS (length ρ) M → κ' ≈k κ → value (term (simp E M)) ≡ false
    → Step-ans (S.eval (term (simp E M)) ρ' κ') (S.eval M ρ κ)
  app-dflt : ∀ L M {E ρ' ρ κ' κ} → Ok E ρ' ρ → WS (length ρ) L → WS (length ρ) M → κ' ≈k κ
    → Step-ans (S.eval (app ⦅ term (simp E L) ,, term (simp E M) ,, Nil ⦆) ρ' κ') (S.eval (app ⦅ L ,, M ,, Nil ⦆) ρ κ)
  app-dflt L M ok wL wM k = lock refl refl (eval~ ok wL (appL ok wM k))

  eval-sim M {E} ok w k with value (term (simp E M)) in isv
  ... | true with run-term M ok w isv
  ...   | v , σ , d = value-ans (term (simp E M)) d σ k
  eval-sim M ok w k | false = structural M ok w k isv

  structural (lam ⦅ ⟩ N ,, Nil ⦆) ok w k ()
  structural (lit B k₀ ⦅ Nil ⦆) ok w k ()
  structural (` x) {E} ok w k isv = absurd (trans (sym (P.small-value (term (E x)) (sml ok x))) isv)
  structural (app ⦅ lam ⦅ ⟩ N ,, Nil ⦆ ,, M ,, Nil ⦆) {E} {ρ' = ρ'} {ρ} ok ((wN , _) , wM , _) k isv
    with small (term (simp E M)) in s | value (term (simp E M)) in v?
  ... | true | _ with run-term M ok wM (P.small-value (term (simp E M)) s)
  ...   | v , σ , d =
    prefix (refl ◅ refl ◅ refl ◅ (σ (S.appR (S.clo N ρ) _) ◅◅ (refl ◅ ε))) (eval-sim N (ok-self ok s d) wN k)
  structural (app ⦅ lam ⦅ ⟩ N ,, Nil ⦆ ,, M ,, Nil ⦆) {E} {ρ' = ρ'} {ρ} {κ'} {κ} ok ((wN , _) , wM , _) k isv
    | false | true with run-term M ok wM v?
  ...   | v , σ , d with trun (term (simp E M)) d
  ...     | w' , τ , r with ahead (refl ◅ refl ◅ (τ (S.appR (S.clo N' ρ') κ') ◅◅ (refl ◅ ε))) (eval~ (ok-let ok r d) wN k)
    where N' = term (simp (((` 0) ∣ just (shift (term (simp E M)))) • (λ x → shift-info (E x))) N)
  ...       | j , m = ans refl (plus refl (refl ◅ refl ◅ (σ (S.appR (S.clo N ρ) κ) ◅◅ (refl ◅ ε)))) m
  structural (app ⦅ lam ⦅ ⟩ N ,, Nil ⦆ ,, M ,, Nil ⦆) {E} ok ((wN , _) , wM , _) k isv | false | false =
    lock refl refl (eval~ {M = lam ⦅ ⟩ N ,, Nil ⦆} ok (wN , tt) (appL ok wM k))
  structural (app ⦅ L@(` x) ,, M ,, Nil ⦆) ok (wL , wM , _) k isv = app-dflt L M ok wL wM k
  structural (app ⦅ L@(app ⦅ _ ⦆) ,, M ,, Nil ⦆) ok (wL , wM , _) k isv = app-dflt L M ok wL wM k
  structural (app ⦅ L@(lit B k₀ ⦅ _ ⦆) ,, M ,, Nil ⦆) ok (wL , wM , _) k isv = app-dflt L M ok wL wM k
  structural (app ⦅ L@(tuple n ⦅ _ ⦆) ,, M ,, Nil ⦆) ok (wL , wM , _) k isv = app-dflt L M ok wL wM k
  structural (app ⦅ L@(get i ⦅ _ ⦆) ,, M ,, Nil ⦆) ok (wL , wM , _) k isv = app-dflt L M ok wL wM k
  structural (app ⦅ L@(inl-op ⦅ _ ⦆) ,, M ,, Nil ⦆) ok (wL , wM , _) k isv = app-dflt L M ok wL wM k
  structural (app ⦅ L@(inr-op ⦅ _ ⦆) ,, M ,, Nil ⦆) ok (wL , wM , _) k isv = app-dflt L M ok wL wM k
  structural (app ⦅ L@(case-op ⦅ _ ⦆) ,, M ,, Nil ⦆) ok (wL , wM , _) k isv = app-dflt L M ok wL wM k
  structural (app ⦅ L@(prim p ⦅ _ ⦆) ,, M ,, Nil ⦆) ok (wL , wM , _) k isv = app-dflt L M ok wL wM k
  structural (tuple n ⦅ as ⦆) {E} {ρ' = ρ'} {ρ} {κ'} {κ} ok w k isv =
    lock refl refl (subst (λ Ms → S.tuple-next [] Ms ρ' κ' ~ S.tuple-next [] (args→list as) ρ κ)
                          (sym (simps-list E as)) (tuple-next~ [] ok (ws-list as w) k))
  structural (get i ⦅ L ,, Nil ⦆) {E} ok (w , _) k isv with component i (known (simp E L)) in c
  ... | nothing = lock refl refl (eval~ ok w (getK k))
  ... | just K with small K in s
  ...   | true = absurd (trans (sym (P.small-value K s)) isv)
  ...   | false = lock refl refl (eval~ ok w (getK k))
  structural (inl-op ⦅ M ,, Nil ⦆) ok (w , _) k isv = lock refl refl (eval~ ok w (inlK k))
  structural (inr-op ⦅ M ,, Nil ⦆) ok (w , _) k isv = lock refl refl (eval~ ok w (inrK k))
  structural (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) {E} ok (wL , (wM , wN , _)) k isv with branch (known (simp E L)) in b
  ... | nothing = lock refl refl (eval~ ok wL (caseK ok wM wN k))
  ... | just (true , K) with run-inl L ok wL b
  ...   | v , σ , d = prefix (refl ◅ σ _ _ _) (eval-sim M (ok-self ok (proj₂ (branch-inl (known (simp E L)) b)) d) wM k)
  structural (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) {E} ok (wL , (wM , wN , _)) k isv | just (false , K) with run-inr L ok wL b
  ...   | v , σ , d = prefix (refl ◅ σ _ _ _) (eval-sim N (ok-self ok (proj₂ (branch-inr (known (simp E L)) b)) d) wN k)
  structural (prim p ⦅ L ,, M ,, Nil ⦆) {E} ok (wL , wM , _) k isv with int-of (known (simp E L)) in e₁
  ... | nothing = lock refl refl (eval~ ok wL (primL ok wM k))
  ... | just n with int-of (known (simp E M)) in e₂
  ...   | nothing = lock refl refl (eval~ ok wL (primL ok wM k))
  ...   | just m = absurd (trans (sym (P.sv-value (P.prim-term-sv (δ p n m)))) isv)

  {- The simulation ------------------------------------------------------------}

  ret?-answers : ∀ {i mv mw κ' κ s} → M.Pointwise _≈_ mv mw → κ' ≈k κ → S.step s ≡ S.ret? mw κ
    → Answers≺ L₂ match i (S.ret? mv κ') s
  ret?-answers (M.just r) k eq = steps (one eq) (base (ret~ r k))
  ret?-answers M.nothing k eq = stops eq

  next~ : ∀ {i s t' t} → S.step s ≡ next t → t' ~ t → Answers≺ L₂ match i (next t') s
  next~ e r = steps (one e) (base r)

  base-sim : ∀ {i s' s} → s' ~ s → Answers≺ L₂ match i (S.step s') s
  base-sim (eval~ {M = M} ok w k) with eval-sim M ok w k
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
  base-sim (ret~ (tup≈ rs) (getK {i = i} k)) = ret?-answers (proj-pw i rs) k refl
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
  base-sim (ret~ s (primR {p} r k)) = ret?-answers (prim≈ p r s) k refl

  sim : ∀ {i s' s} → match i s' s → Answers≺ L₂ match i (S.step s') s
  sim (t , zero , r) = base-sim r
  sim {suc i} {s'} {s} (t , suc {s' = s''} st σ , r) =
    subst (λ a → Answers≺ L₂ match (suc i) a s) (sym st) (stutters (n<1+n i) (t , σ , r))

{- The end theorem: for closed programs ------------------------------------------}

ok₀ : Ok (λ x → self (` x)) [] []
ok₀ = mk-ok (λ x ()) (λ x ()) (λ x → refl)

simplify-correct : ∀ M → Closed M → Equivalent (S.sem M) (S.sem (simplify M))
simplify-correct M c = equiv-sym (equivalent (record
  { match = match (simplify M) M
  ; init = 0 , base (simplify M) M (eval~ ok₀ (closed-ws {M} c) halt)
  ; sim = sim (simplify M) M }))

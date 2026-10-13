{-

  Correctness of the optimize pass (Clos2 → Clos2), clock for clock (see
  the design note in Clock.agda). Optimize only drops free variables of
  closures that are variables, whose evaluation makes no call and, in a
  well-scoped program, cannot error; the big-step interpreter does not
  see those evaluations, so the source and the target call functions in
  lock step.

  Optimize renames variables, so environments agree through a renaming r,
  as in OptimizeSim.agda: Agree M k r ρ₁ ρ₂ says that M, under k binders,
  finds related values at x in ρ₁ and at r x in ρ₂ for every variable x it
  uses, and that M is well scoped (needed for the code of closures inside
  M). A closure of N and vs is related to a closure of
  optimize (ext-var r) N and ws when vs and ws agree through r.

  While the free variables of a closure are evaluated (prune≈), the values
  collected so far agree through the renumbering b of positions that
  prune computes from the free variables already seen (Collected).

  The precondition is well-scopedness (WS 0, Framework.Syntax.Scope), which
  enclose establishes for closed ISWIM programs (enclose-closed).

-}

module proof.Correctness.Interp.OptimizeFuel where

open import Framework.Syntax.SigUtil using (ν-n)
open import Framework.Syntax.SyntaxUtil using (_,,_; Nil; ⟩_,,_)
open import Language.Clos2
open import Compiler.Optimize hiding (bound; bound-arg; bound-args)
open import Compiler.Enclose using (enclose)
open import proof.Framework.Syntax.Scope Op sig using (WS; WS-arg; ws-uses)
open import proof.Compiler.EncloseScope using (Closed; enclose-closed)
open import Semantics.Observation
open import Language.Prim using (int; bool)
open import Data.Bool using (true; false)
open import proof.Framework.ListUtil using (_‼_; proj-pw)
open import proof.Semantics.Interp.Clock
import Semantics.Interp.ISWIM as S
import Semantics.Interp.Clos2 as T
import proof.Correctness.Interp.EncloseFuel as EF

open import Data.Empty using (⊥-elim)
open import Data.List using ([]; _∷_; replicate)
open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_; reverse⁺)
open import Data.Maybe using (just; nothing)
import Data.Maybe.Relation.Binary.Pointwise as M
open import Data.Nat using (ℕ; zero; suc; _+_; z≤n)
open import Data.Nat.Properties using (≤-pred; <-≤-trans; <-irrefl; +-suc; +-identityʳ; +-monoʳ-≤; n≮0)
open import Data.Product using (_×_; Σ-syntax; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst; cong₂)
open import Relation.Nullary using (¬_; Dec; yes; no)

{- The relation -----------------------------------------------------------------}

infix 4 _≈_

data _≈_ : T.Val → T.Val → Set
Lookup : T.Env → ℕ → T.Env → ℕ → Set
data Agree (M : AST) (k : ℕ) (r : Var → Var) (ρ₁ ρ₂ : T.Env) : Set

data _≈_ where
  clo≈ : ∀ {N vs ws r} → Agree N 1 r vs ws → T.clos N vs ≈ T.clos (optimize (ext-var r) N) ws
  const≈ : ∀ {B k} → T.const B k ≈ T.const B k
  tup≈ : ∀ {vs ws} → Pointwise _≈_ vs ws → T.tup vs ≈ T.tup ws
  inl≈ : ∀ {v w} → v ≈ w → T.inl v ≈ T.inl w
  inr≈ : ∀ {v w} → v ≈ w → T.inr v ≈ T.inr w

{- the source value at x and the target value at y are defined and related -}
Lookup ρ₁ x ρ₂ y =
  Σ[ v ∈ T.Val ] Σ[ w ∈ T.Val ] (ρ₁ ‼ x ≡ just v) × (ρ₂ ‼ y ≡ just w) × v ≈ w

data Agree M k r ρ₁ ρ₂ where
  agree : ∀ {j} → WS j M → (∀ x → Uses (k + x) M → Lookup ρ₁ x ρ₂ (r x)) → Agree M k r ρ₁ ρ₂

{- the values collected for the free variables of a closure, with m left:
   U k says that the code uses position k, and the positions k past the m
   left are renumbered b k in the target -}
record Collected (U : ℕ → Set) (m : ℕ) (b : ℕ → ℕ) (vs ws : T.Env) : Set where
  constructor collected
  field look : ∀ k → U (m + k) → Lookup vs k ws (b k)

{- Related values are observed alike -}
obs≈ : ∀ {v w} → v ≈ w → T.obs v ≡ T.obs w
obs≈-list : ∀ {vs ws} → Pointwise _≈_ vs ws → T.obs-list vs ≡ T.obs-list ws
obs≈ (clo≈ _) = refl
obs≈ const≈ = refl
obs≈ (tup≈ rs) = cong o-tuple (obs≈-list rs)
obs≈ (inl≈ r) = cong o-inl (obs≈ r)
obs≈ (inr≈ r) = cong o-inr (obs≈ r)
obs≈-list [] = refl
obs≈-list (r ∷ rs) = cong₂ _∷_ (obs≈ r) (obs≈-list rs)

{- related operands give related results of a primitive -}
prim≈ : ∀ p {v₁ v₂ w₁ w₂} → v₁ ≈ w₁ → v₂ ≈ w₂ → M.Pointwise _≈_ (T.prim? p v₁ v₂) (T.prim? p w₁ w₂)
prim≈ p {w₁ = w₁} {w₂ = w₂} r s rewrite obs≈ r | obs≈ s with δ? p (T.obs w₁) (T.obs w₂)
... | nothing = M.nothing
... | just (int n) = M.just const≈
... | just (bool true) = M.just (inl≈ (tup≈ []))
... | just (bool false) = M.just (inr≈ (tup≈ []))

{- Agreement of environments ---------------------------------------------------}

agree-ext : ∀ {M r ρ₁ ρ₂ v w} → v ≈ w → Agree M 1 r ρ₁ ρ₂
  → Agree M 0 (ext-var r) (v ∷ ρ₁) (w ∷ ρ₂)
agree-ext {M} {r} {ρ₁} {ρ₂} {v} {w} vw (agree sc look) = agree sc look'
  where
  look' : ∀ x → Uses x M → Lookup (v ∷ ρ₁) x (w ∷ ρ₂) (ext-var r x)
  look' zero _ = v , w , refl , refl , vw
  look' (suc x) u = look x u

agree-look : ∀ {M k r ρ₁ ρ₂} → Agree M k r ρ₁ ρ₂ → ∀ x → Uses (k + x) M → Lookup ρ₁ x ρ₂ (r x)
agree-look (agree _ look) = look

{- a subterm M' of M, under k binders -}
agree-sub : ∀ {k M M' r ρ₁ ρ₂} → (∀ {j} → WS j M → WS (k + j) M')
  → (∀ x → Uses (k + x) M' → Uses x M) → Agree M 0 r ρ₁ ρ₂ → Agree M' k r ρ₁ ρ₂
agree-sub sc sub (agree w look) = agree (sc w) (λ x u → look x (sub x u))

{- the first of a list of arguments, and the rest -}
agree-hd : ∀ {n M r ρ₁ ρ₂} {args : Args (replicate n ■)}
  → Agree (tuple (suc n) ⦅ M ,, args ⦆) 0 r ρ₁ ρ₂ → Agree M 0 r ρ₁ ρ₂
agree-hd = agree-sub proj₁ (λ x → inj₁)

agree-tl : ∀ {n M r ρ₁ ρ₂} {args : Args (replicate n ■)}
  → Agree (tuple (suc n) ⦅ M ,, args ⦆) 0 r ρ₁ ρ₂ → Agree (tuple n ⦅ args ⦆) 0 r ρ₁ ρ₂
agree-tl = agree-sub proj₂ (λ x → inj₂)

{- after a kept or a dropped free variable -}
keep-col : ∀ {U m b vs ws v w} → v ≈ w → Collected U (suc m) b vs ws
  → Collected U m (keep-base b) (v ∷ vs) (w ∷ ws)
keep-col {U} {m} {v = v} {w} vw (collected col) = collected look
  where
  look : ∀ k → U (m + k) → _
  look zero _ = v , w , refl , refl , vw
  look (suc k) u = col k (subst U (+-suc m k) u)

drop-col : ∀ {U m b vs ws v} → ¬ U m → Collected U (suc m) b vs ws
  → Collected U m (drop-base b) (v ∷ vs) ws
drop-col {U} {m} nu (collected col) = collected look
  where
  look : ∀ k → U (m + k) → _
  look zero u = ⊥-elim (nu (subst U (+-identityʳ m) u))
  look (suc k) u = col k (subst U (+-suc m k) u)

{- the code of a closure -}
unbind-body : ∀ k (a : Arg (ν-n k (ν ■))) → unbind-n k a ≡ T.body k a
unbind-body zero (bind (ast N)) = refl
unbind-body (suc k) (bind a) = unbind-body k a

opt-body-body : ∀ r k (a : Arg (ν-n k (ν ■))) → opt-body r k a ≡ optimize r (T.body k a)
opt-body-body r zero (bind (ast N)) = refl
opt-body-body r (suc k) (bind a) = opt-body-body r k a

ws-body : ∀ n k (a : Arg (ν-n n (ν ■))) → WS-arg k a → WS (suc (n + k)) (T.body n a)
ws-body zero k (bind (ast N)) w = w
ws-body (suc n) k (bind a) w =
  subst (λ x → WS (suc x) (T.body n a)) (+-suc n k) (ws-body n (suc k) a w)

{- Clock for clock ---------------------------------------------------------------}

var≈ : ∀ ck {r ρ₁ ρ₂} x → Agree (` x) 0 r ρ₁ ρ₂
  → RelResult _≈_ (T.eval ck ρ₁ (` x)) (T.eval ck ρ₂ (` r x))
var≈ ck x ag with agree-look ag x refl
... | v , w , e₁ , e₂ , vw rewrite e₁ | e₂ = ret vw

run≈ : ∀ ck {r ρ₁ ρ₂} M → Agree M 0 r ρ₁ ρ₂
  → RelResult _≈_ (T.eval ck ρ₁ M) (T.eval ck ρ₂ (optimize r M))
args≈ : ∀ ck {n r ρ₁ ρ₂ vs ws} (args : Args (replicate n ■)) → Agree (tuple n ⦅ args ⦆) 0 r ρ₁ ρ₂
  → Pointwise _≈_ vs ws
  → RelResult (Pointwise _≈_) (T.eval-args ck ρ₁ vs args) (T.eval-args ck ρ₂ ws (opt-args r args))
{- the free variables of a closure: the source evaluates all of them, the
   target only those that prune keeps -}
prune≈ : ∀ ck m {r ρ₁ ρ₂ U b vs ws} (dec : ∀ j → Dec (U j)) (fvs : Args (replicate m ■))
  → Agree (tuple m ⦅ fvs ⦆) 0 r ρ₁ ρ₂ → Collected U m b vs ws
  → RelResult (Collected U 0 (index (prune m r dec fvs b)))
      (T.eval-args ck ρ₁ vs fvs) (T.eval-args ck ρ₂ ws (kept (prune m r dec fvs b)))
apply≈ : ∀ ck {r ρ₁ ρ₂ f g} M → Agree M 0 r ρ₁ ρ₂ → f ≈ g
  → RelResult _≈_ (T.apply ck ρ₁ M f) (T.apply ck ρ₂ (optimize r M) g)
call≈ : ∀ ck {r ρ₁ ρ₂} N → Agree N 0 r ρ₁ ρ₂
  → RelResult _≈_ (T.call ck N ρ₁) (T.call ck (optimize r N) ρ₂)
branch≈ : ∀ ck {r ρ₁ ρ₂ v w} M N → Agree M 1 r ρ₁ ρ₂ → Agree N 1 r ρ₁ ρ₂ → v ≈ w
  → RelResult _≈_ (T.branch ck ρ₁ M N v) (T.branch ck ρ₂ (optimize (ext-var r) M) (optimize (ext-var r) N) w)

run≈ ck (` x) ag = var≈ ck x ag
run≈ ck {r} {ρ₁} {ρ₂} (clos-op n ⦅ cons (clear a) fvs ⦆) (agree (wa , wfvs) look) =
  subst (λ B → RelResult _≈_ (T.eval ck ρ₁ (clos-op n ⦅ cons (clear a) fvs ⦆))
                             (T.eval-args ck ρ₂ [] (kept P) >>= λ ws → ret (T.clos B ws)))
        (sym eq)
        (bind-rel (prune≈ ck n U? fvs (agree wfvs (λ x u → look x (inj₂ u))) col₀)
                  (λ col → ret (clo≈ (agree sc (λ x u →
                     Collected.look col x (subst (Uses (suc x)) (sym (unbind-body n a)) u))))))
  where
  U = λ j → Uses (suc j) (unbind-n n a)
  U? = λ j → uses? (suc j) (unbind-n n a)
  P = prune n r U? fvs (λ k → k)
  sc = ws-body n 0 a wa
  {- nothing collected yet: the code uses no position past its n free
     variables, since it is well scoped -}
  col₀ : Collected U n (λ k → k) [] []
  col₀ = collected λ k u → ⊥-elim (<-irrefl refl (<-≤-trans
    (≤-pred (ws-uses (T.body n a) sc (subst (Uses (suc (n + k))) (unbind-body n a) u)))
    (+-monoʳ-≤ n z≤n)))
  eq : T.body (count P) (bind-n-ast (count P) (opt-body (ext-var (index P)) n a))
       ≡ optimize (ext-var (index P)) (T.body n a)
  eq = trans (EF.body-bind (count P) _) (opt-body-body (ext-var (index P)) n a)
run≈ ck (app ⦅ L ,, M ,, Nil ⦆) ag =
  bind-rel (run≈ ck L (agree-sub proj₁ (λ x → inj₁) ag))
           (apply≈ ck M (agree-sub (λ w → proj₁ (proj₂ w)) (λ x u → inj₂ (inj₁ u)) ag))
run≈ ck (lit B k ⦅ Nil ⦆) ag = ret const≈
run≈ ck (tuple n ⦅ args ⦆) ag = bind-rel (args≈ ck args ag []) (λ rs → ret (tup≈ (reverse⁺ rs)))
run≈ ck (get i ⦅ M ,, Nil ⦆) ag = bind-rel (run≈ ck M (agree-sub proj₁ (λ x → inj₁) ag)) get≈
  where
  get≈ : ∀ {v w} → v ≈ w → RelResult _≈_ (T.project i v) (T.project i w)
  get≈ (tup≈ rs) = from-maybe-rel (proj-pw i rs)
  get≈ (clo≈ _) = error
  get≈ const≈ = error
  get≈ (inl≈ _) = error
  get≈ (inr≈ _) = error
run≈ ck (inl-op ⦅ M ,, Nil ⦆) ag =
  bind-rel (run≈ ck M (agree-sub proj₁ (λ x → inj₁) ag)) (λ vw → ret (inl≈ vw))
run≈ ck (inr-op ⦅ M ,, Nil ⦆) ag =
  bind-rel (run≈ ck M (agree-sub proj₁ (λ x → inj₁) ag)) (λ vw → ret (inr≈ vw))
run≈ ck (prim p ⦅ L ,, M ,, Nil ⦆) ag =
  bind-rel (run≈ ck L (agree-sub proj₁ (λ x → inj₁) ag)) λ r →
  bind-rel (run≈ ck M (agree-sub (λ w → proj₁ (proj₂ w)) (λ x u → inj₂ (inj₁ u)) ag)) λ s →
  from-maybe-rel (prim≈ p r s)
run≈ ck (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) ag =
  bind-rel (run≈ ck L (agree-sub proj₁ (λ x → inj₁) ag))
    (branch≈ ck M N (agree-sub (λ w → proj₁ (proj₂ w)) (λ x u → inj₂ (inj₁ u)) ag)
                    (agree-sub (λ w → proj₁ (proj₂ (proj₂ w))) (λ x u → inj₂ (inj₂ (inj₁ u))) ag))
run≈ ck (let-op ⦅ M ,, ⟩ N ,, Nil ⦆) ag =
  bind-rel (run≈ ck M (agree-sub proj₁ (λ x → inj₁) ag)) λ vw →
  run≈ ck N (agree-ext vw (agree-sub (λ w → proj₁ (proj₂ w)) (λ x u → inj₂ (inj₁ u)) ag))

args≈ ck {zero} Nil ag rs = ret rs
args≈ ck {suc n} (M ,, args) ag rs =
  bind-rel (run≈ ck M (agree-hd ag)) (λ vw → args≈ ck args (agree-tl ag) (vw ∷ rs))

prune≈ ck zero dec Nil ag col = ret col
prune≈ ck (suc m) dec ((` y) ,, fvs) ag col with dec m
... | yes _ = bind-rel (var≈ ck y (agree-hd ag)) (λ vw → prune≈ ck m dec fvs (agree-tl ag) (keep-col vw col))
... | no nu with agree-look ag y (inj₁ refl)
...   | _ , _ , e , _ rewrite e = prune≈ ck m dec fvs (agree-tl ag) (drop-col nu col)
prune≈ ck (suc m) dec ((op ⦅ args ⦆) ,, fvs) ag col =
  bind-rel (run≈ ck (op ⦅ args ⦆) (agree-hd ag)) (λ vw → prune≈ ck m dec fvs (agree-tl ag) (keep-col vw col))

apply≈ ck M ag (clo≈ {N} agN) = bind-rel (run≈ ck M ag) (λ vw → call≈ ck N (agree-ext vw agN))
apply≈ ck M ag const≈ = error
apply≈ ck M ag (tup≈ _) = error
apply≈ ck M ag (inl≈ _) = error
apply≈ ck M ag (inr≈ _) = error

call≈ zero N ag = timeout
call≈ (suc ck) N ag = run≈ ck N ag

branch≈ ck M N agM agN (inl≈ vw) = run≈ ck M (agree-ext vw agM)
branch≈ ck M N agM agN (inr≈ vw) = run≈ ck N (agree-ext vw agN)
branch≈ ck M N agM agN (clo≈ _) = error
branch≈ ck M N agM agN const≈ = error
branch≈ ck M N agM agN (tup≈ _) = error

{- The end theorem -------------------------------------------------------------}

optimize-correct : ∀ M → WS 0 M → Equivalent (T.sem M) (T.sem (optimize-program M))
optimize-correct M c =
  clocked _≈_ obs≈ (λ ck → run≈ ck M (agree c (λ x u → ⊥-elim (n≮0 (ws-uses M c u)))))

{- enclose, then optimize, for closed ISWIM programs -}
enclose-optimize-correct : ∀ M → Closed M → Equivalent (S.sem M) (T.sem (optimize-program (enclose M)))
enclose-optimize-correct M c =
  equiv-trans (EF.enclose-correct M c) (optimize-correct (enclose M) (enclose-closed M c))

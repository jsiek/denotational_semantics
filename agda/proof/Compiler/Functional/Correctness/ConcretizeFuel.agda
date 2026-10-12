{-

  Correctness of the concretize pass (Clos2 → Clos3), clock for clock
  (see the design note in Clock.agda): for every clock, a term and its
  concretization, in related environments, both time out, both go wrong,
  or return related values. Concretize maps each application to one
  application, so the two interpreters call functions in lock step.

  The pass needs no precondition: it is correct for every Clos2 program.
  A Clos2 variable that a closure's code reads past its free variables is
  unbound in Clos2 (the code runs in the argument and the n free
  variables only) and becomes ` 2, which is unbound in Clos3 (the code
  runs in the argument and the tuple only): both go wrong.

  Values are related (_≈_) when they agree, except that a Clos2 closure
  of N and the values vs of its free variables is related to a Clos3
  closure of concretize (fv-ref n) N and a tuple ts that holds the same
  values in the opposite order (FV n vs ts): the Clos2 interpreter
  collects the values as an environment, the free variable bound last
  first, and component fv-index n k of the tuple is the k-th of them.

  Environments are related through the map φ : Var → Ref that concretize
  carries (EnvRel), at every variable: a Clos2 variable x finds a related
  value (or none) in the Clos3 variable or tuple component that φ x names.

-}

module proof.Compiler.Functional.Correctness.ConcretizeFuel where

open import Framework.Syntax.SigUtil using (ν-n)
open import Framework.Syntax.SyntaxUtil using (_,,_; Nil; ⟩_,,_)
import Compiler.Lang.Clos2 as C2
open C2 using (`_; _⦅_⦆; clos-op; app; lit; tuple; get; inl-op; inr-op; case-op; prim;
               cons; clear; bind; ast; ν; ■; Var; Args)
open import Compiler.Compile.Concretize
open import Compiler.Observation
open import Compiler.Lang.Prim using (int; bool)
open import Data.Bool using (true; false)
open import proof.Framework.ListUtil
  using (_‼_; proj; has-length; proj-pw; ‼-snoc-<; ‼-snoc-length; ‼-≥; length-snoc)
open import proof.Compiler.Functional.Clock
import Compiler.Functional.Interp.Clos2 as S
import Compiler.Functional.Interp.Clos3 as T

open import Data.Bool using (true)
open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; _∷ʳ_; length; replicate; reverse)
open import Data.List.Properties using (unfold-reverse)
open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_; reverse⁺)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe.Relation.Binary.Pointwise as M
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; _<_; _<?_)
open import Data.Nat.Properties using (+-identityʳ; +-suc; ≤-pred; ≮⇒≥; m≤n⇒m<n∨m≡n)
open import Data.Product using (_×_; Σ-syntax; _,_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst; cong₂)
open import Relation.Nullary using (yes; no)

{- The relation -----------------------------------------------------------------}

infix 4 _≈_

data _≈_ : S.Val → T.Val → Set
data FV : ℕ → List S.Val → List T.Val → Set

data _≈_ where
  clo≈ : ∀ {n N vs ts} → FV n vs ts → S.clos N vs ≈ T.clos (concretize (fv-ref n) N) (T.tup ts)
  const≈ : ∀ {B k} → S.const B k ≈ T.const B k
  tup≈ : ∀ {vs ws} → Pointwise _≈_ vs ws → S.tup vs ≈ T.tup ws
  inl≈ : ∀ {v w} → v ≈ w → S.inl v ≈ T.inl w
  inr≈ : ∀ {v w} → v ≈ w → S.inr v ≈ T.inr w

{- the n values of a closure's free variables, the one bound last first,
   and the tuple of them: the first component is the last value -}
data FV where
  [] : FV 0 [] []
  fv-snoc : ∀ {n vs ts v t} → FV n vs ts → v ≈ t → FV (suc n) (vs ∷ʳ v) (t ∷ ts)

{- where a Clos2 value (or its absence) is found in a Clos3 environment -}
RefRel : Maybe S.Val → Ref → T.Env → Set
RefRel mv (var y) ρ₃ = M.Pointwise _≈_ mv (ρ₃ ‼ y)
RefRel mv (prj i y) ρ₃ = Σ[ ts ∈ List T.Val ] (ρ₃ ‼ y ≡ just (T.tup ts)) × M.Pointwise _≈_ mv (proj i ts)

EnvRel : (Var → Ref) → S.Env → T.Env → Set
EnvRel φ ρ₂ ρ₃ = ∀ x → RefRel (ρ₂ ‼ x) (φ x) ρ₃

{- Related values are observed alike -}
obs≈ : ∀ {v w} → v ≈ w → S.obs v ≡ T.obs w
obs≈-list : ∀ {vs ws} → Pointwise _≈_ vs ws → S.obs-list vs ≡ T.obs-list ws
obs≈ (clo≈ _) = refl
obs≈ const≈ = refl
obs≈ (tup≈ rs) = cong o-tuple (obs≈-list rs)
obs≈ (inl≈ r) = cong o-inl (obs≈ r)
obs≈ (inr≈ r) = cong o-inr (obs≈ r)
obs≈-list [] = refl
obs≈-list (r ∷ rs) = cong₂ _∷_ (obs≈ r) (obs≈-list rs)

{- related operands give related results of a primitive -}
prim≈ : ∀ p {v₁ v₂ w₁ w₂} → v₁ ≈ w₁ → v₂ ≈ w₂ → M.Pointwise _≈_ (S.prim? p v₁ v₂) (T.prim? p w₁ w₂)
prim≈ p {w₁ = w₁} {w₂ = w₂} r s rewrite obs≈ r | obs≈ s with δ? p (T.obs w₁) (T.obs w₂)
... | nothing = M.nothing
... | just (int n) = M.just const≈
... | just (bool true) = M.just (inl≈ (tup≈ []))
... | just (bool false) = M.just (inr≈ (tup≈ []))

{- The free variables of a closure ---------------------------------------------}

FV-length : ∀ {n vs ts} → FV n vs ts → length vs ≡ n
FV-length [] = refl
FV-length (fv-snoc {vs = vs} {v = v} f r) = trans (length-snoc vs v) (cong suc (FV-length f))

FV-has-length : ∀ {n vs ts} → FV n vs ts → has-length n ts ≡ true
FV-has-length [] = refl
FV-has-length (fv-snoc f r) = FV-has-length f

FV-cons : ∀ {n vs ts v w} → FV n vs ts → v ≈ w → FV (suc n) (v ∷ vs) (ts ∷ʳ w)
FV-cons [] r = fv-snoc [] r
FV-cons (fv-snoc f r') r = fv-snoc (FV-cons f r) r'

{- the interpreters collect the values in the same order, and the tuple
   is reversed -}
pw→FV : ∀ {vs ws} → Pointwise _≈_ vs ws → FV (length vs) vs (reverse ws)
pw→FV [] = []
pw→FV {v ∷ vs} {w ∷ ws} (r ∷ rs) =
  subst (FV (suc (length vs)) (v ∷ vs)) (sym (unfold-reverse w ws)) (FV-cons (pw→FV rs) r)

FV-lookup : ∀ {n vs ts} → FV n vs ts → ∀ k (k<n : k < n)
  → M.Pointwise _≈_ (vs ‼ k) (proj (fv-index n k k<n) ts)
FV-lookup (fv-snoc {n} {vs} {ts} {v} {t} f r) k k<sn with k <? n
... | yes k<n
  rewrite ‼-snoc-< vs v k (subst (k <_) (sym (FV-length f)) k<n) = FV-lookup f k k<n
... | no k≮n with m≤n⇒m<n∨m≡n (≤-pred k<sn)
...   | inj₁ k<n = ⊥-elim (k≮n k<n)
...   | inj₂ refl rewrite FV-has-length f | sym (FV-length f) | ‼-snoc-length vs v = M.just r

{- The environment relation ----------------------------------------------------}

env-ext : ∀ {φ ρ₂ ρ₃ v w} → v ≈ w → EnvRel φ ρ₂ ρ₃ → EnvRel (ext-ref φ) (v ∷ ρ₂) (w ∷ ρ₃)
env-ext r er zero = M.just r
env-ext {φ} r er (suc x) with φ x | er x
... | var y | p = p
... | prj i y | p = p

{- the environment of a closure's code: its argument, then its free
   variables (Clos2) or the tuple of them (Clos3) -}
env-clos : ∀ {n vs ts v w} → v ≈ w → FV n vs ts → EnvRel (fv-ref n) (v ∷ vs) (w ∷ T.tup ts ∷ [])
env-clos r f zero = M.just r
env-clos {n} {vs} r f (suc k) with k <? n
... | yes k<n = _ , refl , FV-lookup f k k<n
... | no k≮n rewrite ‼-≥ vs k (subst (_≤ k) (sym (FV-length f)) (≮⇒≥ k≮n)) = M.nothing

env-empty : EnvRel var [] []
env-empty x = M.nothing

conc-body≡ : ∀ n k (a : C2.Arg (ν-n k (ν ■))) → conc-body n k a ≡ concretize (fv-ref n) (S.body k a)
conc-body≡ n zero (bind (ast N)) = refl
conc-body≡ n (suc k) (bind a) = conc-body≡ n k a

{- Clock for clock ---------------------------------------------------------------}

{- the values of the arguments, k of them in all -}
Args≈ : ℕ → List S.Val → List T.Val → Set
Args≈ k vs ws = Pointwise _≈_ vs ws × length vs ≡ k

run≈ : ∀ ck {φ ρ₂ ρ₃} M → EnvRel φ ρ₂ ρ₃
  → RelResult _≈_ (S.eval ck ρ₂ M) (T.eval ck ρ₃ (concretize φ M))
args≈ : ∀ ck {n k φ ρ₂ ρ₃ vs ws} (args : Args (replicate n ■)) → EnvRel φ ρ₂ ρ₃
  → Pointwise _≈_ vs ws → length vs + n ≡ k
  → RelResult (Args≈ k) (S.eval-args ck ρ₂ vs args) (T.eval-args ck ρ₃ ws (conc-args φ args))
apply≈ : ∀ ck {φ ρ₂ ρ₃ f g} M → EnvRel φ ρ₂ ρ₃ → f ≈ g
  → RelResult _≈_ (S.apply ck ρ₂ M f) (T.apply ck ρ₃ (concretize φ M) g)
call≈ : ∀ ck {φ ρ₂ ρ₃} N → EnvRel φ ρ₂ ρ₃
  → RelResult _≈_ (S.call ck N ρ₂) (T.call ck (concretize φ N) ρ₃)
branch≈ : ∀ ck {φ ρ₂ ρ₃ v w} M N → EnvRel φ ρ₂ ρ₃ → v ≈ w
  → RelResult _≈_ (S.branch ck ρ₂ M N v)
                  (T.branch ck ρ₃ (concretize (ext-ref φ) M) (concretize (ext-ref φ) N) w)

project≈ : ∀ {n} (i : Fin n) {v w} → v ≈ w → RelResult _≈_ (S.project i v) (T.project i w)
project≈ i (tup≈ rs) = from-maybe-rel (proj-pw i rs)
project≈ i (clo≈ _) = wrong
project≈ i const≈ = wrong
project≈ i (inl≈ _) = wrong
project≈ i (inr≈ _) = wrong

run≈ ck {φ} {ρ₂} {ρ₃} (` x) er with φ x | er x
... | var y | p = from-maybe-rel p
... | prj i y | ts , eq , p rewrite eq = from-maybe-rel p
run≈ ck {φ} (clos-op n ⦅ cons (clear a) fvs ⦆) er
  rewrite conc-body≡ n n a = bind-rel (args≈ ck fvs er [] refl) clo
  where
  clo : ∀ {vs ws} → Args≈ n vs ws → RelResult _≈_ (ret (S.clos (S.body n a) vs))
          (ret (T.clos (concretize (fv-ref n) (S.body n a)) (T.tup (reverse ws))))
  clo (rs , refl) = ret (clo≈ (pw→FV rs))
run≈ ck (app ⦅ L ,, M ,, Nil ⦆) er = bind-rel (run≈ ck L er) (apply≈ ck M er)
run≈ ck (lit B k ⦅ Nil ⦆) er = ret const≈
run≈ ck (tuple n ⦅ args ⦆) er = bind-rel (args≈ ck args er [] refl) (λ (rs , _) → ret (tup≈ (reverse⁺ rs)))
run≈ ck (get i ⦅ M ,, Nil ⦆) er = bind-rel (run≈ ck M er) (project≈ i)
run≈ ck (inl-op ⦅ M ,, Nil ⦆) er = bind-rel (run≈ ck M er) (λ r → ret (inl≈ r))
run≈ ck (inr-op ⦅ M ,, Nil ⦆) er = bind-rel (run≈ ck M er) (λ r → ret (inr≈ r))
run≈ ck (prim p ⦅ L ,, M ,, Nil ⦆) er =
  bind-rel (run≈ ck L er) λ r → bind-rel (run≈ ck M er) λ s → from-maybe-rel (prim≈ p r s)
run≈ ck (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) er = bind-rel (run≈ ck L er) (branch≈ ck M N er)

args≈ ck {zero} {vs = vs} Nil er rs len = ret (rs , trans (sym (+-identityʳ (length vs))) len)
args≈ ck {suc n} {vs = vs} (M ,, args) er rs len =
  bind-rel (run≈ ck M er) (λ r → args≈ ck args er (r ∷ rs) (trans (sym (+-suc (length vs) n)) len))

apply≈ ck M er (clo≈ {N = N} f) = bind-rel (run≈ ck M er) (λ r → call≈ ck N (env-clos r f))
apply≈ ck M er const≈ = wrong
apply≈ ck M er (tup≈ _) = wrong
apply≈ ck M er (inl≈ _) = wrong
apply≈ ck M er (inr≈ _) = wrong

call≈ zero N er = timeout
call≈ (suc ck) N er = run≈ ck N er

branch≈ ck M N er (inl≈ r) = run≈ ck M (env-ext r er)
branch≈ ck M N er (inr≈ r) = run≈ ck N (env-ext r er)
branch≈ ck M N er (clo≈ _) = wrong
branch≈ ck M N er const≈ = wrong
branch≈ ck M N er (tup≈ _) = wrong

{- The end theorem: for every Clos2 program ------------------------------------}

concretize-correct : ∀ M → Equivalent (S.sem M) (T.sem (concretize-program M))
concretize-correct M = clocked _≈_ obs≈ (λ ck → run≈ ck M env-empty)

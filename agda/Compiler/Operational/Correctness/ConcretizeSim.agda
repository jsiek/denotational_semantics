{-

  Correctness of the concretize pass (Clos2 → Clos3) by a forward
  simulation between their machines (see the design note in
  Smallstep.agda).

  The pass needs no precondition: it is correct for every Clos2 program.
  A Clos2 variable that a closure's code reads past its free variables is
  unbound in the Clos2 machine (the code runs in the argument and the n
  free variables only) and becomes ` 2, which is unbound in the Clos3
  machine (the code runs in the argument and the tuple only).

  The machines run in lock step, except for two places.

  * A free variable of a closure's code, read in one Clos2 step, becomes
    get i ⦅ ` 1 ⦆, which takes three Clos3 steps. So a Clos2 state that
    is about to look up a variable is matched by the Clos3 state that is
    about to project from the tuple (var~), two steps ahead: then both
    machines go wrong at the same time when the variable is unbound. On
    entering a term (enter), the Clos3 machine takes those two steps
    early.

  * Building a closure takes one extra Clos3 step: the free variables are
    evaluated as a tuple, which is then put in a closure (closK).

  Values are related (_≈_) when they agree, except that a Clos2 closure
  of N and the values vs of its free variables is related to a Clos3
  closure of concretize (fv-ref n) N and a tuple ts that holds the same
  values in the opposite order (FV n vs ts): the Clos2 machine collects
  the values as an environment, the free variable bound last first, and
  component fv-index n k of the tuple is the k-th of them.

  Environments are related through the map φ : Var → Ref that concretize
  carries (EnvRel), at every variable: a Clos2 variable x finds a related
  value (or none) in the Clos3 variable or tuple component that φ x names.

-}

module Compiler.Operational.Correctness.ConcretizeSim where

open import NewSigUtil using (ν-n)
open import NewSyntaxUtil using (_,,_; Nil; ⟩_,,_)
import Compiler.Lang.Clos2 as C2
open C2 using (`_; _⦅_⦆; clos-op; app; lit; tuple; get; inl-op; inr-op; case-op; prim;
               cons; clear; bind; ast; ν; ■; Var)
import Compiler.Lang.Clos3 as C3
open import Compiler.Compile.Concretize
open import Compiler.Observation
open import Compiler.Operational.Smallstep
open import Compiler.Operational.Simulation
open import ListUtil
import Compiler.Operational.Machine.Clos2 as S
import Compiler.Operational.Machine.Clos3 as T

open import Compiler.Lang.Prim using (int; bool)
open import Data.Bool using (true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; _∷ʳ_; length; map; replicate; reverse)
open import Data.List.Properties using (unfold-reverse)
open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_; reverse⁺)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe.Relation.Binary.Pointwise as M
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; _<_; _<?_)
open import Data.Nat.Properties using (+-identityʳ; +-suc; ≤-pred; ≮⇒≥; m≤n⇒m<n∨m≡n)
open import Data.Product using (_×_; Σ-syntax; _,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst; subst₂; cong₂)
open import Relation.Nullary using (yes; no)

{- The compiler, on the machines' views of the syntax --------------------------}

conc-body≡ : ∀ n k (a : C2.Arg (ν-n k (ν ■))) → conc-body n k a ≡ concretize (fv-ref n) (S.body k a)
conc-body≡ n zero (bind (ast N)) = refl
conc-body≡ n (suc k) (bind a) = conc-body≡ n k a

conc-list : ∀ {n} φ (args : C2.Args (replicate n ■))
  → args→list (conc-args φ args) ≡ map (concretize φ) (args→list args)
conc-list {zero} φ Nil = refl
conc-list {suc n} φ (M ,, args) = cong (concretize φ M ∷_) (conc-list φ args)

args-length : ∀ {n} (args : C2.Args (replicate n ■)) → length (args→list args) ≡ n
args-length {zero} Nil = refl
args-length {suc n} (M ,, args) = cong suc (args-length args)

{- The simulation relation -----------------------------------------------------}

infix 4 _≈_ _≈k_ _~_

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

data _≈k_ : S.Cont → T.Cont → Set where
  halt : S.halt ≈k T.halt
  appL : ∀ {M φ ρ₂ ρ₃ κ₂ κ₃} → EnvRel φ ρ₂ ρ₃ → κ₂ ≈k κ₃
    → S.appL M ρ₂ κ₂ ≈k T.appL (concretize φ M) ρ₃ κ₃
  appR : ∀ {v w κ₂ κ₃} → v ≈ w → κ₂ ≈k κ₃ → S.appR v κ₂ ≈k T.appR w κ₃
  tupK : ∀ {vs ws Ms φ ρ₂ ρ₃ κ₂ κ₃} → Pointwise _≈_ vs ws → EnvRel φ ρ₂ ρ₃ → κ₂ ≈k κ₃
    → S.tupK vs Ms ρ₂ κ₂ ≈k T.tupK ws (map (concretize φ) Ms) ρ₃ κ₃
  {- evaluating the free variables of a closure, as a tuple in Clos3 -}
  closK : ∀ {n N vs ws Ms φ ρ₂ ρ₃ κ₂ κ₃} → Pointwise _≈_ vs ws → EnvRel φ ρ₂ ρ₃
    → length Ms + suc (length vs) ≡ n → κ₂ ≈k κ₃
    → S.closK N vs Ms ρ₂ κ₂
      ≈k T.tupK ws (map (concretize φ) Ms) ρ₃ (T.closK (concretize (fv-ref n) N) κ₃)
  getK : ∀ {n} {i : Fin n} {κ₂ κ₃} → κ₂ ≈k κ₃ → S.getK i κ₂ ≈k T.getK i κ₃
  inlK : ∀ {κ₂ κ₃} → κ₂ ≈k κ₃ → S.inlK κ₂ ≈k T.inlK κ₃
  inrK : ∀ {κ₂ κ₃} → κ₂ ≈k κ₃ → S.inrK κ₂ ≈k T.inrK κ₃
  caseK : ∀ {M N φ ρ₂ ρ₃ κ₂ κ₃} → EnvRel φ ρ₂ ρ₃ → κ₂ ≈k κ₃
    → S.caseK M N ρ₂ κ₂ ≈k T.caseK (concretize (ext-ref φ) M) (concretize (ext-ref φ) N) ρ₃ κ₃
  primL : ∀ {p M φ ρ₂ ρ₃ κ₂ κ₃} → EnvRel φ ρ₂ ρ₃ → κ₂ ≈k κ₃
    → S.primL p M ρ₂ κ₂ ≈k T.primL p (concretize φ M) ρ₃ κ₃
  primR : ∀ {p v w κ₂ κ₃} → v ≈ w → κ₂ ≈k κ₃ → S.primR p v κ₂ ≈k T.primR p w κ₃

NotVar : C2.AST → Set
NotVar (` x) = ⊥
NotVar (op ⦅ args ⦆) = ⊤

data _~_ : S.State → T.State → Set where
  eval~ : ∀ {M φ ρ₂ ρ₃ κ₂ κ₃} → NotVar M → EnvRel φ ρ₂ ρ₃ → κ₂ ≈k κ₃
    → S.eval M ρ₂ κ₂ ~ T.eval (concretize φ M) ρ₃ κ₃
  {- a variable, matched by a Clos3 state about to return what it finds -}
  var~ : ∀ {x ρ₂ κ₂ mw κ₃ s₃} → M.Pointwise _≈_ (ρ₂ ‼ x) mw → κ₂ ≈k κ₃
    → T.step s₃ ≡ T.ret? mw κ₃ → S.eval (` x) ρ₂ κ₂ ~ s₃
  ret~ : ∀ {v w κ₂ κ₃} → v ≈ w → κ₂ ≈k κ₃ → S.ret v κ₂ ~ T.ret w κ₃

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

{- the machines collect the values in the same order, and the tuple is
   reversed -}
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

{- The simulation, for any Clos3 program P -------------------------------------}

module _ (P : C3.AST) where

  L₃ = T.sem P

  one : ∀ {s s'} → T.step s ≡ next s' → Plus L₃ s s'
  one eq = plus eq ε

  {- a Clos3 state from which a matching state can be reached -}
  Reach : S.State → T.State → Set
  Reach s₂ s₃ = Σ[ s₃' ∈ T.State ] Star L₃ s₃ s₃' × s₂ ~ s₃'

  after : ∀ {s₂ s₃ s₃'} → Plus L₃ s₃ s₃' → Reach s₂ s₃' → Answers L₃ _~_ (next s₂) s₃
  after π (_ , σ , m) = steps (plus-star π σ) m

  {- answering a lookup or a projection -}
  ret?-answers : ∀ {mv mw κ₂ κ₃ s₃} → M.Pointwise _≈_ mv mw → κ₂ ≈k κ₃
    → T.step s₃ ≡ T.ret? mw κ₃ → Answers L₃ _~_ (S.ret? mv κ₂) s₃
  ret?-answers (M.just r) κ eq = steps (one eq) (ret~ r κ)
  ret?-answers M.nothing κ eq = stops eq

  {- entering a term: a free variable of a closure's code reaches the
     tuple first -}
  enter : ∀ M {φ ρ₂ ρ₃ κ₂ κ₃} → EnvRel φ ρ₂ ρ₃ → κ₂ ≈k κ₃
    → Reach (S.eval M ρ₂ κ₂) (T.eval (concretize φ M) ρ₃ κ₃)
  enter (` x) {φ} {κ₃ = κ₃} er κ with φ x | er x
  ... | var y | p = _ , ε , var~ p κ refl
  ... | prj i y | ts , eq , p =
    _ , refl ◅ cong (λ mv → T.ret? mv (T.getK i κ₃)) eq ◅ ε , var~ p κ refl
  enter (op ⦅ args ⦆) er κ = _ , ε , eval~ tt er κ

  tuple-next~ : ∀ {vs ws Ms φ ρ₂ ρ₃ κ₂ κ₃} → Pointwise _≈_ vs ws → EnvRel φ ρ₂ ρ₃ → κ₂ ≈k κ₃
    → Reach (S.tuple-next vs Ms ρ₂ κ₂) (T.tuple-next ws (map (concretize φ) Ms) ρ₃ κ₃)
  tuple-next~ {Ms = []} rs er κ = _ , ε , ret~ (tup≈ (reverse⁺ rs)) κ
  tuple-next~ {Ms = M ∷ Ms} rs er κ = enter M er (tupK rs er κ)

  clos-next~ : ∀ {n N vs ws Ms φ ρ₂ ρ₃ κ₂ κ₃} → Pointwise _≈_ vs ws → EnvRel φ ρ₂ ρ₃
    → length Ms + length vs ≡ n → κ₂ ≈k κ₃
    → Reach (S.clos-next N vs Ms ρ₂ κ₂)
            (T.tuple-next ws (map (concretize φ) Ms) ρ₃ (T.closK (concretize (fv-ref n) N) κ₃))
  clos-next~ {Ms = []} rs er refl κ = _ , refl ◅ ε , ret~ (clo≈ (pw→FV rs)) κ
  clos-next~ {vs = vs} {Ms = M ∷ Ms} rs er len κ =
    enter M er (closK rs er (trans (+-suc (length Ms) (length vs)) len) κ)

  sim : ∀ {s₂ s₃} → s₂ ~ s₃ → Answers L₃ _~_ (S.step s₂) s₃
  sim (var~ p κ eq) = ret?-answers p κ eq
  sim (eval~ {M = ` x} () _ _)
  sim (eval~ {M = clos-op n ⦅ cons (clear a) fvs ⦆} {φ} {ρ₂} {ρ₃} {κ₂} {κ₃} _ er κ) =
    after (one refl)
      (subst₂ (λ Ns B → Reach (S.clos-next (S.body n a) [] (args→list fvs) ρ₂ κ₂)
                              (T.tuple-next [] Ns ρ₃ (T.closK B κ₃)))
              (sym (conc-list φ fvs)) (sym (conc-body≡ n n a))
              (clos-next~ [] er (trans (+-identityʳ _) (args-length fvs)) κ))
  sim (eval~ {M = app ⦅ L ,, M ,, Nil ⦆} _ er κ) = after (one refl) (enter L er (appL er κ))
  sim (eval~ {M = lit B k ⦅ Nil ⦆} _ er κ) = steps (one refl) (ret~ const≈ κ)
  sim (eval~ {M = tuple n ⦅ args ⦆} {φ} {ρ₂} {ρ₃} {κ₂} {κ₃} _ er κ) =
    after (one refl)
      (subst (λ Ns → Reach (S.tuple-next [] (args→list args) ρ₂ κ₂) (T.tuple-next [] Ns ρ₃ κ₃))
             (sym (conc-list φ args)) (tuple-next~ [] er κ))
  sim (eval~ {M = get i ⦅ M ,, Nil ⦆} _ er κ) = after (one refl) (enter M er (getK κ))
  sim (eval~ {M = inl-op ⦅ M ,, Nil ⦆} _ er κ) = after (one refl) (enter M er (inlK κ))
  sim (eval~ {M = inr-op ⦅ M ,, Nil ⦆} _ er κ) = after (one refl) (enter M er (inrK κ))
  sim (eval~ {M = case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆} _ er κ) =
    after (one refl) (enter L er (caseK er κ))
  sim (eval~ {M = prim p ⦅ L ,, M ,, Nil ⦆} _ er κ) = after (one refl) (enter L er (primL er κ))
  sim (ret~ r halt) = stops (cong stop (sym (obs≈ r)))
  sim (ret~ r@(clo≈ _) (appL {M = M} er κ)) = after (one refl) (enter M er (appR r κ))
  sim (ret~ const≈ (appL er κ)) = stops refl
  sim (ret~ (tup≈ _) (appL er κ)) = stops refl
  sim (ret~ (inl≈ _) (appL er κ)) = stops refl
  sim (ret~ (inr≈ _) (appL er κ)) = stops refl
  sim (ret~ r (appR (clo≈ {N = N} f) κ)) = after (one refl) (enter N (env-clos r f) κ)
  sim (ret~ r (appR const≈ κ)) = stops refl
  sim (ret~ r (appR (tup≈ _) κ)) = stops refl
  sim (ret~ r (appR (inl≈ _) κ)) = stops refl
  sim (ret~ r (appR (inr≈ _) κ)) = stops refl
  sim (ret~ r (tupK rs er κ)) = after (one refl) (tuple-next~ (r ∷ rs) er κ)
  sim (ret~ r (closK rs er len κ)) = after (one refl) (clos-next~ (r ∷ rs) er len κ)
  sim (ret~ (tup≈ rs) (getK {i = i} κ)) = ret?-answers (proj-pw i rs) κ refl
  sim (ret~ (clo≈ _) (getK κ)) = stops refl
  sim (ret~ const≈ (getK κ)) = stops refl
  sim (ret~ (inl≈ _) (getK κ)) = stops refl
  sim (ret~ (inr≈ _) (getK κ)) = stops refl
  sim (ret~ r (inlK κ)) = steps (one refl) (ret~ (inl≈ r) κ)
  sim (ret~ r (inrK κ)) = steps (one refl) (ret~ (inr≈ r) κ)
  sim (ret~ (inl≈ r) (caseK {M = M} er κ)) = after (one refl) (enter M (env-ext r er) κ)
  sim (ret~ (inr≈ r) (caseK {N = N} er κ)) = after (one refl) (enter N (env-ext r er) κ)
  sim (ret~ (clo≈ _) (caseK _ κ)) = stops refl
  sim (ret~ const≈ (caseK _ κ)) = stops refl
  sim (ret~ (tup≈ _) (caseK _ κ)) = stops refl
  sim (ret~ r (primL {M = M} er κ)) = after (one refl) (enter M er (primR r κ))
  sim (ret~ s (primR {p} r κ)) = ret?-answers (prim≈ p r s) κ refl

{- The end theorem: for every Clos2 program ------------------------------------}

init~ : ∀ M → S.eval M [] S.halt ~ T.eval (concretize-program M) [] T.halt
init~ (` x) = var~ M.nothing halt refl
init~ (op ⦅ args ⦆) = eval~ tt env-empty halt

concretize-fsim : ∀ M → FSim (S.sem M) (T.sem (concretize-program M))
concretize-fsim M = plus-simulation _~_ (init~ M) (sim (concretize-program M))

concretize-correct : ∀ M → Equivalent (S.sem M) (T.sem (concretize-program M))
concretize-correct M = equivalent (concretize-fsim M)

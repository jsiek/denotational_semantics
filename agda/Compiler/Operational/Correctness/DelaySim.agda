{-

  Correctness of the delay pass (Clos3 → Clos4) by a forward simulation
  between their machines (see the design note in Smallstep.agda).

  delay turns a closure value into a pair of code and environment, and an
  application app L M into

    let x = L' in app (fst x) (snd x) (shift M')

  So one source step can take several target steps: building a closure
  (pair, fun, then the tuple of free variables), and above all calling
  one, which in Clos4 binds the closure by a let, takes it apart by fst
  and snd and only then evaluates the operand.

  Values are related (_≈_) when they agree, except that a Clos3 closure of
  N and v is related to the Clos4 pair of fun (delay N) and a value
  related to v. The operand of an application is evaluated under one more
  variable (the let-bound closure), so a source term M in environment ρ₁
  is related to the target term rename r (delay M) in ρ₂, where the
  renaming r maps the variables of ρ₁ to related ones in ρ₂ (EnvRel).

  Continuations are related frame by frame, except for appL, the frame
  that waits for the operator. Its target counterpart is the let frame,
  but when a value is returned to it the target first runs the let body
  up to the point where it checks that the value is a pair (fstK). Since
  the source checks that the value is a closure right away, a state
  returning a value to appL is related to that later target state
  (retT), which the target reaches by four administrative steps
  (ret-reach) taken as part of the step that returned the value. Then
  both machines go wrong at the same time on a non-function. (Clos4's own
  check, that the operator is code, comes at the call and always passes
  on delay's output.)

  No precondition is needed: unlike enclose, delay does not depend on
  which variables a term uses, so the end theorem holds for every Clos3
  program, closed or not (a free variable goes wrong in both).

-}

module Compiler.Operational.Correctness.DelaySim where

open import Data.Fin using (Fin)
open import Data.List using ([]; _∷_; replicate)
open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_; reverse⁺)
open import Compiler.Lang.Prim using (int; bool)
open import Data.Bool using (true; false)
open import Data.Maybe using (just; nothing)
import Data.Maybe.Relation.Binary.Pointwise as M
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; Σ-syntax; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂)
open import NewSyntaxUtil using (_,,_; Nil; ⟩_,,_)
open import Compiler.Lang.Clos3
import Compiler.Lang.Clos4 as C4
open import Compiler.Compile.Delay
open import Compiler.Observation
open import Compiler.Operational.Smallstep
open import Compiler.Operational.Simulation
open import Compiler.Lang.ListUtil
import Compiler.Operational.Machine.Clos3 as S
import Compiler.Operational.Machine.Clos4 as T

open import Compiler.Lang.Rename C4.Op C4.sig
  using (ext; rename; rename-args; shift; rename-fuse; rename-id)

{- The simulation relation -----------------------------------------------------}

infix 4 _≈_ _≈k_ _~_

data _≈_ : S.Val → T.Val → Set where
  clos≈ : ∀ {N v w} → v ≈ w → S.clos N v ≈ T.pair (T.fun (delay N)) w
  const≈ : ∀ {B k} → S.const B k ≈ T.const B k
  tup≈ : ∀ {vs ws} → Pointwise _≈_ vs ws → S.tup vs ≈ T.tup ws
  inl≈ : ∀ {v w} → v ≈ w → S.inl v ≈ T.inl w
  inr≈ : ∀ {v w} → v ≈ w → S.inr v ≈ T.inr w

{- the renaming r takes each variable of ρ₁ to a related one of ρ₂ (and an
   unbound one to an unbound one) -}
data EnvRel (r : ℕ → ℕ) (ρ₁ : S.Env) (ρ₂ : T.Env) : Set where
  env : (∀ x → M.Pointwise _≈_ (ρ₁ ‼ x) (ρ₂ ‼ r x)) → EnvRel r ρ₁ ρ₂

{- the target code of M, under the renaming r -}
Del : (ℕ → ℕ) → AST → C4.AST → Set
Del r M M' = M' ≡ rename r (delay M)

{- what follows the let-bound closure: app (fst x) (snd x) (shift M') -}
snd0 : C4.AST
snd0 = C4.snd-op C4.⦅ C4.` 0 ,, Nil ⦆

app-body : AST → C4.AST
app-body M = C4.app C4.⦅ C4.fst-op C4.⦅ C4.` 0 ,, Nil ⦆ ,, snd0 ,, shift (delay M) ,, Nil ⦆

data _≈k_ : S.Cont → T.Cont → Set where
  halt : S.halt ≈k T.halt
  appL : ∀ {r M ρ₁ ρ₂ κ₁ κ₂} → EnvRel r ρ₁ ρ₂ → κ₁ ≈k κ₂
    → S.appL M ρ₁ κ₁ ≈k T.letK (rename (ext r) (app-body M)) ρ₂ κ₂
  appR : ∀ {N v w κ₁ κ₂} → v ≈ w → κ₁ ≈k κ₂
    → S.appR (S.clos N v) κ₁ ≈k T.appA (T.fun (delay N)) w κ₂
  tupK : ∀ {r vs ws Ms Ms' ρ₁ ρ₂ κ₁ κ₂} → Pointwise _≈_ vs ws → Pointwise (Del r) Ms Ms'
    → EnvRel r ρ₁ ρ₂ → κ₁ ≈k κ₂ → S.tupK vs Ms ρ₁ κ₁ ≈k T.tupK ws Ms' ρ₂ κ₂
  closK : ∀ {N κ₁ κ₂} → κ₁ ≈k κ₂ → S.closK N κ₁ ≈k T.pairR (T.fun (delay N)) κ₂
  getK : ∀ {n} {i : Fin n} {κ₁ κ₂} → κ₁ ≈k κ₂ → S.getK i κ₁ ≈k T.getK i κ₂
  inlK : ∀ {κ₁ κ₂} → κ₁ ≈k κ₂ → S.inlK κ₁ ≈k T.inlK κ₂
  inrK : ∀ {κ₁ κ₂} → κ₁ ≈k κ₂ → S.inrK κ₁ ≈k T.inrK κ₂
  caseK : ∀ {r M N ρ₁ ρ₂ κ₁ κ₂} → EnvRel r ρ₁ ρ₂ → κ₁ ≈k κ₂
    → S.caseK M N ρ₁ κ₁ ≈k T.caseK (rename (ext r) (delay M)) (rename (ext r) (delay N)) ρ₂ κ₂
  primL : ∀ {p r M ρ₁ ρ₂ κ₁ κ₂} → EnvRel r ρ₁ ρ₂ → κ₁ ≈k κ₂
    → S.primL p M ρ₁ κ₁ ≈k T.primL p (rename r (delay M)) ρ₂ κ₂
  primR : ∀ {p v w κ₁ κ₂} → v ≈ w → κ₁ ≈k κ₂ → S.primR p v κ₁ ≈k T.primR p w κ₂

{- the target state related to returning w to κ₁: for appL, the target has
   already run the let body up to taking the first component of w -}
retT : ∀ {κ₁ κ₂} → T.Val → κ₁ ≈k κ₂ → T.State
retT w (appL {r} {M} {ρ₂ = ρ₂} {κ₂ = κ₂} _ _) =
  T.ret w (T.fstK (T.appF snd0 (rename (ext r) (shift (delay M))) (w ∷ ρ₂) κ₂))
retT {κ₂ = κ₂} w _ = T.ret w κ₂

data _~_ : S.State → T.State → Set where
  eval~ : ∀ {r M M' ρ₁ ρ₂ κ₁ κ₂} → Del r M M' → EnvRel r ρ₁ ρ₂ → κ₁ ≈k κ₂
    → S.eval M ρ₁ κ₁ ~ T.eval M' ρ₂ κ₂
  ret~ : ∀ {v w κ₁ κ₂} (k : κ₁ ≈k κ₂) → v ≈ w → S.ret v κ₁ ~ retT w k

{- Related values are observed alike -}
obs≈ : ∀ {v w} → v ≈ w → S.obs v ≡ T.obs w
obs≈-list : ∀ {vs ws} → Pointwise _≈_ vs ws → S.obs-list vs ≡ T.obs-list ws
obs≈ (clos≈ _) = refl
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

{- Related environments ------------------------------------------------------}

look : ∀ {r ρ₁ ρ₂} → EnvRel r ρ₁ ρ₂ → ∀ x → M.Pointwise _≈_ (ρ₁ ‼ x) (ρ₂ ‼ r x)
look (env l) = l

env-ext : ∀ {r ρ₁ ρ₂ v w} → v ≈ w → EnvRel r ρ₁ ρ₂ → EnvRel (ext r) (v ∷ ρ₁) (w ∷ ρ₂)
env-ext r (env l) = env λ { zero → M.just r ; (suc x) → l x }

{- the let-bound closure, which the source does not see -}
env-skip : ∀ {r ρ₁ ρ₂ w} → EnvRel r ρ₁ ρ₂ → EnvRel (λ x → suc (r x)) ρ₁ (w ∷ ρ₂)
env-skip (env l) = env l

{- the environment of a function body: the argument, then the closure's tuple -}
env-body : ∀ {v w u e} → v ≈ w → u ≈ e → EnvRel (λ x → x) (v ∷ u ∷ []) (w ∷ e ∷ [])
env-body r r' = env λ { zero → M.just r ; (suc zero) → M.just r' ; (suc (suc x)) → M.nothing }

del-args : ∀ {n} r (as : Args (replicate n ■))
  → Pointwise (Del r) (args→list as) (args→list (rename-args r (del-map-args as)))
del-args {zero} r Nil = []
del-args {suc n} r (M ,, as) = refl ∷ del-args r as

{- The simulation, for any Clos4 program P -------------------------------------}

module _ (P : C4.AST) where

  L₂ = T.sem P

  one : ∀ {s s'} → T.step s ≡ next s' → Plus L₂ s s'
  one eq = plus eq ε

  {- the administrative steps of the let body, before checking for a pair -}
  ret-reach : ∀ {w κ₁ κ₂} (k : κ₁ ≈k κ₂) → Star L₂ (T.ret w κ₂) (retT w k)
  ret-reach halt = ε
  ret-reach (appL _ _) = refl ◅ refl ◅ refl ◅ refl ◅ ε
  ret-reach (appR _ _) = ε
  ret-reach (tupK _ _ _ _) = ε
  ret-reach (closK _) = ε
  ret-reach (getK _) = ε
  ret-reach (inlK _) = ε
  ret-reach (inrK _) = ε
  ret-reach (caseK _ _) = ε
  ret-reach (primL _ _) = ε
  ret-reach (primR _ _) = ε

  {- answering a step that returns a value -}
  ret-answers : ∀ {s₂ v w κ₁ κ₂} → Plus L₂ s₂ (T.ret w κ₂) → v ≈ w → (k : κ₁ ≈k κ₂)
    → Answers L₂ _~_ (next (S.ret v κ₁)) s₂
  ret-answers π r k = steps (plus-star π (ret-reach k)) (ret~ k r)

  {- answering a lookup or a projection -}
  ret?-answers : ∀ {mv mw κ₁ κ₂ s₂} → M.Pointwise _≈_ mv mw → κ₁ ≈k κ₂
    → T.step s₂ ≡ T.ret? mw κ₂ → Answers L₂ _~_ (S.ret? mv κ₁) s₂
  ret?-answers (M.just r) k eq = ret-answers (one eq) r k
  ret?-answers M.nothing k eq = stops eq

  tuple-next~ : ∀ {r vs ws Ms Ms' ρ₁ ρ₂ κ₁ κ₂} → Pointwise _≈_ vs ws
    → Pointwise (Del r) Ms Ms' → EnvRel r ρ₁ ρ₂ → κ₁ ≈k κ₂
    → Σ[ s₂ ∈ T.State ] Star L₂ (T.tuple-next ws Ms' ρ₂ κ₂) s₂
        × S.tuple-next vs Ms ρ₁ κ₁ ~ s₂
  tuple-next~ rs [] ρ k = _ , ret-reach k , ret~ k (tup≈ (reverse⁺ rs))
  tuple-next~ rs (d ∷ ds) ρ k = _ , ε , eval~ d ρ (tupK rs ds ρ k)

  sim : ∀ {s₁ s₂} → s₁ ~ s₂ → Answers L₂ _~_ (S.step s₁) s₂
  sim (eval~ {M = ` x} refl ρ k) = ret?-answers (look ρ x) k refl
  sim (eval~ {r} {M = clos-op n ⦅ cons (clear (bind (bind (ast N)))) fvs ⦆} refl ρ k)
    with tuple-next~ [] (del-args r fvs) ρ (closK {N} k)
  ... | s₂ , σ , m = steps (plus refl (refl ◅ refl ◅ refl ◅ σ)) m
  sim (eval~ {M = app ⦅ L ,, M ,, Nil ⦆} refl ρ k) = steps (one refl) (eval~ refl ρ (appL ρ k))
  sim (eval~ {M = lit B k ⦅ Nil ⦆} refl ρ κ) = ret-answers (one refl) const≈ κ
  sim (eval~ {r} {M = tuple n ⦅ as ⦆} refl ρ k) with tuple-next~ [] (del-args r as) ρ k
  ... | s₂ , σ , m = steps (plus refl σ) m
  sim (eval~ {M = get i ⦅ M ,, Nil ⦆} refl ρ k) = steps (one refl) (eval~ refl ρ (getK k))
  sim (eval~ {M = inl-op ⦅ M ,, Nil ⦆} refl ρ k) = steps (one refl) (eval~ refl ρ (inlK k))
  sim (eval~ {M = inr-op ⦅ M ,, Nil ⦆} refl ρ k) = steps (one refl) (eval~ refl ρ (inrK k))
  sim (eval~ {M = case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆} refl ρ k) =
    steps (one refl) (eval~ refl ρ (caseK ρ k))
  sim (eval~ {M = prim p ⦅ L ,, M ,, Nil ⦆} refl ρ k) = steps (one refl) (eval~ refl ρ (primL ρ k))
  sim (ret~ halt r) = stops (cong stop (sym (obs≈ r)))
  {- calling a closure: fst, then snd, then evaluate the operand -}
  sim (ret~ (appL {r} {M} ρ k) (clos≈ r')) =
    steps (plus refl (refl ◅ refl ◅ refl ◅ refl ◅ refl ◅ ε))
          (eval~ (rename-fuse (ext r) suc (delay M)) (env-skip ρ) (appR r' k))
  sim (ret~ (appL ρ k) const≈) = stops refl
  sim (ret~ (appL ρ k) (tup≈ _)) = stops refl
  sim (ret~ (appL ρ k) (inl≈ _)) = stops refl
  sim (ret~ (appL ρ k) (inr≈ _)) = stops refl
  sim (ret~ (appR {N} r' k) r) =
    steps (one refl) (eval~ (sym (rename-id (delay N))) (env-body r r') k)
  sim (ret~ (tupK rs ds ρ k) r) with tuple-next~ (r ∷ rs) ds ρ k
  ... | s₂ , σ , m = steps (plus refl σ) m
  sim (ret~ (closK k) r) = ret-answers (one refl) (clos≈ r) k
  sim (ret~ (getK {i = i} k) (tup≈ rs)) = ret?-answers (proj-pw i rs) k refl
  sim (ret~ (getK k) (clos≈ _)) = stops refl
  sim (ret~ (getK k) const≈) = stops refl
  sim (ret~ (getK k) (inl≈ _)) = stops refl
  sim (ret~ (getK k) (inr≈ _)) = stops refl
  sim (ret~ (inlK k) r) = ret-answers (one refl) (inl≈ r) k
  sim (ret~ (inrK k) r) = ret-answers (one refl) (inr≈ r) k
  sim (ret~ (caseK ρ k) (inl≈ r)) = steps (one refl) (eval~ refl (env-ext r ρ) k)
  sim (ret~ (caseK ρ k) (inr≈ r)) = steps (one refl) (eval~ refl (env-ext r ρ) k)
  sim (ret~ (caseK ρ k) (clos≈ _)) = stops refl
  sim (ret~ (caseK ρ k) const≈) = stops refl
  sim (ret~ (caseK ρ k) (tup≈ _)) = stops refl
  sim (ret~ (primL ρ k) r) = steps (one refl) (eval~ refl ρ (primR r k))
  sim (ret~ (primR {p} r k) s) = ret?-answers (prim≈ p r s) k refl

{- The end theorem: for every Clos3 program -----------------------------------}

delay-fsim : ∀ M → FSim (S.sem M) (T.sem (delay M))
delay-fsim M =
  plus-simulation _~_
    (eval~ (sym (rename-id (delay M))) (env (λ x → M.nothing)) halt)
    (sim (delay M))

delay-correct : ∀ M → Equivalent (S.sem M) (T.sem (delay M))
delay-correct M = equivalent (delay-fsim M)

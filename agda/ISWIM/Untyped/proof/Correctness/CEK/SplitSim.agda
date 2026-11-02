{-

  Correctness of the split pass (Clos3 → Clos4) by a forward simulation
  between their machines (see the design note in Semantics/CEK/Smallstep.agda).

  split turns a closure value into a pair of code and environment, and an
  application app L M into

    let x = L' in app (fst x) (snd x) (shift M')

  So one source step can take several target steps: building a closure
  (pair, fun, then the tuple of free variables), and above all calling
  one, which in Clos4 binds the closure by a let, takes it apart by fst
  and snd and only then evaluates the operand.

  Values are related (_≈_) when they agree, except that a Clos3 closure of
  N and v is related to the Clos4 pair of fun (split N) and a value
  related to v. The operand of an application is evaluated under one more
  variable (the let-bound closure), so a source term M in environment ρ₁
  is related to the target term rename r (split M) in ρ₂, where the
  renaming r maps the variables of ρ₁ to related ones in ρ₂ (EnvRel).

  Continuations are related frame by frame, except for appL, the frame
  that waits for the operator. Its target counterpart is the let frame,
  but when a value is returned to it the target first runs the let body
  up to the point where it checks that the value is a pair (fstK). Since
  the source checks that the value is a closure right away, a state
  returning a value to appL is related to that later target state
  (retT), which the target reaches by four administrative steps
  (ret-reach) taken as part of the step that returned the value. Then
  both machines error at the same time on a non-function. (Clos4's own
  check, that the operator is code, comes at the call and always passes
  on split's output.)

  No precondition is needed: unlike capture, split does not depend on
  which variables a term uses, so the end theorem holds for every Clos3
  program, closed or not (a free variable errors in both).

-}

module Untyped.proof.Correctness.CEK.SplitSim where

open import Data.Fin using (Fin)
open import Data.List using ([]; _∷_; replicate)
open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_; reverse⁺)
open import Language.Prim using (int; bool)
open import Data.Bool using (true; false)
open import Data.Maybe using (just; nothing)
import Data.Maybe.Relation.Binary.Pointwise as M
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; Σ-syntax; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂)
open import Framework.Syntax.SyntaxUtil using (_,,_; Nil; ⟩_,,_)
open import Untyped.Language.Clos3
import Untyped.Language.Clos4 as C4
open import Untyped.Compiler.Split
open import Semantics.Observation
open import proof.Semantics.CEK.Smallstep
open import proof.Semantics.CEK.Simulation
open import proof.Framework.ListUtil
import Untyped.Semantics.CEK.Clos3 as S
import Untyped.Semantics.CEK.Clos4 as T

open import proof.Framework.Syntax.Rename C4.Op C4.sig
  using (ext; rename; rename-args; shift; rename-fuse; rename-id)

{- The simulation relation -----------------------------------------------------}

infix 4 _≈_ _≈k_ _~_

data _≈_ : S.Val → T.Val → Set where
  clos≈ : ∀ {N v w} → v ≈ w → S.clos N v ≈ T.pair (T.fun (split N)) w
  const≈ : ∀ {B k} → S.const B k ≈ T.const B k
  tup≈ : ∀ {vs ws} → Pointwise _≈_ vs ws → S.tup vs ≈ T.tup ws
  inl≈ : ∀ {v w} → v ≈ w → S.inl v ≈ T.inl w
  inr≈ : ∀ {v w} → v ≈ w → S.inr v ≈ T.inr w

{- the renaming r takes each variable of ρ₁ to a related one of ρ₂ (and an
   unbound one to an unbound one) -}
open import proof.Framework.Syntax.EnvRel C4.Op C4.sig using (module Rel)
open Rel _≈_ public

{- the target code of M, under the renaming r -}
Del : (ℕ → ℕ) → AST → C4.AST → Set
Del r M M' = M' ≡ rename r (split M)

{- what follows the let-bound closure: app (fst x) (snd x) (shift M') -}
snd0 : C4.AST
snd0 = C4.snd-op C4.⦅ C4.` 0 ,, Nil ⦆

app-body : AST → C4.AST
app-body M = C4.app C4.⦅ C4.fst-op C4.⦅ C4.` 0 ,, Nil ⦆ ,, snd0 ,, shift (split M) ,, Nil ⦆

data _≈k_ : S.Cont → T.Cont → Set where
  halt : S.halt ≈k T.halt
  appL : ∀ {r M ρ₁ ρ₂ κ₁ κ₂} → EnvRel r ρ₁ ρ₂ → κ₁ ≈k κ₂
    → S.appL M ρ₁ κ₁ ≈k T.letK (rename (ext r) (app-body M)) ρ₂ κ₂
  appR : ∀ {N v w κ₁ κ₂} → v ≈ w → κ₁ ≈k κ₂
    → S.appR (S.clos N v) κ₁ ≈k T.appA (T.fun (split N)) w κ₂
  tupK : ∀ {r vs ws Ms Ms' ρ₁ ρ₂ κ₁ κ₂} → Pointwise _≈_ vs ws → Pointwise (Del r) Ms Ms'
    → EnvRel r ρ₁ ρ₂ → κ₁ ≈k κ₂ → S.tupK vs Ms ρ₁ κ₁ ≈k T.tupK ws Ms' ρ₂ κ₂
  closK : ∀ {N κ₁ κ₂} → κ₁ ≈k κ₂ → S.closK N κ₁ ≈k T.pairR (T.fun (split N)) κ₂
  getK : ∀ {n} {i : Fin n} {κ₁ κ₂} → κ₁ ≈k κ₂ → S.getK i κ₁ ≈k T.getK i κ₂
  inlK : ∀ {κ₁ κ₂} → κ₁ ≈k κ₂ → S.inlK κ₁ ≈k T.inlK κ₂
  inrK : ∀ {κ₁ κ₂} → κ₁ ≈k κ₂ → S.inrK κ₁ ≈k T.inrK κ₂
  caseK : ∀ {r M N ρ₁ ρ₂ κ₁ κ₂} → EnvRel r ρ₁ ρ₂ → κ₁ ≈k κ₂
    → S.caseK M N ρ₁ κ₁ ≈k T.caseK (rename (ext r) (split M)) (rename (ext r) (split N)) ρ₂ κ₂
  primL : ∀ {p r M ρ₁ ρ₂ κ₁ κ₂} → EnvRel r ρ₁ ρ₂ → κ₁ ≈k κ₂
    → S.primL p M ρ₁ κ₁ ≈k T.primL p (rename r (split M)) ρ₂ κ₂
  primR : ∀ {p v w κ₁ κ₂} → v ≈ w → κ₁ ≈k κ₂ → S.primR p v κ₁ ≈k T.primR p w κ₂
  letK : ∀ {r N ρ₁ ρ₂ κ₁ κ₂} → EnvRel r ρ₁ ρ₂ → κ₁ ≈k κ₂
    → S.letK N ρ₁ κ₁ ≈k T.letK (rename (ext r) (split N)) ρ₂ κ₂

{- the target state related to returning w to κ₁: for appL, the target has
   already run the let body up to taking the first component of w -}
retT : ∀ {κ₁ κ₂} → T.Val → κ₁ ≈k κ₂ → T.State
retT w (appL {r} {M} {ρ₂ = ρ₂} {κ₂ = κ₂} _ _) =
  T.ret w (T.fstK (T.appF snd0 (rename (ext r) (shift (split M))) (w ∷ ρ₂) κ₂))
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
  ret-reach (letK _ _) = ε

  {- returning a value: the target runs on to retT (ret-reach) -}
  ret~' : ∀ {v w κ₁ κ₂} → v ≈ w → (k : κ₁ ≈k κ₂) → Reach L₂ _~_ (S.ret v κ₁) (T.ret w κ₂)
  ret~' r k = _ , ret-reach k , ret~ k r

  tuple-next~ : ∀ {r vs ws Ms Ms' ρ₁ ρ₂ κ₁ κ₂} → Pointwise _≈_ vs ws
    → Pointwise (Del r) Ms Ms' → EnvRel r ρ₁ ρ₂ → κ₁ ≈k κ₂
    → Reach L₂ _~_ (S.tuple-next vs Ms ρ₁ κ₁) (T.tuple-next ws Ms' ρ₂ κ₂)
  tuple-next~ rs [] ρ k = ret~' (tup≈ (reverse⁺ rs)) k
  tuple-next~ rs (d ∷ ds) ρ k = _ , ε , eval~ d ρ (tupK rs ds ρ k)

  sim : ∀ {s₁ s₂} → s₁ ~ s₂ → Answers L₂ _~_ (S.step s₁) s₂
  sim (eval~ {M = ` x} refl ρ k) = next?-reach (look ρ x) (λ r → ret~' r k) refl
  sim (eval~ {r} {M = clos-op n ⦅ cons (clear (bind (bind (ast N)))) fvs ⦆} refl ρ k)
    with tuple-next~ [] (del-args r fvs) ρ (closK {N} k)
  ... | s₂ , σ , m = after refl (s₂ , refl ◅ refl ◅ refl ◅ σ , m)
  sim (eval~ {M = app ⦅ L ,, M ,, Nil ⦆} refl ρ k) = steps₁ refl (eval~ refl ρ (appL ρ k))
  sim (eval~ {M = lit B k ⦅ Nil ⦆} refl ρ κ) = after refl (ret~' const≈ κ)
  sim (eval~ {r} {M = tuple n ⦅ as ⦆} refl ρ k) = after refl (tuple-next~ [] (del-args r as) ρ k)
  sim (eval~ {M = get i ⦅ M ,, Nil ⦆} refl ρ k) = steps₁ refl (eval~ refl ρ (getK k))
  sim (eval~ {M = inl-op ⦅ M ,, Nil ⦆} refl ρ k) = steps₁ refl (eval~ refl ρ (inlK k))
  sim (eval~ {M = inr-op ⦅ M ,, Nil ⦆} refl ρ k) = steps₁ refl (eval~ refl ρ (inrK k))
  sim (eval~ {M = case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆} refl ρ k) =
    steps₁ refl (eval~ refl ρ (caseK ρ k))
  sim (eval~ {M = prim p ⦅ L ,, M ,, Nil ⦆} refl ρ k) = steps₁ refl (eval~ refl ρ (primL ρ k))
  sim (eval~ {M = let-op ⦅ M ,, ⟩ N ,, Nil ⦆} refl ρ k) = steps₁ refl (eval~ refl ρ (letK ρ k))
  sim (ret~ halt r) = stops (cong stop (sym (obs≈ r)))
  {- calling a closure: fst, then snd, then evaluate the operand -}
  sim (ret~ (appL {r} {M} ρ k) (clos≈ r')) =
    steps (plus refl (refl ◅ refl ◅ refl ◅ refl ◅ refl ◅ ε))
          (eval~ (rename-fuse (ext r) suc (split M)) (env-skip ρ) (appR r' k))
  sim (ret~ (appL ρ k) const≈) = stops refl
  sim (ret~ (appL ρ k) (tup≈ _)) = stops refl
  sim (ret~ (appL ρ k) (inl≈ _)) = stops refl
  sim (ret~ (appL ρ k) (inr≈ _)) = stops refl
  sim (ret~ (appR {N} r' k) r) =
    steps₁ refl (eval~ (sym (rename-id (split N))) (env-body r r') k)
  sim (ret~ (tupK rs ds ρ k) r) = after refl (tuple-next~ (r ∷ rs) ds ρ k)
  sim (ret~ (closK k) r) = after refl (ret~' (clos≈ r) k)
  sim (ret~ (getK {i = i} k) (tup≈ rs)) = next?-reach (proj-pw i rs) (λ r → ret~' r k) refl
  sim (ret~ (getK k) (clos≈ _)) = stops refl
  sim (ret~ (getK k) const≈) = stops refl
  sim (ret~ (getK k) (inl≈ _)) = stops refl
  sim (ret~ (getK k) (inr≈ _)) = stops refl
  sim (ret~ (inlK k) r) = after refl (ret~' (inl≈ r) k)
  sim (ret~ (inrK k) r) = after refl (ret~' (inr≈ r) k)
  sim (ret~ (caseK ρ k) (inl≈ r)) = steps₁ refl (eval~ refl (env-ext r ρ) k)
  sim (ret~ (caseK ρ k) (inr≈ r)) = steps₁ refl (eval~ refl (env-ext r ρ) k)
  sim (ret~ (caseK ρ k) (clos≈ _)) = stops refl
  sim (ret~ (caseK ρ k) const≈) = stops refl
  sim (ret~ (caseK ρ k) (tup≈ _)) = stops refl
  sim (ret~ (primL ρ k) r) = steps₁ refl (eval~ refl ρ (primR r k))
  sim (ret~ (primR {p} r k) s) = next?-reach (prim≈ p r s) (λ r → ret~' r k) refl
  sim (ret~ (letK ρ k) r) = steps₁ refl (eval~ refl (env-ext r ρ) k)

{- The end theorem: for every Clos3 program -----------------------------------}

split-fsim : ∀ M → FSim (S.sem M) (T.sem (split M))
split-fsim M =
  plus-simulation _~_
    (eval~ (sym (rename-id (split M))) (env (λ x → M.nothing)) halt)
    (sim (split M))

split-correct : ∀ M → Equivalent (S.sem M) (T.sem (split M))
split-correct M = equivalent (split-fsim M)

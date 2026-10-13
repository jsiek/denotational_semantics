{-

  An experiment, for comparison with DelaySim.agda: the backward direction
  of the delay pass (Clos3 → Clos4) proved directly, by a backward
  simulation (Backward.agda), without the determinism of either machine.
  This is what a non-deterministic language would have to pay.

  The relations on values, environments and continuations are those of
  the forward simulation (imported from DelaySim). What changes is the
  state relation: the target moves, and the source answers each target
  step. Where the target takes administrative steps for one source step,
  the source waits at its state, and the index of the match (the number of
  target steps left before the source moves) decreases:

  * building a closure (clos-…~): eval of fun, return of the code to pairL,
    then eval of the tuple of free variables; the source moves (to
    evaluating its free variables) when the target does.
  * calling a closure, when its value w was returned to the let frame
    (let-…~): the let body, fst, the variable 0, then the check that w is
    a pair, at which point both machines go wrong on a non-function;
  * and for a pair (call-…~): the code returned to appF, snd, the variable
    0, the environment returned to appE; the source moves (to evaluating
    the operand) when the target does.

  Every other target step is answered by one source step.

-}

module proof.Correctness.CEK.DelayBackSim where

open import Data.List using (List; []; _∷_; replicate)
open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_; reverse⁺)
import Data.Maybe.Relation.Binary.Pointwise as M
open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (Σ-syntax; _,_; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong)

open import Framework.Syntax.SyntaxUtil using (_,,_; Nil; ⟩_,,_)
open import Language.Clos3
import Language.Clos4 as C4
open import Compiler.Delay
open import Semantics.Observation
open import proof.Semantics.CEK.Smallstep
open import proof.Semantics.CEK.Backward
open import proof.Framework.ListUtil
import Semantics.CEK.Clos3 as S
import Semantics.CEK.Clos4 as T
open import proof.Correctness.CEK.DelaySim
  using (_≈_; clos≈; const≈; tup≈; inl≈; inr≈; EnvRel; env; Del; snd0; app-body;
         _≈k_; halt; appL; appR; tupK; closK; getK; inlK; inrK; caseK;
         primL; primR; obs≈; prim≈; look; env-ext; env-skip; env-body; del-args)

open import proof.Framework.Syntax.Rename C4.Op C4.sig
  using (ext; rename; rename-args; shift; rename-fuse; rename-id)

{- The target states between two source steps ----------------------------------}

{- the operand of an application, under the let-bound closure -}
opd : (ℕ → ℕ) → AST → C4.AST
opd r M = rename (ext r) (shift (delay M))

{- the continuations of the target's fst and snd, in the let body, where w
   is the let-bound closure and f its code -}
κF : (ℕ → ℕ) → AST → T.Val → T.Env → T.Cont → T.Cont
κF r M w ρ₂ κ₂ = T.appF snd0 (opd r M) (w ∷ ρ₂) κ₂

κE : (ℕ → ℕ) → AST → T.Val → T.Val → T.Env → T.Cont → T.Cont
κE r M f w ρ₂ κ₂ = T.appE f (opd r M) (w ∷ ρ₂) κ₂

{- the code and the tuple of free variables of a closure -}
funT : AST → C4.AST
funT N = C4.fun-op C4.⦅ C4.cons (C4.clear (C4.bind (C4.bind (C4.ast (delay N))))) C4.nil ⦆

tupT : ∀ {n} → (ℕ → ℕ) → Args (replicate n ■) → C4.AST
tupT {n} r fvs = C4.tuple n C4.⦅ rename-args r (del-map-args fvs) ⦆

{- The simulation relation, indexed by the target steps left before the
   source moves ------------------------------------------------------------------}

data Match : ℕ → S.State → T.State → Set where
  eval~ : ∀ {r M M' ρ₁ ρ₂ κ₁ κ₂} → Del r M M' → EnvRel r ρ₁ ρ₂ → κ₁ ≈k κ₂
    → Match 3 (S.eval M ρ₁ κ₁) (T.eval M' ρ₂ κ₂)
  ret~ : ∀ {v w κ₁ κ₂} → κ₁ ≈k κ₂ → v ≈ w → Match 9 (S.ret v κ₁) (T.ret w κ₂)

  {- building a closure: the source waits at S.eval (clos-op …) -}
  clos-fun~ : ∀ {r n N fvs ρ₁ ρ₂ κ₁ κ₂} → EnvRel r ρ₁ ρ₂ → κ₁ ≈k κ₂
    → Match 2 (S.eval (clos-op n ⦅ cons (clear (bind (bind (ast N)))) fvs ⦆) ρ₁ κ₁)
              (T.eval (funT N) ρ₂ (T.pairL (tupT r fvs) ρ₂ κ₂))
  clos-code~ : ∀ {r n N fvs ρ₁ ρ₂ κ₁ κ₂} → EnvRel r ρ₁ ρ₂ → κ₁ ≈k κ₂
    → Match 1 (S.eval (clos-op n ⦅ cons (clear (bind (bind (ast N)))) fvs ⦆) ρ₁ κ₁)
              (T.ret (T.fun (delay N)) (T.pairL (tupT r fvs) ρ₂ κ₂))
  clos-env~ : ∀ {r n N fvs ρ₁ ρ₂ κ₁ κ₂} → EnvRel r ρ₁ ρ₂ → κ₁ ≈k κ₂
    → Match 0 (S.eval (clos-op n ⦅ cons (clear (bind (bind (ast N)))) fvs ⦆) ρ₁ κ₁)
              (T.eval (tupT r fvs) ρ₂ (T.pairR (T.fun (delay N)) κ₂))

  {- calling a closure: the source waits at S.ret v (appL M ρ₁ κ₁) while
     the target runs the let body up to checking that w is a pair -}
  let-body~ : ∀ {r M ρ₁ ρ₂ κ₁ κ₂ v w} → EnvRel r ρ₁ ρ₂ → κ₁ ≈k κ₂ → v ≈ w
    → Match 8 (S.ret v (S.appL M ρ₁ κ₁)) (T.eval (rename (ext r) (app-body M)) (w ∷ ρ₂) κ₂)
  let-fst~ : ∀ {r M ρ₁ ρ₂ κ₁ κ₂ v w} → EnvRel r ρ₁ ρ₂ → κ₁ ≈k κ₂ → v ≈ w
    → Match 7 (S.ret v (S.appL M ρ₁ κ₁))
              (T.eval (C4.fst-op C4.⦅ C4.` 0 ,, Nil ⦆) (w ∷ ρ₂) (κF r M w ρ₂ κ₂))
  let-var~ : ∀ {r M ρ₁ ρ₂ κ₁ κ₂ v w} → EnvRel r ρ₁ ρ₂ → κ₁ ≈k κ₂ → v ≈ w
    → Match 6 (S.ret v (S.appL M ρ₁ κ₁)) (T.eval (C4.` 0) (w ∷ ρ₂) (T.fstK (κF r M w ρ₂ κ₂)))
  let-chk~ : ∀ {r M ρ₁ ρ₂ κ₁ κ₂ v w} → EnvRel r ρ₁ ρ₂ → κ₁ ≈k κ₂ → v ≈ w
    → Match 5 (S.ret v (S.appL M ρ₁ κ₁)) (T.ret w (T.fstK (κF r M w ρ₂ κ₂)))

  {- and, for a closure, takes it apart -}
  call-code~ : ∀ {r M N ρ₁ ρ₂ κ₁ κ₂ v e} → EnvRel r ρ₁ ρ₂ → κ₁ ≈k κ₂ → v ≈ e
    → Match 4 (S.ret (S.clos N v) (S.appL M ρ₁ κ₁))
              (T.ret (T.fun (delay N)) (κF r M (T.pair (T.fun (delay N)) e) ρ₂ κ₂))
  call-snd~ : ∀ {r M N ρ₁ ρ₂ κ₁ κ₂ v e} → EnvRel r ρ₁ ρ₂ → κ₁ ≈k κ₂ → v ≈ e
    → Match 3 (S.ret (S.clos N v) (S.appL M ρ₁ κ₁))
              (T.eval snd0 (T.pair (T.fun (delay N)) e ∷ ρ₂)
                 (κE r M (T.fun (delay N)) (T.pair (T.fun (delay N)) e) ρ₂ κ₂))
  call-var~ : ∀ {r M N ρ₁ ρ₂ κ₁ κ₂ v e} → EnvRel r ρ₁ ρ₂ → κ₁ ≈k κ₂ → v ≈ e
    → Match 2 (S.ret (S.clos N v) (S.appL M ρ₁ κ₁))
              (T.eval (C4.` 0) (T.pair (T.fun (delay N)) e ∷ ρ₂)
                 (T.sndK (κE r M (T.fun (delay N)) (T.pair (T.fun (delay N)) e) ρ₂ κ₂)))
  call-chk~ : ∀ {r M N ρ₁ ρ₂ κ₁ κ₂ v e} → EnvRel r ρ₁ ρ₂ → κ₁ ≈k κ₂ → v ≈ e
    → Match 1 (S.ret (S.clos N v) (S.appL M ρ₁ κ₁))
              (T.ret (T.pair (T.fun (delay N)) e)
                 (T.sndK (κE r M (T.fun (delay N)) (T.pair (T.fun (delay N)) e) ρ₂ κ₂)))
  call-env~ : ∀ {r M N ρ₁ ρ₂ κ₁ κ₂ v e} → EnvRel r ρ₁ ρ₂ → κ₁ ≈k κ₂ → v ≈ e
    → Match 0 (S.ret (S.clos N v) (S.appL M ρ₁ κ₁))
              (T.ret e (κE r M (T.fun (delay N)) (T.pair (T.fun (delay N)) e) ρ₂ κ₂))

{- The simulation, for any Clos3 program P -------------------------------------}

module _ (P : AST) where

  L₁ = S.sem P

  one : ∀ {s s'} → S.step s ≡ next s' → Plus L₁ s s'
  one eq = plus eq ε

  {- answering a lookup or a projection -}
  ret?-reflects : ∀ {i s₁ mv mw κ₁ κ₂} → M.Pointwise _≈_ mv mw → κ₁ ≈k κ₂
    → S.step s₁ ≡ S.ret? mv κ₁ → Reflects L₁ Match i s₁ (T.ret? mw κ₂)
  ret?-reflects (M.just r) k eq = steps (one eq) (ret~ k r)
  ret?-reflects M.nothing k eq = stops ε eq

  tuple-next~ : ∀ {r vs ws Ms Ms' ρ₁ ρ₂ κ₁ κ₂} → Pointwise _≈_ vs ws
    → Pointwise (Del r) Ms Ms' → EnvRel r ρ₁ ρ₂ → κ₁ ≈k κ₂
    → Σ[ n ∈ ℕ ] Match n (S.tuple-next vs Ms ρ₁ κ₁) (T.tuple-next ws Ms' ρ₂ κ₂)
  tuple-next~ rs [] ρ k = _ , ret~ k (tup≈ (reverse⁺ rs))
  tuple-next~ rs (d ∷ ds) ρ k = _ , eval~ d ρ (tupK rs ds ρ k)

  wait = ≤-refl

  sim : ∀ {i s₁ s₂} → Match i s₁ s₂ → Reflects L₁ Match i s₁ (T.step s₂)
  sim (eval~ {M = ` x} refl ρ k) = ret?-reflects (look ρ x) k refl
  sim (eval~ {M = clos-op n ⦅ cons (clear (bind (bind (ast N)))) fvs ⦆} refl ρ k) =
    waits wait (clos-fun~ ρ k)
  sim (eval~ {M = app ⦅ L ,, M ,, Nil ⦆} refl ρ k) = steps (one refl) (eval~ refl ρ (appL ρ k))
  sim (eval~ {M = lit B k ⦅ Nil ⦆} refl ρ κ) = steps (one refl) (ret~ κ const≈)
  sim (eval~ {r} {M = tuple n ⦅ as ⦆} refl ρ k) =
    steps (one refl) (proj₂ (tuple-next~ [] (del-args r as) ρ k))
  sim (eval~ {M = get i ⦅ M ,, Nil ⦆} refl ρ k) = steps (one refl) (eval~ refl ρ (getK k))
  sim (eval~ {M = inl-op ⦅ M ,, Nil ⦆} refl ρ k) = steps (one refl) (eval~ refl ρ (inlK k))
  sim (eval~ {M = inr-op ⦅ M ,, Nil ⦆} refl ρ k) = steps (one refl) (eval~ refl ρ (inrK k))
  sim (eval~ {M = case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆} refl ρ k) =
    steps (one refl) (eval~ refl ρ (caseK ρ k))
  sim (eval~ {M = prim p ⦅ L ,, M ,, Nil ⦆} refl ρ k) = steps (one refl) (eval~ refl ρ (primL ρ k))
  sim (ret~ halt r) = stops ε (cong stop (obs≈ r))
  sim (ret~ (appL ρ k) r) = waits wait (let-body~ ρ k r)
  sim (ret~ (appR {N} r' k) r) =
    steps (one refl) (eval~ (sym (rename-id (delay N))) (env-body r r') k)
  sim (ret~ (tupK rs ds ρ k) r) = steps (one refl) (proj₂ (tuple-next~ (r ∷ rs) ds ρ k))
  sim (ret~ (closK k) r) = steps (one refl) (ret~ k (clos≈ r))
  sim (ret~ (getK {i = i} k) (tup≈ rs)) = ret?-reflects (proj-pw i rs) k refl
  sim (ret~ (getK k) (clos≈ _)) = stops ε refl
  sim (ret~ (getK k) const≈) = stops ε refl
  sim (ret~ (getK k) (inl≈ _)) = stops ε refl
  sim (ret~ (getK k) (inr≈ _)) = stops ε refl
  sim (ret~ (inlK k) r) = steps (one refl) (ret~ k (inl≈ r))
  sim (ret~ (inrK k) r) = steps (one refl) (ret~ k (inr≈ r))
  sim (ret~ (caseK ρ k) (inl≈ r)) = steps (one refl) (eval~ refl (env-ext r ρ) k)
  sim (ret~ (caseK ρ k) (inr≈ r)) = steps (one refl) (eval~ refl (env-ext r ρ) k)
  sim (ret~ (caseK ρ k) (clos≈ _)) = stops ε refl
  sim (ret~ (caseK ρ k) const≈) = stops ε refl
  sim (ret~ (caseK ρ k) (tup≈ _)) = stops ε refl
  sim (ret~ (primL ρ k) r) = steps (one refl) (eval~ refl ρ (primR r k))
  sim (ret~ (primR {p} r k) s) = ret?-reflects (prim≈ p r s) k refl
  sim (clos-fun~ ρ k) = waits wait (clos-code~ ρ k)
  sim (clos-code~ ρ k) = waits wait (clos-env~ ρ k)
  sim (clos-env~ {r} {fvs = fvs} ρ k) =
    steps (one refl) (proj₂ (tuple-next~ [] (del-args r fvs) ρ (closK k)))
  sim (let-body~ ρ k r) = waits wait (let-fst~ ρ k r)
  sim (let-fst~ ρ k r) = waits wait (let-var~ ρ k r)
  sim (let-var~ ρ k r) = waits wait (let-chk~ ρ k r)
  sim (let-chk~ ρ k (clos≈ r)) = waits wait (call-code~ ρ k r)
  sim (let-chk~ ρ k const≈) = stops ε refl
  sim (let-chk~ ρ k (tup≈ _)) = stops ε refl
  sim (let-chk~ ρ k (inl≈ _)) = stops ε refl
  sim (let-chk~ ρ k (inr≈ _)) = stops ε refl
  sim (call-code~ ρ k r) = waits wait (call-snd~ ρ k r)
  sim (call-snd~ ρ k r) = waits wait (call-var~ ρ k r)
  sim (call-var~ ρ k r) = waits wait (call-chk~ ρ k r)
  sim (call-chk~ ρ k r) = waits wait (call-env~ ρ k r)
  sim (call-env~ {r} {M} ρ k r') =
    steps (one refl) (eval~ (rename-fuse (ext r) suc (delay M)) (env-skip ρ) (appR r' k))

{- The end theorems: for every Clos3 program -----------------------------------}

delay-bsim : ∀ M → BSim (S.sem M) (T.sem (delay M))
delay-bsim M =
  machine-bsim Match
    (_ , eval~ (sym (rename-id (delay M))) (env (λ x → M.nothing)) halt)
    (sim M)

delay-back-terminates : ∀ M {o} → Terminates (T.sem (delay M)) o → Terminates (S.sem M) o
delay-back-terminates M = backward-terminates (delay-bsim M)

delay-back-diverges : ∀ M → Diverges∞ (T.sem (delay M)) → Diverges∞ (S.sem M)
delay-back-diverges M = backward-diverges (delay-bsim M)

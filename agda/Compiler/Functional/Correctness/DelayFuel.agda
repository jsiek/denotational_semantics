{-

  Correctness of the delay pass (Clos3 → Clos4), clock for clock (see the
  design note in Clock.agda). delay turns an application app L M into

    let x = L' in app (fst x) (snd x) (shift M')

  which calls one function, as the source does, and let does not tick.

  Values are related (_≈_) when they agree, except that a Clos3 closure of
  N and v is related to the Clos4 pair of fun (delay N) and a value
  related to v. The operand M of an application is evaluated under one
  more variable (the let-bound closure), so, as in DelaySim, a source term
  M in ρ₁ is related to the target term rename r (delay M) in ρ₂, where the
  renaming r maps each variable of ρ₁ to a related one of ρ₂ (EnvRel).

  No precondition is needed: the end theorem holds for every Clos3
  program, closed or not (a free variable goes wrong in both).

-}

module Compiler.Functional.Correctness.DelayFuel where

open import NewSyntaxUtil using (_,,_; Nil; ⟩_,,_)
open import Compiler.Lang.Clos3
import Compiler.Lang.Clos4 as C4
open import Compiler.Compile.Delay
open import Compiler.Operational.Observation
open import Compiler.Operational.Machine.Common using (_‼_; proj-pw)
open import Compiler.Operational.Correctness.DelaySim using (module RenameLemmas)
open import Compiler.Functional.Clock
import Compiler.Functional.Interp.Clos3 as S
import Compiler.Functional.Interp.Clos4 as T

open import Compiler.Lang.Rename C4.Op C4.sig using (ext; rename; rename-args; shift)
open RenameLemmas C4.Op C4.sig using (rename-fuse; rename-id)

open import Data.List using (List; []; _∷_; replicate; reverse)
open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_; reverse⁺)
import Data.Maybe.Relation.Binary.Pointwise as M
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂; subst)
open import Function using (_∘_)

{- The relation -----------------------------------------------------------------}

infix 4 _≈_

data _≈_ : S.Val → T.Val → Set where
  clos≈ : ∀ {N v w} → v ≈ w → S.clos N v ≈ T.pair (T.fun (delay N)) w
  const≈ : ∀ {B k} → S.const B k ≈ T.const B k
  tup≈ : ∀ {vs ws} → Pointwise _≈_ vs ws → S.tup vs ≈ T.tup ws
  inl≈ : ∀ {v w} → v ≈ w → S.inl v ≈ T.inl w
  inr≈ : ∀ {v w} → v ≈ w → S.inr v ≈ T.inr w

{- the renaming r takes each variable of ρ₁ to a related one of ρ₂ -}
EnvRel : (ℕ → ℕ) → S.Env → T.Env → Set
EnvRel r ρ₁ ρ₂ = ∀ x → M.Pointwise _≈_ (ρ₁ ‼ x) (ρ₂ ‼ r x)

env-ext : ∀ {r ρ₁ ρ₂ v w} → v ≈ w → EnvRel r ρ₁ ρ₂ → EnvRel (ext r) (v ∷ ρ₁) (w ∷ ρ₂)
env-ext r ρ zero = M.just r
env-ext r ρ (suc x) = ρ x

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

{- Clock for clock ---------------------------------------------------------------}

{- what follows the let-bound closure: app (fst x) (snd x) (shift M') -}
snd0 : C4.AST
snd0 = C4.snd-op C4.⦅ C4.` 0 ,, Nil ⦆

run≈ : ∀ ck r {ρ₁ ρ₂} M → EnvRel r ρ₁ ρ₂
  → RelResult _≈_ (S.eval ck ρ₁ M) (T.eval ck ρ₂ (rename r (delay M)))
args≈ : ∀ ck r {n ρ₁ ρ₂ vs ws} (args : Args (replicate n ■)) → EnvRel r ρ₁ ρ₂
  → Pointwise _≈_ vs ws
  → RelResult (Pointwise _≈_) (S.eval-args ck ρ₁ vs args)
      (T.eval-args ck ρ₂ ws (rename-args r (del-map-args args)))
{- the source checks for a closure; the target takes the first component -}
apply≈ : ∀ ck r {ρ₁ ρ₂ f g} M → EnvRel r ρ₁ ρ₂ → f ≈ g
  → RelResult _≈_ (S.apply ck ρ₁ M f)
      (T.first g >>= T.apply ck (g ∷ ρ₂) snd0 (rename (ext r) (shift (delay M))))
{- under the identity renaming -}
run-id : ∀ ck {ρ₁ ρ₂} M → EnvRel (λ x → x) ρ₁ ρ₂
  → RelResult _≈_ (S.eval ck ρ₁ M) (T.eval ck ρ₂ (delay M))
call≈ : ∀ ck {ρ₁ ρ₂} N → EnvRel (λ x → x) ρ₁ ρ₂
  → RelResult _≈_ (S.call ck N ρ₁) (T.call ck (delay N) ρ₂)
branch≈ : ∀ ck r {ρ₁ ρ₂ v w} M N → EnvRel r ρ₁ ρ₂ → v ≈ w
  → RelResult _≈_ (S.branch ck ρ₁ M N v)
      (T.branch ck ρ₂ (rename (ext r) (delay M)) (rename (ext r) (delay N)) w)

run≈ ck r (` x) ρ = from-maybe-rel (ρ x)
run≈ ck r (clos-op n ⦅ cons (clear (bind (bind (ast N)))) fvs ⦆) ρ =
  clos-rel (args≈ ck r fvs ρ [])
  where
  {- the target builds the tuple, then the pair -}
  clos-rel : ∀ {r₁ r₂} → RelResult (Pointwise _≈_) r₁ r₂
    → RelResult _≈_ (r₁ >>= λ vs → ret (S.clos N (S.tup (reverse vs))))
        ((r₂ >>= λ ws → ret (T.tup (reverse ws))) >>= λ e → ret (T.pair (T.fun (delay N)) e))
  clos-rel timeout = timeout
  clos-rel wrong = wrong
  clos-rel (ret rs) = ret (clos≈ (tup≈ (reverse⁺ rs)))
run≈ ck r (app ⦅ L ,, M ,, Nil ⦆) ρ = bind-rel (run≈ ck r L ρ) (apply≈ ck r M ρ)
run≈ ck r (lit B k ⦅ Nil ⦆) ρ = ret const≈
run≈ ck r (tuple n ⦅ args ⦆) ρ = bind-rel (args≈ ck r args ρ []) (λ rs → ret (tup≈ (reverse⁺ rs)))
run≈ ck r (get i ⦅ M ,, Nil ⦆) ρ = bind-rel (run≈ ck r M ρ) get≈
  where
  get≈ : ∀ {v w} → v ≈ w → RelResult _≈_ (S.project i v) (T.project i w)
  get≈ (tup≈ rs) = from-maybe-rel (proj-pw i rs)
  get≈ (clos≈ _) = wrong
  get≈ const≈ = wrong
  get≈ (inl≈ _) = wrong
  get≈ (inr≈ _) = wrong
run≈ ck r (inl-op ⦅ M ,, Nil ⦆) ρ = bind-rel (run≈ ck r M ρ) (λ v → ret (inl≈ v))
run≈ ck r (inr-op ⦅ M ,, Nil ⦆) ρ = bind-rel (run≈ ck r M ρ) (λ v → ret (inr≈ v))
run≈ ck r (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) ρ =
  bind-rel (run≈ ck r L ρ) (branch≈ ck r M N ρ)

args≈ ck r {zero} Nil ρ rs = ret rs
args≈ ck r {suc n} (M ,, args) ρ rs =
  bind-rel (run≈ ck r M ρ) (λ v → args≈ ck r args ρ (v ∷ rs))

{- the operand sees past the let-bound closure: rename (ext r) ∘ shift = suc ∘ r -}
apply≈ ck r M ρ (clos≈ {N} v) =
  subst (λ M' → RelResult _≈_ _ (T.eval ck _ M' >>= _))
        (sym (rename-fuse (ext r) suc (delay M)))
    (bind-rel (run≈ ck (λ x → suc (r x)) M ρ)
      (λ w → call≈ ck N λ { zero → M.just w ; (suc zero) → M.just v ; (suc (suc x)) → M.nothing }))
apply≈ ck r M ρ const≈ = wrong
apply≈ ck r M ρ (tup≈ _) = wrong
apply≈ ck r M ρ (inl≈ _) = wrong
apply≈ ck r M ρ (inr≈ _) = wrong

call≈ zero N ρ = timeout
call≈ (suc ck) N ρ = run-id ck N ρ

run-id ck {ρ₁} M ρ =
  subst (RelResult _≈_ (S.eval ck ρ₁ M) ∘ T.eval ck _) (rename-id (delay M)) (run≈ ck (λ x → x) M ρ)

branch≈ ck r M N ρ (inl≈ v) = run≈ ck (ext r) M (env-ext v ρ)
branch≈ ck r M N ρ (inr≈ v) = run≈ ck (ext r) N (env-ext v ρ)
branch≈ ck r M N ρ (clos≈ _) = wrong
branch≈ ck r M N ρ const≈ = wrong
branch≈ ck r M N ρ (tup≈ _) = wrong

{- The end theorem: for every Clos3 program -----------------------------------}

delay-correct : ∀ M → Equivalent (S.sem M) (T.sem (delay M))
delay-correct M = clocked _≈_ obs≈ (λ ck → run-id ck {[]} M (λ x → M.nothing))

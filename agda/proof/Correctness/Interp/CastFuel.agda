{-

  Correctness of cast insertion (ISWIM → ISWIMᵀ), clock for clock (see
  the design note in Semantics/Interp/Clock.agda): cast insertion maps
  each application to one, so the interpreters call in lock step.

  An ISWIM value v is related to an ISWIMᵀ value of type Any, dyn G x,
  when x has the flat type G of v's kind (_≈_): a closure of N and ρ to
  a closure of cast (ext r) N under an environment related to ρ through
  the renaming r (Env≈), a tuple to a tuple of related components, and
  so on. Where ISWIM errs on an operand of the wrong kind, the project
  that cast insertion put there fails, at the same point of the run.

-}

module proof.Correctness.Interp.CastFuel where

open import Data.Nat using (ℕ; zero; suc; _<_; s≤s; z≤n)
import Data.Nat as N
open import Framework.Syntax.SyntaxUtil using (_,,_; Nil; ⟩_,,_)
open import Framework.Primitives using (Nat; Int; 𝔹; Unit; Void; Blame)
open import Language.Prim using (sub; eq)
open import Language.ISWIM
open import Framework.Syntax.Scope Op sig using (WS; WS-args)
open import Language.Typed.Type
import Language.Typed.ISWIM as I
open import Compiler.Cast
open import Compiler.EncloseScope using (Closed)
open import proof.Compiler.SimplifyScope using (closed-ws)
open import proof.Compiler.CastScope using (cast-closed-≡)
open import Semantics.Observation using (o-tuple; o-inl; o-inr)
open import Framework.ListUtil using (_‼_; proj; has-length)
open import proof.Semantics.Interp.Clock
open import proof.Framework.VecProj using (proj-pw; proj-bad)
import Semantics.Interp.ISWIM as S
import Semantics.Interp.Typed.ISWIM as T

open import Data.Bool using (true; false)
import Data.Integer as Z
open import Data.Fin using (Fin; fromℕ<) renaming (zero to fz; suc to fs)
open import Data.List using (List; []; _∷_; replicate; reverse; _ʳ++_)
open import Data.List.Properties using (reverse-involutive)
open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_; reverse⁺)
open import Data.Maybe using (just; nothing)
import Data.Maybe.Relation.Binary.Pointwise as M
open import Data.Product using (_,_)
open import Data.Vec using (Vec; []; _∷_; lookup; toList)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; cong; cong₂; subst)
open import Relation.Nullary using (yes; no; does)

{- The relation -------------------------------------------------------------------}

infix 4 _≈_

data _≈_ : S.Val → T.Val Any → Set
Env≈ : ∀ {k k'} → (Fin k → Fin k') → S.Env → T.Env k' → Set

data _≈_ where
  clo≈ : ∀ {k k' N w ρ ρ'} {r : Fin k → Fin k'} → Env≈ r ρ ρ'
    → S.clo N ρ ≈ T.dyn fun (T.pack (T.code (cast (ext r) N w)) (T.tup ρ'))
  const≈ : ∀ {B c} → S.const B c ≈ T.dyn (base B) (T.const c)
  tup≈ : ∀ {n vs} {ws : Vec (T.Val Any) n} → Pointwise _≈_ vs (toList ws) → S.tup vs ≈ T.dyn (tup n) (T.tup ws)
  inl≈ : ∀ {v v'} → v ≈ v' → S.inl v ≈ T.dyn sum (T.inl v')
  inr≈ : ∀ {v v'} → v ≈ v' → S.inr v ≈ T.dyn sum (T.inr v')

Env≈ {k} r ρ ρ' = ∀ x (lt : x < k) → M.Pointwise _≈_ (ρ ‼ x) (just (lookup ρ' (r (fromℕ< lt))))

env-ext : ∀ {k k' ρ ρ' v v'} {r : Fin k → Fin k'} → v ≈ v' → Env≈ r ρ ρ' → Env≈ (ext r) (v ∷ ρ) (v' ∷ ρ')
env-ext r E zero _ = M.just r
env-ext r E (suc x) (s≤s lt) = E x lt

obs≈ : ∀ {v v'} → v ≈ v' → S.obs v ≡ T.obs v'
obs≈-list : ∀ {n vs} {ws : Vec (T.Val Any) n} → Pointwise _≈_ vs (toList ws) → S.obs-list vs ≡ T.obs-vec ws
obs≈ (clo≈ _) = refl
obs≈ const≈ = refl
obs≈ (tup≈ rs) = cong o-tuple (obs≈-list rs)
obs≈ (inl≈ r) = cong o-inl (obs≈ r)
obs≈ (inr≈ r) = cong o-inr (obs≈ r)
obs≈-list {ws = []} [] = refl
obs≈-list {ws = _ ∷ _} (r ∷ rs) = cong₂ _∷_ (obs≈ r) (obs≈-list rs)

{- Primitives: both operands are checked after both are evaluated -}
out≈ : ∀ p n m → S.out (Language.Prim.δ p n m) ≈ T.dyn (out-flat p) (T.δ p (T.const n) (T.const m))
out≈ sub n m = const≈
out≈ eq n m with does (n Z.≟ m)
... | true = inl≈ (tup≈ [])
... | false = inr≈ (tup≈ [])

prim≈ : ∀ p {v v' w w'} → v ≈ v' → w ≈ w'
  → RelResult _≈_ (from-maybe (S.prim? p v w))
      ((T.project? tint v' >>= λ a → T.project? tint w' >>= λ b → ret (T.δ p a b)) >>= λ x → ret (T.dyn (out-flat p) x))
prim≈ p (const≈ {Int}) (const≈ {Int}) = ret (out≈ p _ _)
prim≈ p (const≈ {Int}) (const≈ {Nat}) = error
prim≈ p (const≈ {Int}) (const≈ {𝔹}) = error
prim≈ p (const≈ {Int}) (const≈ {Unit}) = error
prim≈ p (const≈ {Int}) (const≈ {Void}) = error
prim≈ p (const≈ {Int}) (const≈ {Blame}) = error
prim≈ p (const≈ {Int}) (clo≈ _) = error
prim≈ p (const≈ {Int}) (tup≈ _) = error
prim≈ p (const≈ {Int}) (inl≈ _) = error
prim≈ p (const≈ {Int}) (inr≈ _) = error
prim≈ p (const≈ {Nat}) s = error
prim≈ p (const≈ {𝔹}) s = error
prim≈ p (const≈ {Unit}) s = error
prim≈ p (const≈ {Void}) s = error
prim≈ p (const≈ {Blame}) s = error
prim≈ p (clo≈ _) s = error
prim≈ p (tup≈ _) s = error
prim≈ p (inl≈ _) s = error
prim≈ p (inr≈ _) s = error

{- Clock for clock -------------------------------------------------------------------}

{- the values of the components, onto vs, as ISWIM collects them -}
Args≈ : ∀ {n} → List (T.Val Any) → List S.Val → Vec (T.Val Any) n → Set
Args≈ us xs ws = Pointwise _≈_ xs (toList ws ʳ++ us)

run≈ : ∀ ck {k k'} M (w : WS k M) {r : Fin k → Fin k'} {ρ ρ'} → Env≈ r ρ ρ'
  → RelResult _≈_ (S.eval ck ρ M) (T.eval ck ρ' (cast r M w))
args≈ : ∀ ck {k k' n} (Ms : Args (replicate n ■)) (ws : WS-args k Ms) {r : Fin k → Fin k'} {ρ ρ' vs us}
  → Env≈ r ρ ρ' → Pointwise _≈_ vs us
  → RelResult (Args≈ {n} us) (S.eval-args ck ρ vs Ms) (T.evals ck ρ' (casts r Ms ws))
call≈ : ∀ ck {k k' N w ρ ρ' v v'} {r : Fin k → Fin k'} → Env≈ r ρ ρ' → v ≈ v'
  → RelResult _≈_ (S.call ck N (v ∷ ρ)) (T.call ck (T.pack (T.code (cast (ext r) N w)) (T.tup ρ')) v')

run≈ ck (` x) x<k E = from-maybe-rel (E x x<k)
run≈ ck (lam ⦅ ⟩ N ,, Nil ⦆) (w , _) E = ret (clo≈ E)
run≈ ck (app ⦅ L ,, M ,, Nil ⦆) (wL , wM , _) E = bind-rel∘ (run≈ ck L wL E) λ
  { (clo≈ E') → bind-rel (run≈ ck M wM E) (call≈ ck E')
  ; const≈ → error ; (tup≈ _) → error ; (inl≈ _) → error ; (inr≈ _) → error }
run≈ ck (lit B c ⦅ Nil ⦆) _ E = ret const≈
run≈ ck (tuple n ⦅ Ms ⦆) ws E = bind-rel∘ (args≈ ck Ms ws E []) λ {xs} {vs} rs →
  ret (tup≈ (subst (Pointwise _≈_ (reverse xs)) (reverse-involutive (toList vs)) (reverse⁺ rs)))
run≈ ck (get {suc n} i ⦅ M ,, Nil ⦆) (w , _) E = bind-rel∘ (run≈ ck M w E) get≈
  where
  get≈ : ∀ {v v'} → v ≈ v' → RelResult _≈_ (S.project i v) (T.project? (ttup n i) v' >>= λ u → ret (T.nth i u))
  get≈ (tup≈ {n = m} rs) with m N.≟ suc n
  ... | yes refl = from-maybe-rel (proj-pw i rs)
  ... | no ne rewrite proj-bad i ne rs = error
  get≈ (clo≈ _) = error
  get≈ const≈ = error
  get≈ (inl≈ _) = error
  get≈ (inr≈ _) = error
run≈ ck (inl-op ⦅ M ,, Nil ⦆) (w , _) E = bind-rel∘ (run≈ ck M w E) λ r → ret (inl≈ r)
run≈ ck (inr-op ⦅ M ,, Nil ⦆) (w , _) E = bind-rel∘ (run≈ ck M w E) λ r → ret (inr≈ r)
run≈ ck (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) (wL , wM , wN , _) E = bind-rel∘ (run≈ ck L wL E) λ
  { (inl≈ r) → run≈ ck M wM (env-ext r E) ; (inr≈ r) → run≈ ck N wN (env-ext r E)
  ; (clo≈ _) → error ; const≈ → error ; (tup≈ _) → error }
run≈ ck (prim p ⦅ L ,, M ,, Nil ⦆) (wL , wM , _) E =
  bind-rel (run≈ ck L wL E) λ r → bind-rel (run≈ ck M wM E) λ s → prim≈ p r s
run≈ ck (let-op ⦅ M ,, ⟩ N ,, Nil ⦆) (wM , wN , _) E =
  bind-rel (run≈ ck M wM E) λ r → run≈ ck N wN (env-ext r E)

args≈ ck {n = zero} Nil _ E rs = ret rs
args≈ ck {n = suc n} (M ,, Ms) (w , ws) E rs =
  bind-rel (run≈ ck M w E) λ r → rel-map (λ x → x) (args≈ ck Ms ws E (r ∷ rs))

call≈ zero E r = timeout
call≈ (suc ck) {N = N} {w} E r = run≈ ck N w (env-ext r E)

{- The end theorem, for closed programs ----------------------------------------}

cast-correct : ∀ (M : AST) → Closed M → Equivalent (S.sem M) (T.sem (cast-closed M))
cast-correct M c rewrite cast-closed-≡ M (closed-ws {M} c) =
  clocked _≈_ obs≈ λ ck → run≈ ck M (closed-ws {M} c) λ x ()

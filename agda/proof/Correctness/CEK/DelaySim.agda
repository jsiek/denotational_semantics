{-

  Correctness of typed delay (Clos3ᵀ → Clos4ᵀ) by a forward simulation
  between the typed machines (see the design note in
  Semantics/CEK/Smallstep.agda).

  The machines run in lock step, except that building a closure takes
  three more Clos4ᵀ steps (the code, then the tuple of free variables,
  under pack). Neither machine checks the operator, so the only error,
  a failed project, happens in both at the same time.

  Values are related (_≈_) when they agree, except that a Clos3ᵀ closure
  of N and vs is related to the pack of code (delay N) and a tuple of
  values related to vs. Environments are related through the renaming r
  that delay carries (EnvRel): variable x of ρ₁ and variable r x of ρ₂
  hold related values. Continuations are related frame by frame: appL
  to callL, appR to callR, and closK to packR.

-}

module proof.Correctness.CEK.DelaySim where

open import Language.Typed.Type renaming (_≟_ to _≟F_)
open import Language.Typed.Clos3
import Language.Typed.Clos4 as C4
open import Compiler.Delay
open import Semantics.Observation using (o-tuple; o-inl; o-inr)
open import proof.Semantics.CEK.Smallstep
open import proof.Semantics.CEK.Simulation
open import proof.Correctness.CEK.Common using (collected≈; Lock; same-stop; same-next; lock)
import Semantics.CEK.Typed.Clos3 as Src
import Semantics.CEK.Typed.Clos4 as Tgt

open import Data.Bool using (true; false)
open import Data.Integer using (_≟_)
open import Data.List using ([]; _∷_)
import Data.List.Relation.Binary.Pointwise as L
open import Data.List.Relation.Unary.All using ([]; _∷_)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Vec.Relation.Binary.Pointwise.Inductive as V using ([]; _∷_)
open import Language.Prim using (sub; eq)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂)
open import Relation.Nullary using (yes; no; does)

{- The simulation relation -----------------------------------------------------}

infix 4 _≈_ _≈k_ _~_

data _≈_ : ∀ {A} → Src.Val A → Tgt.Val A → Set where
  clos≈ : ∀ {n N} {vs : Vec _ n} {ws} → V.Pointwise _≈_ vs ws
    → Src.clos N vs ≈ Tgt.pack (Tgt.code (delay (λ x → x) N)) (Tgt.tup ws)
  const≈ : ∀ {B c} → Src.const {B} c ≈ Tgt.const c
  tup≈ : ∀ {n} {vs : Vec _ n} {ws} → V.Pointwise _≈_ vs ws → Src.tup vs ≈ Tgt.tup ws
  inl≈ : ∀ {v w} → v ≈ w → Src.inl v ≈ Tgt.inl w
  inr≈ : ∀ {v w} → v ≈ w → Src.inr v ≈ Tgt.inr w
  dyn≈ : ∀ {G v w} → v ≈ w → Src.dyn G v ≈ Tgt.dyn G w

EnvRel : ∀ {Γ Δ} → Ren Γ Δ → Src.Env Γ → Tgt.Env Δ → Set
EnvRel r ρ₁ ρ₂ = ∀ {A} (x : _ ∋ A) → ρ₁ Src.! x ≈ ρ₂ Tgt.! r x

data _≈k_ : ∀ {A} → Src.Cont A → Tgt.Cont A → Set where
  halt : Src.halt ≈k Tgt.halt
  appL : ∀ {Γ Δ} {r : Ren Γ Δ} {M} {ρ₁ : Src.Env Γ} {ρ₂ : Tgt.Env Δ} {κ₁ κ₂} → EnvRel r ρ₁ ρ₂ → κ₁ ≈k κ₂
    → Src.appL M ρ₁ κ₁ ≈k Tgt.callL (delay r M) ρ₂ κ₂
  appR : ∀ {v w κ₁ κ₂} → v ≈ w → κ₁ ≈k κ₂ → Src.appR v κ₁ ≈k Tgt.callR w κ₂
  tupK : ∀ {Γ Δ} {r : Ren Γ Δ} {n j vs ws} {Ms : Vec _ j} {ρ₁ : Src.Env Γ} {ρ₂ : Tgt.Env Δ} {e : _ ≡ n} {e' κ₁ κ₂}
    → L.Pointwise _≈_ vs ws → EnvRel r ρ₁ ρ₂ → κ₁ ≈k κ₂
    → Src.tupK vs Ms ρ₁ e κ₁ ≈k Tgt.tupK ws (delays r Ms) ρ₂ e' κ₂
  closK : ∀ {n N κ₁ κ₂} → κ₁ ≈k κ₂ → Src.closK {n} N κ₁ ≈k Tgt.packR (Tgt.code (delay (λ x → x) N)) κ₂
  getK : ∀ {n i κ₁ κ₂} → κ₁ ≈k κ₂ → Src.getK {n} i κ₁ ≈k Tgt.getK i κ₂
  inlK : ∀ {κ₁ κ₂} → κ₁ ≈k κ₂ → Src.inlK κ₁ ≈k Tgt.inlK κ₂
  inrK : ∀ {κ₁ κ₂} → κ₁ ≈k κ₂ → Src.inrK κ₁ ≈k Tgt.inrK κ₂
  caseK : ∀ {Γ Δ} {r : Ren Γ Δ} {M N} {ρ₁ : Src.Env Γ} {ρ₂ : Tgt.Env Δ} {κ₁ κ₂} → EnvRel r ρ₁ ρ₂ → κ₁ ≈k κ₂
    → Src.caseK M N ρ₁ κ₁ ≈k Tgt.caseK (delay (ext r) M) (delay (ext r) N) ρ₂ κ₂
  primL : ∀ {Γ Δ} {r : Ren Γ Δ} {p M} {ρ₁ : Src.Env Γ} {ρ₂ : Tgt.Env Δ} {κ₁ κ₂} → EnvRel r ρ₁ ρ₂ → κ₁ ≈k κ₂
    → Src.primL p M ρ₁ κ₁ ≈k Tgt.primL p (delay r M) ρ₂ κ₂
  primR : ∀ {p n κ₁ κ₂} → κ₁ ≈k κ₂ → Src.primR p n κ₁ ≈k Tgt.primR p n κ₂
  letK : ∀ {Γ Δ} {r : Ren Γ Δ} {N} {ρ₁ : Src.Env Γ} {ρ₂ : Tgt.Env Δ} {κ₁ κ₂} → EnvRel r ρ₁ ρ₂ → κ₁ ≈k κ₂
    → Src.letK N ρ₁ κ₁ ≈k Tgt.letK (delay (ext r) N) ρ₂ κ₂
  injK : ∀ {G κ₁ κ₂} → κ₁ ≈k κ₂ → Src.injK G κ₁ ≈k Tgt.injK G κ₂
  projK : ∀ {G κ₁ κ₂} → κ₁ ≈k κ₂ → Src.projK G κ₁ ≈k Tgt.projK G κ₂

data _~_ : Src.State → Tgt.State → Set where
  eval~ : ∀ {Γ Δ A} {r : Ren Γ Δ} {M : Tm Γ A} {ρ₁} {ρ₂ : Tgt.Env Δ} {κ₁ κ₂} → EnvRel r ρ₁ ρ₂ → κ₁ ≈k κ₂
    → Src.eval M ρ₁ κ₁ ~ Tgt.eval (delay r M) ρ₂ κ₂
  ret~ : ∀ {A} {v : Src.Val A} {w κ₁ κ₂} → v ≈ w → κ₁ ≈k κ₂ → Src.ret v κ₁ ~ Tgt.ret w κ₂

{- Related values are observed alike, and primitives give related values -}
obs≈ : ∀ {A} {v : Src.Val A} {w} → v ≈ w → Src.obs v ≡ Tgt.obs w
obs≈* : ∀ {n} {vs : Vec _ n} {ws} → V.Pointwise _≈_ vs ws → Src.obs-vec vs ≡ Tgt.obs-vec ws
obs≈ (clos≈ _) = refl
obs≈ const≈ = refl
obs≈ (tup≈ rs) = cong o-tuple (obs≈* rs)
obs≈ (inl≈ r) = cong o-inl (obs≈ r)
obs≈ (inr≈ r) = cong o-inr (obs≈ r)
obs≈ (dyn≈ r) = obs≈ r
obs≈* [] = refl
obs≈* (r ∷ rs) = cong₂ _∷_ (obs≈ r) (obs≈* rs)

δ≈ : ∀ p n m → Src.δᵀ p n m ≈ Tgt.δᵀ p n m
δ≈ sub n m = const≈
δ≈ eq n m with does (n ≟ m)
... | true = inl≈ (dyn≈ (tup≈ []))
... | false = inr≈ (dyn≈ (tup≈ []))

env-ext : ∀ {Γ Δ B} {r : Ren Γ Δ} {ρ₁ : Src.Env Γ} {ρ₂ : Tgt.Env Δ} {v : Src.Val B} {w} → v ≈ w → EnvRel r ρ₁ ρ₂
  → EnvRel (ext r) (v ∷ ρ₁) (w ∷ ρ₂)
env-ext r er Z = r
env-ext r er (S x) = er x

{- the only error: both machines project, and fail, at the same time -}
proj~ : ∀ {H G v w κ₁ κ₂} → v ≈ w → κ₁ ≈k κ₂
  → Lock _~_ (Src.step (Src.ret (Src.dyn H v) (Src.projK G κ₁))) (Tgt.step (Tgt.ret (Tgt.dyn H w) (Tgt.projK G κ₂)))
proj~ {H} {G} r k with H ≟F flat G
... | yes refl = same-next (ret~ r k)
... | no _ = same-stop

{- The simulation, for any Clos4ᵀ program P ------------------------------------}

module _ (P : C4.Tm [] Any) where

  L₂ = Tgt.sem P

  tuple-next~ : ∀ {Γ Δ} {r : Ren Γ Δ} {n j vs ws} {Ms : Vec _ j} {ρ₁ : Src.Env Γ} {ρ₂ : Tgt.Env Δ} {e : _ ≡ n} {e' κ₁ κ₂}
    → L.Pointwise _≈_ vs ws → EnvRel r ρ₁ ρ₂ → κ₁ ≈k κ₂
    → Src.tuple-next vs Ms ρ₁ e κ₁ ~ Tgt.tuple-next ws (delays r Ms) ρ₂ e' κ₂
  tuple-next~ {Ms = []} {e = e} {e'} rs er k = ret~ (tup≈ (collected≈ rs e e')) k
  tuple-next~ {Ms = M ∷ Ms} rs er k = eval~ er (tupK rs er k)

  sim : ∀ {s₁ s₂} → s₁ ~ s₂ → Answers L₂ _~_ (Src.step s₁) s₂
  sim (eval~ {M = ` x} er k) = steps₁ refl (ret~ (er x) k)
  sim (eval~ {M = clos N Ms} er k) = steps (plus refl (refl ◅ refl ◅ refl ◅ ε)) (tuple-next~ L.[] er (closK k))
  sim (eval~ {M = app L M} er k) = steps₁ refl (eval~ er (appL er k))
  sim (eval~ {M = lit B c} er k) = steps₁ refl (ret~ const≈ k)
  sim (eval~ {M = tuple Ms} er k) = steps₁ refl (tuple-next~ L.[] er k)
  sim (eval~ {M = get i M} er k) = steps₁ refl (eval~ er (getK k))
  sim (eval~ {M = inl M} er k) = steps₁ refl (eval~ er (inlK k))
  sim (eval~ {M = inr M} er k) = steps₁ refl (eval~ er (inrK k))
  sim (eval~ {M = case L M N} er k) = steps₁ refl (eval~ er (caseK er k))
  sim (eval~ {M = prim p L M} er k) = steps₁ refl (eval~ er (primL er k))
  sim (eval~ {M = let′ M N} er k) = steps₁ refl (eval~ er (letK er k))
  sim (eval~ {M = inject G M} er k) = steps₁ refl (eval~ er (injK k))
  sim (eval~ {M = project G M} er k) = steps₁ refl (eval~ er (projK k))
  sim (ret~ r halt) = stops (cong stop (sym (obs≈ r)))
  sim (ret~ r (appL er k)) = steps₁ refl (eval~ er (appR r k))
  sim (ret~ r (appR (clos≈ rs) k)) = steps₁ refl (eval~ (λ { Z → r ; (S Z) → tup≈ rs }) k)
  sim (ret~ r (tupK rs er k)) = steps₁ refl (tuple-next~ (r L.∷ rs) er k)
  sim (ret~ (tup≈ rs) (closK k)) = steps₁ refl (ret~ (clos≈ rs) k)
  sim (ret~ (tup≈ rs) (getK {i = i} k)) = steps₁ refl (ret~ (V.lookup rs i) k)
  sim (ret~ r (inlK k)) = steps₁ refl (ret~ (inl≈ r) k)
  sim (ret~ r (inrK k)) = steps₁ refl (ret~ (inr≈ r) k)
  sim (ret~ (inl≈ r) (caseK er k)) = steps₁ refl (eval~ (env-ext r er) k)
  sim (ret~ (inr≈ r) (caseK er k)) = steps₁ refl (eval~ (env-ext r er) k)
  sim (ret~ const≈ (primL er k)) = steps₁ refl (eval~ er (primR k))
  sim (ret~ (const≈ {c = m}) (primR {p} {n} k)) = steps₁ refl (ret~ (δ≈ p n m) k)
  sim (ret~ r (letK er k)) = steps₁ refl (eval~ (env-ext r er) k)
  sim (ret~ r (injK k)) = steps₁ refl (ret~ (dyn≈ r) k)
  sim (ret~ (dyn≈ r) (projK k)) = lock (proj~ r k)

{- The end theorem: for every Clos3ᵀ program -----------------------------------}

delay-correct : ∀ (M : Tm [] Any) → Equivalent (Src.sem M) (Tgt.sem (delay-program M))
delay-correct M = equivalent (plus-simulation _~_ (eval~ (λ ()) halt) (sim (delay-program M)))

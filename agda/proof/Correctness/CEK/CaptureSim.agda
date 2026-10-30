{-

  Correctness of typed capture (ISWIMᵀ → Clos2ᵀ) by a forward simulation
  between the typed machines (see the design note in
  Semantics/CEK/Smallstep.agda).

  The machines run in lock step, except that evaluating a function (one
  ISWIMᵀ step) takes several Clos2ᵀ steps: the closure evaluates the
  variables ` 0 , ... , ` (k - 1) that it captures (capture-fvs), which
  collects exactly the environment, and then builds the closure.

  Values are related (_≈_) when they agree, except that an ISWIMᵀ closure
  of N and ρ is related to a Clos2ᵀ closure of capture N whose captured
  values are related to ρ. Environments are vectors of the same length,
  related pointwise; continuations are related frame by frame. The only
  error, a failed project, happens in both machines at the same time.

-}

module proof.Correctness.CEK.CaptureSim where

open import Language.Typed.Type renaming (_≟_ to _≟F_)
open import Language.Typed.ISWIM
import Language.Typed.Clos2 as C2
open import Compiler.Capture
open import Framework.VecUtil using (_<><_)
open import Semantics.Observation using (o-tuple; o-inl; o-inr)
open import proof.Semantics.CEK.Smallstep
open import proof.Semantics.CEK.Simulation
open import proof.Framework.VecUtil using (_<><₂_)
open import proof.Correctness.CEK.Common using (Lock; same-stop; same-next; lock)
import Semantics.CEK.Typed.ISWIM as Src
import Semantics.CEK.Typed.Clos2 as Tgt

open import Data.Bool using (true; false)
open import Data.Fin using (Fin)
open import Data.Integer using (_≟_)
open import Data.List using ([]; _∷_)
open import Data.Vec using (Vec; []; _∷_; lookup; map; allFin)
open import Data.Vec.Properties using (tabulate-allFin; map-lookup-allFin)
open import Data.Vec.Relation.Binary.Pointwise.Inductive as V using ([]; _∷_)
open import Language.Prim using (sub; eq)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary using (yes; no; does)

{- The simulation relation -----------------------------------------------------}

infix 4 _≈_ _≈k_ _~_

data _≈_ : ∀ {A} → Src.Val A → Tgt.Val A → Set where
  clo≈ : ∀ {k N} {ρ : Vec _ k} {vs} → V.Pointwise _≈_ ρ vs → Src.clo N ρ ≈ Tgt.clos (capture N) vs
  const≈ : ∀ {B c} → Src.const {B} c ≈ Tgt.const c
  tup≈ : ∀ {n} {vs : Vec _ n} {ws} → V.Pointwise _≈_ vs ws → Src.tup vs ≈ Tgt.tup ws
  inl≈ : ∀ {v w} → v ≈ w → Src.inl v ≈ Tgt.inl w
  inr≈ : ∀ {v w} → v ≈ w → Src.inr v ≈ Tgt.inr w
  dyn≈ : ∀ {G v w} → v ≈ w → Src.dyn G v ≈ Tgt.dyn G w

_≈ρ_ : ∀ {k} → Src.Env k → Tgt.Env k → Set
_≈ρ_ = V.Pointwise _≈_

data _≈k_ : ∀ {A} → Src.Cont A → Tgt.Cont A → Set where
  halt : Src.halt ≈k Tgt.halt
  appL : ∀ {k M} {ρ₁ : Src.Env k} {ρ₂ κ₁ κ₂} → ρ₁ ≈ρ ρ₂ → κ₁ ≈k κ₂
    → Src.appL M ρ₁ κ₁ ≈k Tgt.appL (capture M) ρ₂ κ₂
  appR : ∀ {f g κ₁ κ₂} → f ≈ g → κ₁ ≈k κ₂ → Src.appR f κ₁ ≈k Tgt.appR g κ₂
  tupK : ∀ {k m j} {vs : Vec _ m} {ws : Vec _ m} {Ms : Vec _ j} {ρ₁ : Src.Env k} {ρ₂} {κ₁ κ₂}
    → V.Pointwise _≈_ vs ws → ρ₁ ≈ρ ρ₂ → κ₁ ≈k κ₂
    → Src.tupK vs Ms ρ₁ κ₁ ≈k Tgt.tupK ws (encs Ms) ρ₂ κ₂
  getK : ∀ {n i κ₁ κ₂} → κ₁ ≈k κ₂ → Src.getK {n} i κ₁ ≈k Tgt.getK i κ₂
  inlK : ∀ {κ₁ κ₂} → κ₁ ≈k κ₂ → Src.inlK κ₁ ≈k Tgt.inlK κ₂
  inrK : ∀ {κ₁ κ₂} → κ₁ ≈k κ₂ → Src.inrK κ₁ ≈k Tgt.inrK κ₂
  caseK : ∀ {k M N} {ρ₁ : Src.Env k} {ρ₂ κ₁ κ₂} → ρ₁ ≈ρ ρ₂ → κ₁ ≈k κ₂
    → Src.caseK M N ρ₁ κ₁ ≈k Tgt.caseK (capture M) (capture N) ρ₂ κ₂
  primL : ∀ {k p M} {ρ₁ : Src.Env k} {ρ₂ κ₁ κ₂} → ρ₁ ≈ρ ρ₂ → κ₁ ≈k κ₂
    → Src.primL p M ρ₁ κ₁ ≈k Tgt.primL p (capture M) ρ₂ κ₂
  primR : ∀ {p n κ₁ κ₂} → κ₁ ≈k κ₂ → Src.primR p n κ₁ ≈k Tgt.primR p n κ₂
  letK : ∀ {k N} {ρ₁ : Src.Env k} {ρ₂ κ₁ κ₂} → ρ₁ ≈ρ ρ₂ → κ₁ ≈k κ₂
    → Src.letK N ρ₁ κ₁ ≈k Tgt.letK (capture N) ρ₂ κ₂
  injK : ∀ {G κ₁ κ₂} → κ₁ ≈k κ₂ → Src.injK G κ₁ ≈k Tgt.injK G κ₂
  projK : ∀ {G κ₁ κ₂} → κ₁ ≈k κ₂ → Src.projK G κ₁ ≈k Tgt.projK G κ₂

data _~_ : Src.State → Tgt.State → Set where
  eval~ : ∀ {k A} {M : Tm k A} {ρ₁ ρ₂ κ₁ κ₂} → ρ₁ ≈ρ ρ₂ → κ₁ ≈k κ₂
    → Src.eval M ρ₁ κ₁ ~ Tgt.eval (capture M) ρ₂ κ₂
  ret~ : ∀ {A} {v : Src.Val A} {w κ₁ κ₂} → v ≈ w → κ₁ ≈k κ₂ → Src.ret v κ₁ ~ Tgt.ret w κ₂

{- Related values are observed alike, and primitives give related values -}
obs≈ : ∀ {A} {v : Src.Val A} {w} → v ≈ w → Src.obs v ≡ Tgt.obs w
obs≈* : ∀ {n} {vs : Vec _ n} {ws} → V.Pointwise _≈_ vs ws → Src.obs-vec vs ≡ Tgt.obs-vec ws
obs≈ (clo≈ _) = refl
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

{- the only error: both machines project, and fail, at the same time -}
proj~ : ∀ {H G v w κ₁ κ₂} → v ≈ w → κ₁ ≈k κ₂
  → Lock _~_ (Src.step (Src.ret (Src.dyn H v) (Src.projK G κ₁))) (Tgt.step (Tgt.ret (Tgt.dyn H w) (Tgt.projK G κ₂)))
proj~ {H} {G} r k with H ≟F flat G
... | yes refl = same-next (ret~ r k)
... | no _ = same-stop

{- The simulation, for any Clos2ᵀ program P ------------------------------------}

module _ (P : C2.Tm 0 Any) where

  L₂ = Tgt.sem P

  {- evaluating the variables xs as the rest of a tuple -}
  capture-fvs : ∀ {k j m} (xs : Vec (Fin k) j) (vs : Vec _ m) ρ κ
    → Star L₂ (Tgt.tuple-next vs (map C2.`_ xs) ρ κ) (Tgt.ret (Tgt.tup (vs <>< map (lookup ρ) xs)) κ)
  capture-fvs [] vs ρ κ = ε
  capture-fvs (x ∷ xs) vs ρ κ = refl ◅ refl ◅ capture-fvs xs (lookup ρ x ∷ vs) ρ κ

  tuple-next~ : ∀ {k m j} {vs : Vec _ m} {ws : Vec _ m} {Ms : Vec _ j} {ρ₁ : Src.Env k} {ρ₂} {κ₁ κ₂}
    → V.Pointwise _≈_ vs ws → ρ₁ ≈ρ ρ₂ → κ₁ ≈k κ₂
    → Src.tuple-next vs Ms ρ₁ κ₁ ~ Tgt.tuple-next ws (encs Ms) ρ₂ κ₂
  tuple-next~ {Ms = []} rs er k = ret~ (tup≈ (rs <><₂ [])) k
  tuple-next~ {Ms = M ∷ Ms} rs er k = eval~ er (tupK rs er k)

  sim : ∀ {s₁ s₂} → s₁ ~ s₂ → Answers L₂ _~_ (Src.step s₁) s₂
  sim (eval~ {M = ` x} er k) = steps₁ refl (ret~ (V.lookup er x) k)
  sim (eval~ {n} {M = lam N} {ρ₂ = ρ₂} {κ₂ = κ₂} er k) =
    steps (plus refl (subst (λ Ms → Star L₂ (Tgt.tuple-next [] Ms ρ₂ κ') (Tgt.ret (Tgt.tup (map (lookup ρ₂) (allFin n))) κ')) (sym (tabulate-allFin C2.`_))
                       (capture-fvs (allFin n) [] ρ₂ κ') ◅◅ (refl ◅ ε)))
          (ret~ (clo≈ (subst (_≈ρ_ _) (sym (map-lookup-allFin ρ₂)) er)) k)
    where κ' = Tgt.closK (capture N) κ₂
  sim (eval~ {M = app L M} er k) = steps₁ refl (eval~ er (appL er k))
  sim (eval~ {M = lit B c} er k) = steps₁ refl (ret~ const≈ k)
  sim (eval~ {M = tuple Ms} er k) = steps₁ refl (tuple-next~ [] er k)
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
  sim (ret~ r (appR (clo≈ er) k)) = steps₁ refl (eval~ (r ∷ er) k)
  sim (ret~ r (tupK rs er k)) = steps₁ refl (tuple-next~ (r ∷ rs) er k)
  sim (ret~ (tup≈ rs) (getK {i = i} k)) = steps₁ refl (ret~ (V.lookup rs i) k)
  sim (ret~ r (inlK k)) = steps₁ refl (ret~ (inl≈ r) k)
  sim (ret~ r (inrK k)) = steps₁ refl (ret~ (inr≈ r) k)
  sim (ret~ (inl≈ r) (caseK er k)) = steps₁ refl (eval~ (r ∷ er) k)
  sim (ret~ (inr≈ r) (caseK er k)) = steps₁ refl (eval~ (r ∷ er) k)
  sim (ret~ const≈ (primL er k)) = steps₁ refl (eval~ er (primR k))
  sim (ret~ (const≈ {c = m}) (primR {p} {n} k)) = steps₁ refl (ret~ (δ≈ p n m) k)
  sim (ret~ r (letK er k)) = steps₁ refl (eval~ (r ∷ er) k)
  sim (ret~ r (injK k)) = steps₁ refl (ret~ (dyn≈ r) k)
  sim (ret~ (dyn≈ r) (projK k)) = lock (proj~ r k)

{- The end theorem: for every closed ISWIMᵀ program ----------------------------}

capture-correct : ∀ (M : Tm 0 Any) → Equivalent (Src.sem M) (Tgt.sem (capture M))
capture-correct M = equivalent (plus-simulation _~_ (eval~ [] halt) (sim (capture M)))

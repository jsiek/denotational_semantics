{-

  Correctness of typed concretize (Clos2ᵀ → Clos3ᵀ) by a forward
  simulation between the typed machines (see the design note in
  Semantics/CEK/Smallstep.agda).

  The machines run in lock step, except that a free variable of a
  closure's code, read in one Clos2ᵀ step, becomes get i (` 1), which
  takes three Clos3ᵀ steps (ref-run). Since variables are always bound
  in the typed machines, the read cannot fail, and needs no special
  state.

  Values are related (_≈_) when they agree, except that a Clos2ᵀ closure
  of N and vs is related to a Clos3ᵀ closure of concretize fv-ref N and
  values related to vs (as a tuple, in the same order). Environments are
  related through the map φ that concretize carries (EnvRel): Clos2ᵀ
  variable x holds a value related to the one at φ x (ref-val), a
  variable or a component of a tuple. The only error, a failed project,
  happens in both machines at the same time.

-}

module proof.Correctness.CEK.ConcretizeSim where

open import Language.Typed.Type renaming (_≟_ to _≟F_)
open import Language.Typed.Clos2
import Language.Typed.Clos3 as C3
open import Compiler.Concretize
open import Semantics.Observation using (o-tuple; o-inl; o-inr)
open import proof.Semantics.CEK.Smallstep
open import proof.Semantics.CEK.Simulation
open import proof.Framework.VecUtil using (_<><₂_)
open import proof.Correctness.CEK.Common using (Lock; same-stop; same-next; lock)
import Semantics.CEK.Typed.Clos2 as Src
import Semantics.CEK.Typed.Clos3 as Tgt

open import Data.Bool using (true; false)
open import Data.Fin using (Fin; zero; suc)
open import Data.Integer using (_≟_)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.All using ([]; _∷_)
open import Data.Vec using (Vec; []; _∷_; lookup)
open import Data.Vec.Relation.Binary.Pointwise.Inductive as V using ([]; _∷_)
open import Language.Prim using (sub; eq)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂)
open import Relation.Nullary using (yes; no; does)

{- The simulation relation -----------------------------------------------------}

infix 4 _≈_ _≈k_ _~_

data _≈_ : ∀ {A} → Src.Val A → Tgt.Val A → Set where
  clos≈ : ∀ {n N} {vs : Vec _ n} {ws} → V.Pointwise _≈_ vs ws
    → Src.clos N vs ≈ Tgt.clos (concretize fv-ref N) ws
  const≈ : ∀ {B c} → Src.const {B} c ≈ Tgt.const c
  tup≈ : ∀ {n} {vs : Vec _ n} {ws} → V.Pointwise _≈_ vs ws → Src.tup vs ≈ Tgt.tup ws
  inl≈ : ∀ {v w} → v ≈ w → Src.inl v ≈ Tgt.inl w
  inr≈ : ∀ {v w} → v ≈ w → Src.inr v ≈ Tgt.inr w
  dyn≈ : ∀ {G v w} → v ≈ w → Src.dyn G v ≈ Tgt.dyn G w

{- the value at a Ref -}
get-val : ∀ {n} → Fin n → Tgt.Val ⟪ tup n ⟫ → Tgt.Val Any
get-val i (Tgt.tup vs) = lookup vs i

ref-val : ∀ {Γ} → Ref Γ → Tgt.Env Γ → Tgt.Val Any
ref-val (var y) ρ = ρ Tgt.! y
ref-val (prj i y) ρ = get-val i (ρ Tgt.! y)

EnvRel : ∀ {k Γ} → (Fin k → Ref Γ) → Src.Env k → Tgt.Env Γ → Set
EnvRel φ ρ₁ ρ₂ = ∀ x → lookup ρ₁ x ≈ ref-val (φ x) ρ₂

data _≈k_ : ∀ {A} → Src.Cont A → Tgt.Cont A → Set where
  halt : Src.halt ≈k Tgt.halt
  appL : ∀ {k Γ M} {φ : Fin k → Ref Γ} {ρ₁ ρ₂ κ₁ κ₂} → EnvRel φ ρ₁ ρ₂ → κ₁ ≈k κ₂
    → Src.appL M ρ₁ κ₁ ≈k Tgt.appL (concretize φ M) ρ₂ κ₂
  appR : ∀ {f g κ₁ κ₂} → f ≈ g → κ₁ ≈k κ₂ → Src.appR f κ₁ ≈k Tgt.appR g κ₂
  tupK : ∀ {k Γ} {φ : Fin k → Ref Γ} {m j} {vs : Vec _ m} {ws : Vec _ m} {Ms : Vec _ j} {ρ₁ ρ₂} {κ₁ κ₂}
    → V.Pointwise _≈_ vs ws → EnvRel φ ρ₁ ρ₂ → κ₁ ≈k κ₂
    → Src.tupK vs Ms ρ₁ κ₁ ≈k Tgt.tupK ws (concs φ Ms) ρ₂ κ₂
  closK : ∀ {n N κ₁ κ₂} → κ₁ ≈k κ₂ → Src.closK {n} N κ₁ ≈k Tgt.closK (concretize fv-ref N) κ₂
  getK : ∀ {n i κ₁ κ₂} → κ₁ ≈k κ₂ → Src.getK {n} i κ₁ ≈k Tgt.getK i κ₂
  inlK : ∀ {κ₁ κ₂} → κ₁ ≈k κ₂ → Src.inlK κ₁ ≈k Tgt.inlK κ₂
  inrK : ∀ {κ₁ κ₂} → κ₁ ≈k κ₂ → Src.inrK κ₁ ≈k Tgt.inrK κ₂
  caseK : ∀ {k Γ M N} {φ : Fin k → Ref Γ} {ρ₁ ρ₂ κ₁ κ₂} → EnvRel φ ρ₁ ρ₂ → κ₁ ≈k κ₂
    → Src.caseK M N ρ₁ κ₁ ≈k Tgt.caseK (concretize (ext-ref φ) M) (concretize (ext-ref φ) N) ρ₂ κ₂
  primL : ∀ {k Γ p M} {φ : Fin k → Ref Γ} {ρ₁ ρ₂ κ₁ κ₂} → EnvRel φ ρ₁ ρ₂ → κ₁ ≈k κ₂
    → Src.primL p M ρ₁ κ₁ ≈k Tgt.primL p (concretize φ M) ρ₂ κ₂
  primR : ∀ {p n κ₁ κ₂} → κ₁ ≈k κ₂ → Src.primR p n κ₁ ≈k Tgt.primR p n κ₂
  letK : ∀ {k Γ N} {φ : Fin k → Ref Γ} {ρ₁ ρ₂ κ₁ κ₂} → EnvRel φ ρ₁ ρ₂ → κ₁ ≈k κ₂
    → Src.letK N ρ₁ κ₁ ≈k Tgt.letK (concretize (ext-ref φ) N) ρ₂ κ₂
  injK : ∀ {G κ₁ κ₂} → κ₁ ≈k κ₂ → Src.injK G κ₁ ≈k Tgt.injK G κ₂
  projK : ∀ {G κ₁ κ₂} → κ₁ ≈k κ₂ → Src.projK G κ₁ ≈k Tgt.projK G κ₂

data _~_ : Src.State → Tgt.State → Set where
  eval~ : ∀ {k Γ A} {φ : Fin k → Ref Γ} {M : Tm k A} {ρ₁ ρ₂ κ₁ κ₂} → EnvRel φ ρ₁ ρ₂ → κ₁ ≈k κ₂
    → Src.eval M ρ₁ κ₁ ~ Tgt.eval (concretize φ M) ρ₂ κ₂
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

{- the only error: both machines project, and fail, at the same time -}
proj~ : ∀ {H G v w κ₁ κ₂} → v ≈ w → κ₁ ≈k κ₂
  → Lock _~_ (Src.step (Src.ret (Src.dyn H v) (Src.projK G κ₁))) (Tgt.step (Tgt.ret (Tgt.dyn H w) (Tgt.projK G κ₂)))
proj~ {H} {G} r k with H ≟F flat G
... | yes refl = same-next (ret~ r k)
... | no _ = same-stop

{- Related environments --------------------------------------------------------}

env-ext : ∀ {k Γ} {φ : Fin k → Ref Γ} {ρ₁ ρ₂ v} {w : Tgt.Val Any} → v ≈ w → EnvRel φ ρ₁ ρ₂
  → EnvRel (ext-ref φ) (v ∷ ρ₁) (w ∷ ρ₂)
env-ext r er zero = r
env-ext {φ = φ} r er (suc x) with φ x | er x
... | var y | p = p
... | prj i y | p = p

{- the environment of a closure's code: its argument and its free variables -}
env-clos : ∀ {n v w} {vs : Vec _ n} {ws} → v ≈ w → V.Pointwise _≈_ vs ws
  → EnvRel fv-ref (v ∷ vs) (w ∷ Tgt.tup ws ∷ [])
env-clos r rs zero = r
env-clos r rs (suc i) = V.lookup rs i

{- The simulation, for any Clos3ᵀ program P ------------------------------------}

module _ (P : C3.Tm [] Any) where

  L₂ = Tgt.sem P

  {- reading a Ref -}
  ref-run : ∀ {Γ} (r : Ref Γ) ρ κ → Plus L₂ (Tgt.eval (ref-tm r) ρ κ) (Tgt.ret (ref-val r ρ) κ)
  ref-run (var y) ρ κ = step⁺ refl
  ref-run (prj i y) ρ κ = plus refl (refl ◅ get-step (ρ Tgt.! y) ◅ ε)
    where get-step : ∀ t → Tgt.step (Tgt.ret t (Tgt.getK i κ)) ≡ next (Tgt.ret (get-val i t) κ)
          get-step (Tgt.tup vs) = refl

  tuple-next~ : ∀ {k Γ} {φ : Fin k → Ref Γ} {m j} {vs : Vec _ m} {ws : Vec _ m} {Ms : Vec _ j} {ρ₁ ρ₂} {κ₁ κ₂}
    → V.Pointwise _≈_ vs ws → EnvRel φ ρ₁ ρ₂ → κ₁ ≈k κ₂
    → Src.tuple-next vs Ms ρ₁ κ₁ ~ Tgt.tuple-next ws (concs φ Ms) ρ₂ κ₂
  tuple-next~ {Ms = []} rs er k = ret~ (tup≈ (rs <><₂ [])) k
  tuple-next~ {Ms = M ∷ Ms} rs er k = eval~ er (tupK rs er k)

  sim : ∀ {s₁ s₂} → s₁ ~ s₂ → Answers L₂ _~_ (Src.step s₁) s₂
  sim (eval~ {φ = φ} {M = ` x} {ρ₂ = ρ₂} {κ₂ = κ₂} er k) = steps (ref-run (φ x) ρ₂ κ₂) (ret~ (er x) k)
  sim (eval~ {M = clos N Ms} er k) = steps₁ refl (tuple-next~ [] er (closK k))
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
  sim (ret~ r (appR (clos≈ rs) k)) = steps₁ refl (eval~ (env-clos r rs) k)
  sim (ret~ r (tupK rs er k)) = steps₁ refl (tuple-next~ (r ∷ rs) er k)
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

{- The end theorem: for every closed Clos2ᵀ program ----------------------------}

concretize-correct : ∀ (M : Tm 0 Any) → Equivalent (Src.sem M) (Tgt.sem (concretize-program M))
concretize-correct M = equivalent (plus-simulation _~_ (eval~ (λ ()) halt) (sim (concretize-program M)))

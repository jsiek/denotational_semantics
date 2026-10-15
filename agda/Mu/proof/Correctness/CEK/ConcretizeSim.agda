{-

  Correctness of concretize (Clos2μ → Clos3μ) by a forward simulation
  between the typed machines, as for typed concretize
  (proof/Correctness/CEK/ConcretizeSim.agda).

  The machines run in lock step, except that a free variable of a
  closure's code, read in one Clos2μ step, becomes get i (` 1), which
  takes three Clos3μ steps (ref-run). Since variables are always bound
  in the typed machines, the read cannot fail, and needs no special
  state.

  Values are related (_≈_) when they agree, except that a Clos2μ closure
  of N and vs is related to a Clos3μ closure of concretize fv-ref N and
  values related to vs (as a tuple, in the same order). Environments are
  related through the map φ that concretize carries (EnvRel): Clos2μ
  variable x holds a value related to the one at φ x (ref-val), a
  variable or a component of a tuple. Neither machine stops with an
  error.

-}

module Mu.proof.Correctness.CEK.ConcretizeSim where

open import Mu.Language.Type
open import Mu.Language.Clos2
import Mu.Language.Clos3 as C3
open import Mu.Compiler.Concretize
open import Mu.Framework.AllUtil using (All; []; _∷_; lookup; _<><_; All₂; lookup₂; _<><₂_)
open import Semantics.Observation using (o-tuple; o-inl; o-inr)
open import proof.Semantics.CEK.Smallstep
open import proof.Semantics.CEK.Simulation
import Mu.Semantics.CEK.Clos2 as Src
import Mu.Semantics.CEK.Clos3 as Tgt

open import Data.Bool using (true; false)
open import Data.Integer using (_≟_)
open import Data.List using ([]; _∷_)
open import Language.Prim using (sub; eq)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂)
open import Relation.Nullary using (does)

{- The simulation relation -----------------------------------------------------}

infix 4 _≈_ _≈k_ _~_

data _≈_ : ∀ {A} → Src.Val A → Tgt.Val A → Set where
  clos≈ : ∀ {Δ A B} {N : Tm (A ∷ Δ) B} {vs : All _ Δ} {ws} → All₂ _≈_ vs ws
    → Src.clos N vs ≈ Tgt.clos (concretize fv-ref N) ws
  const≈ : ∀ {B c} → Src.const {B} c ≈ Tgt.const c
  tup≈ : ∀ {Δ} {vs : All _ Δ} {ws} → All₂ _≈_ vs ws → Src.tup vs ≈ Tgt.tup ws
  inl≈ : ∀ {A B v w} → v ≈ w → Src.inl {A} {B} v ≈ Tgt.inl w
  inr≈ : ∀ {A B v w} → v ≈ w → Src.inr {A} {B} v ≈ Tgt.inr w
  fold≈ : ∀ {A c v w} → v ≈ w → Src.fold {A} {c} v ≈ Tgt.fold w

{- the value at a Ref -}
get-val : ∀ {Δ A} → Δ ∋ A → Tgt.Val (tup Δ) → Tgt.Val A
get-val i (Tgt.tup vs) = lookup vs i

ref-val : ∀ {Γ A} → Ref Γ A → Tgt.Env Γ → Tgt.Val A
ref-val (var y) ρ = lookup ρ y
ref-val (prj i y) ρ = get-val i (lookup ρ y)

EnvRel : ∀ {Γ Γ'} → Refs Γ Γ' → Src.Env Γ → Tgt.Env Γ' → Set
EnvRel φ ρ₁ ρ₂ = ∀ {C} (x : _ ∋ C) → lookup ρ₁ x ≈ ref-val (φ x) ρ₂

data _≈k_ : ∀ {A} → Src.Cont A → Tgt.Cont A → Set where
  halt : ∀ {A} → Src.halt {A} ≈k Tgt.halt
  appL : ∀ {Γ Γ' A B M} {φ : Refs Γ Γ'} {ρ₁ ρ₂ κ₁ κ₂} → EnvRel φ ρ₁ ρ₂ → κ₁ ≈k κ₂
    → Src.appL {A = A} {B} M ρ₁ κ₁ ≈k Tgt.appL (concretize φ M) ρ₂ κ₂
  appR : ∀ {A B f g κ₁ κ₂} → f ≈ g → κ₁ ≈k κ₂ → Src.appR {A} {B} f κ₁ ≈k Tgt.appR g κ₂
  tupK : ∀ {Γ Γ' Δ' A Δ} {φ : Refs Γ Γ'} {vs : All Src.Val Δ'} {ws : All Tgt.Val Δ'} {Ms : All _ Δ} {ρ₁ ρ₂ κ₁ κ₂}
    → All₂ _≈_ vs ws → EnvRel φ ρ₁ ρ₂ → κ₁ ≈k κ₂
    → Src.tupK {A = A} vs Ms ρ₁ κ₁ ≈k Tgt.tupK ws (concs φ Ms) ρ₂ κ₂
  closK : ∀ {Δ A B N κ₁ κ₂} → κ₁ ≈k κ₂ → Src.closK {Δ} {A} {B} N κ₁ ≈k Tgt.closK (concretize fv-ref N) κ₂
  getK : ∀ {Δ A i κ₁ κ₂} → κ₁ ≈k κ₂ → Src.getK {Δ} {A} i κ₁ ≈k Tgt.getK i κ₂
  inlK : ∀ {A B κ₁ κ₂} → κ₁ ≈k κ₂ → Src.inlK {A} {B} κ₁ ≈k Tgt.inlK κ₂
  inrK : ∀ {A B κ₁ κ₂} → κ₁ ≈k κ₂ → Src.inrK {A} {B} κ₁ ≈k Tgt.inrK κ₂
  caseK : ∀ {Γ Γ' A B C M N} {φ : Refs Γ Γ'} {ρ₁ ρ₂ κ₁ κ₂} → EnvRel φ ρ₁ ρ₂ → κ₁ ≈k κ₂
    → Src.caseK {A = A} {B} {C} M N ρ₁ κ₁ ≈k Tgt.caseK (concretize (ext-ref φ) M) (concretize (ext-ref φ) N) ρ₂ κ₂
  primL : ∀ {Γ Γ' p M} {φ : Refs Γ Γ'} {ρ₁ ρ₂ κ₁ κ₂} → EnvRel φ ρ₁ ρ₂ → κ₁ ≈k κ₂
    → Src.primL p M ρ₁ κ₁ ≈k Tgt.primL p (concretize φ M) ρ₂ κ₂
  primR : ∀ {p n κ₁ κ₂} → κ₁ ≈k κ₂ → Src.primR p n κ₁ ≈k Tgt.primR p n κ₂
  letK : ∀ {Γ Γ' A B N} {φ : Refs Γ Γ'} {ρ₁ ρ₂ κ₁ κ₂} → EnvRel φ ρ₁ ρ₂ → κ₁ ≈k κ₂
    → Src.letK {A = A} {B} N ρ₁ κ₁ ≈k Tgt.letK (concretize (ext-ref φ) N) ρ₂ κ₂
  foldK : ∀ {A c κ₁ κ₂} → κ₁ ≈k κ₂ → Src.foldK {A} {c} κ₁ ≈k Tgt.foldK κ₂
  unfoldK : ∀ {A c κ₁ κ₂} → κ₁ ≈k κ₂ → Src.unfoldK {A} {c} κ₁ ≈k Tgt.unfoldK κ₂

data _~_ : Src.State → Tgt.State → Set where
  eval~ : ∀ {Γ Γ' A} {φ : Refs Γ Γ'} {M : Tm Γ A} {ρ₁ ρ₂ κ₁ κ₂} → EnvRel φ ρ₁ ρ₂ → κ₁ ≈k κ₂
    → Src.eval M ρ₁ κ₁ ~ Tgt.eval (concretize φ M) ρ₂ κ₂
  ret~ : ∀ {A} {v : Src.Val A} {w κ₁ κ₂} → v ≈ w → κ₁ ≈k κ₂ → Src.ret v κ₁ ~ Tgt.ret w κ₂

{- Related values are observed alike, and primitives give related values -}
obs≈ : ∀ {A} {v : Src.Val A} {w} → v ≈ w → Src.obs v ≡ Tgt.obs w
obs≈* : ∀ {Δ} {vs : All _ Δ} {ws} → All₂ _≈_ vs ws → Src.obs-all vs ≡ Tgt.obs-all ws
obs≈ (clos≈ _) = refl
obs≈ const≈ = refl
obs≈ (tup≈ rs) = cong o-tuple (obs≈* rs)
obs≈ (inl≈ r) = cong o-inl (obs≈ r)
obs≈ (inr≈ r) = cong o-inr (obs≈ r)
obs≈ (fold≈ r) = obs≈ r
obs≈* [] = refl
obs≈* (r ∷ rs) = cong₂ _∷_ (obs≈ r) (obs≈* rs)

δ≈ : ∀ p n m → Src.δᵀ p n m ≈ Tgt.δᵀ p n m
δ≈ sub n m = const≈
δ≈ eq n m with does (n ≟ m)
... | true = inl≈ (tup≈ [])
... | false = inr≈ (tup≈ [])

{- Related environments --------------------------------------------------------}

env-ext : ∀ {Γ Γ' B} {φ : Refs Γ Γ'} {ρ₁ ρ₂ v} {w : Tgt.Val B} → v ≈ w → EnvRel φ ρ₁ ρ₂
  → EnvRel (ext-ref φ) (v ∷ ρ₁) (w ∷ ρ₂)
env-ext r er Z = r
env-ext {φ = φ} r er (S x) with φ x | er x
... | var y | p = p
... | prj i y | p = p

{- the environment of a closure's code: its argument and its free variables -}
env-clos : ∀ {Δ A v w} {vs : All _ Δ} {ws} → v ≈ w → All₂ _≈_ vs ws
  → EnvRel (fv-ref {A = A}) (v ∷ vs) (w ∷ Tgt.tup ws ∷ [])
env-clos r rs Z = r
env-clos r rs (S i) = lookup₂ rs i

{- The simulation, for any Clos3μ program P ------------------------------------}

module _ {T : Type} (P : C3.Tm [] T) where

  L₂ = Tgt.sem P

  {- reading a Ref -}
  ref-run : ∀ {Γ A} (r : Ref Γ A) ρ κ → Plus L₂ (Tgt.eval (ref-tm r) ρ κ) (Tgt.ret (ref-val r ρ) κ)
  ref-run (var y) ρ κ = step⁺ refl
  ref-run (prj i y) ρ κ = plus refl (refl ◅ get-step (lookup ρ y) ◅ ε)
    where get-step : ∀ t → Tgt.step (Tgt.ret t (Tgt.getK i κ)) ≡ next (Tgt.ret (get-val i t) κ)
          get-step (Tgt.tup vs) = refl

  tuple-next~ : ∀ {Γ Γ' Δ' Δ} {φ : Refs Γ Γ'} {vs : All Src.Val Δ'} {ws : All Tgt.Val Δ'} {Ms : All _ Δ} {ρ₁ ρ₂}
      {κ₁ : Src.Cont (tup (Δ' <>< Δ))} {κ₂}
    → All₂ _≈_ vs ws → EnvRel φ ρ₁ ρ₂ → κ₁ ≈k κ₂
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
  sim (eval~ {M = fold M} er k) = steps₁ refl (eval~ er (foldK k))
  sim (eval~ {M = unfold M} er k) = steps₁ refl (eval~ er (unfoldK k))
  sim (ret~ r halt) = stops (cong stop (sym (obs≈ r)))
  sim (ret~ r (appL er k)) = steps₁ refl (eval~ er (appR r k))
  sim (ret~ r (appR (clos≈ rs) k)) = steps₁ refl (eval~ (env-clos r rs) k)
  sim (ret~ r (tupK rs er k)) = steps₁ refl (tuple-next~ (r ∷ rs) er k)
  sim (ret~ (tup≈ rs) (closK k)) = steps₁ refl (ret~ (clos≈ rs) k)
  sim (ret~ (tup≈ rs) (getK {i = i} k)) = steps₁ refl (ret~ (lookup₂ rs i) k)
  sim (ret~ r (inlK k)) = steps₁ refl (ret~ (inl≈ r) k)
  sim (ret~ r (inrK k)) = steps₁ refl (ret~ (inr≈ r) k)
  sim (ret~ (inl≈ r) (caseK er k)) = steps₁ refl (eval~ (env-ext r er) k)
  sim (ret~ (inr≈ r) (caseK er k)) = steps₁ refl (eval~ (env-ext r er) k)
  sim (ret~ const≈ (primL er k)) = steps₁ refl (eval~ er (primR k))
  sim (ret~ (const≈ {c = m}) (primR {p} {n} k)) = steps₁ refl (ret~ (δ≈ p n m) k)
  sim (ret~ r (letK er k)) = steps₁ refl (eval~ (env-ext r er) k)
  sim (ret~ r (foldK k)) = steps₁ refl (ret~ (fold≈ r) k)
  sim (ret~ (fold≈ r) (unfoldK k)) = steps₁ refl (ret~ r k)

{- The end theorem: for every closed Clos2μ program ----------------------------}

concretize-correct : ∀ {A} (M : Tm [] A) → Equivalent (Src.sem M) (Tgt.sem (concretize-program M))
concretize-correct M = equivalent (plus-simulation _~_ (eval~ (λ ()) halt) (sim (concretize-program M)))

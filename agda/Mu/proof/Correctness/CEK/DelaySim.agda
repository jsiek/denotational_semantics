{-

  Correctness of delay (Clos3μ → Clos4μ) by a forward simulation between
  the typed machines, as for typed delay
  (proof/Correctness/CEK/DelaySim.agda).

  The machines run in lock step, except that building a closure takes
  three more Clos4μ steps (the code, then the tuple of free variables,
  under pack). Neither machine stops with an error.

  Values are related (_≈_, proof/Semantics/CEK/Rel.agda) when they
  agree, except that a Clos3μ closure of N and vs is related to the pack
  of code (delay N) and a tuple of values related to vs. Environments are related through the renaming r
  that delay carries (EnvRel): variable x of ρ₁ and variable r x of ρ₂
  hold related values. Continuations are related frame by frame: appL
  to callL, appR to callR, and closK to packR.

-}

module Mu.proof.Correctness.CEK.DelaySim where

open import Mu.Language.Type
open import Mu.Language.Clos3
import Mu.Language.Clos4 as C4
open import Mu.Compiler.Delay
open import Mu.Framework.AllUtil using (All; []; _∷_; lookup; _<><_; All₂; lookup₂; _<><₂_)
open import proof.Semantics.CEK.Smallstep
open import proof.Semantics.CEK.Simulation
import Mu.Semantics.CEK.Clos3 as Src
import Mu.Semantics.CEK.Clos4 as Tgt

open import Data.List using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong)

open import Mu.proof.Semantics.CEK.Rel {λ Δ A B → Tm (A ∷ tup Δ ∷ []) B} {λ Δ A B → C4.Tm (A ∷ tup Δ ∷ []) B} (delay (λ x → x))

{- The simulation relation -----------------------------------------------------}

infix 4 _≈k_ _~_

EnvRel : ∀ {Γ Δ} → Ren Γ Δ → Src.Env Γ → Tgt.Env Δ → Set
EnvRel r ρ₁ ρ₂ = ∀ {A} (x : _ ∋ A) → lookup ρ₁ x ≈ lookup ρ₂ (r x)

data _≈k_ : ∀ {A} → Src.Cont A → Tgt.Cont A → Set where
  halt : ∀ {A} → Src.halt {A} ≈k Tgt.halt
  appL : ∀ {Γ Δ A B} {r : Ren Γ Δ} {M : Tm Γ A} {ρ₁ : Src.Env Γ} {ρ₂ : Tgt.Env Δ} {κ₁ : Src.Cont B} {κ₂} → EnvRel r ρ₁ ρ₂ → κ₁ ≈k κ₂
    → Src.appL M ρ₁ κ₁ ≈k Tgt.callL (delay r M) ρ₂ κ₂
  appR : ∀ {A B v w κ₁ κ₂} → v ≈ w → κ₁ ≈k κ₂ → Src.appR {A} {B} v κ₁ ≈k Tgt.callR w κ₂
  tupK : ∀ {Γ Δ Δ' A Δ''} {r : Ren Γ Δ} {vs : All Src.Val Δ'} {ws : All Tgt.Val Δ'} {Ms : All _ Δ''} {ρ₁ : Src.Env Γ}
      {ρ₂ : Tgt.Env Δ} {κ₁ κ₂}
    → All₂ _≈_ vs ws → EnvRel r ρ₁ ρ₂ → κ₁ ≈k κ₂
    → Src.tupK {A = A} vs Ms ρ₁ κ₁ ≈k Tgt.tupK ws (delays r Ms) ρ₂ κ₂
  closK : ∀ {Δ A B N κ₁ κ₂} → κ₁ ≈k κ₂ → Src.closK {Δ} {A} {B} N κ₁ ≈k Tgt.packR (Tgt.code (delay (λ x → x) N)) κ₂
  getK : ∀ {Δ A i κ₁ κ₂} → κ₁ ≈k κ₂ → Src.getK {Δ} {A} i κ₁ ≈k Tgt.getK i κ₂
  inlK : ∀ {A B κ₁ κ₂} → κ₁ ≈k κ₂ → Src.inlK {A} {B} κ₁ ≈k Tgt.inlK κ₂
  inrK : ∀ {A B κ₁ κ₂} → κ₁ ≈k κ₂ → Src.inrK {A} {B} κ₁ ≈k Tgt.inrK κ₂
  caseK : ∀ {Γ Δ A B C} {r : Ren Γ Δ} {M : Tm (A ∷ Γ) C} {N : Tm (B ∷ Γ) C} {ρ₁ : Src.Env Γ} {ρ₂ : Tgt.Env Δ} {κ₁ κ₂} → EnvRel r ρ₁ ρ₂ → κ₁ ≈k κ₂
    → Src.caseK M N ρ₁ κ₁ ≈k Tgt.caseK (delay (ext r) M) (delay (ext r) N) ρ₂ κ₂
  primL : ∀ {Γ Δ} {r : Ren Γ Δ} {p M} {ρ₁ : Src.Env Γ} {ρ₂ : Tgt.Env Δ} {κ₁ κ₂} → EnvRel r ρ₁ ρ₂ → κ₁ ≈k κ₂
    → Src.primL p M ρ₁ κ₁ ≈k Tgt.primL p (delay r M) ρ₂ κ₂
  primR : ∀ {p n κ₁ κ₂} → κ₁ ≈k κ₂ → Src.primR p n κ₁ ≈k Tgt.primR p n κ₂
  letK : ∀ {Γ Δ A B} {r : Ren Γ Δ} {N : Tm (A ∷ Γ) B} {ρ₁ : Src.Env Γ} {ρ₂ : Tgt.Env Δ} {κ₁ κ₂} → EnvRel r ρ₁ ρ₂ → κ₁ ≈k κ₂
    → Src.letK N ρ₁ κ₁ ≈k Tgt.letK (delay (ext r) N) ρ₂ κ₂
  foldK : ∀ {A κ₁ κ₂} → κ₁ ≈k κ₂ → Src.foldK {A} κ₁ ≈k Tgt.foldK κ₂
  unfoldK : ∀ {A κ₁ κ₂} → κ₁ ≈k κ₂ → Src.unfoldK {A} κ₁ ≈k Tgt.unfoldK κ₂

data _~_ : Src.State → Tgt.State → Set where
  eval~ : ∀ {Γ Δ A} {r : Ren Γ Δ} {M : Tm Γ A} {ρ₁} {ρ₂ : Tgt.Env Δ} {κ₁ κ₂} → EnvRel r ρ₁ ρ₂ → κ₁ ≈k κ₂
    → Src.eval M ρ₁ κ₁ ~ Tgt.eval (delay r M) ρ₂ κ₂
  ret~ : ∀ {A} {v : Src.Val A} {w κ₁ κ₂} → v ≈ w → κ₁ ≈k κ₂ → Src.ret v κ₁ ~ Tgt.ret w κ₂

env-ext : ∀ {Γ Δ B} {r : Ren Γ Δ} {ρ₁ : Src.Env Γ} {ρ₂ : Tgt.Env Δ} {v : Src.Val B} {w} → v ≈ w → EnvRel r ρ₁ ρ₂
  → EnvRel (ext r) (v ∷ ρ₁) (w ∷ ρ₂)
env-ext r er Z = r
env-ext r er (S x) = er x

{- The simulation, for any Clos4μ program P ------------------------------------}

module _ {T : Type} (P : C4.Tm [] T) where

  L₂ = Tgt.sem P

  tuple-next~ : ∀ {Γ Δ Δ' Δ''} {r : Ren Γ Δ} {vs : All Src.Val Δ'} {ws : All Tgt.Val Δ'} {Ms : All _ Δ''} {ρ₁ : Src.Env Γ}
      {ρ₂ : Tgt.Env Δ} {κ₁ : Src.Cont (tup (Δ' <>< Δ''))} {κ₂}
    → All₂ _≈_ vs ws → EnvRel r ρ₁ ρ₂ → κ₁ ≈k κ₂
    → Src.tuple-next vs Ms ρ₁ κ₁ ~ Tgt.tuple-next ws (delays r Ms) ρ₂ κ₂
  tuple-next~ {Ms = []} rs er k = ret~ (tup≈ (rs <><₂ [])) k
  tuple-next~ {Ms = M ∷ Ms} rs er k = eval~ er (tupK rs er k)

  sim : ∀ {s₁ s₂} → s₁ ~ s₂ → Answers L₂ _~_ (Src.step s₁) s₂
  sim (eval~ {M = ` x} er k) = steps₁ refl (ret~ (er x) k)
  sim (eval~ {M = clos N Ms} er k) = steps (plus refl (refl ◅ refl ◅ refl ◅ ε)) (tuple-next~ [] er (closK k))
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
  sim (ret~ r (appR (clos≈ rs) k)) = steps₁ refl (eval~ (λ { Z → r ; (S Z) → tup≈ rs }) k)
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

{- The end theorem: for every Clos3μ program -----------------------------------}

delay-correct : ∀ {A} (M : Tm [] A) → Equivalent (Src.sem M) (Tgt.sem (delay-program M))
delay-correct M = equivalent (plus-simulation _~_ (eval~ (λ ()) halt) (sim (delay-program M)))

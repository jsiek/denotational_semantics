{-

  Correctness of enclose (ISWIMμ → Closμ) by a forward simulation
  between the typed machines, as for typed enclose
  (proof/Correctness/CEK/EncloseSim.agda).

  The machines run in lock step, except that evaluating a function (one
  ISWIMμ step) takes several Closμ steps: the closure evaluates the
  variables that it captures (capture), which collects exactly the
  environment, and then builds the closure.

  Values are related (_≈_, proof/Semantics/CEK/Rel.agda) when they
  agree, except that an ISWIMμ closure of N and ρ is related to a Closμ
  closure of enclose N whose captured values are related to ρ. Environments are related pointwise;
  continuations are related frame by frame. Neither machine stops with
  an error.

-}

module Mu.proof.Correctness.AbstractMachines.EncloseSim where

open import Mu.Language.Type
open import Mu.Language.ISWIM
import Mu.Language.Clos as C2
open import Mu.Compiler.Enclose
open import Mu.Framework.AllUtil using (All; []; _∷_; tab; lookup; _<><_; _<><ᵃ_; All₂; lookup₂; _<><₂_; tab-lookup₂)
open import proof.Semantics.CEK.Smallstep
open import proof.Semantics.CEK.Simulation
import Mu.Semantics.AbstractMachines.ISWIM as Src
import Mu.Semantics.AbstractMachines.Clos as Tgt

open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong)

open import Mu.proof.Semantics.AbstractMachines.Rel {λ Δ A B → Tm (A ∷ Δ) B} {λ Δ A B → C2.Tm (A ∷ Δ) B} enclose

{- The simulation relation -----------------------------------------------------}

infix 4 _≈k_ _~_

_≈ρ_ : ∀ {Γ} → Src.Env Γ → Tgt.Env Γ → Set
_≈ρ_ = All₂ _≈_

data _≈k_ : ∀ {A} → Src.Cont A → Tgt.Cont A → Set where
  halt : ∀ {A} → Src.halt {A} ≈k Tgt.halt
  appL : ∀ {Γ A B M} {ρ₁ : Src.Env Γ} {ρ₂ κ₁ κ₂} → ρ₁ ≈ρ ρ₂ → κ₁ ≈k κ₂
    → Src.appL {A = A} {B} M ρ₁ κ₁ ≈k Tgt.appL (enclose M) ρ₂ κ₂
  appR : ∀ {A B f g κ₁ κ₂} → f ≈ g → κ₁ ≈k κ₂ → Src.appR {A} {B} f κ₁ ≈k Tgt.appR g κ₂
  tupK : ∀ {Γ Δ' A Δ} {vs : All Src.Val Δ'} {ws : All Tgt.Val Δ'} {Ms : All (Tm Γ) Δ} {ρ₁ : Src.Env Γ} {ρ₂ κ₁ κ₂}
    → All₂ _≈_ vs ws → ρ₁ ≈ρ ρ₂ → κ₁ ≈k κ₂
    → Src.tupK {Δ' = Δ'} {A} vs Ms ρ₁ κ₁ ≈k Tgt.tupK ws (encs Ms) ρ₂ κ₂
  getK : ∀ {Δ A i κ₁ κ₂} → κ₁ ≈k κ₂ → Src.getK {Δ} {A} i κ₁ ≈k Tgt.getK i κ₂
  inlK : ∀ {A B κ₁ κ₂} → κ₁ ≈k κ₂ → Src.inlK {A} {B} κ₁ ≈k Tgt.inlK κ₂
  inrK : ∀ {A B κ₁ κ₂} → κ₁ ≈k κ₂ → Src.inrK {A} {B} κ₁ ≈k Tgt.inrK κ₂
  caseK : ∀ {Γ A B C M N} {ρ₁ : Src.Env Γ} {ρ₂ κ₁ κ₂} → ρ₁ ≈ρ ρ₂ → κ₁ ≈k κ₂
    → Src.caseK {A = A} {B} {C} M N ρ₁ κ₁ ≈k Tgt.caseK (enclose M) (enclose N) ρ₂ κ₂
  primL : ∀ {Γ p M} {ρ₁ : Src.Env Γ} {ρ₂ κ₁ κ₂} → ρ₁ ≈ρ ρ₂ → κ₁ ≈k κ₂
    → Src.primL p M ρ₁ κ₁ ≈k Tgt.primL p (enclose M) ρ₂ κ₂
  primR : ∀ {p n κ₁ κ₂} → κ₁ ≈k κ₂ → Src.primR p n κ₁ ≈k Tgt.primR p n κ₂
  letK : ∀ {Γ A B N} {ρ₁ : Src.Env Γ} {ρ₂ κ₁ κ₂} → ρ₁ ≈ρ ρ₂ → κ₁ ≈k κ₂
    → Src.letK {A = A} {B} N ρ₁ κ₁ ≈k Tgt.letK (enclose N) ρ₂ κ₂
  foldK : ∀ {A κ₁ κ₂} → κ₁ ≈k κ₂ → Src.foldK {A} κ₁ ≈k Tgt.foldK κ₂
  unfoldK : ∀ {A κ₁ κ₂} → κ₁ ≈k κ₂ → Src.unfoldK {A} κ₁ ≈k Tgt.unfoldK κ₂

data _~_ : Src.State → Tgt.State → Set where
  eval~ : ∀ {Γ A} {M : Tm Γ A} {ρ₁ ρ₂ κ₁ κ₂} → ρ₁ ≈ρ ρ₂ → κ₁ ≈k κ₂
    → Src.eval M ρ₁ κ₁ ~ Tgt.eval (enclose M) ρ₂ κ₂
  ret~ : ∀ {A} {v : Src.Val A} {w κ₁ κ₂} → v ≈ w → κ₁ ≈k κ₂ → Src.ret v κ₁ ~ Tgt.ret w κ₂

{- The simulation, for any Closμ program P ------------------------------------}

module _ {T : Type} (P : C2.Tm [] T) where

  L₂ = Tgt.sem P

  {- evaluating the variables f x of Γ as the rest of a tuple -}
  capture : ∀ {Γ Δ Δ'} (f : ∀ {A} → Δ ∋ A → Γ ∋ A) (vs : All Tgt.Val Δ') (ρ : Tgt.Env Γ) (κ : Tgt.Cont (tup (Δ' <>< Δ)))
    → Star L₂ (Tgt.tuple-next vs (tab (λ x → C2.` f x)) ρ κ) (Tgt.ret (Tgt.tup (vs <><ᵃ tab (λ x → lookup ρ (f x)))) κ)
  capture {Δ = []} f vs ρ κ = ε
  capture {Δ = A ∷ Δ} f vs ρ κ = refl ◅ refl ◅ capture (λ x → f (S x)) (lookup ρ (f Z) ∷ vs) ρ κ

  tuple-next~ : ∀ {Γ Δ' Δ} {vs : All Src.Val Δ'} {ws : All Tgt.Val Δ'} {Ms : All (Tm Γ) Δ} {ρ₁ : Src.Env Γ} {ρ₂} {κ₁ : Src.Cont (tup (Δ' <>< Δ))} {κ₂}
    → All₂ _≈_ vs ws → ρ₁ ≈ρ ρ₂ → κ₁ ≈k κ₂
    → Src.tuple-next vs Ms ρ₁ κ₁ ~ Tgt.tuple-next ws (encs Ms) ρ₂ κ₂
  tuple-next~ {Ms = []} rs er k = ret~ (tup≈ (rs <><₂ [])) k
  tuple-next~ {Ms = M ∷ Ms} rs er k = eval~ er (tupK rs er k)

  sim : ∀ {s₁ s₂} → s₁ ~ s₂ → Answers L₂ _~_ (Src.step s₁) s₂
  sim (eval~ {M = ` x} er k) = steps₁ refl (ret~ (lookup₂ er x) k)
  sim (eval~ {M = lam N} {ρ₂ = ρ₂} {κ₂ = κ₂} er k) =
    steps (plus refl (capture (λ x → x) [] ρ₂ (Tgt.closK (enclose N) κ₂) ◅◅ (refl ◅ ε)))
          (ret~ (clos≈ (tab-lookup₂ er)) k)
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
  sim (ret~ r (appR (clos≈ er) k)) = steps₁ refl (eval~ (r ∷ er) k)
  sim (ret~ r (tupK rs er k)) = steps₁ refl (tuple-next~ (r ∷ rs) er k)
  sim (ret~ (tup≈ rs) (getK {i = i} k)) = steps₁ refl (ret~ (lookup₂ rs i) k)
  sim (ret~ r (inlK k)) = steps₁ refl (ret~ (inl≈ r) k)
  sim (ret~ r (inrK k)) = steps₁ refl (ret~ (inr≈ r) k)
  sim (ret~ (inl≈ r) (caseK er k)) = steps₁ refl (eval~ (r ∷ er) k)
  sim (ret~ (inr≈ r) (caseK er k)) = steps₁ refl (eval~ (r ∷ er) k)
  sim (ret~ const≈ (primL er k)) = steps₁ refl (eval~ er (primR k))
  sim (ret~ (const≈ {c = m}) (primR {p} {n} k)) = steps₁ refl (ret~ (δ≈ p n m) k)
  sim (ret~ r (letK er k)) = steps₁ refl (eval~ (r ∷ er) k)
  sim (ret~ r (foldK k)) = steps₁ refl (ret~ (fold≈ r) k)
  sim (ret~ (fold≈ r) (unfoldK k)) = steps₁ refl (ret~ r k)

{- The end theorem: for every closed ISWIMμ program ----------------------------}

enclose-correct : ∀ {A} (M : Tm [] A) → Equivalent (Src.sem M) (Tgt.sem (enclose M))
enclose-correct M = equivalent (plus-simulation _~_ (eval~ [] halt) (sim (enclose M)))

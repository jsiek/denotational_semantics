{-

  A CEK machine for Clos4μ (Mu/Language/Clos4.agda), as the one for
  Clos3μ (Mu/Semantics/CEK/Clos3.agda). The value of code is the code;
  a closure is a packed pair of code and an environment of the same
  types Δ. callc L M evaluates the closure and the argument, then runs
  the closure's code with its environment and the argument.

-}

module Mu.Semantics.CEK.Clos4 where

open import Framework.Primitives using (Int)
open import Mu.Language.Type
open import Mu.Language.Clos4
open import Mu.Framework.AllUtil using (All; []; _∷_; lookup; _<><_; _<><ᵃ_)
open import Semantics.CEK.Smallstep using (Machine; Next; next; stop; machine)

open import Data.Integer using (ℤ)
open import Data.List using ([]; _∷_)

open import Mu.Semantics.CEK.Values (λ Δ A B → Tm (A ∷ tup Δ ∷ []) B) public

data Cont : Type → Set where
  halt : ∀ {A} → Cont A
  callL : ∀ {Γ A B} → Tm Γ A → Env Γ → Cont B → Cont (A ⇒ B)
  callR : ∀ {A B} → Val (A ⇒ B) → Cont B → Cont A
  packL : ∀ {Γ Δ A B} → Tm Γ (tup Δ) → Env Γ → Cont (A ⇒ B) → Cont (code Δ A B)
  packR : ∀ {Δ A B} → Val (code Δ A B) → Cont (A ⇒ B) → Cont (tup Δ)
  {- the values so far (newest first) and the components still to evaluate -}
  tupK : ∀ {Γ Δ' A Δ} → All Val Δ' → All (Tm Γ) Δ → Env Γ → Cont (tup (Δ' <>< (A ∷ Δ))) → Cont A
  getK : ∀ {Δ A} → Δ ∋ A → Cont A → Cont (tup Δ)
  inlK : ∀ {A B} → Cont (A ⊹ B) → Cont A
  inrK : ∀ {A B} → Cont (A ⊹ B) → Cont B
  caseK : ∀ {Γ A B C} → Tm (A ∷ Γ) C → Tm (B ∷ Γ) C → Env Γ → Cont C → Cont (A ⊹ B)
  primL : ∀ {Γ} p → Tm Γ (base Int) → Env Γ → Cont (out-ty p) → Cont (base Int)
  primR : ∀ p → ℤ → Cont (out-ty p) → Cont (base Int)
  letK : ∀ {Γ A B} → Tm (A ∷ Γ) B → Env Γ → Cont B → Cont A
  foldK : ∀ {A} → Cont (μ A) → Cont (unroll A)
  unfoldK : ∀ {A} → Cont (unroll A) → Cont (μ A)

data State : Set where
  eval : ∀ {Γ A} → Tm Γ A → Env Γ → Cont A → State
  ret : ∀ {A} → Val A → Cont A → State

{- evaluate the rest of a tuple's components, or build it -}
tuple-next : ∀ {Γ Δ' Δ} → All Val Δ' → All (Tm Γ) Δ → Env Γ → Cont (tup (Δ' <>< Δ)) → State
tuple-next vs [] ρ κ = ret (tup (vs <><ᵃ [])) κ
tuple-next vs (M ∷ Ms) ρ κ = eval M ρ (tupK vs Ms ρ κ)

step : State → Next State
step (eval (` x) ρ κ) = next (ret (lookup ρ x) κ)
step (eval (code N) ρ κ) = next (ret (code N) κ)
step (eval (pack L M) ρ κ) = next (eval L ρ (packL M ρ κ))
step (eval (callc L M) ρ κ) = next (eval L ρ (callL M ρ κ))
step (eval (lit B c) ρ κ) = next (ret (const c) κ)
step (eval (tuple Ms) ρ κ) = next (tuple-next [] Ms ρ κ)
step (eval (get i M) ρ κ) = next (eval M ρ (getK i κ))
step (eval (inl M) ρ κ) = next (eval M ρ (inlK κ))
step (eval (inr M) ρ κ) = next (eval M ρ (inrK κ))
step (eval (case L M N) ρ κ) = next (eval L ρ (caseK M N ρ κ))
step (eval (prim p L M) ρ κ) = next (eval L ρ (primL p M ρ κ))
step (eval (let′ M N) ρ κ) = next (eval M ρ (letK N ρ κ))
step (eval (fold M) ρ κ) = next (eval M ρ (foldK κ))
step (eval (unfold M) ρ κ) = next (eval M ρ (unfoldK κ))
step (ret v halt) = stop (obs v)
step (ret f (callL M ρ κ)) = next (eval M ρ (callR f κ))
step (ret w (callR (pack (code N) e) κ)) = next (eval N (w ∷ e ∷ []) κ)
step (ret c (packL M ρ κ)) = next (eval M ρ (packR c κ))
step (ret e (packR c κ)) = next (ret (pack c e) κ)
step (ret v (tupK vs Ms ρ κ)) = next (tuple-next (v ∷ vs) Ms ρ κ)
step (ret (tup vs) (getK i κ)) = next (ret (lookup vs i) κ)
step (ret v (inlK κ)) = next (ret (inl v) κ)
step (ret v (inrK κ)) = next (ret (inr v) κ)
step (ret (inl v) (caseK M N ρ κ)) = next (eval M (v ∷ ρ) κ)
step (ret (inr v) (caseK M N ρ κ)) = next (eval N (v ∷ ρ) κ)
step (ret (const n) (primL p M ρ κ)) = next (eval M ρ (primR p n κ))
step (ret (const m) (primR p n κ)) = next (ret (δᵀ p n m) κ)
step (ret v (letK N ρ κ)) = next (eval N (v ∷ ρ) κ)
step (ret v (foldK κ)) = next (ret (fold v) κ)
step (ret (fold v) (unfoldK κ)) = next (ret v κ)

{- a program starts in the empty environment with the empty continuation -}
sem : ∀ {A} → Tm [] A → Machine
sem M = machine State step (eval M [] halt)

{-

  A CEK machine for Clos3μ (Mu/Language/Clos3.agda), as the one for
  Clos2μ (Mu/Semantics/CEK/Clos2.agda): a closure evaluates the tuple of
  its free variables, and its code runs with the argument and that
  tuple.

-}

module Mu.Semantics.CEK.Clos3 where

open import Framework.Primitives using (Base; base-rep; Int)
open import Language.Prim using (Prim; sub; eq)
open import Mu.Language.Type
open import Mu.Language.Clos3
open import Mu.Framework.AllUtil using (All; []; _∷_; lookup; _<><_; _<><ᵃ_)
open import Semantics.Observation using (Obs; o-const; o-fun; o-tuple; o-inl; o-inr)
open import Semantics.CEK.Smallstep using (Machine; Next; next; stop; machine)

open import Data.Bool using (if_then_else_)
open import Data.Integer using (ℤ; _-_; _≟_)
open import Data.List using (List; []; _∷_)
open import Relation.Nullary using (does)

data Val : Type → Set where
  clos : ∀ {Δ A B} → Tm (A ∷ tup Δ ∷ []) B → All Val Δ → Val (A ⇒ B)
  const : ∀ {B} → base-rep B → Val (base B)
  tup : ∀ {Δ} → All Val Δ → Val (tup Δ)
  inl : ∀ {A B} → Val A → Val (A ⊹ B)
  inr : ∀ {A B} → Val B → Val (A ⊹ B)
  fold : ∀ {A c} → Val (unroll A {c}) → Val (μ A {c})

Env : Ctx → Set
Env = All Val

data Cont : Type → Set where
  halt : ∀ {A} → Cont A
  appL : ∀ {Γ A B} → Tm Γ A → Env Γ → Cont B → Cont (A ⇒ B)
  appR : ∀ {A B} → Val (A ⇒ B) → Cont B → Cont A
  {- the values so far (newest first) and the components still to evaluate -}
  tupK : ∀ {Γ Δ' A Δ} → All Val Δ' → All (Tm Γ) Δ → Env Γ → Cont (tup (Δ' <>< (A ∷ Δ))) → Cont A
  closK : ∀ {Δ A B} → Tm (A ∷ tup Δ ∷ []) B → Cont (A ⇒ B) → Cont (tup Δ)
  getK : ∀ {Δ A} → Δ ∋ A → Cont A → Cont (tup Δ)
  inlK : ∀ {A B} → Cont (A ⊹ B) → Cont A
  inrK : ∀ {A B} → Cont (A ⊹ B) → Cont B
  caseK : ∀ {Γ A B C} → Tm (A ∷ Γ) C → Tm (B ∷ Γ) C → Env Γ → Cont C → Cont (A ⊹ B)
  primL : ∀ {Γ} p → Tm Γ (base Int) → Env Γ → Cont (out-ty p) → Cont (base Int)
  primR : ∀ p → ℤ → Cont (out-ty p) → Cont (base Int)
  letK : ∀ {Γ A B} → Tm (A ∷ Γ) B → Env Γ → Cont B → Cont A
  foldK : ∀ {A c} → Cont (μ A {c}) → Cont (unroll A {c})
  unfoldK : ∀ {A c} → Cont (unroll A {c}) → Cont (μ A {c})

data State : Set where
  eval : ∀ {Γ A} → Tm Γ A → Env Γ → Cont A → State
  ret : ∀ {A} → Val A → Cont A → State

obs : ∀ {A} → Val A → Obs
obs-all : ∀ {Δ} → All Val Δ → List Obs
obs (clos _ _) = o-fun
obs (const {B} c) = o-const B c
obs (tup vs) = o-tuple (obs-all vs)
obs (inl v) = o-inl (obs v)
obs (inr v) = o-inr (obs v)
obs (fold v) = obs v
obs-all [] = []
obs-all (v ∷ vs) = obs v ∷ obs-all vs

{- a primitive on two integers: eq gives inl ⟨⟩ for true -}
δᵀ : ∀ p → ℤ → ℤ → Val (out-ty p)
δᵀ sub n m = const (n - m)
δᵀ eq n m = if does (n ≟ m) then inl (tup []) else inr (tup [])

{- evaluate the rest of a tuple's components, or build it -}
tuple-next : ∀ {Γ Δ' Δ} → All Val Δ' → All (Tm Γ) Δ → Env Γ → Cont (tup (Δ' <>< Δ)) → State
tuple-next vs [] ρ κ = ret (tup (vs <><ᵃ [])) κ
tuple-next vs (M ∷ Ms) ρ κ = eval M ρ (tupK vs Ms ρ κ)

step : State → Next State
step (eval (` x) ρ κ) = next (ret (lookup ρ x) κ)
step (eval (clos N Ms) ρ κ) = next (tuple-next [] Ms ρ (closK N κ))
step (eval (app L M) ρ κ) = next (eval L ρ (appL M ρ κ))
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
step (ret f (appL M ρ κ)) = next (eval M ρ (appR f κ))
step (ret w (appR (clos N vs) κ)) = next (eval N (w ∷ tup vs ∷ []) κ)
step (ret v (tupK vs Ms ρ κ)) = next (tuple-next (v ∷ vs) Ms ρ κ)
step (ret (tup vs) (closK N κ)) = next (ret (clos N vs) κ)
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

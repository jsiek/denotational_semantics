{-

  A CEK machine for Clos3ᵀ (Language/Typed/Clos3.agda), as the one for
  Clos2ᵀ (Semantics/CEK/Typed/Clos2.agda), with environments typed by
  contexts of types: a closure evaluates the tuple of its free
  variables, and its code runs with the argument and that tuple.

-}

module Semantics.CEK.Typed.Clos3 where

open import Framework.Primitives using (Base; base-rep; Int)
open import Language.Prim using (Prim; sub; eq)
open import Language.Typed.Type renaming (_≟_ to _≟F_)
open import Language.Typed.Clos3
open import Semantics.Observation using (Obs; o-const; o-fun; o-tuple; o-inl; o-inr; o-error)
open import Semantics.CEK.Smallstep using (Machine; Next; next; stop; machine)
open import Framework.VecUtil using (more; collected)

open import Data.Bool using (if_then_else_)
open import Data.Fin using (Fin)
open import Data.Integer using (ℤ; _-_; _≟_)
open import Data.List using (List; []; _∷_; length)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Nat using (ℕ; suc; _+_)
open import Data.Vec using (Vec; []; _∷_; lookup)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (yes; no; does)

data Val : Ty → Set where
  clos : ∀ {n} → Tm (Any ∷ ⟪ tup n ⟫ ∷ []) Any → Vec (Val Any) n → Val ⟪ fun ⟫
  const : ∀ {B} → base-rep B → Val ⟪ base B ⟫
  tup : ∀ {n} → Vec (Val Any) n → Val ⟪ tup n ⟫
  inl inr : Val Any → Val ⟪ sum ⟫
  dyn : (G : Flat) → Val ⟪ G ⟫ → Val Any

Env : Ctx → Set
Env Γ = All Val Γ

_!_ : ∀ {Γ A} → Env Γ → Γ ∋ A → Val A
(v ∷ ρ) ! Z = v
(v ∷ ρ) ! S x = ρ ! x

data Cont : Ty → Set where
  halt : Cont Any
  appL : ∀ {Γ} → Tm Γ Any → Env Γ → Cont Any → Cont ⟪ fun ⟫
  appR : Val ⟪ fun ⟫ → Cont Any → Cont Any
  {- the values so far (reversed) and the components still to evaluate -}
  tupK : ∀ {Γ n j} (vs : List (Val Any)) → Vec (Tm Γ Any) j → Env Γ
    → length vs + suc j ≡ n → Cont ⟪ tup n ⟫ → Cont Any
  closK : ∀ {n} → Tm (Any ∷ ⟪ tup n ⟫ ∷ []) Any → Cont ⟪ fun ⟫ → Cont ⟪ tup n ⟫
  getK : ∀ {n} → Fin n → Cont Any → Cont ⟪ tup n ⟫
  inlK inrK : Cont ⟪ sum ⟫ → Cont Any
  caseK : ∀ {Γ} → Tm (Any ∷ Γ) Any → Tm (Any ∷ Γ) Any → Env Γ → Cont Any → Cont ⟪ sum ⟫
  primL : ∀ {Γ} p → Tm Γ ⟪ base Int ⟫ → Env Γ → Cont ⟪ out-flat p ⟫ → Cont ⟪ base Int ⟫
  primR : ∀ p → ℤ → Cont ⟪ out-flat p ⟫ → Cont ⟪ base Int ⟫
  letK : ∀ {Γ} → Tm (Any ∷ Γ) Any → Env Γ → Cont Any → Cont Any
  injK : ∀ G → Cont Any → Cont ⟪ G ⟫
  projK : ∀ G → Cont ⟪ G ⟫ → Cont Any

data State : Set where
  eval : ∀ {Γ A} → Tm Γ A → Env Γ → Cont A → State
  ret : ∀ {A} → Val A → Cont A → State

obs : ∀ {A} → Val A → Obs
obs-vec : ∀ {n} → Vec (Val Any) n → List Obs
obs (clos _ _) = o-fun
obs (const {B} c) = o-const B c
obs (tup vs) = o-tuple (obs-vec vs)
obs (inl v) = o-inl (obs v)
obs (inr v) = o-inr (obs v)
obs (dyn G v) = obs v
obs-vec [] = []
obs-vec (v ∷ vs) = obs v ∷ obs-vec vs

{- a primitive on two integers: eq gives inl ⟨⟩ for true -}
δᵀ : ∀ p → ℤ → ℤ → Val ⟪ out-flat p ⟫
δᵀ sub n m = const (n - m)
δᵀ eq n m = if does (n ≟ m) then inl (dyn (tup 0) (tup [])) else inr (dyn (tup 0) (tup []))

{- evaluate the rest of a tuple's components, or build it -}
tuple-next : ∀ {Γ n j} (vs : List (Val Any)) → Vec (Tm Γ Any) j → Env Γ
  → length vs + j ≡ n → Cont ⟪ tup n ⟫ → State
tuple-next vs [] ρ e κ = ret (tup (collected vs e)) κ
tuple-next vs (M ∷ Ms) ρ e κ = eval M ρ (tupK vs Ms ρ e κ)

step : State → Next State
step (eval (` x) ρ κ) = next (ret (ρ ! x) κ)
step (eval (clos N Ms) ρ κ) = next (tuple-next [] Ms ρ refl (closK N κ))
step (eval (app L M) ρ κ) = next (eval L ρ (appL M ρ κ))
step (eval (lit B c) ρ κ) = next (ret (const c) κ)
step (eval (tuple Ms) ρ κ) = next (tuple-next [] Ms ρ refl κ)
step (eval (get i M) ρ κ) = next (eval M ρ (getK i κ))
step (eval (inl M) ρ κ) = next (eval M ρ (inlK κ))
step (eval (inr M) ρ κ) = next (eval M ρ (inrK κ))
step (eval (case L M N) ρ κ) = next (eval L ρ (caseK M N ρ κ))
step (eval (prim p L M) ρ κ) = next (eval L ρ (primL p M ρ κ))
step (eval (let′ M N) ρ κ) = next (eval M ρ (letK N ρ κ))
step (eval (inject G M) ρ κ) = next (eval M ρ (injK G κ))
step (eval (project G M) ρ κ) = next (eval M ρ (projK G κ))
step (ret v halt) = stop (obs v)
step (ret f (appL M ρ κ)) = next (eval M ρ (appR f κ))
step (ret w (appR (clos N vs) κ)) = next (eval N (w ∷ tup vs ∷ []) κ)
step (ret v (tupK vs Ms ρ e κ)) = next (tuple-next (v ∷ vs) Ms ρ (more {v = v} vs e) κ)
step (ret (tup vs) (closK N κ)) = next (ret (clos N vs) κ)
step (ret (tup vs) (getK i κ)) = next (ret (lookup vs i) κ)
step (ret v (inlK κ)) = next (ret (inl v) κ)
step (ret v (inrK κ)) = next (ret (inr v) κ)
step (ret (inl v) (caseK M N ρ κ)) = next (eval M (v ∷ ρ) κ)
step (ret (inr v) (caseK M N ρ κ)) = next (eval N (v ∷ ρ) κ)
step (ret (const n) (primL p M ρ κ)) = next (eval M ρ (primR p n κ))
step (ret (const m) (primR p n κ)) = next (ret (δᵀ p n m) κ)
step (ret v (letK N ρ κ)) = next (eval N (v ∷ ρ) κ)
step (ret v (injK G κ)) = next (ret (dyn G v) κ)
{- the only error: a value of another flat type -}
step (ret (dyn H v) (projK G κ)) with H ≟F G
... | yes refl = next (ret v κ)
... | no _ = stop o-error

{- a program starts in the empty environment with the empty continuation -}
sem : Tm [] Any → Machine
sem M = machine State step (eval M [] halt)

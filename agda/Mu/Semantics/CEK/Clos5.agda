{-

  A CEK machine for Clos5μ (Mu/Language/Clos5.agda), as the one for
  Clos4μ (Mu/Semantics/CEK/Clos4.agda), except for code: a program
  runs with its table of definitions, fun-ref f evaluates to the code
  pointer code f, and a call runs definition f, as the Clos5ᵀ machine
  (Semantics/CEK/Typed/Clos5.agda) does. Values, environments and
  continuations are indexed by the table Σ.

  The machine takes its values apart with total functions (int, elems,
  choose, unfoldᵥ; call), since their types say what they are; nothing
  fails. The values and these functions are shared with the machines of
  Impμ, CFGμ and X86μ.

-}

module Mu.Semantics.CEK.Clos5 where

open import Framework.Primitives using (Base; base-rep; Int)
open import Language.Prim using (Prim; sub; eq)
open import Mu.Language.Type
open import Mu.Language.Clos5
open import Mu.Framework.AllUtil using (All; []; _∷_; lookup; _<><_; _<><ᵃ_)
open import Semantics.Observation using (Obs; o-const; o-fun; o-tuple; o-inl; o-inr)
open import Semantics.CEK.Smallstep using (Machine; Next; next; stop; machine)

open import Data.Bool using (if_then_else_)
open import Data.Integer using (ℤ; _-_; _≟_)
open import Data.List using (List; []; _∷_)
open import Relation.Nullary using (does)

data Val (Σ : List DSig) : Type → Set where
  code : ∀ {Δ A B} → Σ ∋ sig Δ A B → Val Σ (code Δ A B)
  pack : ∀ {Δ A B} → Val Σ (code Δ A B) → Val Σ (tup Δ) → Val Σ (A ⇒ B)
  const : ∀ {B} → base-rep B → Val Σ (base B)
  tup : ∀ {Δ} → All (Val Σ) Δ → Val Σ (tup Δ)
  inl : ∀ {A B} → Val Σ A → Val Σ (A ⊹ B)
  inr : ∀ {A B} → Val Σ B → Val Σ (A ⊹ B)
  fold : ∀ {A} → Val Σ (unroll A) → Val Σ (μ A)

Env : List DSig → Ctx → Set
Env Σ = All (Val Σ)

module _ {Σ : List DSig} where

  obs : ∀ {A} → Val Σ A → Obs
  obs-all : ∀ {Δ} → All (Val Σ) Δ → List Obs
  obs (code _) = o-fun
  obs (pack _ _) = o-fun
  obs (const {B} c) = o-const B c
  obs (tup vs) = o-tuple (obs-all vs)
  obs (inl v) = o-inl (obs v)
  obs (inr v) = o-inr (obs v)
  obs (fold v) = obs v
  obs-all [] = []
  obs-all (v ∷ vs) = obs v ∷ obs-all vs

  int : Val Σ (base Int) → ℤ
  int (const n) = n

  elems : ∀ {Δ} → Val Σ (tup Δ) → All (Val Σ) Δ
  elems (tup vs) = vs

  {- a case on an injection -}
  choose : ∀ {A B} {X : Set} → Val Σ (A ⊹ B) → (Val Σ A → X) → (Val Σ B → X) → X
  choose (inl v) f g = f v
  choose (inr v) f g = g v

  unfoldᵥ : ∀ {A} → Val Σ (μ A) → Val Σ (unroll A)
  unfoldᵥ (fold v) = v

  {- a primitive on two integers: eq gives inl ⟨⟩ for true -}
  δᵀ : ∀ p → ℤ → ℤ → Val Σ (out-ty p)
  δᵀ sub n m = const (n - m)
  δᵀ eq n m = if does (n ≟ m) then inl (tup []) else inr (tup [])

data Cont (Σ : List DSig) : Type → Set where
  halt : ∀ {A} → Cont Σ A
  callL : ∀ {Γ A B} → Tm Σ Γ A → Env Σ Γ → Cont Σ B → Cont Σ (A ⇒ B)
  callR : ∀ {A B} → Val Σ (A ⇒ B) → Cont Σ B → Cont Σ A
  packL : ∀ {Γ Δ A B} → Tm Σ Γ (tup Δ) → Env Σ Γ → Cont Σ (A ⇒ B) → Cont Σ (code Δ A B)
  packR : ∀ {Δ A B} → Val Σ (code Δ A B) → Cont Σ (A ⇒ B) → Cont Σ (tup Δ)
  {- the values so far (newest first) and the components still to evaluate -}
  tupK : ∀ {Γ Δ' A Δ} → All (Val Σ) Δ' → All (Tm Σ Γ) Δ → Env Σ Γ → Cont Σ (tup (Δ' <>< (A ∷ Δ))) → Cont Σ A
  getK : ∀ {Δ A} → Δ ∋ A → Cont Σ A → Cont Σ (tup Δ)
  inlK : ∀ {A B} → Cont Σ (A ⊹ B) → Cont Σ A
  inrK : ∀ {A B} → Cont Σ (A ⊹ B) → Cont Σ B
  caseK : ∀ {Γ A B C} → Tm Σ (A ∷ Γ) C → Tm Σ (B ∷ Γ) C → Env Σ Γ → Cont Σ C → Cont Σ (A ⊹ B)
  primL : ∀ {Γ} p → Tm Σ Γ (base Int) → Env Σ Γ → Cont Σ (out-ty p) → Cont Σ (base Int)
  primR : ∀ p → ℤ → Cont Σ (out-ty p) → Cont Σ (base Int)
  letK : ∀ {Γ A B} → Tm Σ (A ∷ Γ) B → Env Σ Γ → Cont Σ B → Cont Σ A
  foldK : ∀ {A} → Cont Σ (μ A) → Cont Σ (unroll A)
  unfoldK : ∀ {A} → Cont Σ (unroll A) → Cont Σ (μ A)

data State (Σ : List DSig) : Set where
  eval : ∀ {Γ A} → Tm Σ Γ A → Env Σ Γ → Cont Σ A → State Σ
  ret : ∀ {A} → Val Σ A → Cont Σ A → State Σ

module _ {Σ : List DSig} where

  {- evaluate the rest of a tuple's components, or build it -}
  tuple-next : ∀ {Γ Δ' Δ} → All (Val Σ) Δ' → All (Tm Σ Γ) Δ → Env Σ Γ → Cont Σ (tup (Δ' <>< Δ)) → State Σ
  tuple-next vs [] ρ κ = ret (tup (vs <><ᵃ [])) κ
  tuple-next vs (M ∷ Ms) ρ κ = eval M ρ (tupK vs Ms ρ κ)

  {- what evaluating a term does first -}
  begin : ∀ {Γ A} → Tm Σ Γ A → Env Σ Γ → Cont Σ A → State Σ
  begin (` x) ρ κ = ret (lookup ρ x) κ
  begin (fun-ref f) ρ κ = ret (code f) κ
  begin (pack L M) ρ κ = eval L ρ (packL M ρ κ)
  begin (callc L M) ρ κ = eval L ρ (callL M ρ κ)
  begin (lit B c) ρ κ = ret (const c) κ
  begin (tuple Ms) ρ κ = tuple-next [] Ms ρ κ
  begin (get i M) ρ κ = eval M ρ (getK i κ)
  begin (inl M) ρ κ = eval M ρ (inlK κ)
  begin (inr M) ρ κ = eval M ρ (inrK κ)
  begin (case L M N) ρ κ = eval L ρ (caseK M N ρ κ)
  begin (prim p L M) ρ κ = eval L ρ (primL p M ρ κ)
  begin (let′ M N) ρ κ = eval M ρ (letK N ρ κ)
  begin (fold M) ρ κ = eval M ρ (foldK κ)
  begin (unfold M) ρ κ = eval M ρ (unfoldK κ)

  {- the machine for a program with the definitions ds -}
  module _ (ds : All (Code Σ) Σ) where

    {- run the code of a closure with its environment and the argument -}
    call : ∀ {A B} → Val Σ (A ⇒ B) → Val Σ A → Cont Σ B → State Σ
    call (pack (code f) e) w κ = eval (lookup ds f) (w ∷ e ∷ []) κ

    step : State Σ → Next (State Σ)
    step (eval M ρ κ) = next (begin M ρ κ)
    step (ret v halt) = stop (obs v)
    step (ret f (callL M ρ κ)) = next (eval M ρ (callR f κ))
    step (ret w (callR f κ)) = next (call f w κ)
    step (ret c (packL M ρ κ)) = next (eval M ρ (packR c κ))
    step (ret e (packR c κ)) = next (ret (pack c e) κ)
    step (ret v (tupK vs Ms ρ κ)) = next (tuple-next (v ∷ vs) Ms ρ κ)
    step (ret v (getK i κ)) = next (ret (lookup (elems v) i) κ)
    step (ret v (inlK κ)) = next (ret (inl v) κ)
    step (ret v (inrK κ)) = next (ret (inr v) κ)
    step (ret v (caseK M N ρ κ)) = next (choose v (λ u → eval M (u ∷ ρ) κ) (λ u → eval N (u ∷ ρ) κ))
    step (ret v (primL p M ρ κ)) = next (eval M ρ (primR p (int v) κ))
    step (ret v (primR p n κ)) = next (ret (δᵀ p n (int v)) κ)
    step (ret v (letK N ρ κ)) = next (eval N (v ∷ ρ) κ)
    step (ret v (foldK κ)) = next (ret (fold v) κ)
    step (ret v (unfoldK κ)) = next (ret (unfoldᵥ v) κ)

{- a program starts with main, in the empty environment -}
sem : ∀ {A} → Program A → Machine
sem (program ds M) = machine (State _) (step ds) (eval M [] halt)

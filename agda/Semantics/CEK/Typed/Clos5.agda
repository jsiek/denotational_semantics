{-

  A CEK machine for Clos5ᵀ (Language/Typed/Clos5.agda), as the one for
  Clos4ᵀ (Semantics/CEK/Typed/Clos4.agda), except for code: a program
  runs with its table of definitions, fun-ref f evaluates to the code
  pointer code f, and a call runs definition f, which always exists
  (f is a typed index into the table). Values, environments and
  continuations are indexed by the table Σ.

  The machine takes its values apart with total functions (int, elems,
  choose; call), since their types say what they are; the only error is
  a failed project (proj?). The values and these functions are shared
  with the machines of Impᵀ and CFGᵀ (Semantics/CEK/Typed/Imp.agda,
  CFG.agda).

-}

module Semantics.CEK.Typed.Clos5 where

open import Framework.Primitives using (Base; base-rep; Int)
open import Language.Prim using (Prim; sub; eq)
open import Language.Typed.Type renaming (_≟_ to _≟F_)
open import Language.Typed.Clos5
open import Framework.Lookup using (_!_)
open import Semantics.Observation using (Obs; o-const; o-fun; o-tuple; o-inl; o-inr; o-error)
open import Semantics.CEK.Smallstep using (Machine; Next; next; stop; next?; machine)
open import Framework.VecUtil using (_+ʳ_; _<><_)

open import Data.Bool using (if_then_else_)
open import Data.Fin using (Fin)
open import Data.Integer using (ℤ; _-_; _≟_)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc)
open import Data.Vec using (Vec; []; _∷_; lookup)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (yes; no; does)

data Val (Σ : List ℕ) : Ty → Set where
  code : ∀ {n} → Σ ∋ n → Val Σ (code n)
  pack : ∀ {n} → Val Σ (code n) → Val Σ ⟪ tup n ⟫ → Val Σ ⟪ fun ⟫
  const : ∀ {B} → base-rep B → Val Σ ⟪ base B ⟫
  tup : ∀ {n} → Vec (Val Σ Any) n → Val Σ ⟪ tup n ⟫
  inl inr : Val Σ Any → Val Σ ⟪ sum ⟫
  dyn : (G : Flat) → Val Σ ⟪ G ⟫ → Val Σ Any

Env : List ℕ → Ctx → Set
Env Σ Γ = All (Val Σ) Γ

module _ {Σ : List ℕ} where

  obs : ∀ {A} → Val Σ A → Obs
  obs-vec : ∀ {n} → Vec (Val Σ Any) n → List Obs
  obs (code _) = o-fun
  obs (pack _ _) = o-fun
  obs (const {B} c) = o-const B c
  obs (tup vs) = o-tuple (obs-vec vs)
  obs (inl v) = o-inl (obs v)
  obs (inr v) = o-inr (obs v)
  obs (dyn G v) = obs v
  obs-vec [] = []
  obs-vec (v ∷ vs) = obs v ∷ obs-vec vs

  int : Val Σ ⟪ base Int ⟫ → ℤ
  int (const n) = n

  elems : ∀ {n} → Val Σ ⟪ tup n ⟫ → Vec (Val Σ Any) n
  elems (tup vs) = vs

  {- a case on an injection -}
  choose : ∀ {X : Set} → Val Σ ⟪ sum ⟫ → (Val Σ Any → X) → (Val Σ Any → X) → X
  choose (inl v) f g = f v
  choose (inr v) f g = g v

  {- a primitive on two integers: eq gives inl ⟨⟩ for true -}
  δᵀ : ∀ p → ℤ → ℤ → Val Σ ⟪ out-flat p ⟫
  δᵀ sub n m = const (n - m)
  δᵀ eq n m = if does (n ≟ m) then inl (dyn (tup 0) (tup [])) else inr (dyn (tup 0) (tup []))

  {- the only error: a value of another flat type -}
  proj? : (t : Tag) → Val Σ Any → Maybe (Val Σ ⟪ flat t ⟫)
  proj? t (dyn H v) with H ≟F flat t
  ... | yes refl = just v
  ... | no _ = nothing

data Cont (Σ : List ℕ) : Ty → Set where
  halt : Cont Σ Any
  callL : ∀ {Γ} → Tm Σ Γ Any → Env Σ Γ → Cont Σ Any → Cont Σ ⟪ fun ⟫
  callR : Val Σ ⟪ fun ⟫ → Cont Σ Any → Cont Σ Any
  packL : ∀ {Γ n} → Tm Σ Γ ⟪ tup n ⟫ → Env Σ Γ → Cont Σ ⟪ fun ⟫ → Cont Σ (code n)
  packR : ∀ {n} → Val Σ (code n) → Cont Σ ⟪ fun ⟫ → Cont Σ ⟪ tup n ⟫
  {- the values so far (newest first) and the components still to evaluate -}
  tupK : ∀ {Γ m j} → Vec (Val Σ Any) m → Vec (Tm Σ Γ Any) j → Env Σ Γ → Cont Σ ⟪ tup (m +ʳ suc j) ⟫ → Cont Σ Any
  getK : ∀ {n} → Fin n → Cont Σ Any → Cont Σ ⟪ tup n ⟫
  inlK inrK : Cont Σ ⟪ sum ⟫ → Cont Σ Any
  caseK : ∀ {Γ} → Tm Σ (Any ∷ Γ) Any → Tm Σ (Any ∷ Γ) Any → Env Σ Γ → Cont Σ Any → Cont Σ ⟪ sum ⟫
  primL : ∀ {Γ} p → Tm Σ Γ ⟪ base Int ⟫ → Env Σ Γ → Cont Σ ⟪ out-flat p ⟫ → Cont Σ ⟪ base Int ⟫
  primR : ∀ p → ℤ → Cont Σ ⟪ out-flat p ⟫ → Cont Σ ⟪ base Int ⟫
  letK : ∀ {Γ A B} → Tm Σ (A ∷ Γ) B → Env Σ Γ → Cont Σ B → Cont Σ A
  injK : ∀ G → Cont Σ Any → Cont Σ ⟪ G ⟫
  projK : ∀ t → Cont Σ ⟪ flat t ⟫ → Cont Σ Any

data State (Σ : List ℕ) : Set where
  eval : ∀ {Γ A} → Tm Σ Γ A → Env Σ Γ → Cont Σ A → State Σ
  ret : ∀ {A} → Val Σ A → Cont Σ A → State Σ

module _ {Σ : List ℕ} where

  {- evaluate the rest of a tuple's components, or build it -}
  tuple-next : ∀ {Γ m j} → Vec (Val Σ Any) m → Vec (Tm Σ Γ Any) j → Env Σ Γ → Cont Σ ⟪ tup (m +ʳ j) ⟫ → State Σ
  tuple-next vs [] ρ κ = ret (tup (vs <>< [])) κ
  tuple-next vs (M ∷ Ms) ρ κ = eval M ρ (tupK vs Ms ρ κ)

  {- what evaluating a term does first -}
  begin : ∀ {Γ A} → Tm Σ Γ A → Env Σ Γ → Cont Σ A → State Σ
  begin (` x) ρ κ = ret (ρ ! x) κ
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
  begin (inject G M) ρ κ = eval M ρ (injK G κ)
  begin (project t M) ρ κ = eval M ρ (projK t κ)

  {- the machine for a program with the definitions ds -}
  module _ (ds : All (Code Σ) Σ) where

    {- run the code of a closure with its environment and the argument -}
    call : Val Σ ⟪ fun ⟫ → Val Σ Any → Cont Σ Any → State Σ
    call (pack (code f) e) w κ = eval (ds ! f) (w ∷ e ∷ []) κ

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
    step (ret v (injK G κ)) = next (ret (dyn G v) κ)
    step (ret v (projK t κ)) = next? o-error (λ w → ret w κ) (proj? t v)

{- a program starts with main, in the empty environment -}
sem : Program → Machine
sem (program ds M) = machine (State _) (step ds) (eval M [] halt)

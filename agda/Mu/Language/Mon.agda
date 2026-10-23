{-

  Monμ: monadic normal form of GlobalFunμ, intrinsically. The output of
  remove complex operands (Mu/Compiler/RCO.agda); as Monᵀ
  (Language/Typed/Mon.agda), with the types of GlobalFunμ.

  An atom is a variable, a literal or a reference to a definition. The
  operands of every operation, and the scrutinee of case, are atoms; the
  right-hand side and body of let and the branches of case are
  expressions. Its meaning is that of its embedding into GlobalFunμ (⌜_⌝).

-}

module Mu.Language.Mon where

open import Framework.Primitives using (Base; base-rep; Int)
open import Language.Prim using (Prim)
open import Mu.Language.Type
open import Mu.Language.GlobalFun using (DSig; sig; Args) public
import Mu.Language.GlobalFun as C
open import Mu.Framework.AllUtil using (All; []; _∷_) renaming (map to All-map)

open import Data.List using (List; []; _∷_)

data Atm (Σ : List DSig) (Γ : Ctx) : Type → Set where
  var : ∀ {A} → Γ ∋ A → Atm Σ Γ A
  lit : (B : Base) → base-rep B → Atm Σ Γ (base B)
  ref : ∀ {Δ A B} → Σ ∋ sig Δ A B → Atm Σ Γ (code Δ A B)

data Exp (Σ : List DSig) (Γ : Ctx) : Type → Set where
  atm : ∀ {A} → Atm Σ Γ A → Exp Σ Γ A
  pack : ∀ {Δ A B} → Atm Σ Γ (code Δ A B) → Atm Σ Γ (tup Δ) → Exp Σ Γ (A ⇒ B)
  callc : ∀ {A B} → Atm Σ Γ (A ⇒ B) → Atm Σ Γ A → Exp Σ Γ B
  tuple : ∀ {Δ} → All (Atm Σ Γ) Δ → Exp Σ Γ (tup Δ)
  get : ∀ {Δ A} → Δ ∋ A → Atm Σ Γ (tup Δ) → Exp Σ Γ A
  inl : ∀ {A B} → Atm Σ Γ A → Exp Σ Γ (A ⊹ B)
  inr : ∀ {A B} → Atm Σ Γ B → Exp Σ Γ (A ⊹ B)
  case : ∀ {A B C} → Atm Σ Γ (A ⊹ B) → Exp Σ (A ∷ Γ) C → Exp Σ (B ∷ Γ) C → Exp Σ Γ C
  prim : (p : Prim) → Atm Σ Γ (base Int) → Atm Σ Γ (base Int) → Exp Σ Γ (out-ty p)
  let′ : ∀ {A B} → Exp Σ Γ A → Exp Σ (A ∷ Γ) B → Exp Σ Γ B
  fold : ∀ {A} → Atm Σ Γ (unroll A) → Exp Σ Γ (μ A)
  unfold : ∀ {A} → Atm Σ Γ (μ A) → Exp Σ Γ (unroll A)

record Program (A : Type) : Set where
  constructor program
  field
    {table} : List DSig
    defs : All (λ s → Exp table (Args s) (DSig.cod s)) table
    main : Exp table [] A

{- renaming the variables of an atom -}
ren : ∀ {Σ Γ Δ A} → (∀ {B} → Γ ∋ B → Δ ∋ B) → Atm Σ Γ A → Atm Σ Δ A
ren r (var x) = var (r x)
ren r (lit B c) = lit B c
ren r (ref f) = ref f

{- The embedding into GlobalFunμ: the meaning of a Monμ program -}

⌜_⌝ᵃ : ∀ {Σ Γ A} → Atm Σ Γ A → C.Tm Σ Γ A
⌜ var x ⌝ᵃ = C.` x
⌜ lit B c ⌝ᵃ = C.lit B c
⌜ ref f ⌝ᵃ = C.fun-ref f

⌜_⌝ᵛ : ∀ {Σ Γ Δ} → All (Atm Σ Γ) Δ → All (C.Tm Σ Γ) Δ
⌜ [] ⌝ᵛ = []
⌜ a ∷ as ⌝ᵛ = ⌜ a ⌝ᵃ ∷ ⌜ as ⌝ᵛ

⌜_⌝ : ∀ {Σ Γ A} → Exp Σ Γ A → C.Tm Σ Γ A
⌜ atm a ⌝ = ⌜ a ⌝ᵃ
⌜ pack a b ⌝ = C.pack ⌜ a ⌝ᵃ ⌜ b ⌝ᵃ
⌜ callc a b ⌝ = C.callc ⌜ a ⌝ᵃ ⌜ b ⌝ᵃ
⌜ tuple as ⌝ = C.tuple ⌜ as ⌝ᵛ
⌜ get i a ⌝ = C.get i ⌜ a ⌝ᵃ
⌜ inl a ⌝ = C.inl ⌜ a ⌝ᵃ
⌜ inr a ⌝ = C.inr ⌜ a ⌝ᵃ
⌜ case a M N ⌝ = C.case ⌜ a ⌝ᵃ ⌜ M ⌝ ⌜ N ⌝
⌜ prim p a b ⌝ = C.prim p ⌜ a ⌝ᵃ ⌜ b ⌝ᵃ
⌜ let′ M N ⌝ = C.let′ ⌜ M ⌝ ⌜ N ⌝
⌜ fold a ⌝ = C.fold ⌜ a ⌝ᵃ
⌜ unfold a ⌝ = C.unfold ⌜ a ⌝ᵃ

⌜_⌝ₚ : ∀ {A} → Program A → C.Program A
⌜ program ds M ⌝ₚ = C.program (All-map ⌜_⌝ ds) ⌜ M ⌝

{-

  PairClosμ: PairClos, intrinsically typed, with recursive types. The output
  of delay (Mu/Compiler/Delay.agda).

  A closure is a pair of closed code and the tuple of its free
  variables, packed so that its type A ⇒ B hides the types Δ of the
  tuple: A ⇒ B is the existential ∃Δ. code Δ A B × tup Δ (typed closure
  conversion, Minamide, Morrisett and Harper, POPL 1996), with the
  witness a list of types.

  * code N : code Δ A B, for closed code N with the argument (variable
    Z) and the environment (variable S Z, of type tup Δ);
  * pair L M : A ⇒ B packs code and environment of the same Δ;
  * callc L M opens the closure L and calls its code with its
    environment and the argument M, parametrically in Δ.

-}

module Mu.Language.PairClos where

open import Framework.Primitives using (Base; base-rep; Int)
open import Language.Prim using (Prim)
open import Mu.Language.Type
open import Mu.Framework.AllUtil using (All)

open import Data.List using ([]; _∷_)

data Tm (Γ : Ctx) : Type → Set where
  `_ : ∀ {A} → Γ ∋ A → Tm Γ A
  code : ∀ {Δ A B} → Tm (A ∷ tup Δ ∷ []) B → Tm Γ (code Δ A B)
  pair : ∀ {Δ A B} → Tm Γ (code Δ A B) → Tm Γ (tup Δ) → Tm Γ (A ⇒ B)
  callc : ∀ {A B} → Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B
  lit : (B : Base) → base-rep B → Tm Γ (base B)
  tuple : ∀ {Δ} → All (Tm Γ) Δ → Tm Γ (tup Δ)
  get : ∀ {Δ A} → Δ ∋ A → Tm Γ (tup Δ) → Tm Γ A
  inl : ∀ {A B} → Tm Γ A → Tm Γ (A ⊹ B)
  inr : ∀ {A B} → Tm Γ B → Tm Γ (A ⊹ B)
  case : ∀ {A B C} → Tm Γ (A ⊹ B) → Tm (A ∷ Γ) C → Tm (B ∷ Γ) C → Tm Γ C
  prim : (p : Prim) → Tm Γ (base Int) → Tm Γ (base Int) → Tm Γ (out-ty p)
  let′ : ∀ {A B} → Tm Γ A → Tm (A ∷ Γ) B → Tm Γ B
  fold : ∀ {A} → Tm Γ (unroll A) → Tm Γ (μ A)
  unfold : ∀ {A} → Tm Γ (μ A) → Tm Γ (unroll A)

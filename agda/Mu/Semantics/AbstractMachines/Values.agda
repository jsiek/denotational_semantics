{-

  The values of the CEK machines of ISWIMμ and Closμ–FlatClosμ
  (Mu/Semantics/AbstractMachines/), indexed by their type, as those of the clocked
  interpreters (Mu/Semantics/ClockedInterpreters/Values.agda); C Δ A B is what the
  code of a closure with free variables of types Δ, an argument of type
  A and a result of type B is in each language.

  A closure is a pair of code and the tuple of its environment, packed
  (pack): the code of a function is a value of type code Δ A B only in
  FlatClosμ, but every language uses the same shape, so that the passes
  between them relate values the same way (proof/Semantics/AbstractMachines/Rel.agda).
  A value of a recursive type is a fold of a value of its unfolding. An
  environment is typed by its context.

-}

open import Mu.Language.Type using (Ctx; Type)

module Mu.Semantics.AbstractMachines.Values (C : Ctx → Type → Type → Set) where

open import Framework.Primitives using (Base; base-rep; Int)
open import Language.Prim using (Prim; sub; eq)
open import Mu.Language.Type
open import Mu.Framework.AllUtil using (All; []; _∷_)
open import Semantics.Observation using (Obs; o-const; o-fun; o-tuple; o-inl; o-inr)

open import Data.Bool using (if_then_else_)
open import Data.Integer using (ℤ; _-_; _≟_)
open import Data.List using (List; []; _∷_)
open import Relation.Nullary using (does)

data Val : Type → Set where
  code : ∀ {Δ A B} → C Δ A B → Val (code Δ A B)
  pack : ∀ {Δ A B} → Val (code Δ A B) → Val (tup Δ) → Val (A ⇒ B)
  const : ∀ {B} → base-rep B → Val (base B)
  tup : ∀ {Δ} → All Val Δ → Val (tup Δ)
  inl : ∀ {A B} → Val A → Val (A ⊹ B)
  inr : ∀ {A B} → Val B → Val (A ⊹ B)
  fold : ∀ {A} → Val (unroll A) → Val (μ A)

Env : Ctx → Set
Env = All Val

obs : ∀ {A} → Val A → Obs
obs-all : ∀ {Δ} → All Val Δ → List Obs
obs (code _) = o-fun
obs (pack _ _) = o-fun
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

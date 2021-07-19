{-

This is the language that comes before the "delay" pass.

-}

module ISWIMAnnot where

open import Primitives
open import Data.Empty renaming (⊥ to Bot)
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; length; replicate)
open import Data.Product
   using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Unit using (⊤; tt)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong; cong₂; cong-app)
open Eq.≡-Reasoning
open import Sig
open import Syntax using (Sig; ext; ν; ■; Var; _•_; ↑; id; _⨟_) public

open import ModelISWIM using (Value; ⊥)
open import GraphModel
open import ScopedTuple hiding (𝒫)
open import CurryConst

data Op : Set where
  lam : ℕ → Op         {- number of free variables -}
  app : Op
  lit : (p : Prim) → rep p → Op

sig : Op → List Sig
sig (lam n) = ℕ→sig (suc n) ∷ (replicate n ■)
sig app = ■ ∷ ■ ∷ []
sig (lit p k) = []

open Syntax.OpSig Op sig
  hiding (ABT)
  
open Syntax.OpSig Op sig
  using (`_; Arg; Args; ast; bind; clear; cons; nil)
  renaming (ABT to ISWIMAnn) public

pattern ƛ n bN = (lam n) ⦅ bN ⦆

infixl 7  _·_
pattern _·_ L M = app ⦅ cons (ast L) (cons (ast M) nil) ⦆

pattern $ p k = lit p k ⦅ nil ⦆

open import Fold2 Op sig

interp-iswim  : (op : Op) → Tuple (sig op) (ArgTy (𝒫 Value)) → 𝒫 Value
interp-iswim (lam n) ⟨ f , args ⟩ rewrite tuple≡prod n =
  𝐹-iter n (𝐺-iter (suc n) f) ⟬ args ⟭
interp-iswim app ⟨ d₁ , ⟨ d₂ , _ ⟩ ⟩ = 𝐹 d₁ d₂
interp-iswim (lit p c) args = ℘ {p} c 

ℐ⟦_⟧_ : ISWIMAnn → (Var → 𝒫 Value) → 𝒫 Value
ℐ⟦ M ⟧ ρ = fold interp-iswim (λ v → Bot) ρ M

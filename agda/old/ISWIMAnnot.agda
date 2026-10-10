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
  app : Op             {- application of lambda's -}
  papp : (p : Prim) → rep p → Op  {- primitive application -}

sig : Op → List Sig
sig (lam n) = ν (ν ■) ∷ (replicate n ■)
sig app = ■ ∷ ■ ∷ []
sig (papp p k) = replicate (arity p) ■

open Syntax.OpSig Op sig
  using (`_; Arg; Args; ast; bind; clear; cons; nil; _⦅_⦆)
  renaming (ABT to ISWIMAnn) public

pattern ƛ n bN = (lam n) ⦅ bN ⦆

infixl 7  _·_
pattern _·_ L M = app ⦅ cons (ast L) (cons (ast M) nil) ⦆

open import Fold2 Op sig

interp-iswim  : (op : Op) → Tuple (sig op) (ArgTy (𝒫 Value)) → 𝒫 Value
interp-iswim (lam n) ⟨ f , args ⟩ =
    𝐹 (𝐺-iter 2 f) ⟬ args ⟭
interp-iswim app ⟨ d₁ , ⟨ d₂ , _ ⟩ ⟩ = 𝐹 d₁ d₂
interp-iswim (papp p c) args =
    𝐹-iter (arity p) (℘ {p} c) ⟬ args ⟭

ℐ⟦_⟧_ : ISWIMAnn → (Var → 𝒫 Value) → 𝒫 Value
ℐ⟦ M ⟧ ρ = fold interp-iswim (λ v → Bot) ρ M

ℐ⟦_⟧ₐ_ : ∀{b} → Arg b → (Var → 𝒫 Value) → ArgTy (𝒫 Value) b
ℐ⟦ arg ⟧ₐ ρ = fold-arg interp-iswim (λ v → Bot) ρ arg

ℐ⟦_⟧₊_ : ∀{bs} → Args bs → (Var → 𝒫 Value) → Tuple bs (ArgTy (𝒫 Value))
ℐ⟦ args ⟧₊ ρ = fold-args interp-iswim (λ v → Bot) ρ args

ℐ-lam : ∀ {N : Arg (ν (ν ■))}{n}{ρ}{args : Args (replicate n ■)}
    → ℐ⟦ lam n ⦅ cons N args ⦆ ⟧ ρ
        ≡ (𝐺-iter 2 (ℐ⟦ N ⟧ₐ ρ)) ▪ ⟬ ℐ⟦ args ⟧₊ ρ ⟭
ℐ-lam {L}{M}{ρ} = refl

ℐ-app : ∀ {L M : ISWIMAnn}{ρ}
    → ℐ⟦ L · M ⟧ ρ ≡ (ℐ⟦ L ⟧ ρ) ▪ (ℐ⟦ M ⟧ ρ)
ℐ-app {L}{M}{ρ} = refl

ℐ-papp : ∀ {ρ}{p}{c}{args : Args (replicate (arity p) ■)}
    → ℐ⟦ papp p c ⦅ args ⦆ ⟧ ρ ≡ 𝐹-iter (arity p) (℘ {p} c) (⟬ ℐ⟦ args ⟧₊ ρ ⟭)
ℐ-papp {L}{M}{ρ} = refl



{-

This is the language that comes after the "delay" pass.

-}


module ClosLang where

import Syntax
open import Sig
open import Primitives
open import Var
open import ScopedTuple hiding (𝒫)
open import GraphModel
open import ModelISWIM using (Value; ⊥; _↦_; const; _⊔_; _⊑_)
open import CurryConst

open import Data.Bool using (Bool; true; false; _∨_)
open import Data.Empty using (⊥-elim) renaming (⊥ to False)
open import Data.List using (List; []; _∷_; _++_; length; replicate)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; _≟_; _+_; z≤n; s≤s)
open import Data.Nat.Properties
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; inspect; [_])
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Relation.Nullary using (Dec; yes; no)

data ClosOp : Set where
  fun  : ℕ → ClosOp    {- number of early parameters -}
  early-app : ClosOp
  app : ClosOp
  lit : (p : Prim) → rep p → ClosOp
  tuple : ℕ → ClosOp       {- number of elements -}
  get : ℕ → ClosOp         {- which element -}

closSig : ClosOp → List Sig
closSig (fun n) = ℕ→sig (suc n) ∷ []
closSig early-app = ■ ∷ ■ ∷ ■ ∷ []
closSig app = ■ ∷ ■ ∷ []
closSig (lit p k) = []
closSig (tuple n) = replicate n ■
closSig (get i) = ■ ∷ []

open Syntax.OpSig ClosOp closSig
  hiding (ABT; `_)

open Syntax.OpSig ClosOp closSig
  using ()
  renaming (ABT to Clos; Arg to Argᵪ; Args to Argsᵪ;
      `_ to %_; _⦅_⦆ to _⦑_⦒;
      cons to consᵪ; ast to astᵪ; bind to bindᵪ; clear to clearᵪ; nil to nilᵪ)
      public

pattern # p k = lit p k ⦅ nil ⦆
pattern 𝑓_,_ n bN = (fun n) ⦅ cons bN nil ⦆
pattern _▪_^_ L M n = early-app ⦅ cons (ast L) (cons (ast M) (cons (ast n) nil)) ⦆
pattern _▫_ L M = app ⦅ cons (ast L) (cons (ast M) nil) ⦆
pattern _❲_❳ M i = (get i) ⦅ cons (ast M) nil ⦆

p0 = # (base Nat) 0
p1 = # (base Nat) 0
p+ = # (Nat ⇒ (Nat ⇒ base Nat)) _+_

binds : (n : ℕ) → Clos → Arg (ℕ→sig n)
binds zero N = ast N
binds (suc n) N = bind (binds n N)

test_cl = 𝑓 1 , (binds 2 p0) 

test_tup = (tuple 2) ⦅ cons (ast p0) (cons (ast p1) nil) ⦆

〔_,_〕 : Clos → Clos → Clos
〔 M , N 〕 = (tuple 2) ⦅ cons (ast M) (cons (ast N) nil) ⦆

〔_,_,_〕 : Clos → Clos → Clos → Clos
〔 L , M , N 〕 = (tuple 3) ⦅ cons (ast L) (cons (ast M) (cons (ast N) nil)) ⦆

open import Fold2 ClosOp closSig

interp-clos  : (op : ClosOp) → Tuple (closSig op) (ArgTy (𝒫 Value)) → 𝒫 Value
interp-clos (fun n) ⟨ N , _ ⟩ = 𝐺-iter (suc n) N
interp-clos early-app ⟨ d₁ , ⟨ d₂ , ⟨ d₃ , _ ⟩ ⟩ ⟩ v =
  Σ[ n ∈ ℕ ] d₃ (const n)  ×  𝐹-iter n d₁ d₂ v
interp-clos app ⟨ d₁ , ⟨ d₂ , _ ⟩ ⟩ = 𝐹 d₁ d₂
interp-clos (lit p c) args = ℘ {p} c 
interp-clos (tuple n) args rewrite tuple≡prod n = ⟬ args ⟭
interp-clos (get i) ⟨ d , _ ⟩ = ℕth d i

𝒞⟦_⟧_ : Clos → (Var → 𝒫 Value) → 𝒫 Value
𝒞⟦ M ⟧ ρ = fold interp-clos (λ v → False) ρ M

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
open import Data.Unit.Polymorphic using (⊤; tt)

data ClosOp : Set where
  fun  : ClosOp
  app : ClosOp
  papp : (p : Prim) → rep p → ClosOp
  tuple : ℕ → ClosOp       {- number of elements -}
  get : ℕ → ClosOp         {- which element -}

closSig : ClosOp → List Sig
closSig fun = ν (ν ■) ∷ []
closSig app = ■ ∷ ■ ∷ []
closSig (papp p k) = replicate (arity p) ■
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

pattern # p k = papp p k ⦅ nil ⦆
pattern 𝑓_ N = fun ⦅ cons (bind (bind (ast N))) nil ⦆
pattern _▫_ L M = app ⦅ cons (ast L) (cons (ast M) nil) ⦆
pattern _❲_❳ M i = (get i) ⦅ cons (ast M) nil ⦆

p0 = # (base Nat) 0
p1 = # (base Nat) 0

binds : (n : ℕ) → Clos → Arg (ℕ→sig n)
binds zero N = ast N
binds (suc n) N = bind (binds n N)

test_cl = 𝑓 p0

test_tup = (tuple 2) ⦅ cons (ast p0) (cons (ast p1) nil) ⦆

〔_,_〕 : Clos → Clos → Clos
〔 M , N 〕 = (tuple 2) ⦅ cons (ast M) (cons (ast N) nil) ⦆

〔_,_,_〕 : Clos → Clos → Clos → Clos
〔 L , M , N 〕 = (tuple 3) ⦅ cons (ast L) (cons (ast M) (cons (ast N) nil)) ⦆

open import Fold2 ClosOp closSig

interp-clos  : (op : ClosOp) → Tuple (closSig op) (ArgTy (𝒫 Value)) → 𝒫 Value
interp-clos fun ⟨ λλN , _ ⟩ = 𝐺-iter 2 λλN
interp-clos app ⟨ d₁ , ⟨ d₂ , _ ⟩ ⟩ = 𝐹 d₁ d₂
interp-clos (papp p c) args = 𝐹-iter (arity p) (℘ {p} c) ⟬ args ⟭
interp-clos (tuple n) args = ⟬ args ⟭
interp-clos (get i) ⟨ d , _ ⟩ = ℕth d i

𝒞⟦_⟧_ : Clos → (Var → 𝒫 Value) → 𝒫 Value
𝒞⟦ M ⟧ ρ = fold interp-clos (λ v → False) ρ M

𝒞⟦_⟧ₐ_ : ∀{b} → Arg b → (Var → 𝒫 Value) → ArgTy (𝒫 Value) b
𝒞⟦ arg ⟧ₐ ρ = fold-arg interp-clos (λ v → False) ρ arg

𝒞⟦_⟧₊_ : ∀{bs} → Args bs → (Var → 𝒫 Value) → Tuple bs (ArgTy (𝒫 Value))
𝒞⟦ args ⟧₊ ρ = fold-args interp-clos (λ v → False) ρ args

𝒞-fun : ∀ {N : Arg (ν (ν ■))}{ρ}
    → 𝒞⟦ fun ⦑ cons N nil ⦒ ⟧ ρ ≡ 𝐺-iter 2 (𝒞⟦ N ⟧ₐ ρ)
𝒞-fun {N}{ρ} = refl

𝒞-app : ∀ {L M : Clos}{ρ}
    → 𝒞⟦ L ▫ M ⟧ ρ ≡ (𝒞⟦ L ⟧ ρ) ▪ (𝒞⟦ M ⟧ ρ)
𝒞-app {L}{M}{ρ} = refl

𝒞-papp : ∀ {ρ}{p}{c}{args : Args (replicate (arity p) ■)}
    → 𝒞⟦ papp p c ⦑ args ⦒ ⟧ ρ ≡ 𝐹-iter (arity p) (℘ {p} c) (⟬ 𝒞⟦ args ⟧₊ ρ ⟭)
𝒞-papp {L}{M}{ρ} = refl

𝒞-get : ∀ {M : Clos}{i : ℕ}{ρ}
    → 𝒞⟦ M ❲ i ❳ ⟧ ρ ≡ ℕth (𝒞⟦ M ⟧ ρ) i
𝒞-get {M}{i}{ρ} = refl

𝒞-tuple : ∀ {n}{args}{ρ}
    → 𝒞⟦ tuple n ⦑ args ⦒ ⟧ ρ ≡ ⟬ 𝒞⟦ args ⟧₊ ρ ⟭
𝒞-tuple = refl

𝒞-pair : ∀ {M N}{ρ}
    → 𝒞⟦ 〔 M , N 〕 ⟧ ρ ≡ ⟬ ⟨ 𝒞⟦ M ⟧ ρ , ⟨ 𝒞⟦ N ⟧ ρ , tt ⟩ ⟩ ⟭
𝒞-pair = refl

𝒞-closure : ∀ {n}{N : Arg (ν (ν ■))}{args}{ρ}
  → (𝒞⟦ 〔 (fun ⦑ cons N nil ⦒) , tuple n ⦑ args ⦒ 〕 ⟧ ρ)
    ≡  ⟬ ⟨ 𝐺-iter 2 (𝒞⟦ N ⟧ₐ ρ) , ⟨ ⟬ 𝒞⟦ args ⟧₊ ρ ⟭ , tt ⟩ ⟩ ⟭
𝒞-closure = refl


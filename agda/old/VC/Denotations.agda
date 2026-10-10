{-# OPTIONS --rewriting #-}
open import Primitives
open import SetsAsPredicates
open import Sig renaming (ν to bnd)
open import Var

open import Data.Empty using (⊥-elim) renaming (⊥ to False)
open import Data.List
open import Data.Nat
open import Data.Product using (_,_; _×_; Σ; Σ-syntax; proj₁; proj₂)
open import Data.Unit using (tt) renaming (⊤ to True)
open import Data.Unit.Polymorphic renaming (⊤ to ⊤ᵖ; tt to ttᵖ)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality
    using (_≡_; _≢_; refl; sym; subst)

module VC.Denotations where

data Value : Set where
  const : {B : Base} → base-rep B → Value {- A primitive constant of type B. -}
  _↦_ : List Value → List Value → Value   {- An entry in a function's graph. -}
  ν : Value                               {- A function. -}  
  ⟬_⟭ : List Value → Value                 {- Tuples. -}

Env : Set₁
Env = Var → 𝒫 Value

{- Meaning of primivites -}

℘ : (P : Prim) → rep P → 𝒫 Value
℘ (base B) k (const {B′} k′)
    with base-eq? B B′
... | yes refl = k ≡ k′
... | no neq = False
℘ (base B) k (V ↦ w) = False
℘ (base B) k ν = False
℘ (base B) k ⟬ vs ⟭ = False
℘ (B ⇒ P) f (const k) = False
℘ (B ⇒ P) f (V ↦ W) =
   Σ[ w ∈ Value ] W ≡ (w ∷ []) ×
   (Σ[ k ∈ base-rep B ] V ≡ (const {B} k) ∷ []  ×  w ∈ ℘ P (f k))
℘ (B ⇒ P) f ν = True
℘ (B ⇒ P) k ⟬ vs ⟭ = False

{- Meaning of application -}

infix 10 _▪_
_▪_ : 𝒫 Value → 𝒫 Value → 𝒫 (List Value)
D₁ ▪ D₂ = λ W → Σ[ V ∈ List Value ] (V ↦ W ∈ D₁)  ×  (mem V ⊆ D₂)  ×  V ≢ []

{- Syntax -}

data Op : Set where
  {- Values -}
  lit : (p : Prim) → rep p → Op
  tup : ℕ → Op
  {- Expressions -}
  app : Op
  seq : Op
  choice : Op
  equal : Op
  exist : Op
  
sig : Op → List Sig
sig app = ■ ∷ ■ ∷ []
sig (lit p k) = []
sig (tup zero) = []
sig (tup (suc n)) = ■ ∷ (sig (tup n))
sig seq = ■ ∷ ■ ∷ []
sig choice = ■ ∷ ■ ∷ []
sig equal = ■ ∷ ■ ∷ []
sig exist = bnd ■ ∷ []

open import rewriting.AbstractBindingTree Op sig
  hiding (_⨟_)
  renaming (ABT to Exp)

pattern $ p k = lit p k ⦅ nil ⦆

infixl 7  _·_
pattern _·_ L M = app ⦅ cons (ast L) (cons (ast M) nil) ⦆

infixl 7  _∣_
pattern _∣_ L M = choice ⦅ cons (ast L) (cons (ast M) nil) ⦆

infixl 7  _⍮_
pattern _⍮_ L M = seq ⦅ cons (ast L) (cons (ast M) nil) ⦆

infixl 7  _⩦_
pattern _⩦_ L M = equal ⦅ cons (ast L) (cons (ast M) nil) ⦆

pattern ∃̇ L = exist ⦅ cons (bind (ast L)) nil ⦆

∏ : ℕ → Set₁ → Set₁
∏ zero T = ⊤ᵖ
∏ (suc n) T = T × ∏ n T

𝓣 : ∀ n → ∏ n (𝒫 Value) → 𝒫 Value
𝓣 zero _ ⟬ [] ⟭ = True
𝓣 (suc n) (D , Ds) ⟬ v ∷ vs ⟭ = v ∈ D  ×  𝓣 n Ds ⟬ vs ⟭
𝓣 n Ds _ = False

𝓥⟦_⟧ : Exp → Env → 𝒫 Value
𝓥s⟦_⟧ : ∀{n} → Args (sig (tup n)) → Env → ∏ n (𝒫 Value)

𝓥⟦ ` x ⟧ ρ = ρ x
𝓥⟦ $ p k ⟧ ρ = ℘ p k
𝓥⟦ tup n ⦅ elts ⦆ ⟧ ρ = 𝓣 n (𝓥s⟦ elts ⟧ ρ)
𝓥⟦ v ⟧ ρ w = False

𝓥s⟦_⟧ {zero} nil ρ = ttᵖ
𝓥s⟦_⟧ {suc n} (cons (ast v) args) ρ = 𝓥⟦ v ⟧ ρ , 𝓥s⟦ args ⟧ ρ


unit : 𝒫 Value → 𝒫 (List Value)
unit D ls = Σ[ w ∈ Value ] ls ≡ w ∷ [] × w ∈ D

_⨟_ : 𝒫 (List Value) → 𝒫 (List Value) → 𝒫 (List Value)
D ⨟ E = {!!}

𝓔⟦_⟧ : Exp → Env → 𝒫 (List Value)
𝓔⟦ v₁ · v₂ ⟧ ρ = 𝓥⟦ v₁ ⟧ ρ ▪ 𝓥⟦ v₂ ⟧ ρ
𝓔⟦ e₁ ∣ e₂ ⟧ ρ = {!!}
𝓔⟦ e₁ ⍮ e₂ ⟧ ρ = 𝓔⟦ e₁ ⟧ ρ ⨟ 𝓔⟦ e₂ ⟧ ρ
𝓔⟦ e₁ ⩦ e₂ ⟧ ρ =
   let vs₁ = 𝓔⟦ e₁ ⟧ ρ in
   let vs₂ = 𝓔⟦ e₂ ⟧ ρ in
   {!!}
𝓔⟦ ∃̇ e ⟧ ρ = {!!}
𝓔⟦ v ⟧ ρ = unit (𝓥⟦ v ⟧ ρ)


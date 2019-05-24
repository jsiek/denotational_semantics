
open import LambdaV
   using (AST; $; _·_; ƛ; Term; t-var; t-lam; t-app; lam; app; rename; rename-pres-term)
open LambdaV.ASTMod
   using (Var; Z; S_; `_; α_; _⦅_⦆; extensionality; Rename; Subst; ext; exts)


open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Empty using (⊥-elim) renaming (⊥ to Bot)
open import Function using (_∘_)


module Experiment
  (Value : Set)
  (_⊑_ : Value → Value → Set)
  (Trans⊑ : ∀ {u v w} → u ⊑ v → v ⊑ w → u ⊑ w)
  where

Env : ℕ → Set
Env Γ = Var Γ → Value

Denotation : ℕ → Set₁
Denotation Γ = Env Γ → Value → Set

_iff_ : Set → Set → Set
P iff Q = (P → Q) × (Q → P)

_≃_ : (Value → Set) → (Value → Set) → Set
d ≃ d' = ∀{v : Value} → d v iff d' v

≃-refl : ∀ {M : Value → Set}
  → M ≃ M
≃-refl = ⟨ (λ x → x) , (λ x → x) ⟩

≃-trans : ∀ {M₁ M₂ M₃ : Value → Set}
  → M₁ ≃ M₂
  → M₂ ≃ M₃
    -------
  → M₁ ≃ M₃
≃-trans m12 m23 = ⟨ (λ z → proj₁ m23 (proj₁ m12 z)) , (λ z → proj₂ m12 (proj₂ m23 z)) ⟩

infixr 2 _≃⟨⟩_ _≃⟨_⟩_
infix  3 _☐

_≃⟨⟩_ : ∀ (x : Value → Set) {y : Value → Set}
    → x ≃ y
      -----
    → x ≃ y
x ≃⟨⟩ x≃y  = x≃y

_≃⟨_⟩_ : ∀ (x : Value → Set) {y z : Value → Set}
    → x ≃ y
    → y ≃ z
      -----
    → x ≃ z
(x ≃⟨ x≃y ⟩ y≃z) {v} =  ≃-trans (x≃y{v}) y≃z {v}

_☐ : ∀ (d : Value → Set)
      -----
    → d ≃ d
(d ☐) {v} =  ≃-refl {d}


module Model
  (ℱ : ∀{Γ} → Denotation (suc Γ) → Denotation Γ)
  (_●_ : ∀{Γ} → Denotation Γ → Denotation Γ → Denotation Γ)
  (cong-● : ∀{Γ Δ}{γ : Env Γ}{δ : Env  Δ}{D₁ D₂ : Denotation Γ}{D₁′ D₂′ : Denotation Δ}
          → D₁ γ ≃ D₁′ δ → D₂ γ ≃ D₂′ δ → (D₁ ● D₂) γ ≃ (D₁′ ● D₂′) δ)
  where
  
  
  ℰ : ∀{Γ} → Term Γ → Denotation Γ
  ℰ {Γ} ⟨ _ , t-var x ⟩ γ v = v ⊑ γ x
  ℰ {Γ} ⟨ lam ⦅ (α N) ∷ [] ⦆ , t-lam Nt ⟩ = ℱ (ℰ ⟨ N , Nt ⟩)
  ℰ ⟨ app ⦅ L ∷ M ∷ [] ⦆ , t-app Lt Mt ⟩ = (ℰ ⟨ L , Lt ⟩) ● (ℰ ⟨ M , Mt ⟩)

  _`⊑_ : ∀ {Γ} → Env Γ → Env Γ → Set
  _`⊑_ {Γ} γ δ = (x : Var Γ) → γ x ⊑ δ x

  _`≡_ : ∀ {Γ} → Env Γ → Env Γ → Set
  _`≡_ {Γ} γ δ = (x : Var Γ) → γ x ≡ δ x

  rename-equiv : ∀ {Γ Δ} {γ : Env Γ} {δ : Env Δ} {M : Term Γ} { ρ : Rename Γ Δ }
    → γ `≡ (δ ∘ ρ)
    → ℰ M γ ≃ ℰ (rename ρ M) δ
  rename-equiv {M = ⟨ .(` x) , t-var x ⟩} γ≡δ∘ρ = {!!}
  rename-equiv {M = ⟨ .(lam ⦅ (α _) ∷ [] ⦆) , t-lam Mt ⟩} γ≡δ∘ρ = {!!}
  rename-equiv {Γ}{Δ}{γ}{δ}{⟨ (app ⦅ L ∷ M ∷ [] ⦆) , t-app Lt Mt ⟩}{ρ} γ≡δ∘ρ = G
    where
    L' = ⟨ L , Lt ⟩
    M' = ⟨ M , Mt ⟩
    IH1 : (ℰ L') γ ≃ (ℰ (rename ρ L')) δ
    IH1 {v} = rename-equiv {M = L'} γ≡δ∘ρ {v}
    IH2 : (ℰ M') γ ≃ (ℰ (rename ρ M')) δ
    IH2 {v} = rename-equiv {M = M'} γ≡δ∘ρ {v}
    
    G : ((ℰ L') ● (ℰ M')) γ ≃ ((ℰ (rename ρ L')) ● (ℰ (rename ρ M'))) δ
    G = cong-● IH1 IH2


{-
  ℰ M γ ≃ ℰ (rename ρ M) δ 

  rename-pres : ∀ {Γ Δ v} {γ : Env Γ} {δ : Env Δ} {M : Term Γ}
    → (ρ : Rename Γ Δ)
    → γ `⊑ (δ ∘ ρ)
    → ℰ M γ v
      ------------------
    → ℰ (rename ρ M) δ v
  rename-pres {Γ}{Δ}{v}{γ}{δ}{⟨ .(` x) , t-var x ⟩} ρ γ⊑δ∘ρ v⊑γx = G
    where
    G : v ⊑ δ (ρ x)
    G = Trans⊑ v⊑γx (γ⊑δ∘ρ x)

  rename-pres {M = ⟨ (lam ⦅ (α N) ∷ [] ⦆) , t-lam Nt ⟩} ρ γ⊑δ∘ρ ℱℰNγv = {!!}
  
  rename-pres {Γ}{Δ}{v}{γ}{δ}{⟨ (app ⦅ L ∷ M ∷ [] ⦆) , t-app Lt Mt ⟩} ρ γ⊑δ∘ρ ℰMγv =
     let L' = rename ρ ⟨ L , Lt ⟩ in
     let ih1 = rename-pres {Γ}{Δ}{v}{γ}{δ}{⟨ L , Lt ⟩ } ρ γ⊑δ∘ρ {!!} in
     {!!}


-}

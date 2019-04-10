\begin{code}
module Adequate2 where
\end{code}

## Imports

\begin{code}
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; inspect)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum
open import Agda.Primitive using (lzero)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using (contradiction)
open import Data.Empty using (⊥-elim) renaming (⊥ to Bot)
open import Data.Unit using (⊤; tt)
open import Data.Maybe
open import Data.List using (List; _∷_; _++_; concat; map) renaming ([] to nil)
open import Data.List.NonEmpty using (List⁺; _∷_; _⁺++⁺_; toList) 
open import Data.Nat using (ℕ; suc; zero; _≤_)
open import Relation.Nullary using (Dec; yes; no)

open import Untyped
open import Denot_CBN_BCD
\end{code}

## Adequacy of the denotational semantics

\begin{code}
\begin{code}
data WHNF : ∀ {Γ A} → Γ ⊢ A → Set where

  ƛ_ : ∀ {Γ} {N : Γ , ★ ⊢ ★}
     → WHNF (ƛ N)
\end{code}

\begin{code}
data Clos : Set

data ClosEnv : Context → Set where
  ∅ : ClosEnv ∅
  _,_ : ∀{Γ} → ClosEnv Γ → Clos → ClosEnv (Γ , ★)
  
data Clos where
  clos : ∀{Γ} → (M : Γ ⊢ ★) → ClosEnv Γ → Clos

kth : ∀{Γ} → (Γ ∋ ★) → ClosEnv Γ → Clos
kth () ∅
kth Z (ρ , v) = v
kth (S x) (ρ , v) = kth x ρ

data _⊢_⇓_ : ∀{Γ} → ClosEnv Γ → (Γ ⊢ ★) → Clos → Set where

  ⇓-var : ∀{Γ}{γ : ClosEnv Γ}{x : Γ ∋ ★}{Δ}{δ : ClosEnv Δ}{M : Δ ⊢ ★}{c}
        → kth x γ ≡ clos M δ
        → δ ⊢ M ⇓ c
          -----------
        → γ ⊢ ` x ⇓ c

  ⇓-lam : ∀{Γ}{γ : ClosEnv Γ}{M : Γ , ★ ⊢ ★}
        → γ ⊢ ƛ M ⇓ clos (ƛ M) γ

  ⇓-app : ∀{Γ}{γ : ClosEnv Γ}{L M : Γ ⊢ ★}{Δ}{δ : ClosEnv Δ}{L' : Δ , ★ ⊢ ★}{c}
       → γ ⊢ L ⇓ clos (ƛ L') δ   →   (δ , clos M γ) ⊢ L' ⇓ c
         ---------------------------------------------------
       → γ ⊢ L · M ⇓ c

⇓-determ : ∀{Γ}{γ : ClosEnv Γ}{M : Γ ⊢ ★}{c c' : Clos}
         → γ ⊢ M ⇓ c → γ ⊢ M ⇓ c'
         → c ≡ c'
⇓-determ (⇓-var eq1 mc) (⇓-var eq2 mc')
      with trans (sym eq1) eq2
... | refl = ⇓-determ mc mc'
⇓-determ ⇓-lam ⇓-lam = refl
⇓-determ (⇓-app mc mc₁) (⇓-app mc' mc'') 
    with ⇓-determ mc mc'
... | refl = ⇓-determ mc₁ mc''

AboveFun : Value → Set
AboveFun v = Σ[ v₁ ∈ Value ] Σ[ v₂ ∈ Value ] v₁ ↦ v₂ ⊑ v

AboveFun-⊑ : ∀{v v' : Value}
      → AboveFun v → v ⊑ v'
      → AboveFun v'
AboveFun-⊑ ⟨ v₁ , ⟨ v₂ , lt' ⟩ ⟩ lt = ⟨ v₁ , ⟨ v₂ , Trans⊑ lt' lt ⟩ ⟩


not-AboveFun-⊔-invL : ∀{v₁ v₂ : Value} → ¬ AboveFun (v₁ ⊔ v₂)
              → ¬ AboveFun v₁
not-AboveFun-⊔-invL{v₁}{v₂} af12 ⟨ v , ⟨ v' , lt ⟩ ⟩ =
  contradiction ⟨ v , ⟨ v' , ConjR1⊑ lt ⟩ ⟩ af12
  

not-AboveFun-⊔-invR : ∀{v₁ v₂ : Value} → ¬ AboveFun (v₁ ⊔ v₂)
              → ¬ AboveFun v₂
not-AboveFun-⊔-invR{v₁}{v₂} af12 ⟨ v , ⟨ v' , lt ⟩ ⟩ =
  contradiction ⟨ v , ⟨ v' , ConjR2⊑ lt ⟩ ⟩ af12
  

not-AboveFun-⊔-inv : ∀{v₁ v₂ : Value} → ¬ AboveFun (v₁ ⊔ v₂)
              → ¬ AboveFun v₁ × ¬ AboveFun v₂
not-AboveFun-⊔-inv af = ⟨ (not-AboveFun-⊔-invL af) , (not-AboveFun-⊔-invR af) ⟩


data Fun : Value → Set where
  fun : ∀{v₁ v v'} → v₁ ≡ (v ↦ v') → Fun v₁

dom : (v : Value) → Value
dom ⊥  = ⊥
dom (v ↦ v') = v
dom (v ⊔ v') = dom' v ⊔ dom' v'

cod : (v : Value) → Value
cod ⊥  = ⊥
cod (v ↦ v') = v'
cod (v ⊔ v') = cod' v ⊔ cod' v'

infix 5 _∈_

_∈_ : Value → Value → Set
v ∈ ⊥ = v ≡ ⊥
v ∈ v' ↦ v'' = v ≡ v' ↦ v''
v ∈ (v₁ ⊔ v₂) = v ∈ v₁ ⊎ v ∈ v₂

Funs : Value → Set
Funs v = (∀{v'} → v' ∈ v → Fun v')



\end{code}

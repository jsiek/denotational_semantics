open import Variables
open import Lambda
open Lambda.Reduction
open Lambda.ASTMod
   using (`_; _⦅_⦆; Subst;
          exts; cons; bind; nil; ⟪_⟫; _⨟_; subst-zero)
open import Syntax2 Op sig
   using (ids; _•_; subst-zero-exts-cons; sub-id; sub-sub)


open import Data.Nat using (ℕ; zero; suc)
open import Data.List using ([])
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Function using (_∘_)


module EvalCallByName where

Context = ℕ

ClosEnv : Context → Set

data Clos : Set where
  clos : ∀{Γ} → (M : Term Γ) → ClosEnv Γ → Clos

ClosEnv Γ = ∀ (x : Var Γ) → Clos

∅' : ClosEnv zero
∅' ()

_,'_ : ∀ {Γ} → ClosEnv Γ → Clos → ClosEnv (suc Γ)
(γ ,' c) Z = c
(γ ,' c) (S x) = γ x

data _⊢_⇓_ : ∀{Γ} → ClosEnv Γ → (Term Γ) → Clos → Set where

  ⇓-var : ∀{Γ}{γ : ClosEnv Γ}{x : Var Γ}{Δ}{δ : ClosEnv Δ}{M : Term Δ}{V}
        → γ x ≡ clos M δ
        → δ ⊢ M ⇓ V
          -----------
        → γ ⊢ ` x ⇓ V

  ⇓-lam : ∀{Γ}{γ : ClosEnv Γ}{N : Term (suc Γ)}
        → γ ⊢ ƛ N ⇓ clos (ƛ N) γ

  ⇓-app : ∀{Γ}{γ : ClosEnv Γ}{L M : Term Γ}{Δ}{δ : ClosEnv Δ}
           {N : Term (suc Δ)}{V}
       → γ ⊢ L ⇓ clos (ƛ N) δ   →   (δ ,' clos M γ) ⊢ N ⇓ V
         ---------------------------------------------------
       → γ ⊢ L · M ⇓ V

⇓-determ : ∀{Γ}{γ : ClosEnv Γ}{M : Term Γ}{V V' : Clos}
         → γ ⊢ M ⇓ V → γ ⊢ M ⇓ V'
         → V ≡ V'
⇓-determ (⇓-var eq1 mc) (⇓-var eq2 mc')
      with trans (sym eq1) eq2
... | refl = ⇓-determ mc mc'
⇓-determ ⇓-lam ⇓-lam = refl
⇓-determ (⇓-app mc mc₁) (⇓-app mc' mc'') 
    with ⇓-determ mc mc'
... | refl = ⇓-determ mc₁ mc''



_≈_ : Clos → (Term zero) → Set
_≈ₑ_ : ∀{Γ} → ClosEnv Γ → Subst Γ zero → Set

(clos {Γ} M γ) ≈ N = Σ[ σ ∈ Subst Γ zero ] γ ≈ₑ σ × (N ≡ ⟪ σ ⟫ M)

γ ≈ₑ σ = ∀{x} → (γ x) ≈ (σ x)


≈ₑ-id : ∅' ≈ₑ (ids {Γ = zero})
≈ₑ-id {()}


ext-subst : ∀{Γ Δ} → Subst Γ Δ → Term Δ → Subst (suc Γ) Δ
ext-subst{Γ}{Δ} σ N = ⟪ subst-zero N ⟫ ∘ exts σ

≈ₑ-ext : ∀ {Γ} {γ : ClosEnv Γ} {σ : Subst Γ zero} {c} {N : Term zero}
      → γ ≈ₑ σ  →  c ≈ N
        --------------------------
      → (γ ,' c) ≈ₑ (ext-subst σ N)
≈ₑ-ext {Γ} {γ} {σ} {c} {N} γ≈ₑσ c≈N {x} = goal
   where
   ext-cons : (γ ,' c) ≈ₑ (N • σ)
   ext-cons {Z} = c≈N
   ext-cons {S x} = γ≈ₑσ

   goal : (γ ,' c) x ≈ ext-subst σ N x
   goal
       with ext-cons {x}
   ... | a rewrite sym (subst-zero-exts-cons{Γ}{zero}{σ}{N}) = a


⇓→—↠×𝔹 : ∀{Γ}{γ : ClosEnv Γ}{σ : Subst Γ zero}{M : Term Γ}{c : Clos}
       → γ ⊢ M ⇓ c  →  γ ≈ₑ σ
         ---------------------------------------
       → Σ[ N ∈ Term zero ] (⟪ σ ⟫ M —↠ N) × c ≈ N
⇓→—↠×𝔹 {γ = γ} (⇓-var{x = x} γx≡Lδ δ⊢L⇓c) γ≈ₑσ
    with γ x | γ≈ₑσ {x} | γx≡Lδ
... | clos L δ | ⟨ τ , ⟨ δ≈ₑτ , σx≡τL ⟩ ⟩ | refl
    with ⇓→—↠×𝔹{σ = τ} δ⊢L⇓c δ≈ₑτ
... | ⟨ N , ⟨ τL—↠N , c≈N ⟩ ⟩ rewrite σx≡τL =
      ⟨ N , ⟨ τL—↠N , c≈N ⟩ ⟩
⇓→—↠×𝔹 {σ = σ} {c = clos (lam ⦅ bind N nil ⦆) γ} ⇓-lam γ≈ₑσ =
    ⟨ ⟪ σ ⟫ (ƛ N) , ⟨ ⟪ σ ⟫ (ƛ N) □ , ⟨ σ , ⟨ γ≈ₑσ , refl ⟩ ⟩ ⟩ ⟩
⇓→—↠×𝔹{Γ}{γ} {σ = σ} {app ⦅ cons L (cons M nil) ⦆} {c} (⇓-app {N = N} L⇓ƛNδ N⇓c) γ≈ₑσ
    with ⇓→—↠×𝔹{σ = σ} L⇓ƛNδ γ≈ₑσ
... | ⟨ _ , ⟨ σL—↠ƛτN , ⟨ τ , ⟨ δ≈ₑτ , ≡ƛτN ⟩ ⟩ ⟩ ⟩ rewrite ≡ƛτN
    with ⇓→—↠×𝔹 {σ = ext-subst τ (⟪ σ ⟫ M)} N⇓c
           (λ {x} → ≈ₑ-ext{σ = τ} δ≈ₑτ ⟨ σ , ⟨ γ≈ₑσ , refl ⟩ ⟩ {x})
       | β-rule{zero}{⟪ exts τ ⟫ N}{⟪ σ ⟫ M}
... | ⟨ N' , ⟨ —↠N' , c≈N' ⟩ ⟩ | ƛτN·σM—→
    rewrite sub-sub{M = N}{σ₁ = exts τ}{σ₂ = subst-zero (⟪ σ ⟫ M)} =
    ⟨ N' , ⟨ r , c≈N' ⟩ ⟩
    where
    r = (app ⦅ cons (⟪ σ ⟫ L) (cons (⟪ σ ⟫ M) nil) ⦆)
        —↠⟨ appL-cong σL—↠ƛτN ⟩
        ((app ⦅ cons (lam ⦅ bind (⟪ exts τ ⟫ N) nil ⦆) (cons (⟪ σ ⟫ M) nil) ⦆))
        —→⟨ ƛτN·σM—→ ⟩
        ⟪ exts τ ⨟ subst-zero (⟪ σ ⟫ M) ⟫ N
        —↠⟨ —↠N' ⟩
        N' □

cbn→reduce :  ∀{M : Term zero}{Δ}{δ : ClosEnv Δ}{N′ : Term (suc Δ)}
     → ∅' ⊢ M ⇓ clos (ƛ N′) δ
       -----------------------------
     → Σ[ N ∈ Term (suc zero) ] (M —↠ ƛ N)
cbn→reduce {M}{Δ}{δ}{N′} M⇓c
    with ⇓→—↠×𝔹{σ = ids} M⇓c ≈ₑ-id
... | ⟨ N , ⟨ rs , ⟨ σ , ⟨ h , eq2 ⟩ ⟩ ⟩ ⟩
    rewrite sub-id{M = M} | eq2 =
    ⟨ ⟪ exts σ ⟫ N′ , rs ⟩

open import Lambda
open Lambda.ASTMod
   using (Var; `_; _⦅_⦆; Subst;
          exts; cons; bind; ast; nil; ⟪_⟫; _⨟_; subst-zero)
open import Syntax3 Op sig
   using (ids; _•_; subst-zero-exts-cons; sub-id; sub-sub)
open import LambdaCallByValue

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using ([])
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Function using (_∘_)


module EvalCallByValue where

Context = ℕ

ClosEnv : Context → Set

data Clos : Set where
  clos : ∀{Γ} → (N : Term (suc Γ)) → ClosEnv Γ → Clos

ClosEnv Γ = ∀ (x : Var Γ) → Clos

∅' : ClosEnv zero
∅' ()

_,'_ : ∀ {Γ} → ClosEnv Γ → Clos → ClosEnv (suc Γ)
(γ ,' c) Z = c
(γ ,' c) (S x) = γ x

data _⊢_⇓_ : ∀{Γ} → ClosEnv Γ → (Term Γ) → Clos → Set where

  ⇓-var : ∀{Γ}{γ : ClosEnv Γ}{x : Var Γ}
          -------------
        → γ ⊢ ` x ⇓ γ x

  ⇓-lam : ∀{Γ}{γ : ClosEnv Γ}{N : Term (suc Γ)}
        → γ ⊢ ƛ N ⇓ clos N γ

  ⇓-app : ∀{Γ}{γ : ClosEnv Γ}{L M : Term Γ}{Δ}{δ : ClosEnv Δ}
           {N : Term (suc Δ)}{V V′}
       → γ ⊢ L ⇓ clos N δ  →  γ ⊢ M ⇓ V
       → (δ ,' V) ⊢ N ⇓ V′
         ---------------------------------------------------
       → γ ⊢ L · M ⇓ V′

⇓-determ : ∀{Γ}{γ : ClosEnv Γ}{M : Term Γ}{V V' : Clos}
         → γ ⊢ M ⇓ V → γ ⊢ M ⇓ V'
         → V ≡ V'
⇓-determ (⇓-var) (⇓-var) = refl
⇓-determ ⇓-lam ⇓-lam = refl
⇓-determ (⇓-app mc₁ mc₂ mc₃) (⇓-app mc₁′ mc₂′ mc₃′) 
    with ⇓-determ mc₁ mc₁′ | ⇓-determ mc₂ mc₂′ 
... | refl | refl = ⇓-determ mc₃ mc₃′

_≈_ : Clos → (Term zero) → Set
_≈ₑ_ : ∀{Γ} → ClosEnv Γ → Subst Γ zero → Set

(clos {Γ} M γ) ≈ N = Σ[ σ ∈ Subst Γ zero ] γ ≈ₑ σ × (N ≡ ⟪ σ ⟫ (ƛ M))

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

≈→TermValue : ∀{V : Clos}{M : Term zero}
            → V ≈ M
            → TermValue M
≈→TermValue {clos N x} {M} ⟨ _ , ⟨ _ , refl ⟩ ⟩ = V-ƛ

⇓→—↠×≈ : ∀{Γ}{γ : ClosEnv Γ}{σ : Subst Γ zero}{M : Term Γ}{c : Clos}
       → γ ⊢ M ⇓ c  →  γ ≈ₑ σ
         ---------------------------------------
       → Σ[ N ∈ Term zero ] (⟪ σ ⟫ M —↠ N) × c ≈ N
⇓→—↠×≈ {γ = γ}{σ} (⇓-var{x = x}) γ≈ₑσ = ⟨ σ x , ⟨ σ x □ , γ≈ₑσ ⟩ ⟩
⇓→—↠×≈ {σ = σ} {c = clos N γ} ⇓-lam γ≈ₑσ =
    ⟨ ⟪ σ ⟫ (ƛ N) , ⟨ ⟪ σ ⟫ (ƛ N) □ , ⟨ σ , ⟨ γ≈ₑσ , refl ⟩ ⟩ ⟩ ⟩
⇓→—↠×≈{Γ}{γ} {σ = σ} {app ⦅ cons (ast L) (cons (ast M) nil) ⦆} {c}
    (⇓-app {Γ}{δ = δ}{N}{V}{V′} L⇓ƛNδ M⇓V N⇓V′) γ≈ₑσ
    with ⇓→—↠×≈{σ = σ} L⇓ƛNδ γ≈ₑσ
... | ⟨ L′ , ⟨ σL—↠ƛτN , ⟨ τ , ⟨ δ≈ₑτ , L′≡ ⟩ ⟩ ⟩ ⟩
    rewrite L′≡
    with ⇓→—↠×≈{σ = σ} M⇓V γ≈ₑσ
... | ⟨ M′ , ⟨ σM—↠M′ , V≈M′ ⟩ ⟩
    with ⇓→—↠×≈ {σ = ext-subst τ M′} N⇓V′
             (λ {x} → ≈ₑ-ext δ≈ₑτ V≈M′ {x} )
       | β-rule{zero}{⟪ exts τ ⟫ N}{M′} (≈→TermValue {V}{M′} V≈M′)
... | ⟨ N′ , ⟨ —↠N′ , c≈N′ ⟩ ⟩ | ƛτN·σM—→
    rewrite sub-sub{M = N}{σ₁ = exts τ}{σ₂ = subst-zero M′} =
    ⟨ N′ , ⟨ r , c≈N′ ⟩ ⟩
    where
    r = (⟪ σ ⟫ L) · (⟪ σ ⟫ M)
        —↠⟨ appL-cong σL—↠ƛτN ⟩
        (ƛ (⟪ exts τ ⟫ N)) · (⟪ σ ⟫ M)
        —↠⟨ appR-cong V-ƛ σM—↠M′ ⟩
        (ƛ (⟪ exts τ ⟫ N)) · M′
        —→⟨ ƛτN·σM—→ ⟩
        ⟪ exts τ ⨟ subst-zero M′ ⟫ N
        —↠⟨ —↠N′ ⟩
        N′ □

cbv→reduce :  ∀{M : Term zero}{Δ}{δ : ClosEnv Δ}{N′ : Term (suc Δ)}
     → ∅' ⊢ M ⇓ clos N′ δ
       -----------------------------
     → Σ[ N ∈ Term (suc zero) ] (M —↠ ƛ N)
cbv→reduce {M}{Δ}{δ}{N′} M⇓c
    with ⇓→—↠×≈{σ = ids} M⇓c ≈ₑ-id
... | ⟨ N , ⟨ rs , ⟨ σ , ⟨ h , eq2 ⟩ ⟩ ⟩ ⟩
    rewrite sub-id{M = M} | eq2 =
    ⟨ ⟪ exts σ ⟫ N′ , rs ⟩

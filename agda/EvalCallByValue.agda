open import Variables
open import Lambda
open Lambda.ASTMod
   using (`_; _⦅_⦆; Subst;
          exts; cons; bind; nil; ⟪_⟫; _⨟_; subst-zero)
open import Syntax2 Op sig
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

  ⇓-var : ∀{Γ}{γ : ClosEnv Γ}{x : Var Γ}{Δ}{δ : ClosEnv Δ}{M : Term Δ}
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
... | refl | refl = {!!}



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


⇓→—↠×𝔹 : ∀{Γ}{γ : ClosEnv Γ}{σ : Subst Γ zero}{M : Term Γ}{c : Clos}
       → γ ⊢ M ⇓ c  →  γ ≈ₑ σ
         ---------------------------------------
       → Σ[ N ∈ Term zero ] (⟪ σ ⟫ M —↠ N) × c ≈ N
⇓→—↠×𝔹 {γ = γ}{σ} (⇓-var{x = x}) γ≈ₑσ = ⟨ σ x , ⟨ σ x ▩ , γ≈ₑσ ⟩ ⟩
⇓→—↠×𝔹 {σ = σ} {c = clos N γ} ⇓-lam γ≈ₑσ =
    ⟨ ⟪ σ ⟫ (ƛ N) , ⟨ ⟪ σ ⟫ (ƛ N) ▩ , ⟨ σ , ⟨ γ≈ₑσ , refl ⟩ ⟩ ⟩ ⟩
⇓→—↠×𝔹{Γ}{γ} {σ = σ} {app ⦅ cons L (cons M nil) ⦆} {c}
    (⇓-app {Γ}{δ = δ}{N}{V = clos M₁ δ₁}{V′ = clos N₁ δ₂} L⇓ƛNδ M⇓V N⇓V′) γ≈ₑσ
    with ⇓→—↠×𝔹{σ = σ} L⇓ƛNδ γ≈ₑσ
... | ⟨ L′ , ⟨ σL—↠ƛτN , ⟨ τ , ⟨ δ≈ₑτ , L′≡ ⟩ ⟩ ⟩ ⟩
    rewrite L′≡
    with ⇓→—↠×𝔹{σ = σ} M⇓V γ≈ₑσ
... | ⟨ M′ , ⟨ σM—↠M′ , ⟨ θ , ⟨ δ₁≈ₑθ , M′≡ ⟩ ⟩ ⟩ ⟩
    rewrite M′≡
    with ⇓→—↠×𝔹 {σ = ext-subst τ (lam ⦅ bind (⟪ exts θ ⟫ M₁) nil ⦆)} N⇓V′
             (λ {x} → ≈ₑ-ext δ≈ₑτ ⟨ θ , ⟨ δ₁≈ₑθ , refl ⟩ ⟩ {x} )
       | β-rule{zero}{⟪ exts τ ⟫ N}{lam ⦅ bind (⟪ exts θ ⟫ M₁) nil ⦆} V-ƛ
... | ⟨ N′ , ⟨ —↠N′ , ⟨ ψ , ⟨ δ₂≈ₑψ , N′≡ ⟩ ⟩ ⟩ ⟩ | ƛτN·σM—→
    rewrite sub-sub{M = N}{σ₁ = exts τ}
                   {σ₂ = subst-zero (lam ⦅ bind (⟪ exts θ ⟫ M₁) nil ⦆)} =
    ⟨ N′ , ⟨ r , ⟨ ψ , ⟨ δ₂≈ₑψ , N′≡ ⟩ ⟩ ⟩ ⟩
    where
    r = (app ⦅ cons (⟪ σ ⟫ L) (cons (⟪ σ ⟫ M) nil) ⦆)
        —↠⟨ appL-cong σL—↠ƛτN ⟩
        ((app ⦅ cons (lam ⦅ bind (⟪ exts τ ⟫ N) nil ⦆) (cons (⟪ σ ⟫ M) nil) ⦆))
        —↠⟨ appR-cong V-ƛ σM—↠M′ ⟩
        (((app ⦅ cons (lam ⦅ bind (⟪ exts τ ⟫ N) nil ⦆)
                (cons (lam ⦅ bind (⟪ exts θ ⟫ M₁) nil ⦆) nil) ⦆)))
        —→⟨ ƛτN·σM—→ ⟩
        ⟪ exts τ ⨟ subst-zero (lam ⦅ bind (⟪ exts θ ⟫ M₁) nil ⦆) ⟫ N
        —↠⟨ —↠N′ ⟩
        N′ ▩

cbn→reduce :  ∀{M : Term zero}{Δ}{δ : ClosEnv Δ}{N′ : Term (suc Δ)}
     → ∅' ⊢ M ⇓ clos N′ δ
       -----------------------------
     → Σ[ N ∈ Term (suc zero) ] (M —↠ ƛ N)
cbn→reduce {M}{Δ}{δ}{N′} M⇓c
    with ⇓→—↠×𝔹{σ = ids} M⇓c ≈ₑ-id
... | ⟨ N , ⟨ rs , ⟨ σ , ⟨ h , eq2 ⟩ ⟩ ⟩ ⟩
    rewrite sub-id{M = M} | eq2 =
    ⟨ ⟪ exts σ ⟫ N′ , rs ⟩

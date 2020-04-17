open import Lambda
open Lambda.Reduction
open Lambda.ASTMod
   using (`_; _⦅_⦆; Subst;
          exts; cons; bind; ast; nil; ⟦_⟧; ⟪_⟫; _⨟_; subst-zero;
          subst-zero-exts-cons; sub-id; sub-sub)

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Function using (_∘_)


module EvalCallByName where

Context = ℕ

ClosEnv : Set

data Clos : Set where
  clos : (M : Term) → ClosEnv → Clos

ClosEnv = List Clos

∅' : ClosEnv
∅' =  []

_,'_ : ClosEnv → Clos → ClosEnv
(γ ,' c) = c ∷ γ

nth : ClosEnv → Var → Clos
nth [] 0 = clos (` 0) [] {- bogus -}
nth (c ∷ γ) 0 = c
nth [] (suc x) = clos (` (suc x)) [] {- bogus -}
nth (x₁ ∷ γ) (suc x) = nth γ x

data _⊢_⇓_ : ClosEnv → Term → Clos → Set where

  ⇓-var : ∀{γ : ClosEnv}{x : Var}{δ : ClosEnv}{M : Term}{V}
        → nth γ x ≡ clos M δ
        → δ ⊢ M ⇓ V
          -----------
        → γ ⊢ ` x ⇓ V

  ⇓-lam : ∀{γ : ClosEnv}{N : Term}
        → γ ⊢ ƛ N ⇓ clos (ƛ N) γ

  ⇓-app : ∀{γ : ClosEnv}{L M : Term}{δ : ClosEnv}
           {N : Term}{V}
       → γ ⊢ L ⇓ clos (ƛ N) δ   →   (δ ,' clos M γ) ⊢ N ⇓ V
         ---------------------------------------------------
       → γ ⊢ L · M ⇓ V

⇓-determ : ∀{γ : ClosEnv}{M : Term}{V V' : Clos}
         → γ ⊢ M ⇓ V → γ ⊢ M ⇓ V'
         → V ≡ V'
⇓-determ (⇓-var eq1 mc) (⇓-var eq2 mc')
      with trans (sym eq1) eq2
... | refl = ⇓-determ mc mc'
⇓-determ ⇓-lam ⇓-lam = refl
⇓-determ (⇓-app mc mc₁) (⇓-app mc' mc'') 
    with ⇓-determ mc mc'
... | refl = ⇓-determ mc₁ mc''



_≈_ : Clos → Term → Set
data _≈ₑ_ : ClosEnv → Subst → Set

(clos M γ) ≈ N = Σ[ σ ∈ Subst ] γ ≈ₑ σ × (N ≡ ⟪ σ ⟫ M)

data _≈ₑ_ where
  ≈ₑ-id : ∅' ≈ₑ id
  ≈ₑ-ext : ∀ {γ : ClosEnv} {σ : Subst} {c} {N : Term}
      → γ ≈ₑ σ  →  c ≈ N
        -------------------
      → (γ ,' c) ≈ₑ (N • σ)

γ≈ₑσ→γ[x]≈σ[x] : ∀{x}{γ}{σ} → γ ≈ₑ σ → nth γ x ≈ ⟦ σ ⟧ x
γ≈ₑσ→γ[x]≈σ[x] {zero} {.[]} {.(↑ 0)} ≈ₑ-id = ⟨ (↑ 0) , ⟨ ≈ₑ-id , refl ⟩ ⟩
γ≈ₑσ→γ[x]≈σ[x] {suc x} {.[]} {.(↑ 0)} ≈ₑ-id = ⟨ (↑ 0) , ⟨ ≈ₑ-id , refl ⟩ ⟩
γ≈ₑσ→γ[x]≈σ[x] {zero} {.(_ ∷ _)} {.(_ • _)} (≈ₑ-ext γ≈ₑσ c≈N) = c≈N
γ≈ₑσ→γ[x]≈σ[x] {suc x} {.(_ ∷ _)} {.(_ • _)} (≈ₑ-ext γ≈ₑσ c≈N) =
    γ≈ₑσ→γ[x]≈σ[x] γ≈ₑσ


⇓→—↠×≈ : ∀{γ : ClosEnv}{σ : Subst}{M : Term}{c : Clos}
       → γ ⊢ M ⇓ c  →  γ ≈ₑ σ
         ---------------------------------------
       → Σ[ N ∈ Term ] (⟪ σ ⟫ M —↠ N) × c ≈ N
⇓→—↠×≈ {γ = γ} (⇓-var{x = x} γx≡Lδ δ⊢L⇓c) γ≈ₑσ
    with nth γ x | γ≈ₑσ→γ[x]≈σ[x] {x} γ≈ₑσ | γx≡Lδ
... | clos L δ | ⟨ τ , ⟨ δ≈ₑτ , σx≡τL ⟩ ⟩ | refl
    with ⇓→—↠×≈{σ = τ} δ⊢L⇓c δ≈ₑτ
... | ⟨ N , ⟨ τL—↠N , c≈N ⟩ ⟩ rewrite σx≡τL =
      ⟨ N , ⟨ τL—↠N , c≈N ⟩ ⟩
⇓→—↠×≈ {σ = σ} {c = clos (lam ⦅ cons (bind (ast N)) nil ⦆) γ} ⇓-lam γ≈ₑσ =
    ⟨ ⟪ σ ⟫ (ƛ N) , ⟨ ⟪ σ ⟫ (ƛ N) □ , ⟨ σ , ⟨ γ≈ₑσ , refl ⟩ ⟩ ⟩ ⟩
⇓→—↠×≈ {γ} {σ = σ} {app ⦅ cons (ast L) (cons (ast M) nil) ⦆} {c}
       (⇓-app {N = N} L⇓ƛNδ N⇓c) γ≈ₑσ
    with ⇓→—↠×≈{σ = σ} L⇓ƛNδ γ≈ₑσ
... | ⟨ _ , ⟨ σL—↠ƛτN , ⟨ τ , ⟨ δ≈ₑτ , ≡ƛτN ⟩ ⟩ ⟩ ⟩ rewrite ≡ƛτN
    with ⇓→—↠×≈ {σ = (⟪ σ ⟫ M) • τ} N⇓c (≈ₑ-ext δ≈ₑτ ⟨ σ , ⟨ γ≈ₑσ , refl ⟩ ⟩)
       | β-rule {⟪ exts τ ⟫ N} {⟪ σ ⟫ M}
... | ⟨ N' , ⟨ —↠N' , c≈N' ⟩ ⟩ | ƛτN·σM—→
    rewrite sub-sub{M = N}{σ₁ = exts τ}{σ₂ = subst-zero (⟪ σ ⟫ M)}
    | sym (subst-zero-exts-cons{τ}{⟪ σ ⟫ M}) =
    ⟨ N' , ⟨ r , c≈N' ⟩ ⟩
    where
    r = (app ⦅ cons (ast (⟪ σ ⟫ L)) (cons (ast (⟪ σ ⟫ M)) nil) ⦆)
        —↠⟨ appL-cong σL—↠ƛτN ⟩
        (ƛ (⟪ exts τ ⟫ N)) · ⟪ σ ⟫ M
        —→⟨ ƛτN·σM—→ ⟩
        ⟪ exts τ ⨟ subst-zero (⟪ σ ⟫ M) ⟫ N
        —↠⟨ —↠N' ⟩
        N' □

cbn→reduce :  ∀{M : Term}{δ : ClosEnv}{N′ : Term}
     → ∅' ⊢ M ⇓ clos (ƛ N′) δ
       -----------------------------
     → Σ[ N ∈ Term ] (M —↠ ƛ N)
cbn→reduce {M}{δ}{N′} M⇓c
    with ⇓→—↠×≈{σ = id} M⇓c ≈ₑ-id
... | ⟨ N , ⟨ rs , ⟨ σ , ⟨ h , eq2 ⟩ ⟩ ⟩ ⟩
    rewrite sub-id{M = M} | eq2 =
    ⟨ ⟪ exts σ ⟫ N′ , rs ⟩


open import Lambda
open Lambda.ASTMod
   using (Var; `_; _⦅_⦆; Subst;
          exts; cons; bind; ast; nil; ⟦_⟧; ⟪_⟫; _⨟_; subst-zero;
          id; _•_; subst-zero-exts-cons; sub-id; sub-sub;
          WF; WF-var; WF-op; WF-ast; WF-nil; WF-cons)
open import LambdaCallByValue

open import Data.Nat using (ℕ; zero; suc; _<_)
open import Data.Nat.Properties using (≤-pred)
open import Data.List using (List; []; _∷_; length)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Function using (_∘_)


module EvalCallByValue where

Context = ℕ

data Clos : Set

ClosEnv : Set
ClosEnv = List Clos

data Clos where
  clos : (N : Term) → (γ : ClosEnv) → .{wf : WF (suc (length γ)) N} → Clos
  bogus : Clos


∅' : ClosEnv
∅' =  []

_,'_ : ClosEnv → Clos → ClosEnv
(γ ,' c) = c ∷ γ

nth : ClosEnv → Var → Clos
nth [] 0 = bogus
nth (c ∷ γ) 0 = c
nth [] (suc x) = bogus
nth (x₁ ∷ γ) (suc x) = nth γ x

data _⊢_⇓_ : ClosEnv → Term → Clos → Set where

  ⇓-var : ∀{γ : ClosEnv}{x : Var}
          -----------------
        → γ ⊢ ` x ⇓ nth γ x

  ⇓-lam : ∀{γ : ClosEnv}{N : Term}{wf : WF (suc (length γ)) N}
        → γ ⊢ ƛ N ⇓ clos N γ {wf}

  ⇓-app : ∀{γ : ClosEnv}{L M : Term}{δ : ClosEnv}
           {N : Term}{V V′}{wf : WF (suc (length δ)) N}
       → γ ⊢ L ⇓ clos N δ {wf}  →  γ ⊢ M ⇓ V
       → (δ ,' V) ⊢ N ⇓ V′
         ---------------------------------------------------
       → γ ⊢ L · M ⇓ V′

⇓-determ : ∀{γ : ClosEnv}{M : Term}{V V' : Clos}
         → γ ⊢ M ⇓ V → γ ⊢ M ⇓ V'
         → V ≡ V'
⇓-determ (⇓-var) (⇓-var) = refl
⇓-determ ⇓-lam ⇓-lam = refl
⇓-determ (⇓-app mc₁ mc₂ mc₃) (⇓-app mc₁′ mc₂′ mc₃′) 
    with ⇓-determ mc₁ mc₁′ | ⇓-determ mc₂ mc₂′ 
... | refl | refl = ⇓-determ mc₃ mc₃′

data _≈_ : Clos → Term → Set
data _≈ₑ_ : ClosEnv → Subst → Set

data _≈_ where
  ≈-clos : ∀ {σ}{γ}{M N : Term}{wf : WF (suc (length γ)) M}
     → γ ≈ₑ σ
     → (N ≡ ⟪ σ ⟫ (ƛ M))
     → (clos M γ {wf}) ≈ N

data _≈ₑ_ where
  ≈ₑ-id : ∅' ≈ₑ id
  ≈ₑ-ext : ∀ {γ : ClosEnv} {σ : Subst} {c} {N : Term}
      → γ ≈ₑ σ  →  c ≈ N
        -------------------
      → (γ ,' c) ≈ₑ (N • σ)

γ≈ₑσ→γ[x]≈σ[x] : ∀{x}{γ}{σ}
   → γ ≈ₑ σ
   → x < length γ
   → nth γ x ≈ ⟦ σ ⟧ x
γ≈ₑσ→γ[x]≈σ[x] {zero} {.(_ ∷ _)} {.(_ • _)} (≈ₑ-ext γ≈ₑσ c≈N) x<γ = c≈N
γ≈ₑσ→γ[x]≈σ[x] {suc x} {.(_ ∷ _)} {.(_ • _)} (≈ₑ-ext γ≈ₑσ c≈N) x<γ =
    γ≈ₑσ→γ[x]≈σ[x] γ≈ₑσ (≤-pred x<γ )

≈→TermValue : ∀{V : Clos}{M : Term}
            → V ≈ M
            → TermValue M
≈→TermValue {clos N x {wf}} {_} (≈-clos _ refl) = V-ƛ

⇓→—↠×≈ : ∀{γ : ClosEnv}{σ : Subst}{M : Term}{c : Clos}
       → WF (length γ) M
       → γ ⊢ M ⇓ c  →  γ ≈ₑ σ
         ---------------------------------------
       → Σ[ N ∈ Term ] (⟪ σ ⟫ M —↠ N) × c ≈ N
⇓→—↠×≈ {γ} {σ} (WF-var x lt) (⇓-var {x = x}) γ≈ₑσ =
    ⟨ ⟦ σ ⟧ x , ⟨ (⟦ σ ⟧ x □) , (γ≈ₑσ→γ[x]≈σ[x] γ≈ₑσ lt) ⟩ ⟩
⇓→—↠×≈ {σ = σ} {c = clos N γ {wfN}} wf (⇓-lam {wf = wf'}) γ≈ₑσ =
    ⟨ ⟪ σ ⟫ (ƛ N) , ⟨ ⟪ σ ⟫ (ƛ N) □ , ≈-clos  {wf = wf'} γ≈ₑσ refl ⟩ ⟩
⇓→—↠×≈ {γ} {σ = σ} {app ⦅ cons (ast L) (cons (ast M) nil) ⦆} {c}
    (WF-op (WF-cons (WF-ast wfL) (WF-cons (WF-ast wfM) WF-nil)))
    (⇓-app {δ = δ}{N}{V}{V′} L⇓ƛNδ M⇓V N⇓V′) γ≈ₑσ
    with ⇓→—↠×≈{σ = σ} wfL L⇓ƛNδ γ≈ₑσ
... | ⟨ L′ , ⟨ σL—↠ƛτN , (≈-clos {τ}{wf = wfN} δ≈ₑτ L′≡) ⟩ ⟩
    rewrite L′≡
    with ⇓→—↠×≈{σ = σ} wfM M⇓V γ≈ₑσ
... | ⟨ M′ , ⟨ σM—↠M′ , V≈M′ ⟩ ⟩
    with ⇓→—↠×≈ {σ = M′ • τ } wfN N⇓V′ (≈ₑ-ext δ≈ₑτ V≈M′)
       | β-rule{⟪ exts τ ⟫ N}{M′} (≈→TermValue {V}{M′} V≈M′)
... | ⟨ N′ , ⟨ —↠N′ , c≈N′ ⟩ ⟩ | ƛτN·σM—→
    rewrite sub-sub{M = N}{σ₁ = exts τ}{σ₂ = subst-zero M′}
    | sym (subst-zero-exts-cons {τ}{M′}) =
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

cbv→reduce : ∀{M : Term}{δ : ClosEnv}{N′ : Term}
       { wfM : WF 0 M }{wfN′ : WF (suc (length δ)) N′}
     → ∅' ⊢ M ⇓ clos N′ δ {wfN′}
       -----------------------------
     → Σ[ N ∈ Term ] (M —↠ ƛ N)
cbv→reduce {M}{δ}{N′}{wfM}{wfN′} M⇓c
    with ⇓→—↠×≈{σ = id} wfM M⇓c ≈ₑ-id
... | ⟨ N , ⟨ rs , (≈-clos {σ} h eq2) ⟩ ⟩
    rewrite sub-id{M = M} | eq2 =
    ⟨ ⟪ exts σ ⟫ N′ , rs ⟩


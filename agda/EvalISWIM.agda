open import Primitives
open import ISWIM
open ISWIM.ASTMod
   using (`_; _⦅_⦆; Subst;
          exts; cons; bind; ast; nil; ⟦_⟧; ⟪_⟫; _⨟_; subst-zero;
          subst-zero-exts-cons; sub-id; sub-sub; len-mk-list;
          WF; WF-var; WF-op; WF-ast; WF-nil; WF-cons)
open import Data.Nat using (ℕ; zero; suc; _<_)
open import Data.Nat.Properties using (≤-pred)
open import Data.List using (List; []; _∷_; length)
open import Relation.Binary.PropositionalEquality
    using (_≡_; refl; sym; trans; subst)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Function using (_∘_)


module EvalISWIM where

Context = ℕ

data Val : Set

ValEnv : Set
ValEnv = List Val

data Val where
  val-const : ∀{p : Prim} → rep p → Val
  val-clos : (N : Term) → (γ : ValEnv) → .{wf : WF (suc (length γ)) N} → Val
  bogus : Val


∅' : ValEnv
∅' = []

_,'_ : ValEnv → Val → ValEnv
(γ ,' c) = c ∷ γ

nth : ValEnv → Var → Val
nth [] 0 = bogus
nth (v ∷ γ) 0 = v
nth [] (suc x) = bogus
nth (v ∷ γ) (suc x) = nth γ x


data _⊢_⇓_ : ValEnv → Term → Val → Set where

  ⇓-lit : ∀{γ : ValEnv}{p : Prim}{k : rep p}
          ---------------------------------
        → γ ⊢ $ p k ⇓ val-const {p} k
        
  ⇓-var : ∀{γ : ValEnv}{x : Var}
          -----------------
        → γ ⊢ ` x ⇓ nth γ x

  ⇓-lam : ∀{γ : ValEnv}{N : Term}{wf : WF (suc (length γ)) N }
        → γ ⊢ ƛ N ⇓ val-clos N γ {wf}

  ⇓-app : ∀{γ : ValEnv}{L M : Term}{δ : ValEnv}
           {N : Term}{V V′}{wf : WF (suc (length δ)) N}
       → γ ⊢ L ⇓ val-clos N δ {wf} →  γ ⊢ M ⇓ V
       → (δ ,' V) ⊢ N ⇓ V′
         ---------------------------------------------------
       → γ ⊢ L · M ⇓ V′
  ⇓-prim : ∀{γ : ValEnv}{L M : Term}{P : Prim}{B : Base}
                {f : rep (B ⇒ P)}{k : base-rep B}
       → γ ⊢ L ⇓ val-const {B ⇒ P} f  →  γ ⊢ M ⇓ val-const {base B} k
         ------------------------------------------------------------
       → γ ⊢ L · M ⇓ val-const {P} (f k)

⇓-determ : ∀{γ : ValEnv}{M : Term}{V V' : Val}
         → γ ⊢ M ⇓ V → γ ⊢ M ⇓ V'
         → V ≡ V'
⇓-determ (⇓-lit) (⇓-lit) = refl         
⇓-determ (⇓-var) (⇓-var) = refl
⇓-determ ⇓-lam ⇓-lam = refl
⇓-determ (⇓-app mc₁ mc₂ mc₃) (⇓-app mc₁′ mc₂′ mc₃′) 
    with ⇓-determ mc₁ mc₁′ | ⇓-determ mc₂ mc₂′ 
... | refl | refl = ⇓-determ mc₃ mc₃′
⇓-determ (⇓-prim mc₁ mc₂) (⇓-prim mc₁′ mc₂′)
    with ⇓-determ mc₁ mc₁′ | ⇓-determ mc₂ mc₂′ 
... | refl | refl = refl
⇓-determ (⇓-app mc₁ mc₂ mc₃) (⇓-prim mc₁′ mc₂′)
    with ⇓-determ mc₁ mc₁′
... | ()    
⇓-determ (⇓-prim mc₁ mc₂) (⇓-app mc₁′ mc₂′ mc₃′)
    with ⇓-determ mc₁ mc₁′
... | ()    

data _≈_ : Val → Term → Set
data _≈ₑ_ : ValEnv → Subst → Set

data _≈_ where
  ≈-const : ∀{N}{p}{k}
     → N ≡ $ p k
     → (val-const {p} k) ≈ N
  ≈-clos : ∀ {σ}{γ}{M N : Term}{wf : WF (suc (length γ)) M}
     → γ ≈ₑ σ
     → (N ≡ ⟪ σ ⟫ (ƛ M))
     → (val-clos M γ {wf}) ≈ N

data _≈ₑ_ where
  ≈ₑ-id : ∅' ≈ₑ id
  ≈ₑ-ext : ∀ {γ : ValEnv} {σ : Subst} {c} {N : Term}
      → γ ≈ₑ σ  →  c ≈ N
        -------------------
      → (γ ,' c) ≈ₑ (N • σ)

{-
_≈_ : Val → (Term zero) → Set
_≈ₑ_ : ∀{Γ} → ValEnv Γ → Subst Γ zero → Set

(val-const {p} k) ≈ N = N ≡ $ p k
(val-clos {Γ} M γ) ≈ N = Σ[ σ ∈ Subst Γ zero ] γ ≈ₑ σ × (N ≡ ⟪ σ ⟫ (ƛ M))

γ ≈ₑ σ = ∀{x} → (γ x) ≈ (σ x)


≈ₑ-id : ∅' ≈ₑ (id {Γ = zero})
≈ₑ-id {()}
-}

≈→TermValue : ∀{V : Val}{M : Term}
            → V ≈ M
            → TermValue M
≈→TermValue {val-const x} {M} (≈-const refl) = V-lit
≈→TermValue {val-clos N x} {M} (≈-clos _ refl) = V-ƛ

{-
ext-subst : ∀{Γ Δ} → Subst Γ Δ → Term Δ → Subst (suc Γ) Δ
ext-subst{Γ}{Δ} σ N = ⟪ subst-zero N ⟫ ∘ exts σ
-}
{-
≈ₑ-ext : ∀ {Γ} {γ : ValEnv Γ} {σ : Subst Γ zero} {c} {N : Term zero}
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
-}

γ≈ₑσ→γ[x]≈σ[x] : ∀{x}{γ}{σ}
   → γ ≈ₑ σ
   → x < length γ
   → nth γ x ≈ ⟦ σ ⟧ x
γ≈ₑσ→γ[x]≈σ[x] {zero} {.(_ ∷ _)} {.(_ • _)} (≈ₑ-ext γ≈ₑσ c≈N) x<γ = c≈N
γ≈ₑσ→γ[x]≈σ[x] {suc x} {.(_ ∷ _)} {.(_ • _)} (≈ₑ-ext γ≈ₑσ c≈N) x<γ =
    γ≈ₑσ→γ[x]≈σ[x] γ≈ₑσ (≤-pred x<γ )

⇓→—↠×≈ : ∀{γ : ValEnv}{σ : Subst}{M : Term}{c : Val}
       → WF (length γ) M
       → γ ⊢ M ⇓ c  →  γ ≈ₑ σ
         ---------------------------------------
       → Σ[ N ∈ Term ] (⟪ σ ⟫ M —↠ N) × c ≈ N
⇓→—↠×≈ wf (⇓-lit {p = p}{k}) γ≈ₑσ =
    ⟨ $ p k , ⟨ $ p k □ , ≈-const refl ⟩ ⟩
⇓→—↠×≈ {γ = γ}{σ} (WF-var ∋x lt) (⇓-var {x = x}) γ≈ₑσ
    with subst (λ □ → x < □) (len-mk-list (length γ)) lt
... | lt' =
    ⟨ ⟦ σ ⟧ x , ⟨ ⟦ σ ⟧ x □ , γ≈ₑσ→γ[x]≈σ[x] γ≈ₑσ lt' ⟩ ⟩
⇓→—↠×≈ {σ = σ} {c = val-clos N γ} wf (⇓-lam{wf = wf'}) γ≈ₑσ =
    ⟨ ⟪ σ ⟫ (ƛ N) , ⟨ ⟪ σ ⟫ (ƛ N) □ , ≈-clos {wf = wf'} γ≈ₑσ refl ⟩ ⟩
⇓→—↠×≈ {γ} {σ = σ} {app ⦅ cons (ast L) (cons (ast M) nil) ⦆} {c}
    (WF-op (WF-cons (WF-ast wfL) (WF-cons (WF-ast wfM) WF-nil)) _)
    (⇓-prim {P = P}{B}{f}{k} L⇓f M⇓k) γ≈ₑσ 
    with ⇓→—↠×≈{σ = σ} wfL L⇓f γ≈ₑσ
... | ⟨ L′ , ⟨ σL—↠f , ≈-const L′≡ ⟩ ⟩
    rewrite L′≡ 
    with ⇓→—↠×≈{σ = σ} wfM M⇓k γ≈ₑσ
... | ⟨ M′ , ⟨ σM—↠M′ , ≈-const M′≡ ⟩ ⟩
    rewrite M′≡ =
    ⟨ $ P (f k) , ⟨ r , ≈-const refl ⟩ ⟩
    where
    r = (⟪ σ ⟫ L) · (⟪ σ ⟫ M)
        —↠⟨ appL-cong σL—↠f  ⟩
        ($ (B ⇒ P) f) · (⟪ σ ⟫ M)
        —↠⟨ appR-cong V-lit σM—↠M′ ⟩
        ($ (B ⇒ P) f) · ($ (base B) k)
        —→⟨ δ-rule ⟩
        ($ P (f k))  □
⇓→—↠×≈ {γ} {σ = σ} {app ⦅ cons (ast L) (cons (ast M) nil) ⦆} {c}
    (WF-op (WF-cons (WF-ast wfL) (WF-cons (WF-ast wfM) WF-nil)) _)
    (⇓-app {Γ}{δ = δ}{N}{V}{V′} L⇓ƛNδ M⇓V N⇓V′) γ≈ₑσ
    with ⇓→—↠×≈{σ = σ} wfL L⇓ƛNδ γ≈ₑσ
... | ⟨ L′ , ⟨ σL—↠ƛτN , ≈-clos {σ = τ}{wf = wfN} δ≈ₑτ L′≡ ⟩ ⟩
    rewrite L′≡
    with ⇓→—↠×≈{σ = σ} wfM M⇓V γ≈ₑσ
... | ⟨ M′ , ⟨ σM—↠M′ , V≈M′ ⟩ ⟩
    with ⇓→—↠×≈ {σ = M′ • τ} wfN N⇓V′ (≈ₑ-ext δ≈ₑτ V≈M′)
       | β-rule {⟪ exts τ ⟫ N}{M′} (≈→TermValue V≈M′)
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

⇓→—↠ :  ∀{M : Term}{c : Val} {wfM : WF 0 M}
     → ∅' ⊢ M ⇓ c
       -----------------------------------------
     → Σ[ N ∈ Term ] TermValue N × (M —↠ N)
⇓→—↠ {M} {c} {wfM} M⇓c
    with ⇓→—↠×≈{σ = id} wfM M⇓c ≈ₑ-id
... | ⟨ N , ⟨ rs , c≈N ⟩ ⟩
    rewrite sub-id{M = M} =
    ⟨ N , ⟨ (≈→TermValue c≈N) , rs ⟩ ⟩

open import Primitives
open import Variables
open import ISWIM
open ISWIM.ASTMod
   using (`_; _⦅_⦆; Subst;
          exts; cons; bind; ast; nil; ⟪_⟫; _⨟_; subst-zero)
open import Syntax3 Op sig
   using (ids; _•_; subst-zero-exts-cons; sub-id; sub-sub)

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using ([])
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Function using (_∘_)


module EvalISWIM where

Context = ℕ

ValEnv : Context → Set

data Val : Set where
  val-const : ∀{p : Prim} → rep p → Val
  val-clos : ∀{Γ} → (N : Term (suc Γ)) → ValEnv Γ → Val

ValEnv Γ = ∀ (x : Var Γ) → Val

∅' : ValEnv zero
∅' ()

_,'_ : ∀ {Γ} → ValEnv Γ → Val → ValEnv (suc Γ)
(γ ,' c) Z = c
(γ ,' c) (S x) = γ x

data _⊢_⇓_ : ∀{Γ} → ValEnv Γ → (Term Γ) → Val → Set where

  ⇓-lit : ∀{Γ}{γ : ValEnv Γ}{p : Prim}{k : rep p}
          ---------------------------------
        → γ ⊢ $_ {Γ}{p} k ⇓ val-const {p} k
        
  ⇓-var : ∀{Γ}{γ : ValEnv Γ}{x : Var Γ}
          -------------
        → γ ⊢ ` x ⇓ γ x

  ⇓-lam : ∀{Γ}{γ : ValEnv Γ}{N : Term (suc Γ)}
        → γ ⊢ ƛ N ⇓ val-clos N γ

  ⇓-app : ∀{Γ}{γ : ValEnv Γ}{L M : Term Γ}{Δ}{δ : ValEnv Δ}
           {N : Term (suc Δ)}{V V′}
       → γ ⊢ L ⇓ val-clos N δ  →  γ ⊢ M ⇓ V
       → (δ ,' V) ⊢ N ⇓ V′
         ---------------------------------------------------
       → γ ⊢ L · M ⇓ V′
  ⇓-prim : ∀{Γ}{γ : ValEnv Γ}{L M : Term Γ}{P : Prim}{B : Base}
                {f : rep (B ⇒ P)}{k : base-rep B}
       → γ ⊢ L ⇓ val-const {B ⇒ P} f  →  γ ⊢ M ⇓ val-const {base B} k
         ------------------------------------------------------------
       → γ ⊢ L · M ⇓ val-const {P} (f k)

⇓-determ : ∀{Γ}{γ : ValEnv Γ}{M : Term Γ}{V V' : Val}
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

_≈_ : Val → (Term zero) → Set
_≈ₑ_ : ∀{Γ} → ValEnv Γ → Subst Γ zero → Set

(val-const {p} k) ≈ N = N ≡ lit {p} k ⦅ nil ⦆
(val-clos {Γ} M γ) ≈ N = Σ[ σ ∈ Subst Γ zero ] γ ≈ₑ σ × (N ≡ ⟪ σ ⟫ (ƛ M))

γ ≈ₑ σ = ∀{x} → (γ x) ≈ (σ x)


≈ₑ-id : ∅' ≈ₑ (ids {Γ = zero})
≈ₑ-id {()}

≈→TermValue : ∀{V : Val}{M : Term zero}
            → V ≈ M
            → TermValue M
≈→TermValue {val-const x} {M} refl = V-lit
≈→TermValue {val-clos N x} {M} ⟨ _ , ⟨ _ , refl ⟩ ⟩ = V-ƛ

ext-subst : ∀{Γ Δ} → Subst Γ Δ → Term Δ → Subst (suc Γ) Δ
ext-subst{Γ}{Δ} σ N = ⟪ subst-zero N ⟫ ∘ exts σ

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


⇓→—↠×≈ : ∀{Γ}{γ : ValEnv Γ}{σ : Subst Γ zero}{M : Term Γ}{c : Val}
       → γ ⊢ M ⇓ c  →  γ ≈ₑ σ
         ---------------------------------------
       → Σ[ N ∈ Term zero ] (⟪ σ ⟫ M —↠ N) × c ≈ N
⇓→—↠×≈ (⇓-lit {p = p}{k}) γ≈ₑσ =
    ⟨ lit {p} k ⦅ nil ⦆ , ⟨ lit {p} k ⦅ nil ⦆ □ , refl ⟩ ⟩
⇓→—↠×≈ {γ = γ}{σ} (⇓-var {x = x}) γ≈ₑσ = ⟨ σ x , ⟨ σ x □ , γ≈ₑσ ⟩ ⟩
⇓→—↠×≈ {σ = σ} {c = val-clos N γ} ⇓-lam γ≈ₑσ =
    ⟨ ⟪ σ ⟫ (ƛ N) , ⟨ ⟪ σ ⟫ (ƛ N) □ , ⟨ σ , ⟨ γ≈ₑσ , refl ⟩ ⟩ ⟩ ⟩
⇓→—↠×≈{Γ}{γ} {σ = σ} {app ⦅ cons (ast L) (cons (ast M) nil) ⦆} {c}
    (⇓-prim {P = P}{B}{f}{k} L⇓f M⇓k) γ≈ₑσ 
    with ⇓→—↠×≈{σ = σ} L⇓f γ≈ₑσ
... | ⟨ L′ , ⟨ σL—↠f , L′≡ ⟩ ⟩
    rewrite L′≡ 
    with ⇓→—↠×≈{σ = σ} M⇓k γ≈ₑσ
... | ⟨ M′ , ⟨ σM—↠M′ , M′≡ ⟩ ⟩
    rewrite M′≡ =
    ⟨ lit {P} (f k) ⦅ nil ⦆ , ⟨ r , refl ⟩ ⟩
    where
    r = (⟪ σ ⟫ L) · (⟪ σ ⟫ M)
        —↠⟨ appL-cong σL—↠f  ⟩
        (lit f ⦅ nil ⦆) · (⟪ σ ⟫ M)
        —↠⟨ appR-cong V-lit σM—↠M′ ⟩
        (lit f ⦅ nil ⦆) · (lit k ⦅ nil ⦆)
        —→⟨ δ-rule ⟩
        (lit (f k) ⦅ nil ⦆)  □
⇓→—↠×≈{Γ}{γ} {σ = σ} {app ⦅ cons (ast L) (cons (ast M) nil) ⦆} {c}
    (⇓-app {Γ}{δ = δ}{N}{V}{V′} L⇓ƛNδ M⇓V N⇓V′) γ≈ₑσ
    with ⇓→—↠×≈{σ = σ} L⇓ƛNδ γ≈ₑσ
... | ⟨ L′ , ⟨ σL—↠ƛτN , ⟨ τ , ⟨ δ≈ₑτ , L′≡ ⟩ ⟩ ⟩ ⟩
    rewrite L′≡
    with ⇓→—↠×≈{σ = σ} M⇓V γ≈ₑσ
... | ⟨ M′ , ⟨ σM—↠M′ , V≈M′ ⟩ ⟩
    with ⇓→—↠×≈ {σ = ext-subst τ M′} N⇓V′
             (λ {x} → ≈ₑ-ext δ≈ₑτ V≈M′ {x} )
       | β-rule{zero}{⟪ exts τ ⟫ N}{M′} (≈→TermValue V≈M′)
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

⇓→—↠ :  ∀{M : Term zero}{c : Val}
     → ∅' ⊢ M ⇓ c
       -----------------------------------------
     → Σ[ N ∈ Term zero ] TermValue N × (M —↠ N)
⇓→—↠ {M}{c} M⇓c
    with ⇓→—↠×≈{σ = ids} M⇓c ≈ₑ-id
... | ⟨ N , ⟨ rs , c≈N ⟩ ⟩
    rewrite sub-id{M = M} =
    ⟨ N , ⟨ (≈→TermValue c≈N) , rs ⟩ ⟩

open import Variables
open import Structures
open import Lambda using (_·_; ƛ; Term; lam; app)
open Lambda.Reduction using (_—→_; ξ₁-rule; ξ₂-rule; β-rule; ζ-rule)
open Lambda.ASTMod
   using (`_; _⦅_⦆; Subst;
          exts; cons; bind; nil; rename; ⟪_⟫; subst-zero; _[_]; rename-id)
import RenamePreserveReflect
import Filter

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; sym; cong; cong₂; cong-app; subst)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥-elim) renaming (⊥ to Bot)
open import Function using (_∘_)
open import Data.Unit using (⊤; tt)
open import Data.Empty renaming (⊥ to Bot)
open import Relation.Nullary using (¬_; Dec; yes; no)

module SubstitutionReflect where

module SubstReflect
  (D : Domain)
  (V : ValueOrdering D)
  (_●_ : ∀{Γ} → DomainAux.Denotation D Γ
       → DomainAux.Denotation D Γ → DomainAux.Denotation D Γ)
  (ℱ : ∀{Γ} → DomainAux.Denotation D (suc Γ) → DomainAux.Denotation D Γ)
  (MB : OrderingAux.LambdaModelBasics D V _●_ ℱ)
  where
  
  open Domain D
  open OrderingAux D V
  open DomainAux D
  open ValueOrdering V
  open LambdaDenot D V _●_ ℱ
  open Filter D V _●_ ℱ MB
  open RenamePreserveReflect D V _●_ ℱ MB using (⊑-env)

  SubRef : (Γ : ℕ) → (Δ : ℕ) → Env Δ → Term Γ → Term Δ
         → Subst Γ Δ → Value → Set
  SubRef Γ Δ δ M L σ v = ℰ L δ v → L ≡ ⟪ σ ⟫ M → δ `⊢ σ ↓ `⊥
                         → Σ[ γ ∈ Env Γ ] δ `⊢ σ ↓ γ  ×  ℰ M γ v

  module LambdaApp
    (subst-reflect-lambda : ∀{Γ Δ} {δ : Env Δ} {N : Term (suc Γ)}
                      {σ : Subst Γ Δ} {v}
          → (∀{u w}
             → SubRef (suc Γ) (suc Δ) (δ `, u) N (⟪ exts σ ⟫ N)  (exts σ) w)
          → SubRef Γ Δ δ (ƛ N) (⟪ σ ⟫ (ƛ N)) σ v)
    (subst-reflect-app : ∀ {Γ Δ} {δ : Env Δ} {L : Term Γ} {M : Term Γ} 
                      {σ : Subst Γ Δ} {v}
          → (∀ {v : Value} → SubRef Γ Δ δ L (⟪ σ ⟫ L) σ v)
          → (∀ {v : Value} → SubRef Γ Δ δ M (⟪ σ ⟫ M) σ v)
          → SubRef Γ Δ δ (L · M) (⟪ σ ⟫ (L · M)) σ v)
    where


    subst-reflect : ∀ {Γ Δ} {δ : Env Δ} {M : Term Γ} {L : Term Δ}
                      {σ : Subst Γ Δ} {v}
                  → SubRef Γ Δ δ M L σ v
    subst-reflect {Γ}{Δ}{δ}{` x}{L}{σ}{v} ℰLδv L≡σM δ⊢σ↓⊥
      rewrite L≡σM | sym (nth-const-env {Γ}{x}{v}) =
        ⟨ const-env x v , ⟨ const-env-ok , ⊑-refl ⟩ ⟩
      where
      const-env-ok : δ `⊢ σ ↓ const-env x v
      const-env-ok y with x var≟ y
      ... | yes x≡y rewrite sym x≡y | nth-const-env {Γ}{x}{v} = ℰLδv
      ... | no x≢y rewrite diff-nth-const-env {Γ}{x}{y}{v} x≢y = δ⊢σ↓⊥ y

    subst-reflect {Γ}{Δ}{δ}{lam ⦅ bind N nil ⦆} {L} {σ} {v} ℰLδv L≡σM δ⊢σ↓⊥
        rewrite L≡σM =
        subst-reflect-lambda {N = N}{v = v} IH ℰLδv refl δ⊢σ↓⊥ 
        where
        IH : ∀ {u w : Value}
           → SubRef (suc Γ) (suc Δ) (δ `, u) N (⟪ exts σ ⟫ N)  (exts σ) w
        IH {u}{w} ℰLδv L≡σM δu⊢eσ↓⊥ =
          subst-reflect {δ = δ `, u} {M = N} {L = ⟪ exts σ ⟫ N}
               {σ = exts σ} {w} ℰLδv L≡σM δu⊢eσ↓⊥
               
    subst-reflect {Γ}{Δ}{δ}{app ⦅ cons L (cons M nil) ⦆}{_}{σ}{v} ℰσL●ℰσMδv
                  L≡σM δ⊢σ↓⊥ rewrite L≡σM =
        subst-reflect-app {L = L}{M} IH1 IH2 ℰσL●ℰσMδv refl δ⊢σ↓⊥
        where
        IH1 : ∀ {v : Value} → SubRef Γ Δ δ L (⟪ σ ⟫ L) σ v
        IH1 {v} ℰLδv L≡σM δ⊢σ↓⊥ =
          subst-reflect {δ = δ} {M = L} {L = ⟪ σ ⟫ L}
               {σ = σ} {v} ℰLδv L≡σM δ⊢σ↓⊥
        IH2 : ∀ {v : Value} → SubRef Γ Δ δ M (⟪ σ ⟫ M) σ v
        IH2 {v} ℰLδv L≡σM δ⊢σ↓⊥ =
          subst-reflect {δ = δ} {M = M} {L = ⟪ σ ⟫ M}
               {σ = σ} {v} ℰLδv L≡σM δ⊢σ↓⊥

    subst-zero-reflect : ∀ {Δ} {δ : Env Δ} {γ : Env (suc Δ)} {M : Term Δ}
      → δ `⊢ subst-zero M ↓ γ
        ----------------------------------------
      → Σ[ w ∈ Value ] γ `⊑ (δ `, w) × ℰ M δ w
    subst-zero-reflect {δ = δ} {γ = γ} δσγ = ⟨ last γ , ⟨ lemma , δσγ Z ⟩ ⟩   
      where
      lemma : γ `⊑ (δ `, last γ)
      lemma Z  =  ⊑-refl
      lemma (S x) = δσγ (S x)

    subst-zero-⊥ : ∀{Γ}{γ : Env Γ}{M : Term Γ}
                 → ℰ M γ ⊥
                 → γ `⊢ subst-zero M ↓ `⊥
    subst-zero-⊥ ℰMγ⊥ Z = ℰMγ⊥
    subst-zero-⊥ ℰMγ⊥ (S x) = ⊑-⊥

    substitution-reflect : ∀ {Δ} {δ : Env Δ} {N : Term (suc Δ)} {M : Term Δ} {v}
      → ℰ (N [ M ]) δ v  → ℰ M δ ⊥
        ------------------------------------------------
      → Σ[ w ∈ Value ] ℰ M δ w  ×  ℰ N (δ `, w) v
    substitution-reflect{N = N}{M = M} ℰNMδv ℰMδ⊥
         with subst-reflect {M = N} ℰNMδv refl (subst-zero-⊥ ℰMδ⊥)
    ...  | ⟨ γ , ⟨ δσγ , γNv ⟩ ⟩
         with subst-zero-reflect δσγ
    ...  | ⟨ w , ⟨ γ⊑δw , δMw ⟩ ⟩ =
           ⟨ w , ⟨ δMw , ⊑-env {M = N} γNv γ⊑δw ⟩ ⟩


open import ValueBCD
open DomainAux domain
  
module LambdaValueBCD
  (_●_ : ∀{Γ} → Denotation Γ → Denotation Γ → Denotation Γ)
  (MB : OrderingAux.LambdaModelBasics domain ordering _●_ ℱ)
  where
  open OrderingAux domain ordering
  open RenamePreserveReflect domain ordering _●_ ℱ MB
    using (rename-inc-reflect; EnvExt⊑; ⊑-env)
  open Filter domain ordering _●_ ℱ MB using (subst-⊔; δu⊢extσ⊥; ℰ-⊑)
  open DenotAux domain ordering _●_ ℱ MB
  open LambdaDenot domain ordering _●_ ℱ
  open LambdaModelBasics MB

  SubRef : (Γ : ℕ) → (Δ : ℕ) → Env Δ → Term Γ → Term Δ
         → Subst Γ Δ → Value → Set
  SubRef Γ Δ δ M L σ v = ℰ L δ v → L ≡ ⟪ σ ⟫ M → δ `⊢ σ ↓ `⊥
                         → Σ[ γ ∈ Env Γ ] δ `⊢ σ ↓ γ  ×  ℰ M γ v

  subst-reflect-lambda : ∀{Γ Δ} {δ : Env Δ} {N : Term (suc Γ)}
                      {σ : Subst Γ Δ} {v}
          → (∀{u w}
             → SubRef (suc Γ) (suc Δ) (δ `, u) N (⟪ exts σ ⟫ N)  (exts σ) w)
          → SubRef Γ Δ δ (ƛ N) (⟪ σ ⟫ (ƛ N)) σ v
  subst-reflect-lambda {Γ}{N = N}{v = ⊥} IH _ L≡ δ⊢σ↓⊥ =
      ⟨ `⊥ , ⟨ δ⊢σ↓⊥ , ƛ-⊥ {Γ}{N}{`⊥} ⟩ ⟩
  subst-reflect-lambda {Γ}{Δ}{δ}{N = N}{σ} {u ↦ w} IH ℰLδv L≡ δ⊢σ↓⊥
      with IH {u}{w} ℰLδv refl (δu⊢extσ⊥ δ⊢σ↓⊥)
  ... | ⟨ γ , ⟨ subst-γ , m ⟩ ⟩ =
        ⟨ init γ ,
        ⟨ (λ x → rename-inc-reflect {M = σ x} (subst-γ (S x))) ,
          (let m' = split{M = N} m in
           EnvExt⊑{M = N} m' (subst-γ Z)) ⟩ ⟩
  subst-reflect-lambda {Γ}{N = N}{σ}{u ⊔ w} IH ⟨ aa , bb ⟩ L≡ δ⊢σ↓⊥
      with subst-reflect-lambda{N = N}{σ}{u} IH aa L≡ δ⊢σ↓⊥
         | subst-reflect-lambda{N = N}{σ}{w} IH bb L≡ δ⊢σ↓⊥
  ... | ⟨ δ₁ , ⟨ subst-δ₁ , m1 ⟩ ⟩ | ⟨ δ₂ , ⟨ subst-δ₂ , m2 ⟩ ⟩ =
     ⟨ δ₁ `⊔ δ₂ ,
     ⟨ subst-⊔ {σ = σ} subst-δ₁ subst-δ₂ ,
     ⟨ ⊑-env{Γ}{δ₁}{δ₁ `⊔ δ₂}{lam ⦅ bind N nil ⦆}{u}m1(EnvConjR1⊑ δ₁ δ₂) ,
       ⊑-env{Γ}{δ₂}{δ₁ `⊔ δ₂}{lam ⦅ bind N nil ⦆}{w}m2(EnvConjR2⊑ δ₁ δ₂) ⟩
       ⟩ ⟩


module CallByName where

  open import ModelCallByName
  open OrderingAux domain ordering
  open LambdaDenot domain ordering _●_ ℱ
  open RenamePreserveReflect domain ordering _●_ ℱ model_basics
    using (⊑-env)
  open Filter domain ordering _●_ ℱ model_basics using (subst-⊔; ℰ-⊑)

  SubRef : (Γ : ℕ) → (Δ : ℕ) → Env Δ → Term Γ → Term Δ
         → Subst Γ Δ → Value → Set
  SubRef Γ Δ δ M L σ v = ℰ L δ v → L ≡ ⟪ σ ⟫ M → δ `⊢ σ ↓ `⊥
                         → Σ[ γ ∈ Env Γ ] δ `⊢ σ ↓ γ  ×  ℰ M γ v
                         
  subst-reflect-app : ∀ {Γ Δ} {δ : Env Δ} {L : Term Γ} {M : Term Γ} 
                      {σ : Subst Γ Δ} {v}
          → (∀ {v : Value} → SubRef Γ Δ δ L (⟪ σ ⟫ L) σ v)
          → (∀ {v : Value} → SubRef Γ Δ δ M (⟪ σ ⟫ M) σ v)
          → SubRef Γ Δ δ (L · M) (⟪ σ ⟫ (L · M)) σ v
  subst-reflect-app {Γ}{Δ}{δ}{L}{M}{σ}{v} IH1 IH2 ℰσL●ℰσMδv L≡σM δ⊢σ↓⊥
      rewrite L≡σM 
      with ℰσL●ℰσMδv
  ... | inj₁ v⊑⊥ = 
        ⟨ `⊥ , ⟨ δ⊢σ↓⊥ , ℰ-⊑{M = L · M} (ℰ-⊥{M = L · M}) v⊑⊥  ⟩ ⟩
  ... | inj₂ ⟨ u , ⟨ ℰσLδu↦v , ℰσMδu ⟩ ⟩
      with IH1 ℰσLδu↦v refl δ⊢σ↓⊥
         | IH2 ℰσMδu refl δ⊢σ↓⊥
  ... | ⟨ δ₁  , ⟨ subst-δ₁ , ℰLδ₁u↦v ⟩ ⟩
      | ⟨ δ₂  , ⟨ subst-δ₂ , ℰMδ₂u ⟩ ⟩ =
        ⟨ (δ₁ `⊔ δ₂) ,
        ⟨ (subst-⊔ {γ₁ = δ₁}{γ₂ = δ₂}{σ = σ} subst-δ₁ subst-δ₂) ,
          inj₂ ⟨ u , ⟨ ℰLδ₁⊔δ₂u↦v , ℰMδ₁⊔δ₂u ⟩ ⟩ ⟩ ⟩
        where
        ℰLδ₁⊔δ₂u↦v : ℰ L (λ z → (δ₁ `⊔ δ₂) z) (u ↦ v)
        ℰLδ₁⊔δ₂u↦v = ⊑-env{M = L} ℰLδ₁u↦v (EnvConjR1⊑ δ₁ δ₂)

        ℰMδ₁⊔δ₂u  : ℰ M (λ z → (δ₁ `⊔ δ₂) z) u
        ℰMδ₁⊔δ₂u = ⊑-env{M = M} ℰMδ₂u (EnvConjR2⊑ δ₁ δ₂)

  open SubstReflect domain ordering _●_ ℱ model_basics
  open LambdaValueBCD _●_ model_basics
  
  open LambdaApp
          (λ {Γ}{Δ}{δ}{N}{σ}{v} IH a b c →
             subst-reflect-lambda{Γ}{Δ}{δ}{N}{σ}{v} IH a b c)
          (λ {Γ}{Δ}{δ}{L}{M}{σ}{v} IH1 IH2 a b c →
             subst-reflect-app{Γ}{Δ}{δ}{L}{M}{σ}{v} IH1 IH2 a b c) public

module CallByValue where

  open import ModelCallByValue
  open OrderingAux domain ordering
  open LambdaDenot domain ordering _●_ ℱ
  open RenamePreserveReflect domain ordering _●_ ℱ model_basics
    using (⊑-env)
  open Filter domain ordering _●_ ℱ model_basics using (subst-⊔; ℰ-⊑)

  SubRef : (Γ : ℕ) → (Δ : ℕ) → Env Δ → Term Γ → Term Δ
         → Subst Γ Δ → Value → Set
  SubRef Γ Δ δ M L σ v = ℰ L δ v → L ≡ ⟪ σ ⟫ M → δ `⊢ σ ↓ `⊥
                         → Σ[ γ ∈ Env Γ ] δ `⊢ σ ↓ γ  ×  ℰ M γ v

  subst-reflect-app : ∀ {Γ Δ} {δ : Env Δ} {L : Term Γ} {M : Term Γ} 
                      {σ : Subst Γ Δ} {v}
          → (∀ {v : Value} → SubRef Γ Δ δ L (⟪ σ ⟫ L) σ v)
          → (∀ {v : Value} → SubRef Γ Δ δ M (⟪ σ ⟫ M) σ v)
          → SubRef Γ Δ δ (L · M) (⟪ σ ⟫ (L · M)) σ v
  subst-reflect-app {Γ}{Δ}{δ}{L}{M}{σ}{v} IH1 IH2 ℰσL●ℰσMδv L≡σM δ⊢σ↓⊥
      rewrite L≡σM 
      with ℰσL●ℰσMδv
  ... | ⟨ u , ⟨ ℰσLδu↦v , ℰσMδu ⟩ ⟩
      with IH1 ℰσLδu↦v refl δ⊢σ↓⊥
         | IH2 ℰσMδu refl δ⊢σ↓⊥
  ... | ⟨ δ₁  , ⟨ subst-δ₁ , ℰLδ₁u↦v ⟩ ⟩
      | ⟨ δ₂  , ⟨ subst-δ₂ , ℰMδ₂u ⟩ ⟩ =
        ⟨ (δ₁ `⊔ δ₂) ,
        ⟨ (subst-⊔ {γ₁ = δ₁}{γ₂ = δ₂}{σ = σ} subst-δ₁ subst-δ₂) ,
          ⟨ u , ⟨ ℰLδ₁⊔δ₂u↦v , ℰMδ₁⊔δ₂u ⟩ ⟩ ⟩ ⟩
        where
        ℰLδ₁⊔δ₂u↦v : ℰ L (λ z → (δ₁ `⊔ δ₂) z) (u ↦ v)
        ℰLδ₁⊔δ₂u↦v = ⊑-env{M = L} ℰLδ₁u↦v (EnvConjR1⊑ δ₁ δ₂)

        ℰMδ₁⊔δ₂u  : ℰ M (λ z → (δ₁ `⊔ δ₂) z) u
        ℰMδ₁⊔δ₂u = ⊑-env{M = M} ℰMδ₂u (EnvConjR2⊑ δ₁ δ₂)

  open SubstReflect domain ordering _●_ ℱ model_basics
  open LambdaValueBCD _●_ model_basics
  
  open LambdaApp
          (λ {Γ}{Δ}{δ}{N}{σ}{v} IH a b c →
             subst-reflect-lambda{Γ}{Δ}{δ}{N}{σ}{v} IH a b c)
          (λ {Γ}{Δ}{δ}{L}{M}{σ}{v} IH1 IH2 a b c →
             subst-reflect-app{Γ}{Δ}{δ}{L}{M}{σ}{v} IH1 IH2 a b c)

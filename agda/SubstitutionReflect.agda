open import Variables
open import Primitives
open import Structures
import RenamePreserveReflect
import Filter
import ValueStructAux
import OrderingAux
import CurryApplyStruct

open import Data.Bool
open import Data.Empty using (⊥-elim) renaming (⊥ to Bot)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Function using (_∘_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; sym; cong; cong₂; cong-app; subst)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Relation.Nullary using (¬_; Dec; yes; no)


{- to do: 

   There's a bunch of duplication in these proofs that should
   be eliminated... need a way to abstract over Lambda versus
   ISWIM Terms in proofs that don't actually touch the terms,
   but need to refer to them.

-}


module SubstitutionReflect where

module ForLambdaModel
  (D : ValueStruct)
  (V : ValueOrdering D)
  (_●_ : ∀{Γ} → ValueStructAux.Denotation D Γ
       → ValueStructAux.Denotation D Γ → ValueStructAux.Denotation D Γ)
  (ℱ : ∀{Γ} → ValueStructAux.Denotation D (suc Γ)
     → ValueStructAux.Denotation D Γ)
  (MB : CurryApplyStruct.CurryApplyStruct D V _●_ ℱ)
  where
  
  open ValueStruct D
  open OrderingAux D V
  open ValueStructAux D
  open ValueOrdering V

  module ForLambda where

    open import Lambda
    open import LambdaDenot D V _●_ ℱ
    open RenamePreserveReflect.ForLambda D V _●_ ℱ MB using (⊑-env)

    SubRef : (Γ : ℕ) → (Δ : ℕ) → Env Δ → Term Γ → Term Δ
           → Subst Γ Δ → Value → Set
    SubRef Γ Δ δ M L σ v = ℰ L δ v → L ≡ ⟪ σ ⟫ M → δ `⊢ σ ↓ `⊥
                           → Σ[ γ ∈ Env Γ ] δ `⊢ σ ↓ γ  ×  ℰ M γ v

    subst-reflect-var : ∀ {Γ Δ} {δ : Env Δ} {x : Var Γ} {σ : Subst Γ Δ} {v}
            → SubRef Γ Δ δ (` x) (⟪ σ ⟫ (` x)) σ v
    subst-reflect-var {Γ}{Δ}{δ}{x}{σ}{v} ℰLδv L≡σM δ⊢σ↓⊥ 
        rewrite L≡σM | sym (nth-const-env {Γ}{x}{v}) =
          ⟨ const-env x v , ⟨ const-env-ok , ⊑-refl ⟩ ⟩
        where
        const-env-ok : δ `⊢ σ ↓ const-env x v
        const-env-ok y with x var≟ y
        ... | yes x≡y rewrite sym x≡y | nth-const-env {Γ}{x}{v} = ℰLδv
        ... | no x≢y rewrite diff-nth-const-env {Γ}{x}{y}{v} x≢y = δ⊢σ↓⊥ y
    
    module SubstReflect
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
      subst-reflect {Γ}{Δ}{δ}{` x}{L}{σ}{v} ℰLδv L≡σM δ⊢σ↓⊥ rewrite L≡σM =
        subst-reflect-var {x = x}{σ} ℰLδv refl δ⊢σ↓⊥
      subst-reflect {Γ}{Δ}{δ}{lam ⦅ bind N nil ⦆} {L} {σ} {v} ℰLδv L≡σM δ⊢σ↓⊥
          rewrite L≡σM =
          subst-reflect-lambda {N = N}{v = v} IH ℰLδv refl δ⊢σ↓⊥
          where
          IH = λ {u}{w} → subst-reflect {δ = δ `, u} {M = N}
                              {L = ⟪ exts σ ⟫ N} {σ = exts σ} {v = w}
      subst-reflect {Γ}{Δ}{δ}{app ⦅ cons L (cons M nil) ⦆}{_}{σ}{v} ℰσL●ℰσMδv
                    L≡σM δ⊢σ↓⊥ rewrite L≡σM =
          subst-reflect-app {L = L}{M} IH1 IH2 ℰσL●ℰσMδv refl δ⊢σ↓⊥
          where
          IH1 = λ {v} → subst-reflect {δ = δ} {M = L} {L = ⟪ σ ⟫ L} {σ = σ} {v}
          IH2 = λ {v} → subst-reflect {δ = δ} {M = M} {L = ⟪ σ ⟫ M} {σ = σ} {v}


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


      substitution-reflect : ∀ {Δ}{δ : Env Δ}{N : Term (suc Δ)} {M : Term Δ} {v}
        → ℰ (N [ M ]) δ v  → ℰ M δ ⊥
          ------------------------------------------------
        → Σ[ w ∈ Value ] ℰ M δ w  ×  ℰ N (δ `, w) v
      substitution-reflect{N = N}{M = M} ℰNMδv ℰMδ⊥
           with subst-reflect {M = N} ℰNMδv refl (subst-zero-⊥ ℰMδ⊥)
      ...  | ⟨ γ , ⟨ δσγ , γNv ⟩ ⟩
           with subst-zero-reflect δσγ
      ...  | ⟨ w , ⟨ γ⊑δw , δMw ⟩ ⟩ =
             ⟨ w , ⟨ δMw , ⊑-env {M = N} γNv γ⊑δw ⟩ ⟩

  module ForISWIM 
    (℘ : ∀{P : Prim} → rep P → ValueStruct.Value D → Set)
    where

    open import ISWIM
    open import ISWIMDenot D V _●_ ℱ (λ {P} k v → ℘ {P} k v)
    open RenamePreserveReflect.ForISWIM D V _●_ ℱ MB (λ {P} k v → ℘ {P} k v)
      using (⊑-env)

    SubRef : (Γ : ℕ) → (Δ : ℕ) → Env Δ → Term Γ → Term Δ
           → Subst Γ Δ → Value → Set
    SubRef Γ Δ δ M L σ v = ℰ L δ v → L ≡ ⟪ σ ⟫ M → δ `⊢ σ ↓ `⊥
                           → Σ[ γ ∈ Env Γ ] δ `⊢ σ ↓ γ  ×  ℰ M γ v

    subst-reflect-var : ∀ {Γ Δ} {δ : Env Δ} {x : Var Γ} {σ : Subst Γ Δ} {v}
            → SubRef Γ Δ δ (` x) (⟪ σ ⟫ (` x)) σ v
    subst-reflect-var {Γ}{Δ}{δ}{x}{σ}{v} ℰLδv L≡σM δ⊢σ↓⊥ 
        rewrite L≡σM | sym (nth-const-env {Γ}{x}{v}) =
          ⟨ const-env x v , ⟨ const-env-ok , ⊑-refl ⟩ ⟩
        where
        const-env-ok : δ `⊢ σ ↓ const-env x v
        const-env-ok y with x var≟ y
        ... | yes x≡y rewrite sym x≡y | nth-const-env {Γ}{x}{v} = ℰLδv
        ... | no x≢y rewrite diff-nth-const-env {Γ}{x}{y}{v} x≢y = δ⊢σ↓⊥ y
    
    module SubstReflect
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
      subst-reflect {M = lit {P} k ⦅ nil ⦆} ℰLδv L≡σM δ⊢σ↓⊥ rewrite L≡σM =
          ⟨ `⊥ , ⟨ δ⊢σ↓⊥ , ℰLδv ⟩ ⟩
      subst-reflect {Γ}{Δ}{δ}{` x}{L}{σ}{v} ℰLδv L≡σM δ⊢σ↓⊥ rewrite L≡σM =
          subst-reflect-var {x = x}{σ} ℰLδv refl δ⊢σ↓⊥
      subst-reflect {Γ}{Δ}{δ}{lam ⦅ bind N nil ⦆} {L} {σ} {v} ℰLδv L≡σM δ⊢σ↓⊥
          rewrite L≡σM =
          subst-reflect-lambda {N = N}{v = v} IH ℰLδv refl δ⊢σ↓⊥
          where
          IH = λ {u}{w} → subst-reflect {δ = δ `, u} {M = N}
                              {L = ⟪ exts σ ⟫ N} {σ = exts σ} {v = w}
      subst-reflect {Γ}{Δ}{δ}{app ⦅ cons L (cons M nil) ⦆}{_}{σ}{v} ℰσL●ℰσMδv
                    L≡σM δ⊢σ↓⊥ rewrite L≡σM =
          subst-reflect-app {L = L}{M} IH1 IH2 ℰσL●ℰσMδv refl δ⊢σ↓⊥
          where
          IH1 = λ {v} → subst-reflect {δ = δ} {M = L} {L = ⟪ σ ⟫ L} {σ = σ} {v}
          IH2 = λ {v} → subst-reflect {δ = δ} {M = M} {L = ⟪ σ ⟫ M} {σ = σ} {v}


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


      substitution-reflect : ∀ {Δ}{δ : Env Δ}{N : Term (suc Δ)} {M : Term Δ} {v}
        → ℰ (N [ M ]) δ v  → ℰ M δ ⊥
          ------------------------------------------------
        → Σ[ w ∈ Value ] ℰ M δ w  ×  ℰ N (δ `, w) v
      substitution-reflect{N = N}{M = M} ℰNMδv ℰMδ⊥
           with subst-reflect {M = N} ℰNMδv refl (subst-zero-⊥ ℰMδ⊥)
      ...  | ⟨ γ , ⟨ δσγ , γNv ⟩ ⟩
           with subst-zero-reflect δσγ
      ...  | ⟨ w , ⟨ γ⊑δw , δMw ⟩ ⟩ =
             ⟨ w , ⟨ δMw , ⊑-env {M = N} γNv γ⊑δw ⟩ ⟩


module SubstReflectAppCBV
{-
  (D : ValueStruct)
  (V : ValueOrdering D)
  (ℱ : ∀{Γ} → ValueStructAux.Denotation D (suc Γ) → ValueStructAux.Denotation D Γ)
  (MC : OrderingAux.ModelCurry D V ℱ)
-}
  where

{-
  open import ModelCallByValue D V ℱ MC
  open ValueStruct D
  open ValueOrdering V
  open ValueStructAux D
  open OrderingAux D V
-}

{-
  module ForLambda (MB : LambdaModelBasics _●_ ℱ) where
-}
  module ForLambda where

    open import ValueBCD
    open ValueStructAux domain
    open OrderingAux domain ordering
    open import ModelCallByValue domain ordering ℱ model_curry

    open import Lambda
    open LambdaDenot domain ordering _●_ ℱ
    open RenamePreserveReflect.ForLambda domain ordering _●_ ℱ model_basics
      using (⊑-env)
    open Filter.ForLambda domain ordering _●_ ℱ model_basics using (subst-⊔; ℰ-⊑)

{-
    open import Lambda
    open LambdaDenot D V _●_ ℱ
    open RenamePreserveReflect.ForLambda D V _●_ ℱ MB
      using (⊑-env)
    open Filter.ForLambda D V _●_ ℱ MB using (subst-⊔; ℰ-⊑)
-}

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

  module ForISWIM
{-
    (MB : LambdaModelBasics _●_ ℱ)
    (℘ : ∀{P : Prim} → rep P → ValueStruct.Value D → Set)
    (℘-⊔ : ∀{P : Prim } {D : rep P} {u v : Value}
          → ℘ {P} D u → ℘ {P} D v → ℘ {P} D (u ⊔ v))
    (℘-⊑ : ∀{P : Prim} {D : rep P} {v w : Value}
          → ℘ {P} D v → w ⊑ v → ℘ {P} D w)
-}
    where

    open import ISWIM
    open import ValueBCDConst 
    open import ModelISWIM
{-
    open ISWIMDenot D V _●_ ℱ (λ {P} k v → ℘ {P} k v)
    open RenamePreserveReflect.ForISWIM D V _●_ ℱ MB (λ {P} k v → ℘ {P} k v)
        using (⊑-env)
    open Filter.ForISWIM D V _●_ ℱ MB (λ {P} k v → ℘ {P} k v) ℘-⊔ ℘-⊑
        using (subst-⊔; ℰ-⊑)
-}
    open ValueStructAux domain
    open OrderingAux domain ordering
    open ISWIMDenot domain ordering _●_ ℱ (λ {P} k v → ℘ {P} k v)
    open RenamePreserveReflect.ForISWIM domain ordering _●_ ℱ model_basics (λ {P} k v → ℘ {P} k v)
        using (⊑-env)
    open Filter.ForISWIM domain ordering _●_ ℱ model_basics
        (λ {P} k v → ℘ {P} k v)
        (λ {P} {k} {u} {v} → ℘-⊔ {P} {k} {u} {v})
        ℘-⊑
        using (subst-⊔; ℰ-⊑)

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


module SubstReflectLambdaBCD where
  open import ValueBCD
  open ValueStructAux domain

  module Inner
    (_●_ : ∀{Γ} → Denotation Γ → Denotation Γ → Denotation Γ)
    (MB : OrderingAux.LambdaModelBasics domain ordering _●_ ℱ)
    where
    
    open OrderingAux domain ordering
    open RenamePreserveReflect.ForLambda domain ordering _●_ ℱ MB
       using (rename-inc-reflect; EnvExt⊑; ⊑-env; δu⊢extσ⊥)
    open Filter.ForLambda domain ordering _●_ ℱ MB
       using (subst-⊔; ℰ-⊑)
    open DenotAux domain ordering _●_ ℱ MB
    open LambdaDenot domain ordering _●_ ℱ
    open LambdaModelBasics MB
    open import Lambda

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


module SubstReflectLambdaBCDConst where

  open import ValueBCDConst
  open ValueStructAux domain
  open OrderingAux domain ordering

  module Inner
    (_●_ : ∀{Γ} → Denotation Γ → Denotation Γ → Denotation Γ)
    (MB : OrderingAux.LambdaModelBasics domain ordering _●_ ℱ)
    (℘ : ∀{P : Prim} → rep P → Value → Set)
    (℘-⊔ : ∀{P : Prim } {D : rep P} {u v : Value}
          → ℘ {P} D u → ℘ {P} D v → ℘ {P} D (u ⊔ v))
    (℘-⊑ : ∀{P : Prim} {D : rep P} {v w : Value}
          → ℘ {P} D v → w ⊑ v → ℘ {P} D w)
    where

    open import ISWIM    
    open ISWIMDenot domain ordering _●_ ℱ (λ {P} k v → ℘ {P} k v)
    open ISWIMDenotAux domain ordering _●_ ℱ MB (λ {P} k v → ℘ {P} k v)
    open RenamePreserveReflect.ForISWIM
      domain ordering _●_ ℱ MB (λ {P} k v → ℘ {P} k v)
      using (rename-inc-reflect; EnvExt⊑; ⊑-env; δu⊢extσ⊥)
    open Filter.ForISWIM domain ordering _●_ ℱ MB
      (λ {P} k v → ℘ {P} k v) ℘-⊔ ℘-⊑
      using (subst-⊔; ℰ-⊑)

    SubRef : (Γ : ℕ) → (Δ : ℕ) → Env Δ → Term Γ → Term Δ
           → Subst Γ Δ → Value → Set
    SubRef Γ Δ δ M L σ v = ℰ L δ v → L ≡ ⟪ σ ⟫ M → δ `⊢ σ ↓ `⊥
                           → Σ[ γ ∈ Env Γ ] δ `⊢ σ ↓ γ  ×  ℰ M γ v

    subst-reflect-lambda : ∀{Γ Δ} {δ : Env Δ} {N : Term (suc Γ)}
                        {σ : Subst Γ Δ} {v}
            → (∀{u w}
               → SubRef (suc Γ) (suc Δ) (δ `, u) N (⟪ exts σ ⟫ N)  (exts σ) w)
            → SubRef Γ Δ δ (ƛ N) (⟪ σ ⟫ (ƛ N)) σ v
    subst-reflect-lambda {Γ}{N = N}{v = const {B} k} IH () L≡ δ⊢σ↓⊥
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

  open import ValueBCD
  open ValueStructAux domain
  open import ModelCallByName
  open OrderingAux domain ordering
  open LambdaDenot domain ordering _●_ ℱ
  open RenamePreserveReflect.ForLambda domain ordering _●_ ℱ model_basics
    using (⊑-env)
  open Filter.ForLambda domain ordering _●_ ℱ model_basics using (subst-⊔; ℰ-⊑)
  open import Lambda

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

  open ForLambdaModel domain ordering _●_ ℱ model_basics
  open SubstReflectLambdaBCD.Inner _●_ model_basics
  
  open ForLambda.SubstReflect
          (λ {Γ}{Δ}{δ}{N}{σ}{v} IH a b c →
             subst-reflect-lambda{Γ}{Δ}{δ}{N}{σ}{v} IH a b c)
          (λ {Γ}{Δ}{δ}{L}{M}{σ}{v} IH1 IH2 a b c →
             subst-reflect-app{Γ}{Δ}{δ}{L}{M}{σ}{v} IH1 IH2 a b c) public


module CallByValue where

  open import ValueBCD
  open ValueStructAux domain
  open import ModelCallByValue domain ordering ℱ model_curry
{-
  open SubstReflectAppCBV.ForLambda domain ordering ℱ model_curry model_basics
-}
  open SubstReflectAppCBV.ForLambda
  open ForLambdaModel domain ordering _●_ ℱ model_basics
  open SubstReflectLambdaBCD.Inner _●_ model_basics
  
  open ForLambda.SubstReflect
          (λ {Γ}{Δ}{δ}{N}{σ}{v} IH a b c →
             subst-reflect-lambda{Γ}{Δ}{δ}{N}{σ}{v} IH a b c)
          (λ {Γ}{Δ}{δ}{L}{M}{σ}{v} IH1 IH2 a b c →
             subst-reflect-app{Γ}{Δ}{δ}{L}{M}{σ}{v} IH1 IH2 a b c) public


module ISWIM where

  open import ValueBCDConst
  open import ModelISWIM

  open SubstReflectAppCBV.ForISWIM
  {-
  open SubstReflectAppCBV.ForISWIM domain ordering ℱ model_curry model_basics
     (λ {P} k v → ℘ {P} k v)
     (λ {P} {k} {u} {v} → ℘-⊔ {P} {k} {u} {v})
     ℘-⊑
-}

  open ForLambdaModel domain ordering _●_ ℱ model_basics
  open SubstReflectLambdaBCDConst.Inner _●_ model_basics 
       (λ {P} k v → ℘ {P} k v)
       (λ {P} {k} {u} {v} → ℘-⊔ {P} {k} {u} {v})
       ℘-⊑
       
  open ForISWIM.SubstReflect
          (λ {P} k v → ℘ {P} k v)
          (λ {Γ}{Δ}{δ}{N}{σ}{v} IH a b c →
             subst-reflect-lambda{Γ}{Δ}{δ}{N}{σ}{v} IH a b c)
          (λ {Γ}{Δ}{δ}{L}{M}{σ}{v} IH1 IH2 a b c →
             subst-reflect-app{Γ}{Δ}{δ}{L}{M}{σ}{v} IH1 IH2 a b c) public

{-# OPTIONS --rewriting #-}

open import Primitives
open import Structures
import RenamePreserveReflect
import Filter
import ValueStructAux
import OrderingAux
import CurryApplyStruct
import RenamePreserveReflect

open import Data.Bool using ()
open import Data.Empty using (⊥-elim) renaming (⊥ to Bot)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _≟_)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Function using (_∘_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; sym; cong; cong₂; cong-app; subst)
open Eq.≡-Reasoning
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
  (C : Consistent D V)
  (_●_ : ValueStructAux.Denotation D
       → ValueStructAux.Denotation D → ValueStructAux.Denotation D)
  (ℱ : ValueStructAux.Denotation D → ValueStructAux.Denotation D)
  (MB : CurryApplyStruct.CurryApplyStruct D V C _●_ ℱ)
  where

  open ValueStruct D
  open OrderingAux D V
  open ValueStructAux D
  open ValueOrdering V
  open Consistent C
  open import ConsistentAux D V C

  module ForLambda where

    open import Lambda
    open ASTMod using (Subst; ⟪_⟫; exts; subst-zero)
    open import LambdaDenot D V _●_ ℱ
    open RenamePreserveReflect.ForLambda D V C _●_ ℱ MB using (⊑-env)

    SubRef : Env → Term → Term → Subst → Value → Set
    SubRef δ M L σ v = WFEnv δ → wf v → ℰ L δ v → L ≡ ⟪ σ ⟫ M → δ `⊢ σ ↓ `⊥
                           → Σ[ γ ∈ Env ] WFEnv γ × δ `⊢ σ ↓ γ  ×  ℰ M γ v

    subst-reflect-var : ∀ {δ : Env} {x : Var} {σ : Subst} {v}
            → SubRef δ (` x) (⟪ σ ⟫ (` x)) σ v
    subst-reflect-var {δ}{x}{σ}{v} wfδ wfv ℰLδv refl δ⊢σ↓⊥ =
          ⟨ const-env x v , ⟨ (wf-const-env {x} {v} wfv)
          , ⟨ const-env-ok , subst (v ⊑_) (sym (nth-const-env {x} {v})) ⊑-refl ⟩ ⟩ ⟩
        where
        const-env-ok : δ `⊢ σ ↓ const-env x v
        const-env-ok y with x ≟ y
        ... | yes x≡y rewrite sym x≡y | nth-const-env {x}{v} = ℰLδv
        ... | no x≢y rewrite diff-nth-const-env {x}{y}{v} x≢y = δ⊢σ↓⊥ y
        const-env-wf : (y : Var) → wf (const-env x v y)
        const-env-wf y
            with x ≟ x
        ... | yes refl = wf-const-env {x}{v} wfv y
        ... | no neq = ⊥-elim (neq refl)


    module SubstReflect
      (subst-reflect-lambda : ∀ {δ : Env} {N : Term} {σ : Subst} {v}
            → (∀{u w}
               → SubRef (δ `, u) N (⟪ exts σ ⟫ N)  (exts σ) w)
            → SubRef δ (ƛ N) (⟪ σ ⟫ (ƛ N)) σ v)
      (subst-reflect-app : ∀ {δ : Env} {L : Term} {M : Term}
                        {σ : Subst} {v}
            → (∀ {v : Value} → SubRef δ L (⟪ σ ⟫ L) σ v)
            → (∀ {v : Value} → SubRef δ M (⟪ σ ⟫ M) σ v)
            → SubRef δ (L · M) (⟪ σ ⟫ (L · M)) σ v)
      where

      subst-reflect : ∀ {δ : Env} {M : Term} {L : Term}
                        {σ : Subst} {v}
                    → SubRef δ M L σ v
      subst-reflect {δ}{` x}{L}{σ}{v} wfδ wfv ℰLδv L≡σM δ⊢σ↓⊥ rewrite L≡σM =
        subst-reflect-var {x = x}{σ} wfδ wfv ℰLδv refl δ⊢σ↓⊥
      subst-reflect {δ}{lam ⦅ cons (bind (ast N)) nil ⦆} {L} {σ} {v} wfδ wfv ℰLδv L≡σM δ⊢σ↓⊥
          rewrite L≡σM =
          subst-reflect-lambda {N = N}{v = v} IH wfδ wfv ℰLδv refl δ⊢σ↓⊥
          where
          IH = λ {u}{w} → subst-reflect {δ = δ `, u} {M = N}
                              {L = ⟪ exts σ ⟫ N} {σ = exts σ} {v = w}
      subst-reflect {δ}{app ⦅ cons (ast L) (cons (ast M) nil) ⦆}{_}{σ}{v} wfδ wfv ℰσL●ℰσMδv
                    L≡σM δ⊢σ↓⊥ rewrite L≡σM =
          subst-reflect-app {L = L}{M}{σ} IH1 IH2 wfδ wfv ℰσL●ℰσMδv refl δ⊢σ↓⊥
          where
          IH1 = λ {v} → subst-reflect {δ = δ} {M = L} {L = ⟪ σ ⟫ L} {σ = σ} {v}
          IH2 = λ {v} → subst-reflect {δ = δ} {M = M} {L = ⟪ σ ⟫ M} {σ = σ} {v}


      subst-zero-reflect : ∀ {δ : Env} {γ : Env} {M : Term}
        → δ `⊢ subst-zero M ↓ γ
          ----------------------------------------
        → Σ[ w ∈ Value ] γ `⊑ (δ `, w) × ℰ M δ w
      subst-zero-reflect {δ = δ} {γ = γ} δσγ = ⟨ last γ , ⟨ lemma , δσγ 0 ⟩ ⟩
        where
        lemma : γ `⊑ (δ `, last γ)
        lemma 0  =  ⊑-refl
        lemma (suc x) = δσγ (suc x)


      subst-zero-⊥ : ∀{γ : Env}{M : Term}
                   → ℰ M γ ⊥
                   → γ `⊢ subst-zero M ↓ `⊥
      subst-zero-⊥ ℰMγ⊥ 0 = ℰMγ⊥
      subst-zero-⊥ ℰMγ⊥ (suc x) = ⊑-⊥


      substitution-reflect : ∀{δ : Env}{N : Term} {M : Term} {v}
        → ℰ (N [ M ]) δ v  → ℰ M δ ⊥ → WFEnv δ → wf v
          ------------------------------------------------
        → Σ[ w ∈ Value ] ℰ M δ w  ×  ℰ N (δ `, w) v
      substitution-reflect {δ}{N}{M}{v} ℰNMδv ℰMδ⊥ wfδ wfv
           with subst-reflect {M = N}{σ = subst-zero M} wfδ wfv ℰNMδv refl (subst-zero-⊥ {δ}{M} ℰMδ⊥)
      ...  | ⟨ γ , ⟨ wfγ , ⟨ δσγ , γNv ⟩ ⟩ ⟩
           with subst-zero-reflect {M = M} δσγ
      ...  | ⟨ w , ⟨ γ⊑δw , δMw ⟩ ⟩ =
             ⟨ w , ⟨ δMw , ⊑-env {M = N} wfv γ⊑δw γNv  ⟩ ⟩

  module ForISWIM
    (℘ : ∀{P : Prim} → rep P → ValueStruct.Value D → Set)
    where

    open import ISWIM
    open import ISWIMDenot D V _●_ ℱ (λ {P} k v → ℘ {P} k v)
    open RenamePreserveReflect.ForISWIM D V C _●_ ℱ MB (λ {P} k v → ℘ {P} k v)
      using (⊑-env)

    SubRef : Env → Term → Term → Subst → Value → Set
    SubRef δ M L σ v = WFEnv δ → wf v → ℰ L δ v → L ≡ ⟪ σ ⟫ M → δ `⊢ σ ↓ `⊥
                           → Σ[ γ ∈ Env ] WFEnv γ × δ `⊢ σ ↓ γ  ×  ℰ M γ v

    subst-reflect-var : ∀ {δ : Env} {x : Var} {σ : Subst} {v}
            → SubRef δ (` x) (⟪ σ ⟫ (` x)) σ v
    subst-reflect-var {δ}{x}{σ}{v} wfδ wfv ℰLδv refl δ⊢σ↓⊥
        = ⟨ const-env x v , ⟨ (wf-const-env {x} {v} wfv)
          , ⟨ const-env-ok , subst (v ⊑_) (sym (nth-const-env {x} {v})) ⊑-refl ⟩ ⟩ ⟩
        where
        const-env-ok : δ `⊢ σ ↓ const-env x v
        const-env-ok y with x ≟ y
        ... | yes x≡y rewrite sym x≡y | nth-const-env {x}{v} = ℰLδv
        ... | no x≢y rewrite diff-nth-const-env {x}{y}{v} x≢y = δ⊢σ↓⊥ y
        const-env-wf : (y : Var) → wf (const-env x v y)
        const-env-wf y
            with x ≟ x
        ... | yes refl = wf-const-env {x}{v} wfv y
        ... | no neq = ⊥-elim (neq refl)

    module SubstReflect
      (subst-reflect-lambda : ∀ {δ : Env} {N : Term}
                        {σ : Subst} {v}
            → (∀{u w}
               → SubRef (δ `, u) N (⟪ exts σ ⟫ N)  (exts σ) w)
            → SubRef δ (ƛ N) (⟪ σ ⟫ (ƛ N)) σ v)
      (subst-reflect-app : ∀ {δ : Env} {L : Term} {M : Term}
                        {σ : Subst} {v}
            → (∀ {v : Value} → SubRef δ L (⟪ σ ⟫ L) σ v)
            → (∀ {v : Value} → SubRef δ M (⟪ σ ⟫ M) σ v)
            → SubRef δ (L · M) (⟪ σ ⟫ (L · M)) σ v)
      where

      subst-reflect : ∀ {δ : Env} {M : Term} {L : Term}
                        {σ : Subst} {v}
                    → SubRef δ M L σ v
      subst-reflect {M = $ P k} wfδ wfv ℰLδv L≡σM δ⊢σ↓⊥ rewrite L≡σM =
          ⟨ `⊥ , ⟨ (λ z → wf-bot) , ⟨ δ⊢σ↓⊥ , ℰLδv ⟩ ⟩ ⟩
      subst-reflect {δ}{` x}{L}{σ}{v} wfδ wfv ℰLδv L≡σM δ⊢σ↓⊥ rewrite L≡σM =
          subst-reflect-var {x = x}{σ} wfδ wfv ℰLδv refl δ⊢σ↓⊥
      subst-reflect {δ}{ƛ N} {L} {σ} {v} wfδ wfv ℰLδv L≡σM δ⊢σ↓⊥
          rewrite L≡σM =
          subst-reflect-lambda {N = N}{v = v} IH wfδ wfv ℰLδv refl δ⊢σ↓⊥
          where
          IH = λ {u}{w} → subst-reflect {δ = δ `, u} {M = N}
                              {L = ⟪ exts σ ⟫ N} {σ = exts σ} {v = w}
      subst-reflect {δ}{L · M}{_}{σ}{v} wfδ wfv ℰσL●ℰσMδv
                    L≡σM δ⊢σ↓⊥ rewrite L≡σM =
          subst-reflect-app {L = L}{M}{σ} IH1 IH2 wfδ wfv ℰσL●ℰσMδv refl δ⊢σ↓⊥
          where
          IH1 = λ {v} → subst-reflect {δ = δ} {M = L} {L = ⟪ σ ⟫ L} {σ = σ} {v}
          IH2 = λ {v} → subst-reflect {δ = δ} {M = M} {L = ⟪ σ ⟫ M} {σ = σ} {v}


      subst-zero-reflect : ∀ {δ : Env} {γ : Env} {M : Term}
        → WFEnv γ
        → δ `⊢ subst-zero M ↓ γ
          ----------------------------------------
        → Σ[ w ∈ Value ] wf w × γ `⊑ (δ `, w) × ℰ M δ w
      subst-zero-reflect {δ = δ} {γ = γ} wfγ δσγ = ⟨ last γ , ⟨ wfγ 0 , ⟨ lemma , δσγ 0 ⟩ ⟩ ⟩
          where
          lemma : γ `⊑ (δ `, last γ)
          lemma 0  =  ⊑-refl
          lemma (suc x) = δσγ (suc x)


      subst-zero-⊥ : ∀{γ : Env}{M : Term}
                   → ℰ M γ ⊥
                   → γ `⊢ subst-zero M ↓ `⊥
      subst-zero-⊥ ℰMγ⊥ 0 = ℰMγ⊥
      subst-zero-⊥ ℰMγ⊥ (suc x) = ⊑-⊥


      substitution-reflect : ∀{δ : Env}{N : Term} {M : Term} {v}
        → ℰ (N [ M ]) δ v  → ℰ M δ ⊥ → WFEnv δ → wf v
          ------------------------------------------------
        → Σ[ w ∈ Value ] wf w × ℰ M δ w  ×  ℰ N (δ `, w) v
      substitution-reflect {δ}{N}{M}{v} ℰNMδv ℰMδ⊥ wfδ wfv
           with subst-reflect {M = N}{σ = subst-zero M} wfδ wfv ℰNMδv refl (subst-zero-⊥ {δ}{M} ℰMδ⊥)
      ...  | ⟨ γ , ⟨ wfγ , ⟨ δσγ , γNv ⟩ ⟩ ⟩
           with subst-zero-reflect {M = M} wfγ δσγ
      ...  | ⟨ w , ⟨ wfw , ⟨ γ⊑δw , δMw ⟩ ⟩ ⟩ =
             ⟨ w , ⟨ wfw , ⟨ δMw , ⊑-env {M = N} wfv γ⊑δw γNv ⟩ ⟩ ⟩


module SubstReflectAppCBV where

  module ForLambda where

    open import ValueBCD
    open ValueStructAux value_struct
    open OrderingAux value_struct ordering

    open import ConsistentAux value_struct ordering consistent
    open import ModelCallByValue value_struct ordering consistent ℱ model_curry

    open import Lambda
    open ASTMod using (Subst; ⟪_⟫)
    open import LambdaDenot value_struct ordering _●_ ℱ
    open RenamePreserveReflect.ForLambda value_struct ordering consistent
            _●_ ℱ model_curry_apply
      using (⊑-env)
    open Filter.ForLambda value_struct ordering consistent _●_ ℱ
       model_curry_apply
       using (subst-⊔; ℰ-⊑)

    SubRef : Env → Term → Term → Subst → Value → Set
    SubRef δ M L σ v = WFEnv δ → wf v → ℰ L δ v → L ≡ ⟪ σ ⟫ M → δ `⊢ σ ↓ `⊥
                     → Σ[ γ ∈ Env ] WFEnv γ × δ `⊢ σ ↓ γ  ×  ℰ M γ v

    subst-reflect-app : ∀ {δ : Env} {L : Term} {M : Term}
                        {σ : Subst} {v}
            → (∀ {v : Value} → SubRef δ L (⟪ σ ⟫ L) σ v)
            → (∀ {v : Value} → SubRef δ M (⟪ σ ⟫ M) σ v)
            → SubRef δ (L · M) (⟪ σ ⟫ (L · M)) σ v
    subst-reflect-app {δ}{L}{M}{σ}{v} IH1 IH2 wfδ wfv ℰσL●ℰσMδv L≡σM δ⊢σ↓⊥
        rewrite L≡σM
        with ℰσL●ℰσMδv
    ... | ⟨ u , ⟨ _ , ⟨ ℰσLδu↦v , ℰσMδu ⟩ ⟩ ⟩
        with IH1 (λ x → tt) tt ℰσLδu↦v refl δ⊢σ↓⊥
           | IH2 (λ x → tt) tt ℰσMδu refl δ⊢σ↓⊥
    ... | ⟨ δ₁  , ⟨ wfδ₁ , ⟨ subst-δ₁ , ℰLδ₁u↦v ⟩ ⟩ ⟩
        | ⟨ δ₂  , ⟨ wfδ₂ , ⟨ subst-δ₂ , ℰMδ₂u ⟩ ⟩ ⟩ =
          ⟨ (δ₁ `⊔ δ₂) ,
          ⟨ (λ x → tt) ,
          ⟨ (subst-⊔ {γ₁ = δ₁}{γ₂ = δ₂}{σ = σ} (λ x → tt) (λ x → tt)
                (λ x → tt) subst-δ₁ subst-δ₂) ,
          ⟨ u ,
          ⟨ tt ,
          ⟨ ℰLδ₁⊔δ₂u↦v ,
            ℰMδ₁⊔δ₂u ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
          where
          ℰLδ₁⊔δ₂u↦v : ℰ L (λ z → (δ₁ `⊔ δ₂) z) (u ↦ v)
          ℰLδ₁⊔δ₂u↦v = ⊑-env{M = L} tt (EnvConjR1⊑ δ₁ δ₂) ℰLδ₁u↦v

          ℰMδ₁⊔δ₂u  : ℰ M (λ z → (δ₁ `⊔ δ₂) z) u
          ℰMδ₁⊔δ₂u = ⊑-env{M = M} tt (EnvConjR2⊑ δ₁ δ₂) ℰMδ₂u


  module ForISWIM where

    open import ISWIM
    open ASTMod using (⟦_⟧)
    open import ValueConst
    open import Consistency
    open import ModelISWIM
    open import CurryConst
    open import PrimConst
    open import ConsistentAux value_struct ordering consistent
    open import ISWIMDenot value_struct ordering _●_ ℱ (λ {P} k v → ℘ {P} k v)
    open RenamePreserveReflect.ForISWIM value_struct ordering consistent _●_ ℱ model_curry_apply (λ {P} k v → ℘ {P} k v)
        using (⊑-env)
    open Filter.ForISWIM value_struct ordering consistent _●_ ℱ model_curry_apply
        (λ {P} k v → ℘ {P} k v)
        (λ {P} {k} {u} {v} → ℘-⊔ {P} {k} {u} {v})
        ℘-⊑
        (λ {P} {k} {u} {v} → ℘-~ {P} {k} {u} {v})
        using (subst-⊔; ℰ-⊑; ℰ-~)

    SubRef : Env → Term → Term → Subst → Value → Set
    SubRef δ M L σ v = WFEnv δ → wf v → ℰ L δ v → L ≡ ⟪ σ ⟫ M → δ `⊢ σ ↓ `⊥
                      → Σ[ γ ∈ Env ] WFEnv γ × δ `⊢ σ ↓ γ  ×  ℰ M γ v

    subst-reflect-app : ∀ {δ : Env} {L : Term} {M : Term}
                        {σ : Subst} {v}
            → (∀ {v : Value} → SubRef δ L (⟪ σ ⟫ L) σ v)
            → (∀ {v : Value} → SubRef δ M (⟪ σ ⟫ M) σ v)
            → SubRef δ (L · M) (⟪ σ ⟫ (L · M)) σ v
    subst-reflect-app {δ}{L}{M}{σ}{v} IH1 IH2 wfδ wfv ℰσL●ℰσMδv L≡σM δ⊢σ↓⊥
        rewrite L≡σM
        with ℰσL●ℰσMδv
    ... | ⟨ u , ⟨ wfu , ⟨ ℰσLδu↦v , ℰσMδu ⟩ ⟩ ⟩
        with IH1 wfδ(wf-fun wfu wfv) ℰσLδu↦v refl δ⊢σ↓⊥
           | IH2 wfδ wfu ℰσMδu refl δ⊢σ↓⊥
    ... | ⟨ δ₁  , ⟨ wfδ₁ , ⟨ subst-δ₁ , ℰLδ₁u↦v ⟩ ⟩ ⟩
        | ⟨ δ₂  , ⟨ wfδ₂ , ⟨ subst-δ₂ , ℰMδ₂u ⟩ ⟩ ⟩ =
          ⟨ δ₁ `⊔ δ₂ ,
          ⟨ (λ z → wf-⊔ (δ₁~δ₂ z) (wfδ₁ z) (wfδ₂ z)) ,
          ⟨ (subst-⊔ {γ₁ = δ₁}{γ₂ = δ₂}{σ = σ} wfδ wfδ₁ wfδ₂ subst-δ₁ subst-δ₂) ,
          ⟨ u ,
          ⟨ wfu ,
          ⟨ ℰLδ₁⊔δ₂u↦v , ℰMδ₁⊔δ₂u ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
          where
          δ₁~δ₂ : δ₁ ~′ δ₂
          δ₁~δ₂ x = ℰ-~ {M = ⟦ σ ⟧ x} wfδ wfδ (~′-refl (wfδ))
                          (wfδ₁ x) (wfδ₂ x) (subst-δ₁ x) (subst-δ₂ x)

          ℰLδ₁⊔δ₂u↦v : ℰ L (λ z → (δ₁ `⊔ δ₂) z) (u ↦ v)
          ℰLδ₁⊔δ₂u↦v = ⊑-env{M = L} (wf-fun wfu wfv) (EnvConjR1⊑ δ₁ δ₂) ℰLδ₁u↦v

          ℰMδ₁⊔δ₂u  : ℰ M (λ z → (δ₁ `⊔ δ₂) z) u
          ℰMδ₁⊔δ₂u = ⊑-env{M = M} wfu (EnvConjR2⊑ δ₁ δ₂) ℰMδ₂u


module SubstReflectLambdaBCD where
  open import ValueBCD
  open ValueStructAux value_struct

  module Inner
    (_●_ : Denotation → Denotation → Denotation)
    (MB : CurryApplyStruct.CurryApplyStruct value_struct ordering consistent _●_ ℱ)
    where
    
    open OrderingAux value_struct ordering
    open RenamePreserveReflect.ForLambda value_struct ordering consistent _●_ ℱ MB
       using (rename-inc-reflect; EnvExt⊑; ⊑-env; δu⊢extσ⊥)
    open Filter.ForLambda value_struct ordering consistent _●_ ℱ MB
       using (subst-⊔; ℰ-⊑)
    open import LambdaDenot value_struct ordering _●_ ℱ
    open CurryApplyStruct.CurryApplyStruct MB
    open import Lambda
    open ASTMod using (Subst; ⟪_⟫; ⟦_⟧; exts; rename-subst; exts-0; exts-suc-rename)
    open import Compositionality
    open import ConsistentAux value_struct ordering consistent
    open DenotAux value_struct ordering _●_ ℱ consistent MB

    SubRef : Env → Term → Term → Subst → Value → Set
    SubRef δ M L σ v = WFEnv δ → wf v → ℰ L δ v → L ≡ ⟪ σ ⟫ M → δ `⊢ σ ↓ `⊥
                       → Σ[ γ ∈ Env ] WFEnv γ × δ `⊢ σ ↓ γ  ×  ℰ M γ v

    subst-reflect-lambda : ∀ {δ : Env} {N : Term}
                        {σ : Subst} {v}
            → (∀{u w}
               → SubRef (δ `, u) N (⟪ exts σ ⟫ N)  (exts σ) w)
            → SubRef δ (ƛ N) (⟪ σ ⟫ (ƛ N)) σ v
    subst-reflect-lambda {N = N}{v = ⊥} IH wfδ wfv _ L≡ δ⊢σ↓⊥ =
        ⟨ `⊥ , ⟨ (λ x → tt) , ⟨ δ⊢σ↓⊥ , ƛ-⊥ {N}{`⊥} ⟩ ⟩ ⟩ 
    subst-reflect-lambda {δ}{N = N}{σ} {u ↦ w} IH wfδ wfv ℰLδv L≡ δ⊢σ↓⊥
        with IH {u}{w} (λ x → tt) tt ℰLδv refl (δu⊢extσ⊥ δ⊢σ↓⊥)
    ... | ⟨ γ , ⟨ wfγ , ⟨ subst-γ , m ⟩ ⟩ ⟩ 
          =
          ⟨ init γ ,
          ⟨ (λ x → tt) ,
          ⟨ RIR ,
            (let m' = split{M = N} m in
             EnvExt⊑ {M = N} tt SG0 m') ⟩ ⟩ ⟩
         where
         SG0 : γ zero ⊑ u
         SG0
             with subst-γ 0
         ... | sg rewrite exts-0 σ = sg
         SG1 : ∀ x → _
         SG1 x
             with subst-γ (suc x)
         ... | sg rewrite sym (rename-subst (↑ 1) (⟦ σ ⟧ x))= sg
         RIR : (x : ℕ) → ℰ (⟦ σ ⟧ x) δ (γ (suc x))
         RIR x with SG1 x
         ... | sg1 rewrite exts-suc-rename σ x = rename-inc-reflect {M = ⟦ σ ⟧ x} tt sg1
    subst-reflect-lambda {N = N}{σ}{u ⊔ w} IH wfδ wfv ⟨ aa , bb ⟩ L≡ δ⊢σ↓⊥
        with subst-reflect-lambda{N = N}{σ}{u} IH (λ x → tt) wfv aa L≡ δ⊢σ↓⊥
           | subst-reflect-lambda{N = N}{σ}{w} IH (λ x → tt) wfv bb L≡ δ⊢σ↓⊥
    ... | ⟨ δ₁ , ⟨ wfδ₁ , ⟨ subst-δ₁ , m1 ⟩ ⟩ ⟩
        | ⟨ δ₂ , ⟨ wfδ₂ , ⟨ subst-δ₂ , m2 ⟩ ⟩ ⟩ =
        ⟨ δ₁ `⊔ δ₂ ,
        ⟨ (λ x → tt) ,
        ⟨ subst-⊔ {σ = σ} (λ x → tt) (λ x → tt) (λ x → tt)
                  subst-δ₁ subst-δ₂ ,
        ⟨ ⊑-env {δ₁}{δ₁ `⊔ δ₂}{lam ⦅ cons (bind (ast N)) nil ⦆}{u}
               tt (EnvConjR1⊑ δ₁ δ₂) m1 ,
          ⊑-env {δ₂}{δ₁ `⊔ δ₂}{lam ⦅ cons (bind (ast N)) nil ⦆}{w}
               tt (EnvConjR2⊑ δ₁ δ₂) m2 ⟩
          ⟩ ⟩ ⟩


module SubstReflectLambdaConst where

  open import ValueConst
  open import CurryConst
  open import PrimConst
  open import Consistency
  open ValueStructAux value_struct
  open OrderingAux value_struct ordering

  module Inner
    (_●_ : Denotation → Denotation → Denotation)
    (MB : CurryApplyStruct.CurryApplyStruct value_struct ordering consistent _●_ ℱ)
    (℘ : ∀{P : Prim} → rep P → Value → Set)
    (℘-⊔ : ∀{P : Prim } {D : rep P} {u v : Value}
          → ℘ {P} D u → ℘ {P} D v → ℘ {P} D (u ⊔ v))
    (℘-⊑ : ∀{P : Prim} {D : rep P} {v w : Value}
          → wf w → ℘ {P} D v → w ⊑ v → ℘ {P} D w)
    (℘-~ : ∀{P : Prim } {D : rep P} {u v : Value}
         → ℘ {P} D u → ℘ {P} D v
         → u ~ v)
    where

    open import ISWIM
    open ASTMod using (exts-0; exts-suc-rename; rename-subst)
    open import ISWIMDenot value_struct ordering _●_ ℱ (λ {P} k v → ℘ {P} k v)
    open import Compositionality
    open ISWIMDenotAux value_struct ordering _●_ ℱ consistent MB (λ {P} k v → ℘ {P} k v)
    open RenamePreserveReflect.ForISWIM
      value_struct ordering consistent _●_ ℱ MB (λ {P} k v → ℘ {P} k v)
      using (rename-inc-reflect; EnvExt⊑; ⊑-env; δu⊢extσ⊥)
    open Filter.ForISWIM value_struct ordering consistent _●_ ℱ MB
      (λ {P} k v → ℘ {P} k v) ℘-⊔ ℘-⊑ ℘-~
      using (subst-⊔; ℰ-⊑; ℰ-~)

    open import ConsistentAux value_struct ordering consistent

    SubRef : Env → Term → Term → Subst → Value → Set
    SubRef δ M L σ v = WFEnv δ → wf v → ℰ L δ v → L ≡ ⟪ σ ⟫ M → δ `⊢ σ ↓ `⊥
                       → Σ[ γ ∈ Env ] WFEnv γ × δ `⊢ σ ↓ γ  ×  ℰ M γ v

    subst-reflect-lambda : ∀ {δ : Env} {N : Term}
                        {σ : Subst} {v}
            → (∀{u w}
               → SubRef (δ `, u) N (⟪ exts σ ⟫ N)  (exts σ) w)
            → SubRef δ (ƛ N) (⟪ σ ⟫ (ƛ N)) σ v
    subst-reflect-lambda {N = N}{v = const {B} k} IH wfδ wfv () L≡ δ⊢σ↓⊥
    subst-reflect-lambda {N = N}{v = ⊥} IH wfδ wfv _ L≡ δ⊢σ↓⊥ =
        ⟨ `⊥ , ⟨ (λ z → wf-bot) , ⟨ δ⊢σ↓⊥ , ƛ-⊥ {N}{`⊥} ⟩ ⟩ ⟩
    subst-reflect-lambda {δ}{N = N}{σ} {u ↦ w} IH wfδ (wf-fun wfu wfw) ℰLδv L≡ δ⊢σ↓⊥
        with IH {u}{w} (WFEnv-extend wfδ wfu) wfw ℰLδv refl (δu⊢extσ⊥ δ⊢σ↓⊥)
    ... | ⟨ γ , ⟨ wfγ , ⟨ subst-γ , m ⟩ ⟩ ⟩ =
          ⟨ init γ ,
          ⟨ (λ z → wfγ (suc z)) ,
          ⟨ RIR ,
            (let m' = split{M = N} m in
             EnvExt⊑{M = N} wfw SG0 m') ⟩ ⟩ ⟩
          where
          SG0 : γ zero ⊑ u
          SG0 with subst-γ 0
          ... | sg rewrite exts-0 σ = sg
          SG1 : ∀ x → _
          SG1 x
              with subst-γ (suc x)
          ... | sg rewrite sym (rename-subst (↑ 1) (⟦ σ ⟧ x))= sg
          RIR : (x : ℕ) → ℰ (⟦ σ ⟧ x) δ (γ (suc x))
          RIR x with SG1 x
          ... | sg1 rewrite exts-suc-rename σ x =
              rename-inc-reflect {M = ⟦ σ ⟧ x} (wfγ (suc x)) sg1
      
    subst-reflect-lambda {δ}{N = N}{σ}{u ⊔ w} IH wfδ (wf-⊔ u~w wfu wfw) ⟨ aa , bb ⟩ L≡ δ⊢σ↓⊥
        with subst-reflect-lambda{N = N}{σ}{u} IH wfδ wfu aa L≡ δ⊢σ↓⊥
           | subst-reflect-lambda{N = N}{σ}{w} IH wfδ wfw bb L≡ δ⊢σ↓⊥
    ... | ⟨ δ₁ , ⟨ wfδ₁ , ⟨ subst-δ₁ , m1 ⟩ ⟩ ⟩
        | ⟨ δ₂ , ⟨ wfδ₂ , ⟨ subst-δ₂ , m2 ⟩ ⟩ ⟩ =
        ⟨ δ₁ `⊔ δ₂ ,
        ⟨ (λ z → wf-⊔ (δ₁~δ₂ z) (wfδ₁ z) (wfδ₂ z)) ,
        ⟨ subst-⊔ {σ = σ} wfδ wfδ₁ wfδ₂ subst-δ₁ subst-δ₂ ,
        ⟨ ⊑-env{δ₁}{δ₁ `⊔ δ₂}{lam ⦅ cons (bind (ast N)) nil ⦆}{u}wfu(EnvConjR1⊑ δ₁ δ₂) m1 ,
          ⊑-env{δ₂}{δ₁ `⊔ δ₂}{lam ⦅ cons (bind (ast N)) nil ⦆}{w}wfw(EnvConjR2⊑ δ₁ δ₂) m2 ⟩
          ⟩ ⟩ ⟩
        where
        δ₁~δ₂ : δ₁ ~′ δ₂
        δ₁~δ₂ x = ℰ-~{M = ⟦ σ ⟧ x} wfδ wfδ (~′-refl (wfδ)) (wfδ₁ x) (wfδ₂ x) (subst-δ₁ x) (subst-δ₂ x)

module CallByName where

  open import ValueBCD
  open ValueStructAux value_struct
  open import ModelCallByName
  open import OrderingAux value_struct ordering
  open import ConsistentAux value_struct ordering consistent
  open import LambdaDenot value_struct ordering _●_ ℱ
  open RenamePreserveReflect.ForLambda value_struct ordering consistent _●_ ℱ model_curry_apply
    using (⊑-env)
  open Filter.ForLambda value_struct ordering consistent _●_ ℱ model_curry_apply using (subst-⊔; ℰ-⊑)
  open import Lambda
  open ASTMod using (Subst; ⟪_⟫)

  SubRef : Env → Term → Term → Subst → Value → Set
  SubRef δ M L σ v = WFEnv δ → wf v → ℰ L δ v → L ≡ ⟪ σ ⟫ M → δ `⊢ σ ↓ `⊥
                     → Σ[ γ ∈ Env ] WFEnv γ × δ `⊢ σ ↓ γ  ×  ℰ M γ v

  subst-reflect-app : ∀ {δ : Env} {L : Term} {M : Term} 
                      {σ : Subst} {v}
          → (∀ {v : Value} → SubRef δ L (⟪ σ ⟫ L) σ v)
          → (∀ {v : Value} → SubRef δ M (⟪ σ ⟫ M) σ v)
          → SubRef δ (L · M) (⟪ σ ⟫ (L · M)) σ v
  subst-reflect-app {δ}{L}{M}{σ}{v} IH1 IH2 wfδ wfv ℰσL●ℰσMδv L≡σM δ⊢σ↓⊥
      rewrite L≡σM 
      with ℰσL●ℰσMδv
  ... | inj₁ v⊑⊥ = 
        ⟨ `⊥ , ⟨ (λ x → tt) , ⟨ δ⊢σ↓⊥ , ℰ-⊑{M = L · M} (λ x → tt) tt tt v⊑⊥ (ℰ-⊥{M = L · M}) ⟩ ⟩ ⟩
  ... | inj₂ ⟨ u , ⟨ ℰσLδu↦v , ℰσMδu ⟩ ⟩
      with IH1 (λ x → tt) tt ℰσLδu↦v refl δ⊢σ↓⊥
         | IH2 (λ x → tt) tt ℰσMδu refl δ⊢σ↓⊥
  ... | ⟨ δ₁  , ⟨ wfδ₁ , ⟨ subst-δ₁ , ℰLδ₁u↦v ⟩ ⟩ ⟩ 
      | ⟨ δ₂  , ⟨ wfδ₂ , ⟨ subst-δ₂ , ℰMδ₂u ⟩ ⟩ ⟩ = 
        ⟨ (δ₁ `⊔ δ₂) ,
        ⟨ (λ x → tt) ,
        ⟨ (subst-⊔ {γ₁ = δ₁}{γ₂ = δ₂}{σ = σ} (λ x → tt) (λ x → tt) (λ x → tt) subst-δ₁ subst-δ₂) ,
          inj₂ ⟨ u , ⟨ ℰLδ₁⊔δ₂u↦v , ℰMδ₁⊔δ₂u ⟩ ⟩ ⟩ ⟩ ⟩ 
        where
        ℰLδ₁⊔δ₂u↦v : ℰ L (λ z → (δ₁ `⊔ δ₂) z) (u ↦ v)
        ℰLδ₁⊔δ₂u↦v = ⊑-env{M = L} tt (EnvConjR1⊑ δ₁ δ₂) ℰLδ₁u↦v 

        ℰMδ₁⊔δ₂u  : ℰ M (λ z → (δ₁ `⊔ δ₂) z) u
        ℰMδ₁⊔δ₂u = ⊑-env{M = M} tt (EnvConjR2⊑ δ₁ δ₂) ℰMδ₂u

  open ForLambdaModel value_struct ordering consistent _●_ ℱ model_curry_apply
  open SubstReflectLambdaBCD.Inner _●_ model_curry_apply

  

  open ForLambda.SubstReflect
          (λ {δ}{N}{σ}{v} → subst-reflect-lambda {δ}{N}{σ}{v})
          (λ {δ}{L}{M}{σ}{v} → subst-reflect-app {δ}{L}{M}{σ}{v}) public

module CallByValue where

  open import ValueBCD
  open ValueStructAux value_struct
  open import ModelCallByValue value_struct ordering consistent ℱ model_curry
  open SubstReflectAppCBV.ForLambda
  open ForLambdaModel value_struct ordering consistent _●_ ℱ model_curry_apply
  open SubstReflectLambdaBCD.Inner _●_ model_curry_apply

  open ForLambda.SubstReflect
          (λ {δ}{N}{σ}{v} →
             subst-reflect-lambda{δ}{N}{σ}{v})
          (λ {δ}{L}{M}{σ}{v} →
             subst-reflect-app{δ}{L}{M}{σ}{v}) public

module ISWIM where

  open import ValueConst
  open import CurryConst
  open import PrimConst
  open import Consistency
  open import ModelISWIM

  open SubstReflectAppCBV.ForISWIM
  open ForLambdaModel value_struct ordering consistent _●_ ℱ model_curry_apply
  open SubstReflectLambdaConst.Inner _●_ model_curry_apply 
       (λ {P} k v → ℘ {P} k v)
       (λ {P} {k} {u} {v} → ℘-⊔ {P} {k} {u} {v})
       (λ {P}{k}{v}{w} → ℘-⊑ {P}{k}{v}{w})
       (λ {P}{k}{u}{v} → ℘-~ {P}{k}{u}{v})

  open ForISWIM.SubstReflect
          (λ {P} k v → ℘ {P} k v)
          (λ {δ}{N}{σ}{v} →
             subst-reflect-lambda{δ}{N}{σ}{v})
          (λ {δ}{L}{M}{σ}{v} →
             subst-reflect-app{δ}{L}{M}{σ}{v}) public


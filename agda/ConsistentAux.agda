open import Utilities using (_iff_)
open import Data.Nat using (ℕ; zero; suc; _≟_)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥-elim) renaming (⊥ to Bot)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Syntax using (Var)
open import Structures
import ValueStructAux

module ConsistentAux
  (D : ValueStruct) (V : ValueOrdering D) (C : Consistent D V)
  where
  
  open ValueStruct D
  open ValueOrdering V
  open import OrderingAux D V
  open Consistent C
  open ValueStructAux D

  _≲_ : (Value → Set) → (Value → Set) → Set
  d ≲ d' = ∀{v : Value} → wf v → d v → d' v

  ≲-refl : ∀ {d : Value → Set}
         → d ≲ d
  ≲-refl wfv dv = dv

  ≲-trans : ∀ {d₁ d₂ d₃ : Value → Set}
    → d₁ ≲ d₂
    → d₂ ≲ d₃
      ------- 
    → d₁ ≲ d₃
  ≲-trans m12 m23 wfv d₁v = m23 wfv (m12 wfv d₁v)

  infixr 2 _≲⟨⟩_ _≲⟨_⟩_
  infix  3 _☐

  _≲⟨⟩_ : ∀ (x : Value → Set) {y : Value → Set}
      → x ≲ y
        -----
      → x ≲ y
  x ≲⟨⟩ x≲y  = x≲y

  _≲⟨_⟩_ : ∀ (x : Value → Set) {y z : Value → Set}
      → x ≲ y
      → y ≲ z
        -----
      → x ≲ z
  (x ≲⟨ x≲y ⟩ y≲z) {v} wfv xv = y≲z wfv (x≲y wfv xv)

  _☐ : ∀ (d : Value → Set)
        -----
      → d ≲ d
  (d ☐) {v} =  ≲-refl {d}


  WFEnv : Env → Set
  WFEnv γ = ∀{x : Var} → wf (γ x)

  WFEnv-extend : ∀{γ : Env}{v}
              → WFEnv γ
              → wf v
              → WFEnv (γ `, v)
  WFEnv-extend {γ} {v} wfγ wfv {0} = wfv
  WFEnv-extend {γ} {v} wfγ wfv {suc x} = wfγ

  infix 3 _≃_

  _≃_ : Denotation → Denotation → Set
  (_≃_ D₁ D₂) = (γ : Env) → (v : Value) → WFEnv γ → wf v → D₁ γ v iff D₂ γ v

  ≃-refl : ∀ {M : Denotation}
    → M ≃ M
  ≃-refl γ v wfγ wfv = ⟨ (λ x → x) , (λ x → x) ⟩

  ≃-sym : ∀ {M N : Denotation}
    → M ≃ N
      -----
    → N ≃ M
  ≃-sym eq γ v wfγ wfv = ⟨ (proj₂ (eq γ v wfγ wfv)) , (proj₁ (eq γ v wfγ wfv)) ⟩

  ≃-trans : ∀ {M₁ M₂ M₃ : Denotation}
    → M₁ ≃ M₂
    → M₂ ≃ M₃
      -------
    → M₁ ≃ M₃
  ≃-trans eq1 eq2 γ v wfγ wfv =
      ⟨ (λ z → proj₁ (eq2 γ v wfγ wfv) (proj₁ (eq1 γ v wfγ wfv) z)) ,
        (λ z → proj₂ (eq1 γ v wfγ wfv) (proj₂ (eq2 γ v wfγ wfv) z)) ⟩

  infixr 2 _≃⟨⟩_ _≃⟨_⟩_
  infix  3 _■

  _≃⟨⟩_ : ∀ (x : Denotation) {y : Denotation}
      → x ≃ y
        -----
      → x ≃ y
  x ≃⟨⟩ x≃y  = x≃y

  _≃⟨_⟩_ : ∀ (x : Denotation) {y z : Denotation}
      → x ≃ y
      → y ≃ z
        -----
      → x ≃ z
  (x ≃⟨ x≃y ⟩ y≃z) =  ≃-trans x≃y y≃z

  _■ : ∀ (d : Denotation)
        -----
      → d ≃ d
  (d ■) =  ≃-refl


  _~′_ : Env → Env → Set
  _~′_ γ δ = ∀{x : Var} → γ x ~ δ x

  ~′-refl : ∀{γ : Env}
              → WFEnv γ
              → γ ~′ γ
  ~′-refl {γ} wfγ {x} = ~-refl {γ x} {wfγ} 


  ~′-extend : ∀{γ δ : Env}{u v}
            → γ ~′ δ → u ~ v
            → (γ `, u) ~′ (δ `, v)
  ~′-extend γ~′δ u~v {0} = u~v
  ~′-extend γ~′δ u~v {suc x} = γ~′δ

  app-consistency : ∀{u₁ u₂ v₁ w₁ v₂ w₂}
        → u₁ ~ u₂
        → v₁ ~ v₂
        → v₁ ↦ w₁ ⊑ u₁
        → v₂ ↦ w₂ ⊑ u₂
        → w₁ ~ w₂
  app-consistency {u₁}{u₂}{v₁}{w₁}{v₂}{w₂} u₁~u₂ v₁~v₂ v₁↦w₁⊑u₁ v₂↦w₂⊑u₂
      with ~-⊑ u₁~u₂ v₁↦w₁⊑u₁ v₂↦w₂⊑u₂
  ... | v₁↦w₁~v₂↦w₂ 
      with ~-↦ {v₁}{w₁}{v₂}{w₂} v₁↦w₁~v₂↦w₂ 
  ... | inj₁ ⟨ _ , w₁~w₂ ⟩ = w₁~w₂
  ... | inj₂ v₁~̸v₂ = ⊥-elim (contradiction v₁~v₂ v₁~̸v₂)


  ~-↦-~ : ∀{v w v′ w′} → (v ↦ w ~ v′ ↦ w′) → v ~ v′ → w ~ w′
  ~-↦-~ vw~vw′ v~v'
      with ~-↦ vw~vw′
  ... | inj₁ ⟨ _ , w~w′ ⟩ = w~w′
  ... | inj₂ ¬v~v′ = ⊥-elim (contradiction v~v' ¬v~v′)

  wf-const-env : ∀ {x v} → wf v → ∀ {y} → wf (const-env x v y)
  wf-const-env {x}{v} wfv {y}
      with x ≟ y
  ... | yes eq = wfv
  ... | no neq = wf-bot

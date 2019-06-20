open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥-elim) renaming (⊥ to Bot)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)


open import Variables
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


  WFEnv : ∀ {Γ : ℕ} → Env Γ → Set
  WFEnv {Γ} γ = ∀{x : Var Γ} → wf (γ x)

  WFEnv-extend : ∀{Γ}{γ : Env Γ}{v}
              → WFEnv {Γ} γ
              → wf v
              → WFEnv {suc Γ} (γ `, v)
  WFEnv-extend {Γ} {γ} {v} wfγ wfv {Z} = wfv
  WFEnv-extend {Γ} {γ} {v} wfγ wfv {S x} = wfγ

  infix 3 _≃_

  _≃_ : ∀ {Γ} → (Denotation Γ) → (Denotation Γ) → Set
  (_≃_ {Γ} D₁ D₂) = (γ : Env Γ) → (v : Value) → WFEnv γ → wf v → D₁ γ v iff D₂ γ v

  ≃-refl : ∀ {Γ } → {M : Denotation Γ}
    → M ≃ M
  ≃-refl γ v wfγ wfv = ⟨ (λ x → x) , (λ x → x) ⟩

  ≃-sym : ∀ {Γ } → {M N : Denotation Γ}
    → M ≃ N
      -----
    → N ≃ M
  ≃-sym eq γ v wfγ wfv = ⟨ (proj₂ (eq γ v wfγ wfv)) , (proj₁ (eq γ v wfγ wfv)) ⟩

  ≃-trans : ∀ {Γ } → {M₁ M₂ M₃ : Denotation Γ}
    → M₁ ≃ M₂
    → M₂ ≃ M₃
      -------
    → M₁ ≃ M₃
  ≃-trans eq1 eq2 γ v wfγ wfv =
      ⟨ (λ z → proj₁ (eq2 γ v wfγ wfv) (proj₁ (eq1 γ v wfγ wfv) z)) ,
        (λ z → proj₂ (eq1 γ v wfγ wfv) (proj₂ (eq2 γ v wfγ wfv) z)) ⟩

  infixr 2 _≃⟨⟩_ _≃⟨_⟩_
  infix  3 _■

  _≃⟨⟩_ : ∀ {Γ} (x : Denotation Γ) {y : Denotation Γ}
      → x ≃ y
        -----
      → x ≃ y
  x ≃⟨⟩ x≃y  = x≃y

  _≃⟨_⟩_ : ∀ {Γ} (x : Denotation Γ) {y z : Denotation Γ}
      → x ≃ y
      → y ≃ z
        -----
      → x ≃ z
  (x ≃⟨ x≃y ⟩ y≃z) =  ≃-trans x≃y y≃z

  _■ : ∀ {Γ} (d : Denotation Γ)
        -----
      → d ≃ d
  (d ■) =  ≃-refl


  _~′_ : ∀{Γ} → Env Γ → Env Γ → Set
  _~′_ {Γ} γ δ = ∀{x : Var Γ} → γ x ~ δ x

  ~′-refl : ∀{Γ}{γ : Env Γ}
              → WFEnv {Γ} γ
              → γ ~′ γ
  ~′-refl {Γ}{γ} wfγ {x} = ~-refl {γ x} {wfγ} 


  ~′-extend : ∀{Γ}{γ δ : Env Γ}{u v}
            → γ ~′ δ → u ~ v
            → (γ `, u) ~′ (δ `, v)
  ~′-extend γ~′δ u~v {Z} = u~v
  ~′-extend γ~′δ u~v {S x} = γ~′δ

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

  wf-const-env : ∀ {Γ}{x v} → wf v → ∀ {y} → wf (const-env {Γ} x v y)
  wf-const-env {Γ}{x}{v} wfv {y}
      with x var≟ y
  ... | yes eq = wfv
  ... | no neq = wf-bot

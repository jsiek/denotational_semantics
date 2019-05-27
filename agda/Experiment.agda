
open import LambdaV
   using ($; _·_; ƛ; Term; prim; lam; app)
open LambdaV.ASTMod
   using (Var; Z; S_; `_; _⦅_⦆; extensionality; Rename; Subst;
          ext; exts; cons; bind; nil; rename; ⟪_⟫)
open import Primitives
   using (Base; Prim; rep; base; base-rep; _⇒_; base-eq?)


open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong; cong₂; cong-app)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥-elim) renaming (⊥ to Bot)
open import Function using (_∘_)
open import Data.Unit using (⊤)
open import Data.Empty renaming (⊥ to Bot)
open import Relation.Nullary using (¬_; Dec; yes; no)


module Experiment where


module Domain
  (Value : Set)
  (_⊑_ : Value → Value → Set)
  (Trans⊑ : ∀ {u v w} → u ⊑ v → v ⊑ w → u ⊑ w)
  (lit : {B : Base} → base-rep B → Value)
  where

  Env : ℕ → Set
  Env Γ = Var Γ → Value

  `∅ : Env zero
  `∅ ()

  infixl 5 _`,_

  _`,_ : ∀ {Γ} → Env Γ → Value → Env (suc Γ)
  (γ `, v) Z = v
  (γ `, v) (S x) = γ x

  init : ∀ {Γ} → Env (suc Γ) → Env Γ
  init γ x = γ (S x)

  last : ∀ {Γ} → Env (suc Γ) → Value
  last γ = γ Z

  init-last : ∀ {Γ} → (γ : Env (suc Γ)) → γ ≡ (init γ `, last γ)
  init-last {Γ} γ = extensionality lemma
    where
    lemma : ∀ (x : Var (suc Γ)) → γ x ≡ (init γ `, last γ) x
    lemma Z      =  refl
    lemma (S x)  =  refl

  Denotation : ℕ → Set₁
  Denotation Γ = Env Γ → Value → Set

  _iff_ : Set → Set → Set
  P iff Q = (P → Q) × (Q → P)

  _≃_ : (Value → Set) → (Value → Set) → Set
  d ≃ d' = ∀{v : Value} → d v iff d' v

  ≃-refl : ∀ {M : Value → Set}
    → M ≃ M
  ≃-refl = ⟨ (λ x → x) , (λ x → x) ⟩

  ≃-trans : ∀ {M₁ M₂ M₃ : Value → Set}
    → M₁ ≃ M₂
    → M₂ ≃ M₃
      -------
    → M₁ ≃ M₃
  ≃-trans m12 m23 = ⟨ (λ z → proj₁ m23 (proj₁ m12 z)) ,
                      (λ z → proj₂ m12 (proj₂ m23 z)) ⟩

  infixr 2 _≃⟨⟩_ _≃⟨_⟩_
  infix  3 _☐

  _≃⟨⟩_ : ∀ (x : Value → Set) {y : Value → Set}
      → x ≃ y
        -----
      → x ≃ y
  x ≃⟨⟩ x≃y  = x≃y

  _≃⟨_⟩_ : ∀ (x : Value → Set) {y z : Value → Set}
      → x ≃ y
      → y ≃ z
        -----
      → x ≃ z
  (x ≃⟨ x≃y ⟩ y≃z) {v} =  ≃-trans (x≃y{v}) y≃z {v}

  _☐ : ∀ (d : Value → Set)
        -----
      → d ≃ d
  (d ☐) {v} =  ≃-refl {d}


  module Denot
    (℘ : ∀{P : Prim} → rep P → Value → Set)
    (ℱ : ∀{Γ} → Denotation (suc Γ) → Denotation Γ)
    (_●_ : ∀{Γ} → Denotation Γ → Denotation Γ → Denotation Γ)
    (cong-● : ∀{Γ Δ}{γ : Env Γ}{δ : Env  Δ}{D₁ D₂ : Denotation Γ}
               {D₁′ D₂′ : Denotation Δ}
            → D₁ γ ≃ D₁′ δ → D₂ γ ≃ D₂′ δ → (D₁ ● D₂) γ ≃ (D₁′ ● D₂′) δ)
    (cong-ℱ : ∀{Γ Δ}{γ : Env Γ}{δ : Env Δ}{D : Denotation (suc Γ)}
               {D′ : Denotation (suc Δ)}
            → (∀{v : Value} → D (γ `, v) ≃ D′ (δ `, v)) → ℱ D γ ≃ ℱ D′ δ)
    where

    ℰ : ∀{Γ} → Term Γ → Denotation Γ
    ℰ {Γ} (` x) γ v = v ⊑ γ x
    ℰ {Γ} (lam ⦅ bind N nil ⦆) = ℱ (ℰ N)
    ℰ {Γ} (app ⦅ cons L (cons M nil) ⦆) = (ℰ L) ● (ℰ M)
    ℰ ((prim {p} k) ⦅ nil ⦆) γ = ℘ {p} k

    _`⊑_ : ∀ {Γ} → Env Γ → Env Γ → Set
    _`⊑_ {Γ} γ δ = (x : Var Γ) → γ x ⊑ δ x

    _`≡_ : ∀ {Γ} → Env Γ → Env Γ → Set
    _`≡_ {Γ} γ δ = (x : Var Γ) → γ x ≡ δ x

    rename-equiv : ∀ {Γ Δ} {γ : Env Γ} {δ : Env Δ} {M : Term Γ}
                     {ρ : Rename Γ Δ}
      → γ `≡ (δ ∘ ρ)
      → ℰ M γ ≃ ℰ (rename ρ M) δ
    rename-equiv {M = (prim {p} k ⦅ nil ⦆)} γ≡δ∘ρ = ⟨ (λ z → z) , (λ z → z) ⟩
    rename-equiv {M = ` x} γ≡δ∘ρ rewrite γ≡δ∘ρ x = ⟨ (λ x → x) , (λ x → x) ⟩
    rename-equiv {Γ}{Δ}{γ}{δ}{lam ⦅ bind N nil ⦆}{ρ} γ≡δ∘ρ =
       cong-ℱ {D = ℰ N}{D′ = ℰ (rename (ext ρ) N)} G
       where
       H : ∀{v} → (γ `, v) `≡ ((λ {x} → δ `, v) ∘ ext ρ)
       H {v} Z = refl
       H {v} (S x) = γ≡δ∘ρ x

       G : ∀{v} → ℰ N (γ `, v) ≃ ℰ (rename (ext ρ) N) (δ `, v)
       G {v} = rename-equiv {suc Γ}{suc Δ}{γ `, v}{δ `, v}{M = N}{ext ρ} H
    rename-equiv {Γ}{Δ}{γ}{δ}{app ⦅ cons L (cons M nil) ⦆}{ρ} γ≡δ∘ρ =
      cong-● (rename-equiv {M = L} γ≡δ∘ρ) (rename-equiv {M = M} γ≡δ∘ρ)

    _⊨_↓_ : ∀{Δ Γ} → Env Δ → Subst Γ Δ → Env Γ → Set
    _⊨_↓_ {Δ}{Γ} δ σ γ = ∀{k : Var Γ} →  ℰ (σ k) δ (γ k)

    subst-equiv : ∀ {Γ Δ} {γ : Env Γ} {δ : Env Δ} {M : Term Γ}
      → (σ : Subst Γ Δ)  →  δ ⊨ σ ↓ γ
        -----------------------------
      → ℰ M γ ≃ ℰ (⟪ σ ⟫ M) δ 
    subst-equiv {M = M} σ δ⊨σ↓γ = {!!}

module Instance where

  infixr 7 _↦_
  infixl 5 _⊔_

  data Value : Set where
    lit : {B : Base} → base-rep B → Value
    ⊥ : Value
    _↦_ : Value → Value → Value
    _⊔_ : Value → Value → Value

  infix 4 _⊑_

  data _⊑_ : Value → Value → Set where

    Bot⊑ : ∀ {v} → ⊥ ⊑ v

    Lit⊑ : ∀{B k} → lit {B} k ⊑ lit {B} k

    ConjL⊑ : ∀ {u v w}
        → v ⊑ u
        → w ⊑ u
          -----------
        → (v ⊔ w) ⊑ u

    ConjR1⊑ : ∀ {u v w}
       → u ⊑ v
         -----------
       → u ⊑ (v ⊔ w)

    ConjR2⊑ : ∀ {u v w}
       → u ⊑ w
         -----------
       → u ⊑ (v ⊔ w)

    Trans⊑ : ∀ {u v w}
       → u ⊑ v
       → v ⊑ w
         -----
       → u ⊑ w

    Fun⊑ : ∀ {v w v′ w′}
         → v′ ⊑ v
         → w ⊑ w′
           -------------------
         → (v ↦ w) ⊑ (v′ ↦ w′)

    Dist⊑ : ∀{v w w′}
           ---------------------------------
         → v ↦ (w ⊔ w′) ⊑ (v ↦ w) ⊔ (v ↦ w′)

  Refl⊑ : ∀ {v} → v ⊑ v
  Refl⊑ {⊥} = Bot⊑
  Refl⊑ {lit {B} k} = Lit⊑
  Refl⊑ {v ↦ v′} = Fun⊑ Refl⊑ Refl⊑
  Refl⊑ {v₁ ⊔ v₂} = ConjL⊑ (ConjR1⊑ Refl⊑) (ConjR2⊑ Refl⊑)

  ⊔⊑⊔ : ∀ {v w v′ w′}
        → v ⊑ v′  →  w ⊑ w′
          -----------------------
        → (v ⊔ w) ⊑ (v′ ⊔ w′)
  ⊔⊑⊔ d₁ d₂ = ConjL⊑ (ConjR1⊑ d₁) (ConjR2⊑ d₂)

  Dist⊔↦⊔ : ∀{v v′ w w′ : Value}
          → (v ⊔ v′) ↦ (w ⊔ w′) ⊑ (v ↦ w) ⊔ (v′ ↦ w′)
  Dist⊔↦⊔ = Trans⊑ Dist⊑ (⊔⊑⊔ (Fun⊑ (ConjR1⊑ Refl⊑) Refl⊑)
                              (Fun⊑ (ConjR2⊑ Refl⊑) Refl⊑))

  module Dom = Domain Value _⊑_ Trans⊑ lit
  open Dom

  ℱ : ∀{Γ} → Denotation (suc Γ) → Denotation Γ
  ℱ D γ (v ↦ w) = D (γ `, v) w
  ℱ D γ ⊥ = ⊤
  ℱ D γ (u ⊔ v) = (ℱ D γ u) × (ℱ D γ v)
  ℱ D γ (lit k) = Bot

  cong-ℱ : ∀{Γ Δ}{γ : Env Γ}{δ : Env Δ}{D : Denotation (suc Γ)}
            {D′ : Denotation (suc Δ)}
         → (∀{v : Value} → D (γ `, v) ≃ D′ (δ `, v)) → ℱ D γ ≃ ℱ D′ δ
  cong-ℱ D≃D′ {lit k} = ⟨ (λ x → x) , (λ x → x) ⟩
  cong-ℱ D≃D′ {⊥} = ⟨ (λ x → ⊤.tt) , (λ x → ⊤.tt) ⟩
  cong-ℱ D≃D′ {v ↦ w} = D≃D′
  cong-ℱ {γ = γ}{δ}{D}{D′} D≃D′ {u ⊔ v}
      with cong-ℱ {D = D}{D′} D≃D′ {u} | cong-ℱ {D = D}{D′} D≃D′ {v}
  ... | ⟨ a , b ⟩ | ⟨ c , d ⟩ =
      ⟨ (λ x → ⟨ a (proj₁ x) , c (proj₂ x) ⟩) ,
        (λ x → ⟨ b (proj₁ x) , d (proj₂ x) ⟩) ⟩

  infixl 7 _●_

  _●_ : ∀{Γ} → Denotation Γ → Denotation Γ → Denotation Γ
  _●_ {Γ} D₁ D₂ γ w = w ⊑ ⊥ ⊎ Σ[ v ∈ Value ] D₁ γ (v ↦ w) × D₂ γ v 

  cong-● : ∀{Γ Δ}{γ : Env Γ}{δ : Env  Δ}{D₁ D₂ : Denotation Γ}
            {D₁′ D₂′ : Denotation Δ}
         → D₁ γ ≃ D₁′ δ → D₂ γ ≃ D₂′ δ → (D₁ ● D₂) γ ≃ (D₁′ ● D₂′) δ
  cong-● {γ = γ}{δ}{D₁}{D₂}{D₁′}{D₂′} eq1 eq2 {w}
      with eq1 {w} | eq2 {w}
  ... | ⟨ a , b ⟩ | ⟨ c , d ⟩ = ⟨ G , H ⟩
      where
      G : (D₁ ● D₂) γ w → (D₁′ ● D₂′) δ w
      G (inj₁ w⊑⊥) = inj₁ w⊑⊥
      G (inj₂ ⟨ v , ⟨ D₁γv↦w , D₂γv ⟩ ⟩) =
        inj₂ ⟨ v , ⟨ (proj₁ eq1 D₁γv↦w) , (proj₁ eq2 D₂γv) ⟩ ⟩

      H : (D₁′ ● D₂′) δ w → (D₁ ● D₂) γ w
      H (inj₁ w⊑⊥) = inj₁ w⊑⊥
      H (inj₂ ⟨ v , ⟨ D₁′δv↦w , D₂′δv ⟩ ⟩) =
        inj₂ ⟨ v , ⟨ (proj₂ eq1 D₁′δv↦w) , (proj₂ eq2 D₂′δv) ⟩ ⟩

  ℘ : ∀{P : Prim} → rep P → Value → Set
  ℘ {base B} k (lit {B'} k')
      with base-eq? B B'
  ... | yes refl = k ≡ k'
  ... | no B≠B' = Bot
  ℘ {B ⇒ P} p (lit k) = Bot
  ℘ {base B} p ⊥ = ⊤
  ℘ {B ⇒ P} p ⊥ = ⊤
  ℘ {base B} p (v ↦ w) = Bot
  ℘ {B ⇒ P} f (v ↦ w) = Σ[ k ∈ base-rep B ] v ≡ lit k × ℘ {P} (f k) w
  ℘ {base B} p (u ⊔ v) = ℘ {base B} p u × ℘ {base B} p v
  ℘ {B ⇒ P} p (u ⊔ v) = ℘ {B ⇒ P} p u × ℘ {B ⇒ P} p v  

  module Den = Denot (λ {P} p v → ℘ {P} p v)
                     ℱ
                     _●_
                     (λ {Γ}{Δ}{γ}{δ}{D₁}{D₂}{D₁′}{D₂′} eq1 eq2 →
                       cong-● {Γ}{Δ}{γ}{δ}{D₁}{D₂}{D₁′}{D₂′} eq1 eq2)
                     cong-ℱ

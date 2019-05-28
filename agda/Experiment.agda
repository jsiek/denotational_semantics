
open import LambdaV
   using (_·_; ƛ; Term; lam; app; _—→_; ξ₁-rule; ξ₂-rule; β-rule)
open LambdaV.ASTMod
   using (Var; Z; S_; `_; _⦅_⦆; extensionality; Rename; Subst;
          ext; exts; cons; bind; nil; rename; ⟪_⟫; subst-zero; _[_]; rename-id)
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
open import Data.Unit using (⊤; tt)
open import Data.Empty renaming (⊥ to Bot)
open import Relation.Nullary using (¬_; Dec; yes; no)


module Experiment where


module Domain
  (Value : Set)
{-
  (lit : {B : Base} → base-rep B → Value)
-}
  (_⊔_ : Value → Value → Value)
  (_⊑_ : Value → Value → Set)
  (Refl⊑ : ∀ {v} → v ⊑ v)
  (Trans⊑ : ∀ {u v w} → u ⊑ v → v ⊑ w → u ⊑ w)
  (ConjL⊑ : ∀ {u v w} → v ⊑ u → w ⊑ u → (v ⊔ w) ⊑ u)
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

  _`⊑_ : ∀ {Γ} → Env Γ → Env Γ → Set
  _`⊑_ {Γ} γ δ = (x : Var Γ) → γ x ⊑ δ x

  _`≡_ : ∀ {Γ} → Env Γ → Env Γ → Set
  _`≡_ {Γ} γ δ = (x : Var Γ) → γ x ≡ δ x

  Denotation : ℕ → Set₁
  Denotation Γ = Env Γ → Value → Set

  _≲_ : (Value → Set) → (Value → Set) → Set
  d ≲ d' = ∀{v : Value} → d v → d' v

  ≲-refl : ∀ {M : Value → Set}
         → M ≲ M
  ≲-refl = λ z → z

  ≲-trans : ∀ {d₁ d₂ d₃ : Value → Set}
    → d₁ ≲ d₂
    → d₂ ≲ d₃
      ------- 
    → d₁ ≲ d₃
  ≲-trans m12 m23 = λ z → m23 (m12 z)

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
  (x ≲⟨ x≲y ⟩ y≲z) {v} =  ≲-trans (x≲y{v}) y≲z {v}

  _☐ : ∀ (d : Value → Set)
        -----
      → d ≲ d
  (d ☐) {v} =  ≲-refl {d}

  _iff_ : Set → Set → Set
  P iff Q = (P → Q) × (Q → P)

  
  _≃_ : (Value → Set) → (Value → Set) → Set
  d ≃ d' = ∀{v : Value} → d v iff d' v

  ≃-refl : ∀ {d : Value → Set}
    → d ≃ d
  ≃-refl = ⟨ (λ x → x) , (λ x → x) ⟩

  ≃-trans : ∀ {d₁ d₂ d₃ : Value → Set}
    → d₁ ≃ d₂
    → d₂ ≃ d₃
      ------- 
   → d₁ ≃ d₃
  ≃-trans m12 m23 = ⟨ (λ z → proj₁ m23 (proj₁ m12 z)) ,
                      (λ z → proj₂ m12 (proj₂ m23 z)) ⟩

  infixr 2 _≃⟨⟩_ _≃⟨_⟩_
  infix  3 _□

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

  _□ : ∀ (d : Value → Set)
        -----
      → d ≃ d
  (d □) {v} =  ≃-refl {d}

  record WFDenot (Γ : ℕ) (E : Denotation Γ) : Set₁ where
    field
      ⊑-env : ∀{γ δ}{v} → E γ v → γ `⊑ δ → E δ v
      ⊑-closed : ∀{γ}{v w} → E γ v → w ⊑ v → E γ w
      ⊔-closed : ∀{γ u v} → E γ u → E γ v → E γ (u ⊔ v)

  module Denot
    (ℱ : ∀{Γ} → Denotation (suc Γ) → Denotation Γ)
    (_●_ : ∀{Γ} → Denotation Γ → Denotation Γ → Denotation Γ)
    where
    
    ℰ : ∀{Γ} → Term Γ → Denotation Γ
    ℰ {Γ} (` x) γ v = v ⊑ γ x
    ℰ {Γ} (lam ⦅ bind N nil ⦆) = ℱ (ℰ N)
    ℰ {Γ} (app ⦅ cons L (cons M nil) ⦆) = (ℰ L) ● (ℰ M)

  module RenamePres
    (ℱ : ∀{Γ} → Denotation (suc Γ) → Denotation Γ)
    (_●_ : ∀{Γ} → Denotation Γ → Denotation Γ → Denotation Γ)
    (ℱ-≲ : ∀{Γ Δ}{γ : Env Γ}{δ : Env Δ}{D : Denotation (suc Γ)}
            {D′ : Denotation (suc Δ)}
         → (∀{v : Value} → D (γ `, v) ≲ D′ (δ `, v))
         → ℱ D γ ≲ ℱ D′ δ)
    (●-≲ : ∀{Γ Δ}{γ : Env Γ}{δ : Env  Δ}{D₁ D₂ : Denotation Γ}
            {D₁′ D₂′ : Denotation Δ}
         → D₁ γ ≲ D₁′ δ  →  D₂ γ ≲ D₂′ δ
         → (D₁ ● D₂) γ ≲ (D₁′ ● D₂′) δ)
    where
    module Den = Denot ℱ _●_
    open Den

    rename-pres : ∀ {Γ Δ v} {γ : Env Γ} {δ : Env Δ} {M : Term Γ}
           → (ρ : Rename Γ Δ)
           → γ `⊑ (δ ∘ ρ)
           → ℰ M γ v
             ------------------
           → ℰ (rename ρ M) δ v
    rename-pres {M = ` x} ρ γ⊑δ∘ρ ℰMγv = Trans⊑ ℰMγv (γ⊑δ∘ρ x)
    rename-pres {v = v}{γ}{δ}{lam ⦅ bind N nil ⦆} ρ γ⊑δ∘ρ =
       ℱ-≲ λ {v} → rename-pres {γ = γ `, v}{δ = δ `, v}{M = N} (ext ρ) H
       where
       H : ∀{v} → (γ `, v) `⊑ ((λ {x} → δ `, v) ∘ ext ρ)
       H {v} Z = Refl⊑
       H {v} (S x) = γ⊑δ∘ρ x
    rename-pres {M = app ⦅ cons L (cons M nil) ⦆} ρ γ⊑δ∘ρ =
      ●-≲ (rename-pres {M = L} ρ γ⊑δ∘ρ) (rename-pres {M = M} ρ γ⊑δ∘ρ)

    Env⊑ : ∀ {Γ} {γ : Env Γ} {δ : Env Γ} {M v}
      → ℰ M γ v
      → γ `⊑ δ
        ----------
      → ℰ M δ v
    Env⊑{Γ}{γ}{δ}{M}{v} d lt
          with rename-pres{Γ}{Γ}{v}{γ}{δ}{M} (λ x → x) lt d
    ... | d′ rewrite rename-id {Γ}{M} =
          d′

    EnvExt⊑ : ∀ {Γ} {γ : Env Γ} {M v u₁ u₂}
      → ℰ M (γ `, u₁) v
      → u₁ ⊑ u₂
        -----------------
      → ℰ M (γ `, u₂) v
    EnvExt⊑ {M = M} d lt = Env⊑{M = M} d (env-le lt)
      where
      env-le : ∀ {γ u₁ u₂} → u₁ ⊑ u₂ → (γ `, u₁) `⊑ (γ `, u₂)
      env-le lt Z = lt
      env-le lt (S n) = Refl⊑
    
  
  module DenotProps
    (ℱ : ∀{Γ} → Denotation (suc Γ) → Denotation Γ)
    (_●_ : ∀{Γ} → Denotation Γ → Denotation Γ → Denotation Γ)
    (ℱ-≲ : ∀{Γ Δ}{γ : Env Γ}{δ : Env Δ}{D : Denotation (suc Γ)}
            {D′ : Denotation (suc Δ)}
         → (∀{v : Value} → D (γ `, v) ≲ D′ (δ `, v))
         → ℱ D γ ≲ ℱ D′ δ)
    (●-≲ : ∀{Γ Δ}{γ : Env Γ}{δ : Env  Δ}{D₁ D₂ : Denotation Γ}
            {D₁′ D₂′ : Denotation Δ}
         → D₁ γ ≲ D₁′ δ  →  D₂ γ ≲ D₂′ δ
         → (D₁ ● D₂) γ ≲ (D₁′ ● D₂′) δ)
    (●-⊑ : ∀{Γ}{D₁ D₂ : Denotation Γ} {γ : Env Γ} {v w : Value}
         → WFDenot Γ D₁ → (D₁ ● D₂) γ v → w ⊑ v → (D₁ ● D₂) γ w)
    (ℱ-⊑ : ∀{Γ}{D : Denotation (suc Γ)}{γ : Env Γ} {v w : Value}
         → WFDenot (suc Γ) D → ℱ D γ v → w ⊑ v → ℱ D γ w)
    (ℱ-⊔ : ∀{Γ}{D : Denotation (suc Γ)}{γ : Env Γ} {u v : Value}
          → ℱ D γ u → ℱ D γ v → ℱ D γ (u ⊔ v))
    (●-⊔ : ∀{Γ}{D₁ D₂ : Denotation Γ}{γ : Env Γ} {u v : Value}
      → (∀{v w} → D₁ γ v → w ⊑ v → D₁ γ w)
      → (∀{u v} → D₁ γ u → D₁ γ v → D₁ γ (u ⊔ v))
      → (∀{u v} → D₂ γ u → D₂ γ v → D₂ γ (u ⊔ v))
      → (D₁ ● D₂) γ u → (D₁ ● D₂) γ v → (D₁ ● D₂) γ (u ⊔ v))
    where
    
    module Den = Denot ℱ _●_
    open Den

    cong-ℱ : ∀{Γ Δ}{γ : Env Γ}{δ : Env Δ}{D : Denotation (suc Γ)}
              {D′ : Denotation (suc Δ)}
           → (∀{v : Value} → D (γ `, v) ≃ D′ (δ `, v))
           → ℱ D γ ≃ ℱ D′ δ
    cong-ℱ {D = D}{D′} D≃D′ {v} =
      ⟨ (ℱ-≲ (proj₁ D≃D′)) {v = v} , (ℱ-≲ (proj₂ D≃D′)) {v = v} ⟩
  
    cong-● : ∀{Γ Δ}{γ : Env Γ}{δ : Env  Δ}{D₁ D₂ : Denotation Γ}
              {D₁′ D₂′ : Denotation Δ}
           → D₁ γ ≃ D₁′ δ → D₂ γ ≃ D₂′ δ → (D₁ ● D₂) γ ≃ (D₁′ ● D₂′) δ
    cong-● {γ = γ}{δ}{D₁}{D₂}{D₁′}{D₂′} eq1 eq2 {w} =
      ⟨ (●-≲{D₁ = D₁}{D₂}{D₁′}{D₂′} (proj₁ eq1) (proj₁ eq2)) {v = w} ,
        (●-≲{D₁ = D₁′}{D₂′}{D₁}{D₂} (proj₂ eq1) (proj₂ eq2)) {v = w} ⟩


    {- unused -}
    rename-equiv : ∀ {Γ Δ} {γ : Env Γ} {δ : Env Δ} {M : Term Γ}
                     {ρ : Rename Γ Δ}
      → γ `≡ (δ ∘ ρ)
      → ℰ M γ ≃ ℰ (rename ρ M) δ
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

    module RP = RenamePres ℱ _●_ ℱ-≲
                       (λ {Γ}{Δ}{γ}{δ}{D₁}{D₂}{D₁′}{D₂′} leq1 leq2 →
                         ●-≲ {Γ}{Δ}{γ}{δ}{D₁}{D₂}{D₁′}{D₂′} leq1 leq2)
    open RP using (Env⊑; rename-pres)  

    ℰ-⊔ : ∀{Γ} {γ : Env Γ} {M : Term Γ} {u v : Value}
        → ℰ M γ u → ℰ M γ v → ℰ M γ (u ⊔ v)
    ℰ-⊑ : ∀{Γ} {γ : Env Γ} {M : Term Γ} {v w : Value}
        → ℰ M γ v → w ⊑ v → ℰ M γ w
        
    ℰ-⊔ {M = ` x} ℰMγu ℰMγv = ConjL⊑ ℰMγu ℰMγv
    ℰ-⊔ {M = lam ⦅ bind N nil ⦆} ℰMγu ℰMγv = ℱ-⊔ ℰMγu ℰMγv
    ℰ-⊔ {γ = γ}{app ⦅ cons L (cons M nil) ⦆} ℰMγu ℰMγv =
       let a = ℰ-⊔ {γ = γ} {M = L} in
       let b = ℰ-⊔ {γ = γ} {M = M} in
       let c = ℰ-⊑ {γ = γ} {M = L} in
       ●-⊔ c a b ℰMγu ℰMγv
        
    ℰ-⊑ {M = ` x} ℰMγv w⊑v = Trans⊑ w⊑v ℰMγv
    ℰ-⊑ {Γ}{γ}{lam ⦅ bind N nil ⦆}{v}{w} ℰMγv w⊑v =
      ℱ-⊑ G ℰMγv w⊑v
      where G : WFDenot (suc Γ) (ℰ N)
            G = record { ⊑-env = Env⊑{M = N} ;
                         ⊑-closed = λ{γ}{v}{w} ℰNv w⊑v → ℰ-⊑ {M = N} ℰNv w⊑v ;
                         ⊔-closed = λ{γ}{u}{v} ℰNu ℰNv → ℰ-⊔ {M = N} ℰNu ℰNv  }

    ℰ-⊑ {Γ}{γ} {app ⦅ cons L (cons M nil) ⦆} {v} {w} ℰMγv w⊑v =
       ●-⊑ G ℰMγv w⊑v
       where G : WFDenot Γ (ℰ L)
             G = record { ⊑-env = Env⊑{M = L} ;
                          ⊑-closed = λ{γ}{v}{w} ℰLv w⊑v → ℰ-⊑ {M = L} ℰLv w⊑v ;
                          ⊔-closed = λ{γ}{u}{v} ℰLu ℰLv → ℰ-⊔ {M = L} ℰLu ℰLv }

    infix 3 _`⊢_↓_
    _`⊢_↓_ : ∀{Δ Γ} → Env Δ → Subst Γ Δ → Env Γ → Set
    _`⊢_↓_ {Δ}{Γ} δ σ γ = (∀ (x : Var Γ) → ℰ (σ x) δ (γ x))

    subst-ext : ∀ {Γ Δ v} {γ : Env Γ} {δ : Env Δ}
      → (σ : Subst Γ Δ)
      → δ `⊢ σ ↓ γ
       --------------------------
      → δ `, v `⊢ exts σ ↓ γ `, v
    subst-ext σ d Z = Refl⊑
    subst-ext σ d (S x′) = rename-pres {M = σ x′} S_ (λ _ → Refl⊑) (d x′)

    subst-pres : ∀ {Γ Δ v} {γ : Env Γ} {δ : Env Δ} {M : Term Γ}
      → (σ : Subst Γ Δ)
      → δ `⊢ σ ↓ γ
      → ℰ M γ v
        ------------------
      → ℰ (⟪ σ ⟫ M) δ v
    subst-pres {M = ` x} σ δ⊢σ↓γ ℰMγv = ℰ-⊑ {M = σ x} (δ⊢σ↓γ x) ℰMγv
    subst-pres {Γ}{Δ}{v}{γ}{δ}{lam ⦅ bind N nil ⦆} σ δ⊢σ↓γ ℰMγv =
       (ℱ-≲ {Γ}{Δ}{γ}{δ}{ℰ N}{ℰ (⟪ exts σ ⟫ N)}
             λ {v} → subst-pres {γ = γ `, v}{δ = δ `, v}{M = N} (exts σ) (subst-ext σ δ⊢σ↓γ))
        ℰMγv
    subst-pres {Γ}{Δ}{v}{γ}{δ}{app ⦅ cons L (cons M nil) ⦆} σ δ⊢σ↓γ ℰMγv =
       (●-≲{Γ}{Δ}{γ}{δ}{D₁ = ℰ L}{D₂ = ℰ M}{D₁′ = ℰ (⟪ σ ⟫ L)}{D₂′ = ℰ (⟪ σ ⟫ M)}
            (λ ℰLγv → subst-pres {Γ}{Δ}{γ = γ}{δ}{L} σ δ⊢σ↓γ ℰLγv)
            (λ ℰMδv → subst-pres {Γ}{Δ}{γ = γ}{δ}{M} σ δ⊢σ↓γ ℰMδv))
        ℰMγv

    substitution : ∀ {Γ} {γ : Env Γ} {N M v w}
       → ℰ N (γ `, v) w
       → ℰ M γ v
         ---------------
       → ℰ (N [ M ]) γ w   
    substitution{Γ}{γ}{N}{M}{v}{w} dn dm =
      subst-pres{M = N} (subst-zero M) sub-z-ok dn
      where
      sub-z-ok : γ `⊢ subst-zero M ↓ (γ `, v)
      sub-z-ok Z = dm
      sub-z-ok (S x) = Refl⊑

    preserve : ∀ {Γ} {γ : Env Γ} {M N v}
      → ℰ M γ v
      → M —→ N
        ----------
      → ℰ N γ v
    preserve {γ = γ} ℰL●ℰMγv (ξ₁-rule{L = L}{L´}{M} L—→L′) =
      (●-≲ {γ = γ}{γ}{D₁ = ℰ L}{D₂ = ℰ M}{D₁′ = ℰ L´}{D₂′ = ℰ M}
                  (λ x → preserve x L—→L′)
                  (λ x → x))
       ℰL●ℰMγv
    preserve {γ = γ} ℰL●ℰMγv (ξ₂-rule{L = L}{M}{M′} Lv M—→M′) =
      (●-≲ {γ = γ}{γ}{D₁ = ℰ L}{D₂ = ℰ M}{D₁′ = ℰ L}{D₂′ = ℰ M′}
                  (λ x → x)
                  (λ x → preserve x M—→M′))
       ℰL●ℰMγv
    preserve {γ = γ}{M}{N}{v} ℱℰN●ℰMγv (β-rule Mv) = substitution {!!} {!!}



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

  module Dom = Domain Value _⊔_ _⊑_ Refl⊑ Trans⊑ ConjL⊑
  open Dom

  ℱ : ∀{Γ} → Denotation (suc Γ) → Denotation Γ
  ℱ D γ (v ↦ w) = D (γ `, v) w
  ℱ D γ ⊥ = ⊤
  ℱ D γ (u ⊔ v) = (ℱ D γ u) × (ℱ D γ v)
  ℱ D γ (lit k) = Bot

  infixl 7 _●_
  _●_ : ∀{Γ} → Denotation Γ → Denotation Γ → Denotation Γ
  _●_ {Γ} D₁ D₂ γ w = w ⊑ ⊥ ⊎ Σ[ v ∈ Value ] D₁ γ (v ↦ w) × D₂ γ v 

  ℘ : ∀{P : Prim} → rep P → Value → Set
  ℘ {base B} k (lit {B'} k')
      with base-eq? B B'
  ... | yes refl = k ≡ k'
  ... | no B≠B' = Bot
  ℘ {B ⇒ P} p (lit k) = Bot
  ℘ {base B} p ⊥ = ⊤
  ℘ {B ⇒ P} p ⊥ = ⊤
  ℘ {base B} p (v ↦ w) = Bot
  ℘ {B ⇒ P} f (v ↦ w) = Σ[ k ∈ base-rep B ] lit k ⊑ v × ℘ {P} (f k) w
  ℘ {base B} p (u ⊔ v) = ℘ {base B} p u × ℘ {base B} p v
  ℘ {B ⇒ P} p (u ⊔ v) = ℘ {B ⇒ P} p u × ℘ {B ⇒ P} p v


  ℱ-≲ : ∀{Γ Δ}{γ : Env Γ}{δ : Env Δ}{D : Denotation (suc Γ)}
            {D′ : Denotation (suc Δ)}
         → (∀{v : Value} → D (γ `, v) ≲ D′ (δ `, v))
         → ℱ D γ ≲ ℱ D′ δ
  ℱ-≲ D≲D′ {lit x} = λ z → z
  ℱ-≲ D≲D′ {⊥} = λ _ → tt
  ℱ-≲ D≲D′ {v ↦ w} = D≲D′
  ℱ-≲ {D = D}{D′} D≲D′ {u ⊔ v} ℱDγ
      with ℱ-≲{D = D}{D′} D≲D′ {u} | ℱ-≲{D = D}{D′} D≲D′ {v}
  ... | a | b =
      ⟨ (a (proj₁ ℱDγ)) , (b (proj₂ ℱDγ)) ⟩

  cong-ℱ : ∀{Γ Δ}{γ : Env Γ}{δ : Env Δ}{D : Denotation (suc Γ)}
            {D′ : Denotation (suc Δ)}
         → (∀{v : Value} → D (γ `, v) ≃ D′ (δ `, v))
         → ℱ D γ ≃ ℱ D′ δ
  cong-ℱ {D = D}{D′} D≃D′ {v} =
    ⟨ (ℱ-≲ (proj₁ D≃D′)) {v = v} , (ℱ-≲ (proj₂ D≃D′)) {v = v} ⟩
  
  ●-≲ : ∀{Γ Δ}{γ : Env Γ}{δ : Env  Δ}{D₁ D₂ : Denotation Γ}
            {D₁′ D₂′ : Denotation Δ}
         → D₁ γ ≲ D₁′ δ  →  D₂ γ ≲ D₂′ δ
         → (D₁ ● D₂) γ ≲ (D₁′ ● D₂′) δ
  ●-≲ {γ = γ} {δ} {D₁} {D₂} {D₁′} {D₂′} D₁γ≲D₁′δ D₂γ≲D₂′δ {w} (inj₁ w⊑⊥) =
     inj₁ w⊑⊥
  ●-≲ {γ = γ} {δ} {D₁} {D₂} {D₁′} {D₂′} D₁γ≲D₁′δ D₂γ≲D₂′δ {w}
      (inj₂ ⟨ v , ⟨ fst₁ , snd ⟩ ⟩)
      with D₁γ≲D₁′δ {w} | D₂γ≲D₂′δ {w}
  ... | a | b = inj₂ ⟨ v , ⟨ (D₁γ≲D₁′δ fst₁) , (D₂γ≲D₂′δ snd) ⟩ ⟩

  module RP = RenamePres ℱ _●_ ℱ-≲
                     (λ {Γ}{Δ}{γ}{δ}{D₁}{D₂}{D₁′}{D₂′} leq1 leq2 →
                       ●-≲ {Γ}{Δ}{γ}{δ}{D₁}{D₂}{D₁′}{D₂′} leq1 leq2)
  open RP using (Env⊑)  

  ℱ-⊔ : ∀{Γ}{D : Denotation (suc Γ)}{γ : Env Γ} {u v : Value}
      → ℱ D γ u → ℱ D γ v → ℱ D γ (u ⊔ v)
  ℱ-⊔ d1 d2 = ⟨ d1 , d2 ⟩

  ●-⊔ : ∀{Γ}{D₁ D₂ : Denotation Γ}{γ : Env Γ} {u v : Value}
      → (∀{v w} → D₁ γ v → w ⊑ v → D₁ γ w)
      → (∀{u v} → D₁ γ u → D₁ γ v → D₁ γ (u ⊔ v))
      → (∀{u v} → D₂ γ u → D₂ γ v → D₂ γ (u ⊔ v))
      → (D₁ ● D₂) γ u → (D₁ ● D₂) γ v → (D₁ ● D₂) γ (u ⊔ v)
  ●-⊔ {u = u} {v} sub cup1 cup2 (inj₁ u⊑⊥) (inj₁ v⊑⊥) = inj₁ (ConjL⊑ u⊑⊥ v⊑⊥)
  ●-⊔ {u = u} {v} sub cup1 cup2 (inj₁ u⊑⊥) (inj₂ ⟨ v' , ⟨ fst₁ , snd ⟩ ⟩) =
    inj₂ ⟨ v' , ⟨ sub fst₁ lt , snd ⟩ ⟩
    where lt : v' ↦ (u ⊔ v) ⊑ v' ↦ v
          lt = Fun⊑ Refl⊑ (ConjL⊑ (Trans⊑ u⊑⊥ Bot⊑) Refl⊑)
  ●-⊔ {u = u} {v} sub cup1 cup2 (inj₂ ⟨ u' , ⟨ fst₁ , snd ⟩ ⟩) (inj₁ v⊑⊥) =
    inj₂ ⟨ u' , ⟨ (sub fst₁ lt) , snd ⟩ ⟩
    where lt : u' ↦ (u ⊔ v) ⊑ u' ↦ u
          lt = Fun⊑ Refl⊑ (ConjL⊑ Refl⊑ (Trans⊑ v⊑⊥ Bot⊑))
  ●-⊔ {Γ}{D₁}{D₂}{γ}{u}{v} sub cup1 cup2 (inj₂ ⟨ u' , ⟨ fst₁ , snd ⟩ ⟩)
                      (inj₂ ⟨ v' , ⟨ fst₃ , snd₁ ⟩ ⟩) =
    let a = cup1 fst₁ fst₃ in                      
    inj₂ ⟨ (u' ⊔ v') , ⟨  sub a Dist⊔↦⊔ , cup2 snd snd₁ ⟩ ⟩

{-
  ℘-⊔ : ∀{P : Prim}{p : rep P}{u v : Value} → ℘ {P} p u → ℘ {P} p v → ℘ {P} p (u ⊔ v)
  ℘-⊔ {base x} pu pv = ⟨ pu , pv ⟩
  ℘-⊔ {x ⇒ P} pu pv = ⟨ pu , pv ⟩

  ℘-⊑ : ∀{P : Prim}{p : rep P}{v w : Value} → ℘ {P} p v → w ⊑ v → ℘ {P} p w
  ℘-⊑ {base B} pv Bot⊑ = tt
  ℘-⊑ {base B} pv Lit⊑ = pv
  ℘-⊑ {base B}{v}{w} pv (ConjL⊑{v = v'}{w = w'} v'⊑w w'⊑w) =
     ⟨ ℘-⊑ {base B} pv v'⊑w , ℘-⊑ {base B} pv w'⊑w ⟩
  ℘-⊑ {base B}{w = w} ⟨ ℘v , ℘w ⟩ (ConjR1⊑ {w} {v} {w'} w⊑v) = ℘-⊑ {base B} ℘v w⊑v
  ℘-⊑ {base B} ⟨ fst , snd ⟩ (ConjR2⊑ w⊑v) = ℘-⊑ {base B} snd w⊑v
  ℘-⊑ {base B} pv (Trans⊑ w⊑v w⊑v₁) = ℘-⊑ {base B} (℘-⊑ {base B} pv w⊑v₁) w⊑v
  ℘-⊑ {base B} () (Fun⊑ w⊑v w⊑v₁)
  ℘-⊑ {base B} ⟨ fst , snd ⟩ Dist⊑ = snd
  
  ℘-⊑ {B ⇒ P} pv Bot⊑ = tt
  ℘-⊑ {B ⇒ P} pv Lit⊑ = pv
  ℘-⊑ {B ⇒ P} pv (ConjL⊑ w⊑v w⊑v₁) = ⟨ ℘-⊑ {B ⇒ P} pv w⊑v , ℘-⊑ {B ⇒ P} pv w⊑v₁ ⟩
  ℘-⊑ {B ⇒ P} ⟨ fst , snd ⟩ (ConjR1⊑ w⊑v) = ℘-⊑ {B ⇒ P} fst w⊑v
  ℘-⊑ {B ⇒ P} ⟨ fst , snd ⟩ (ConjR2⊑ w⊑v) = ℘-⊑ {B ⇒ P} snd w⊑v
  ℘-⊑ {B ⇒ P} pv (Trans⊑ w⊑v w⊑v₁) = ℘-⊑ {B ⇒ P} (℘-⊑ {B ⇒ P} pv w⊑v₁) w⊑v
  ℘-⊑ {B ⇒ P}{f} ⟨ k , ⟨ v′⊑k , ℘fkw′ ⟩ ⟩ (Fun⊑{v}{w}{v´}{w′} w⊑v w⊑v₁) =
      ⟨ k , ⟨ Trans⊑ v′⊑k w⊑v , ℘-⊑ {P}{f k} ℘fkw′ w⊑v₁ ⟩ ⟩
  ℘-⊑ {B ⇒ P} ⟨ ⟨ k , ⟨ fst , snd₁ ⟩ ⟩ , ⟨ k' , ⟨ fst₁ , snd ⟩ ⟩ ⟩ (Dist⊑{v = v}) = {!!}
-}


  ℱ-⊑ : ∀{Γ}{D : Denotation (suc Γ)}{γ : Env Γ} {v w : Value}
         → WFDenot (suc Γ) D
         → ℱ D γ v → w ⊑ v → ℱ D γ w
  ℱ-⊑ d ℱDγv Bot⊑ = tt
  ℱ-⊑ d ℱDγv Lit⊑ = ℱDγv
  ℱ-⊑ d ℱDγv (ConjL⊑ w⊑v w⊑v₁) = ⟨ (ℱ-⊑ d ℱDγv w⊑v) , (ℱ-⊑ d ℱDγv w⊑v₁) ⟩
  ℱ-⊑ d ℱDγv (ConjR1⊑ w⊑v) = ℱ-⊑ d (proj₁ ℱDγv) w⊑v
  ℱ-⊑ d ℱDγv (ConjR2⊑ w⊑v) = ℱ-⊑ d (proj₂ ℱDγv) w⊑v
  ℱ-⊑ d ℱDγv (Trans⊑ w⊑v w⊑v₁) = ℱ-⊑ d (ℱ-⊑ d ℱDγv w⊑v₁) w⊑v
  ℱ-⊑ {Γ}{D}{γ}{v ↦ w}{v' ↦ w'} d ℱDγv (Fun⊑ v⊑v' w'⊑w) =
    WFDenot.⊑-closed d (WFDenot.⊑-env d ℱDγv b) w'⊑w
    where b : (γ `, v) `⊑ (γ `, v')
          b Z = v⊑v'
          b (S x) = Refl⊑ 
  ℱ-⊑ d ℱDγv Dist⊑ = WFDenot.⊔-closed d (proj₁ ℱDγv) (proj₂ ℱDγv)

  ●-⊑ : ∀{Γ}{D₁ D₂ : Denotation Γ} {γ : Env Γ} {v w : Value}
         → WFDenot Γ D₁ → (D₁ ● D₂) γ v → w ⊑ v
         → (D₁ ● D₂) γ w
  ●-⊑ d (inj₁ x) w⊑v = inj₁ (Trans⊑ w⊑v x)
  ●-⊑ {v = v}{w} d (inj₂ ⟨ v' , ⟨ fst₁ , snd ⟩ ⟩) w⊑v =
    inj₂ ⟨ v' , ⟨ WFDenot.⊑-closed d fst₁ lt  , snd ⟩ ⟩
    where lt : v' ↦ w ⊑ v' ↦ v
          lt = Fun⊑ Refl⊑ w⊑v




  module Den = DenotProps
                     ℱ
                     _●_
                     ℱ-≲
                     (λ {Γ}{Δ}{γ}{δ}{D₁}{D₂}{D₁′}{D₂′} leq1 leq2 →
                       ●-≲ {Γ}{Δ}{γ}{δ}{D₁}{D₂}{D₁′}{D₂′} leq1 leq2)
                     (λ {Γ}{D₁}{D₂}{γ}{v}{w} x x₁ x₂ →
                         ●-⊑ {Γ}{D₁}{D₂}{γ}{v}{w} x x₁ x₂)
                     ℱ-⊑
                     (λ {Γ}{D}{γ}{u}{v} du dv → ℱ-⊔ {Γ}{D}{γ}{u}{v} du dv)
                     (λ {Γ}{D₁}{D₂}{γ}{u}{v} a b c d e →
                       ●-⊔{Γ}{D₁}{D₂}{γ}{u}{v} a b c d e)

  open Den

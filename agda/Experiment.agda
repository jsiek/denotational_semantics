
open import LambdaV
   using (_·_; ƛ; Term; lam; app)
open LambdaV.ASTMod
   using (Var; Z; S_; `_; _⦅_⦆; extensionality; Rename; Subst;
          ext; exts; cons; bind; nil; rename; ⟪_⟫; subst-zero; _[_]; rename-id)
open import Primitives
   using (Base; Prim; rep; base; base-rep; _⇒_; base-eq?)


open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; sym; cong; cong₂; cong-app)
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

infixr 7 _↦_
infixl 5 _⊔_

data Value : Set where
  ⊥ : Value
  _↦_ : Value → Value → Value
  _⊔_ : Value → Value → Value

Env : ℕ → Set
Env Γ = Var Γ → Value

Denotation : ℕ → Set₁
Denotation Γ = Env Γ → Value → Set

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

_`⊔_ : ∀ {Γ} → Env Γ → Env Γ → Env Γ
(γ `⊔ δ) x = γ x ⊔ δ x

ℱ : ∀{Γ} → Denotation (suc Γ) → Denotation Γ
ℱ D γ (v ↦ w) = D (γ `, v) w
ℱ D γ ⊥ = ⊤
ℱ D γ (u ⊔ v) = (ℱ D γ u) × (ℱ D γ v)

ℱ-⊔ : ∀{Γ}{D : Denotation (suc Γ)}{γ : Env Γ} {u v : Value}
    → ℱ D γ u → ℱ D γ v → ℱ D γ (u ⊔ v)
ℱ-⊔ d1 d2 = ⟨ d1 , d2 ⟩

ℱ-⊥ : ∀{Γ}{D : Denotation (suc Γ)}{γ : Env Γ}
    → ℱ D γ ⊥
ℱ-⊥ = tt

_≲_ : (Value → Set) → (Value → Set) → Set
d ≲ d' = ∀{v : Value} → d v → d' v

≲-refl : ∀ {d : Value → Set}
       → d ≲ d
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

ℱ-≲ : ∀{Γ Δ}{γ : Env Γ}{δ : Env Δ}{D : Denotation (suc Γ)}
          {D′ : Denotation (suc Δ)}
       → (∀{v : Value} → D (γ `, v) ≲ D′ (δ `, v))
       → ℱ D γ ≲ ℱ D′ δ
ℱ-≲ D≲D′ {⊥} = λ _ → tt
ℱ-≲ D≲D′ {v ↦ w} = D≲D′
ℱ-≲ {D = D}{D′} D≲D′ {u ⊔ v} ℱDγ
    with ℱ-≲{D = D}{D′} D≲D′ {u} | ℱ-≲{D = D}{D′} D≲D′ {v}
... | a | b =
    ⟨ (a (proj₁ ℱDγ)) , (b (proj₂ ℱDγ)) ⟩


record ValueOrder : Set₁ where
  infix 4 _⊑_
  field
    _⊑_ : Value → Value → Set
    ⊑-refl : ∀ {v} → v ⊑ v
    ⊑-trans : ∀ {u v w} → u ⊑ v → v ⊑ w → u ⊑ w
    ⊑-conj-L : ∀ {u v w} → v ⊑ u → w ⊑ u → v ⊔ w ⊑ u
    ⊑-conj-R1 : ∀ {u v w} → u ⊑ v → u ⊑ v ⊔ w
    ⊑-conj-R2 : ∀ {u v w} → u ⊑ w → u ⊑ v ⊔ w
    ⊑-fun : ∀ {v w v′ w′} → v′ ⊑ v → w ⊑ w′ → v ↦ w ⊑ v′ ↦ w′
    ⊑-dist : ∀{v w w′} → v ↦ (w ⊔ w′) ⊑ v ↦ w ⊔ v ↦ w′

record ValueOrderWithBot (dom : ValueOrder) : Set₁ where
  open ValueOrder dom
  field
    ⊑-⊥ : ∀ {v} → ⊥ ⊑ v

module ValueOrderAux (D : ValueOrder) where

  open ValueOrder D

  ⊔⊑⊔ : ∀ {v w v′ w′}
        → v ⊑ v′  →  w ⊑ w′
          -----------------------
        → (v ⊔ w) ⊑ (v′ ⊔ w′)
  ⊔⊑⊔ d₁ d₂ = ⊑-conj-L (⊑-conj-R1 d₁) (⊑-conj-R2 d₂)

  Dist⊔↦⊔ : ∀{v v′ w w′ : Value}
          → ((v ⊔ v′) ↦ (w ⊔ w′)) ⊑ ((v ↦ w) ⊔ (v′ ↦ w′))
  Dist⊔↦⊔ = ⊑-trans ⊑-dist (⊔⊑⊔ (⊑-fun (⊑-conj-R1 ⊑-refl) ⊑-refl)
                              (⊑-fun (⊑-conj-R2 ⊑-refl) ⊑-refl))

  infixr 2 _⊑⟨⟩_ _⊑⟨_⟩_
  infix  3 _◼

  _⊑⟨⟩_ : ∀ (x : Value) {y : Value}
      → x ⊑ y
        -----
      → x ⊑ y
  x ⊑⟨⟩ x⊑y  = x⊑y

  _⊑⟨_⟩_ : ∀ (x : Value) {y z : Value}
      → x ⊑ y
      → y ⊑ z
        -----
      → x ⊑ z
  (x ⊑⟨ x⊑y ⟩ y⊑z) =  ⊑-trans x⊑y y⊑z

  _◼ : ∀ (v : Value)
        -----
      → v ⊑ v
  (v ◼) =  ⊑-refl


  _`⊑_ : ∀ {Γ} → Env Γ → Env Γ → Set
  _`⊑_ {Γ} γ δ = (x : Var Γ) → γ x ⊑ δ x

  _`≡_ : ∀ {Γ} → Env Γ → Env Γ → Set
  _`≡_ {Γ} γ δ = (x : Var Γ) → γ x ≡ δ x

  `Refl⊑ : ∀ {Γ} {γ : Env Γ} → γ `⊑ γ
  `Refl⊑ {Γ} {γ} x = ⊑-refl {γ x}
  
  EnvConjR1⊑ : ∀ {Γ} → (γ : Env Γ) → (δ : Env Γ) → γ `⊑ (γ `⊔ δ)
  EnvConjR1⊑ γ δ x = ⊑-conj-R1 ⊑-refl

  EnvConjR2⊑ : ∀ {Γ} → (γ : Env Γ) → (δ : Env Γ) → δ `⊑ (γ `⊔ δ)
  EnvConjR2⊑ γ δ x = ⊑-conj-R2 ⊑-refl
  

  record WFDenot (Γ : ℕ) (E : Denotation Γ) : Set₁ where
    field
      ⊑-env : ∀{γ δ}{v} → E γ v → γ `⊑ δ → E δ v
      ⊑-closed : ∀{γ}{v w} → E γ v → w ⊑ v → E γ w
      ⊔-closed : ∀{γ u v} → E γ u → E γ v → E γ (u ⊔ v)

  record ModelCong
         (_●_ : ∀{Γ} → Denotation Γ → Denotation Γ → Denotation Γ)
         : Set₁ where
    field
      ●-≲ : ∀{Γ Δ}{γ : Env Γ}{δ : Env  Δ}{D₁ D₂ : Denotation Γ}
              {D₁′ D₂′ : Denotation Δ}
           → D₁ γ ≲ D₁′ δ  →  D₂ γ ≲ D₂′ δ
           → (D₁ ● D₂) γ ≲ (D₁′ ● D₂′) δ


module InValueOrder (D : ValueOrder) where

  open ValueOrder D
  open ValueOrderAux D

  record ModelBasics
         (_●_ : ∀{Γ} → Denotation Γ → Denotation Γ → Denotation Γ)
         : Set₁ where
    field
      Cong : ModelCong _●_
      ●-⊑ : ∀{Γ}{D₁ D₂ : Denotation Γ} {γ : Env Γ} {v w : Value}
           → WFDenot Γ D₁ → (D₁ ● D₂) γ v → w ⊑ v → (D₁ ● D₂) γ w
      ℱ-⊑ : ∀{Γ}{D : Denotation (suc Γ)}{γ : Env Γ} {v w : Value}
           → WFDenot (suc Γ) D → ℱ D γ v → w ⊑ v → ℱ D γ w
      ●-⊔ : ∀{Γ}{D₁ D₂ : Denotation Γ}{γ : Env Γ} {u v : Value}
           → WFDenot Γ D₁ → WFDenot Γ D₂
           → (D₁ ● D₂) γ u → (D₁ ● D₂) γ v → (D₁ ● D₂) γ (u ⊔ v)
           
  module Denot
    (_●_ : ∀{Γ} → Denotation Γ → Denotation Γ → Denotation Γ)
    where
    
    ℰ : ∀{Γ} → Term Γ → Denotation Γ
    ℰ {Γ} (` x) γ v = v ⊑ γ x
    ℰ {Γ} (lam ⦅ bind N nil ⦆) = ℱ (ℰ N)
    ℰ {Γ} (app ⦅ cons L (cons M nil) ⦆) = (ℰ L) ● (ℰ M)

    infix 3 _`⊢_↓_
    _`⊢_↓_ : ∀{Δ Γ} → Env Δ → Subst Γ Δ → Env Γ → Set
    _`⊢_↓_ {Δ}{Γ} δ σ γ = (∀ (x : Var Γ) → ℰ (σ x) δ (γ x))

  module RenamePreserveReflect
    (_●_ : ∀{Γ} → Denotation Γ → Denotation Γ → Denotation Γ)
    (Cong : ModelCong _●_)
    where
    
    module Den = Denot _●_
    open Den
    open ModelCong Cong

    rename-pres : ∀ {Γ Δ v} {γ : Env Γ} {δ : Env Δ} {M : Term Γ}
           → (ρ : Rename Γ Δ)
           → γ `⊑ (δ ∘ ρ)
           → ℰ M γ v
             ------------------
           → ℰ (rename ρ M) δ v
    rename-pres {v = v}{γ}{δ}{` x} ρ γ⊑δ∘ρ ℰMγv =
        v  ⊑⟨ ℰMγv ⟩ γ x  ⊑⟨ γ⊑δ∘ρ x ⟩ δ (ρ x) ◼
    rename-pres {Γ}{Δ}{v}{γ}{δ}{lam ⦅ bind N nil ⦆} ρ γ⊑δ∘ρ =
       ℱ-≲ {Γ}{Δ}{γ}{δ}{ℰ N}{ℰ (rename (ext ρ) N)} IH {v}
       where
       H : ∀{v} → (γ `, v) `⊑ ((λ {x} → δ `, v) ∘ ext ρ)
       H {v} Z = ⊑-refl
       H {v} (S x) = γ⊑δ∘ρ x

       IH : ∀ {v₁} → ℰ N (γ `, v₁) ≲ ℰ (rename (ext ρ) N) (δ `, v₁)
       IH {v} = rename-pres {γ = γ `, v}{δ = δ `, v}{M = N} (ext ρ) H

    rename-pres {M = app ⦅ cons L (cons M nil) ⦆} ρ γ⊑δ∘ρ =
      ●-≲ (rename-pres {M = L} ρ γ⊑δ∘ρ) (rename-pres {M = M} ρ γ⊑δ∘ρ)

    ⊑-env : ∀ {Γ} {γ : Env Γ} {δ : Env Γ} {M v}
      → ℰ M γ v
      → γ `⊑ δ
        ----------
      → ℰ M δ v
    ⊑-env{Γ}{γ}{δ}{M}{v} d lt
          with rename-pres{Γ}{Γ}{v}{γ}{δ}{M} (λ x → x) lt d
    ... | d′ rewrite rename-id {Γ}{M} =
          d′

    EnvExt⊑ : ∀ {Γ} {γ : Env Γ} {M v u₁ u₂}
      → ℰ M (γ `, u₁) v
      → u₁ ⊑ u₂
        -----------------
      → ℰ M (γ `, u₂) v
    EnvExt⊑ {M = M} d lt = ⊑-env{M = M} d (env-le lt)
      where
      env-le : ∀ {γ u₁ u₂} → u₁ ⊑ u₂ → (γ `, u₁) `⊑ (γ `, u₂)
      env-le lt Z = lt
      env-le lt (S n) = ⊑-refl

    rename-reflect : ∀ {Γ Δ} {γ : Env Γ} {δ : Env Δ} { M : Term Γ}
                       {ρ : Rename Γ Δ}
      → (δ ∘ ρ) `⊑ γ
        -------------------------
      → ℰ (rename ρ M) δ ≲ ℰ M γ
    rename-reflect {Γ}{Δ}{γ}{δ}{` x} {ρ} δ∘ρ⊑γ {v} ℰρMδv  =
      v  ⊑⟨ ℰρMδv ⟩ δ (ρ x)  ⊑⟨ δ∘ρ⊑γ x ⟩  γ x ◼
    rename-reflect {Γ}{Δ}{γ}{δ}{lam ⦅ bind N nil ⦆} {ρ} δ∘ρ⊑γ {v} = ℱ-≲ IH {v}
      where ⊑-ext : ∀ {Γ Δ v} {γ : Env Γ} {δ : Env Δ}
                  → (ρ : Rename Γ Δ)  →  (δ ∘ ρ) `⊑ γ
                    ---------------------------------
                  → ((δ `, v) ∘ ext ρ) `⊑ (γ `, v)
            ⊑-ext ρ lt Z = ⊑-refl
            ⊑-ext ρ lt (S x) = lt x
            
            IH : ∀ {v} → ℰ (rename (ext ρ) N) (δ `, v) ≲ ℰ N (γ `, v)
            IH {v} = rename-reflect{M = N}{ρ = ext ρ} (⊑-ext ρ δ∘ρ⊑γ)
    rename-reflect {M = app ⦅ cons L (cons M nil) ⦆} {ρ} δ∘ρ⊑γ =
      ●-≲ (rename-reflect{M = L} δ∘ρ⊑γ) (rename-reflect{M = M} δ∘ρ⊑γ)

    rename-inc-reflect : ∀ {Γ v′ v} {γ : Env Γ} { M : Term Γ}
      → ℰ (rename S_ M) (γ `, v′) v
        ----------------------------
      → ℰ M γ v
    rename-inc-reflect {M = M} d = rename-reflect {M = M} `Refl⊑ d

    rename-equiv : ∀ {Γ Δ} {γ : Env Γ} {δ : Env Δ} {M : Term Γ} {ρ : Rename Γ Δ}
      → γ `≡ (δ ∘ ρ)
        ------------------------
      → ℰ M γ ≃ ℰ (rename ρ M) δ
    rename-equiv {γ = γ}{δ}{M}{ρ} γ≡δ∘ρ =
        ⟨ rename-pres {M = M} ρ γ⊑δ∘ρ , rename-reflect {M = M} {ρ} δ∘ρ⊑γ ⟩
        where γ⊑δ∘ρ : γ `⊑ (δ ∘ ρ)
              γ⊑δ∘ρ x rewrite γ≡δ∘ρ x = ⊑-refl
              
              δ∘ρ⊑γ : (δ ∘ ρ) `⊑ γ
              δ∘ρ⊑γ x rewrite γ≡δ∘ρ x = ⊑-refl

  module Filter
      (_●_ : ∀{Γ} → Denotation Γ → Denotation Γ → Denotation Γ)
      (MB : ModelBasics _●_)
      where

    open ModelBasics MB
    
    module Den = Denot _●_
    open Den
    
    module RP = RenamePreserveReflect _●_ Cong
    open RP using (⊑-env; rename-pres)  
  
    ℰ-⊔ : ∀{Γ} {γ : Env Γ} {M : Term Γ} {u v : Value}
        → ℰ M γ u → ℰ M γ v → ℰ M γ (u ⊔ v)
    ℰ-⊑ : ∀{Γ} {γ : Env Γ} {M : Term Γ} {v w : Value}
        → ℰ M γ v → w ⊑ v → ℰ M γ w
        
    ℰ-⊔ {M = ` x} ℰMγu ℰMγv = ⊑-conj-L ℰMγu ℰMγv
    ℰ-⊔ {Γ}{γ}{lam ⦅ bind N nil ⦆}{u}{v} ℰMγu ℰMγv =
       ℱ-⊔ {Γ}{ℰ N}{γ}{u}{v} ℰMγu ℰMγv
    ℰ-⊔ {Γ}{γ = γ}{app ⦅ cons L (cons M nil) ⦆} ℰMγu ℰMγv =
       let a = ℰ-⊔ {γ = γ} {M = L} in
       let b = ℰ-⊔ {γ = γ} {M = M} in
       let c = ℰ-⊑ {γ = γ} {M = L} in
       ●-⊔ G H ℰMγu ℰMγv
      where G : WFDenot Γ (ℰ L)
            G = record { ⊑-env = ⊑-env{M = L} ;
                         ⊑-closed = ℰ-⊑ {M = L} ;
                         ⊔-closed = ℰ-⊔ {M = L}  }
            H : WFDenot Γ (ℰ M)
            H = record { ⊑-env = ⊑-env{M = M} ;
                         ⊑-closed = ℰ-⊑ {M = M} ;
                         ⊔-closed = ℰ-⊔ {M = M}  }
       
        
    ℰ-⊑ {M = ` x} ℰMγv w⊑v = ⊑-trans w⊑v ℰMγv
    ℰ-⊑ {Γ}{γ}{lam ⦅ bind N nil ⦆}{v}{w} ℰMγv w⊑v =
      ℱ-⊑ G ℰMγv w⊑v
      where G : WFDenot (suc Γ) (ℰ N)
            G = record { ⊑-env = ⊑-env{M = N} ;
                         ⊑-closed = ℰ-⊑ {M = N} ;
                         ⊔-closed = ℰ-⊔ {M = N} }

    ℰ-⊑ {Γ}{γ} {app ⦅ cons L (cons M nil) ⦆} {v} {w} ℰMγv w⊑v =
       ●-⊑ G ℰMγv w⊑v
       where G : WFDenot Γ (ℰ L)
             G = record { ⊑-env = ⊑-env{M = L} ;
                          ⊑-closed = ℰ-⊑ {M = L} ;
                          ⊔-closed = ℰ-⊔ {M = L} }

    WF : ∀{Γ}{M : Term Γ} → WFDenot Γ (ℰ M)
    WF {Γ} {M} = record { ⊑-env = ⊑-env {M = M} ;
                          ⊑-closed = ℰ-⊑ {M = M} ;
                          ⊔-closed = ℰ-⊔ {M = M} }

  module SubstPres
    (_●_ : ∀{Γ} → Denotation Γ → Denotation Γ → Denotation Γ)
    (MB : ModelBasics _●_)
    where
    
    open Denot _●_
    open ModelBasics MB
    open ModelCong Cong
    module RP = RenamePreserveReflect _●_ Cong
    open RP using (⊑-env; rename-pres)  
    open Filter _●_ MB using (ℰ-⊑; ℰ-⊔)
    
    subst-ext : ∀ {Γ Δ v} {γ : Env Γ} {δ : Env Δ}
      → (σ : Subst Γ Δ)
      → δ `⊢ σ ↓ γ
       --------------------------
      → δ `, v `⊢ exts σ ↓ γ `, v
    subst-ext σ d Z = ⊑-refl
    subst-ext σ d (S x′) = rename-pres {M = σ x′} S_ (λ _ → ⊑-refl) (d x′)

    subst-pres : ∀ {Γ Δ v} {γ : Env Γ} {δ : Env Δ} {M : Term Γ}
      → (σ : Subst Γ Δ)
      → δ `⊢ σ ↓ γ
      → ℰ M γ v
        ------------------
      → ℰ (⟪ σ ⟫ M) δ v
    subst-pres {M = ` x} σ δ⊢σ↓γ ℰMγv = ℰ-⊑ {M = σ x} (δ⊢σ↓γ x) ℰMγv
    subst-pres {Γ}{Δ}{v}{γ}{δ}{lam ⦅ bind N nil ⦆} σ δ⊢σ↓γ ℰMγv =
       (ℱ-≲ {Γ}{Δ}{γ}{δ}{ℰ N}{ℰ (⟪ exts σ ⟫ N)}
             λ {v} → subst-pres {γ = γ `, v}{δ = δ `, v}{M = N} (exts σ)
                          (subst-ext σ δ⊢σ↓γ)) {v}
        ℰMγv
    subst-pres {Γ}{Δ}{v}{γ}{δ}{app ⦅ cons L (cons M nil) ⦆} σ δ⊢σ↓γ ℰMγv =
       (●-≲{Γ}{Δ}{γ}{δ}{D₁ = ℰ L}{D₂ = ℰ M}{D₁′ = ℰ (⟪ σ ⟫ L)}
            {D₂′ = ℰ (⟪ σ ⟫ M)}
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
      sub-z-ok (S x) = ⊑-refl


module InValueOrderWithBot (D : ValueOrder) (D' : ValueOrderWithBot D) where

  open ValueOrder D
  open ValueOrderWithBot D'
  open ValueOrderAux D

  `⊥ : ∀ {Γ} → Env Γ
  `⊥ x = ⊥

  record ModelBot
         (_●_ : ∀{Γ} → Denotation Γ → Denotation Γ → Denotation Γ)
         : Set₁ where
    field
      MB : InValueOrder.ModelBasics D _●_
      ●-⊥ : ∀{Γ}{D₁ D₂ : Denotation Γ} {γ : Env Γ}
           → (D₁ ● D₂) γ ⊥

  record ModelExtra
         (_●_ : ∀{Γ} → Denotation Γ → Denotation Γ → Denotation Γ)
         : Set₁ where
    field
      MBot : ModelBot _●_
      ●-≡ : ∀{Γ}{D₁ D₂ : Denotation Γ}{γ : Env Γ} {w : Value}
          → (D₁ ● D₂) γ w ≡ (w ⊑ ⊥ ⊎ (Σ[ v ∈ Value ] D₁ γ (v ↦ w) × D₂ γ v))
      ℱ-inv : ∀{Γ}{D : Denotation (suc Γ)}{γ : Env Γ}{u : Value}
            → ℱ D γ u
            → u ⊑ ⊥ ⊎ (Σ[ v ∈ Value ] Σ[ w ∈ Value ]
                        (D (γ `, v) w) × ((v ↦ w) ⊑ u))


  module Preservation
    (_●_ : ∀{Γ} → Denotation Γ → Denotation Γ → Denotation Γ)
    (ME : ModelExtra _●_)
    where

    module Den = InValueOrder.Denot D _●_
    open Den
    open ModelExtra ME
    open ModelBot MBot
    open InValueOrder.ModelBasics MB
    open ModelCong Cong
    module RP = InValueOrder.RenamePreserveReflect D _●_ Cong
    open RP using (⊑-env; rename-pres)  
    module F = InValueOrder.Filter D _●_ MB
    open F using (ℰ-⊑; ℰ-⊔)
    open InValueOrder.SubstPres D _●_ MB
    
    ℱ●-inv : ∀{Γ} {D₁ : Denotation (suc Γ)}{D₂ : Denotation Γ}{γ : Env Γ}
              {w : Value}
            → (ℱ D₁ ● D₂) γ w
            → w ⊑ ⊥ ⊎ (Σ[ v ∈ Value ] D₁ (γ `, v) w × D₂ γ v)
    ℱ●-inv {Γ}{D₁}{D₂}{γ}{w} ℱD₁●D₂γw
        rewrite ●-≡{Γ}{ℱ D₁}{D₂}{γ}{w}
        with ℱD₁●D₂γw
    ... | inj₁ w⊑⊥ = inj₁ w⊑⊥ 
    ... | inj₂ ⟨ v , ⟨ ℱD₁γv↦w , D₂γv ⟩ ⟩ =
          inj₂ ⟨ v , ⟨ ℱD₁γv↦w , D₂γv ⟩ ⟩
        
    ℰ-⊥ : ∀{Γ}{γ : Env Γ}{M : Term Γ}
        → ℰ M γ ⊥
    ℰ-⊥ {M = ` x} = ⊑-⊥
    ℰ-⊥ {Γ}{γ}{M = lam ⦅ bind N nil ⦆} = ℱ-⊥ {Γ}{ℰ N}{γ}
    ℰ-⊥ {M = app ⦅ cons L (cons M nil) ⦆} = ●-⊥


    open LambdaV.Reduction using (_—→_; ξ₁-rule; ξ₂-rule; β-rule)

    preserve : ∀ {Γ} {γ : Env Γ} {M N v}
      → M —→ N
      → ℰ M γ v
        ----------
      → ℰ N γ v
    preserve {γ = γ} (ξ₁-rule{L = L}{L´}{M} L—→L′) =
      ●-≲ {γ = γ}{γ}{D₁ = ℰ L}{D₂ = ℰ M}{D₁′ = ℰ L´}{D₂′ = ℰ M}
                  (λ x → preserve L—→L′ x)
                  (λ x → x)
    preserve {γ = γ} (ξ₂-rule{L = L}{M}{M′} M—→M′) =
      ●-≲ {γ = γ}{γ}{D₁ = ℰ L}{D₂ = ℰ M}{D₁′ = ℰ L}{D₂′ = ℰ M′}
                  (λ x → x)
                  (λ x → preserve M—→M′ x)
    preserve (β-rule{N = N}{M = M}) ℱℰN●ℰMγw 
        with ℱ●-inv ℱℰN●ℰMγw
    ... | inj₁ w⊑⊥ =
        ℰ-⊑ {M = ⟪ subst-zero M ⟫ N} (ℰ-⊥{M = ⟪ subst-zero M ⟫ N}) w⊑⊥
    ... | inj₂ ⟨ v , ⟨ ℰNγvw , ℰMγv ⟩ ⟩ = 
        substitution{N = N}{M = M} ℰNγvw ℰMγv

  module Reflect
    (_●_ : ∀{Γ} → Denotation Γ → Denotation Γ → Denotation Γ)
    (ME : ModelExtra _●_)
    where
    
    module Den = InValueOrder.Denot D _●_
    open Den
    open ModelExtra ME
    open ModelBot MBot
    open InValueOrder.ModelBasics MB
    open ModelCong Cong

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


    module RP = InValueOrder.RenamePreserveReflect D _●_ Cong
    open RP using (⊑-env; EnvExt⊑; rename-pres; rename-inc-reflect)  

    module F = InValueOrder.Filter D _●_ MB
    open F using (ℰ-⊑; ℰ-⊔; WF)

    module P = Preservation _●_ ME
    open P using (ℰ-⊥)


    _var≟_ : ∀ {Γ} → (x y : Var Γ) → Dec (x ≡ y)
    Z var≟ Z  =  yes refl
    Z var≟ (S _)  =  no λ()
    (S _) var≟ Z  =  no λ()
    (S x) var≟ (S y) with  x var≟ y
    ...                 |  yes refl =  yes refl
    ...                 |  no neq   =  no λ{refl → neq refl}

    var≟-refl : ∀ {Γ} (x : Var Γ) → (x var≟ x) ≡ yes refl
    var≟-refl Z = refl
    var≟-refl (S x) rewrite var≟-refl x = refl

    const-env : ∀{Γ} → (x : Var Γ) → Value → Env Γ
    const-env x v y with x var≟ y
    ...             | yes _       = v
    ...             | no _        = ⊥

    nth-const-env : ∀{Γ} {x : Var Γ} {v} → (const-env x v) x ≡ v
    nth-const-env {x = x} rewrite var≟-refl x = refl

    diff-nth-const-env : ∀{Γ} {x y : Var Γ} {v}
      → x ≢ y
        -------------------
      → const-env x v y ≡ ⊥
    diff-nth-const-env {Γ} {x} {y} neq with x var≟ y
    ...  | yes eq  =  ⊥-elim (neq eq)
    ...  | no _    =  refl

    subst-reflect-var : ∀ {Γ Δ} {γ : Env Δ} {x : Var Γ} {v} {σ : Subst Γ Δ}
      → ℰ (σ x) γ v  →  γ `⊢ σ ↓ `⊥
        -----------------------------------------
      → Σ[ δ ∈ Env Γ ] γ `⊢ σ ↓ δ  ×  ℰ (` x) δ v
    subst-reflect-var {Γ}{Δ}{γ}{x}{v}{σ} xv γ⊢σ↓⊥
      rewrite sym (nth-const-env {Γ}{x}{v}) =
        ⟨ const-env x v , ⟨ const-env-ok , ⊑-refl ⟩ ⟩
      where
      const-env-ok : γ `⊢ σ ↓ const-env x v
      const-env-ok y with x var≟ y
      ... | yes x≡y rewrite sym x≡y | nth-const-env {Γ}{x}{v} = xv
      ... | no x≢y rewrite diff-nth-const-env {Γ}{x}{y}{v} x≢y = γ⊢σ↓⊥ y

    subst-⊥ : ∀{Γ Δ}{γ : Env Δ}{σ : Subst Γ Δ}
        -----------------
      → γ `⊢ σ ↓ `⊥
    subst-⊥ {σ = σ} x = ℰ-⊥ {M = σ x}

    subst-⊔ : ∀{Γ Δ}{γ : Env Δ}{γ₁ γ₂ : Env Γ}{σ : Subst Γ Δ}
               → γ `⊢ σ ↓ γ₁
               → γ `⊢ σ ↓ γ₂
                 -------------------------
               → γ `⊢ σ ↓ (γ₁ `⊔ γ₂)
    subst-⊔ {σ = σ} γ₁-ok γ₂-ok x = ℰ-⊔ {M = σ x} (γ₁-ok x) (γ₂-ok x)

    split : ∀ {Γ} {M : Term (suc Γ)} {δ : Env (suc Γ)} {v}
      → ℰ M δ v
        ------------------------
      → ℰ M (init δ `, last δ) v
    split {δ = δ} δMv rewrite init-last δ = δMv

    δu⊢extσ⊥ : ∀{Γ}{Δ}{δ : Env Δ}{σ : Subst Γ Δ}{u}
             → δ `⊢ σ ↓ `⊥ → δ `, u `⊢ exts σ ↓ `⊥
    δu⊢extσ⊥ δ⊢σ↓⊥ Z = ⊑-⊥
    δu⊢extσ⊥ {σ = σ} δ⊢σ↓⊥ (S x) =
       rename-pres {M = σ x} S_ (λ x₁ → ⊑-refl) (δ⊢σ↓⊥ x)

    subst-reflect : ∀ {Γ Δ} {δ : Env Δ} {M : Term Γ} {L : Term Δ}
                      {σ : Subst Γ Δ} {v}
      → ℰ L δ v
      → L ≡ ⟪ σ ⟫ M
      → δ `⊢ σ ↓ `⊥
        --------------------------------------------
      → Σ[ γ ∈ Env Γ ] δ `⊢ σ ↓ γ  ×  ℰ M γ v
    subst-reflect {δ = δ}{` x}{L}{σ} ℰLδv L≡σM δ⊢σ↓⊥ rewrite L≡σM =
        subst-reflect-var{σ = σ} ℰLδv δ⊢σ↓⊥
    subst-reflect {Γ}{Δ}{δ}{lam ⦅ bind N nil ⦆} {L} {σ} {v} ℰLδv L≡σM δ⊢σ↓⊥
        rewrite L≡σM
        = G {v} ℰLδv
        where
        G : ∀{v}
          → ℱ (ℰ (⟪ exts σ ⟫ N)) δ v
          → Σ[ γ ∈ Env Γ ] δ `⊢ σ ↓ γ  ×  ℱ (ℰ N) γ v
        G {⊥} tt = ⟨ `⊥ , ⟨ subst-⊥ {σ = σ} , tt  ⟩ ⟩
        G {u ↦ w} ℰLδv
            with subst-reflect {δ = δ `, u} {M = N} {L = ⟪ exts σ ⟫ N}
                     {σ = exts σ} {w} ℰLδv refl (δu⊢extσ⊥ δ⊢σ↓⊥)
        ... | ⟨ γ , ⟨ subst-γ , m ⟩ ⟩ =
              ⟨ init γ ,
              ⟨ (λ x → rename-inc-reflect {M = σ x} (subst-γ (S x))) ,
                (let m' = split{M = N} m in
                 EnvExt⊑{M = N} m' (subst-γ Z)) ⟩ ⟩
        G {u ⊔ w} ⟨ aa , bb ⟩ 
            with G {u} aa | G {w} bb
        ... | ⟨ δ₁ , ⟨ subst-δ₁ , m1 ⟩ ⟩ | ⟨ δ₂ , ⟨ subst-δ₂ , m2 ⟩ ⟩ =
           ⟨ δ₁ `⊔ δ₂ ,
           ⟨ subst-⊔ {σ = σ} subst-δ₁ subst-δ₂ ,
           ⟨ ⊑-env{Γ}{δ₁}{δ₁ `⊔ δ₂}{lam ⦅ bind N nil ⦆}{u}m1(EnvConjR1⊑ δ₁ δ₂) ,
             ⊑-env{Γ}{δ₂}{δ₁ `⊔ δ₂}{lam ⦅ bind N nil ⦆}{w}m2(EnvConjR2⊑ δ₁ δ₂) ⟩
             ⟩ ⟩
    subst-reflect {Γ}{Δ}{δ}{app ⦅ cons L (cons M nil) ⦆}{_}{σ}{v} ℰσL●ℰσMδv
                  L≡σM δ⊢σ↓⊥
        rewrite L≡σM | ●-≡ {Δ}{ℰ (⟪ σ ⟫ L)}{ℰ (⟪ σ ⟫ M)}{δ}{v}
        with ℰσL●ℰσMδv
    ... | inj₁ v⊑⊥ =
          ⟨ `⊥ , ⟨ subst-⊥ {σ = σ} , ℰ-⊑{M = L · M} (ℰ-⊥{M = L · M}) v⊑⊥  ⟩ ⟩
    ... | inj₂ ⟨ u , ⟨ ℰσLδu↦v , ℰσMδu ⟩ ⟩
        with subst-reflect{M = L} ℰσLδu↦v refl δ⊢σ↓⊥
           | subst-reflect{M = M} ℰσMδu refl δ⊢σ↓⊥
    ... | ⟨ δ₁  , ⟨ subst-δ₁ , ℰLδ₁u↦v ⟩ ⟩
        | ⟨ δ₂  , ⟨ subst-δ₂ , ℰMδ₂u ⟩ ⟩ =
          ⟨ (δ₁ `⊔ δ₂) ,
          ⟨ (subst-⊔ {γ₁ = δ₁}{γ₂ = δ₂}{σ = σ} subst-δ₁ subst-δ₂) ,
            G ⟩ ⟩
          where
          ℰLδ₁⊔δ₂u↦v : ℰ L (λ z → (δ₁ `⊔ δ₂) z) (u ↦ v)
          ℰLδ₁⊔δ₂u↦v = ⊑-env{M = L} ℰLδ₁u↦v (EnvConjR1⊑ δ₁ δ₂)
          
          ℰMδ₁⊔δ₂u  : ℰ M (λ z → (δ₁ `⊔ δ₂) z) u
          ℰMδ₁⊔δ₂u = ⊑-env{M = M} ℰMδ₂u (EnvConjR2⊑ δ₁ δ₂)
          
          G : (ℰ L ● ℰ M) (δ₁ `⊔ δ₂) v
          G rewrite ●-≡ {Γ}{ℰ L}{ℰ M}{δ₁ `⊔ δ₂}{v} =
            inj₂ ⟨ u , ⟨ ℰLδ₁⊔δ₂u↦v , ℰMδ₁⊔δ₂u ⟩ ⟩

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

    reflect-beta : ∀{Γ}{γ : Env Γ}{M N}{v}
        → ℰ (N [ M ]) γ v
        → ℰ ((ƛ N) · M) γ v
    reflect-beta {Γ}{γ}{M}{N}{v} d 
        with substitution-reflect{N = N}{M = M} d (ℰ-⊥ {M = M})
    ... | ⟨ v₂′ , ⟨ d₁′ , d₂′ ⟩ ⟩ rewrite ●-≡ {Γ}{ℱ (ℰ N)}{ℰ M}{γ}{v} =
          inj₂ ⟨ v₂′ , ⟨ d₂′ , d₁′ ⟩ ⟩

    open LambdaV.Reduction using (_—→_; ξ₁-rule; ξ₂-rule; β-rule)

    reflect : ∀ {Γ} {γ : Env Γ} {M M′ N v}
      →  M —→ M′  →   M′ ≡ N  →  ℰ N γ v
        --------------------------------
      → ℰ M γ v    
    reflect {γ = γ} (ξ₁-rule {L = L}{L′}{M} L—→L′) L′·M≡N
        rewrite sym L′·M≡N =
        ●-≲ (reflect L—→L′ refl) (≲-refl {d = ℰ M γ})
    reflect {γ = γ} (ξ₂-rule {L = L}{M}{M′} M—→M′) L·M′≡N
        rewrite sym L·M′≡N =
        ●-≲ (≲-refl {d = ℰ L γ}) (reflect M—→M′ refl)
    reflect (β-rule {N = N}{M = M}) M′≡N rewrite sym M′≡N =
        reflect-beta {M = M}{N}


module CallByName where

  infix 4 _⊑_

  data _⊑_ : Value → Value → Set where

    ⊑-⊥ : ∀ {v} → ⊥ ⊑ v

    ⊑-conj-L : ∀ {u v w}
        → v ⊑ u
        → w ⊑ u
          -----------
        → (v ⊔ w) ⊑ u

    ⊑-conj-R1 : ∀ {u v w}
       → u ⊑ v
         -----------
       → u ⊑ (v ⊔ w)

    ⊑-conj-R2 : ∀ {u v w}
       → u ⊑ w
         -----------
       → u ⊑ (v ⊔ w)

    ⊑-trans : ∀ {u v w}
       → u ⊑ v
       → v ⊑ w
         -----
       → u ⊑ w

    ⊑-fun : ∀ {v w v′ w′}
         → v′ ⊑ v
         → w ⊑ w′
           -------------------
         → (v ↦ w) ⊑ (v′ ↦ w′)

    ⊑-dist : ∀{v w w′}
           ---------------------------------
         → v ↦ (w ⊔ w′) ⊑ (v ↦ w) ⊔ (v ↦ w′)

  ⊑-refl : ∀ {v} → v ⊑ v
  ⊑-refl {⊥} = ⊑-⊥
  ⊑-refl {v ↦ v′} = ⊑-fun ⊑-refl ⊑-refl
  ⊑-refl {v₁ ⊔ v₂} = ⊑-conj-L (⊑-conj-R1 ⊑-refl) (⊑-conj-R2 ⊑-refl)

  domain : ValueOrder
  domain = record
             { _⊑_ = _⊑_
             ; ⊑-refl = ⊑-refl
             ; ⊑-trans = ⊑-trans
             ; ⊑-conj-L = ⊑-conj-L
             ; ⊑-conj-R1 = ⊑-conj-R1
             ; ⊑-conj-R2 = ⊑-conj-R2
             ; ⊑-fun = ⊑-fun
             ; ⊑-dist = ⊑-dist
             }

  domain_bot : ValueOrderWithBot domain
  domain_bot = record { ⊑-⊥ = ⊑-⊥ }

  open ValueOrderAux domain
  open InValueOrderWithBot domain

  infixl 7 _●_
  _●_ : ∀{Γ} → Denotation Γ → Denotation Γ → Denotation Γ
  _●_ {Γ} D₁ D₂ γ w = w ⊑ ⊥ ⊎ Σ[ v ∈ Value ] D₁ γ (v ↦ w) × D₂ γ v 

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

  Cong : ModelCong _●_
  Cong = record { ●-≲ = λ {Γ}{Δ}{γ}{δ}{D₁}{D₂}{D₁′}{D₂′} x y →
                         ●-≲ {D₁ = D₁}{D₂ = D₂}{D₁′ = D₁′}{D₂′ = D₂′} x y }

  module RP = InValueOrder.RenamePreserveReflect domain _●_ Cong
  open RP using (⊑-env)  

  ●-⊔ : ∀{Γ}{D₁ D₂ : Denotation Γ}{γ : Env Γ} {u v : Value}
      → WFDenot Γ D₁ → WFDenot Γ D₂
      → (D₁ ● D₂) γ u → (D₁ ● D₂) γ v → (D₁ ● D₂) γ (u ⊔ v)
  ●-⊔ {u = u} {v} wf1 wf2 (inj₁ u⊑⊥) (inj₁ v⊑⊥) = inj₁ (⊑-conj-L u⊑⊥ v⊑⊥)
  ●-⊔ {u = u} {v} wf1 wf2 (inj₁ u⊑⊥) (inj₂ ⟨ v' , ⟨ fst₁ , snd ⟩ ⟩) =
    inj₂ ⟨ v' , ⟨ WFDenot.⊑-closed wf1 fst₁ lt , snd ⟩ ⟩
    where lt : v' ↦ (u ⊔ v) ⊑ v' ↦ v
          lt = ⊑-fun ⊑-refl (⊑-conj-L (⊑-trans u⊑⊥ ⊑-⊥) ⊑-refl)
  ●-⊔ {u = u} {v} wf1 wf2 (inj₂ ⟨ u' , ⟨ fst₁ , snd ⟩ ⟩) (inj₁ v⊑⊥) =
    inj₂ ⟨ u' , ⟨ (WFDenot.⊑-closed wf1 fst₁ lt) , snd ⟩ ⟩
    where lt : u' ↦ (u ⊔ v) ⊑ u' ↦ u
          lt = ⊑-fun ⊑-refl (⊑-conj-L ⊑-refl (⊑-trans v⊑⊥ ⊑-⊥))
  ●-⊔ {Γ}{D₁}{D₂}{γ}{u}{v} wf1 wf2 (inj₂ ⟨ u' , ⟨ fst₁ , snd ⟩ ⟩)
                      (inj₂ ⟨ v' , ⟨ fst₃ , snd₁ ⟩ ⟩) =
    let a = WFDenot.⊔-closed wf1 fst₁ fst₃ in                      
    inj₂ ⟨ (u' ⊔ v') ,
         ⟨ WFDenot.⊑-closed wf1 a Dist⊔↦⊔ ,
           WFDenot.⊔-closed wf2 snd snd₁ ⟩ ⟩

  ℱ-⊑ : ∀{Γ}{D : Denotation (suc Γ)}{γ : Env Γ} {v w : Value}
         → WFDenot (suc Γ) D
         → ℱ D γ v → w ⊑ v → ℱ D γ w
  ℱ-⊑ d ℱDγv ⊑-⊥ = tt
  ℱ-⊑ d ℱDγv (⊑-conj-L w⊑v w⊑v₁) = ⟨ (ℱ-⊑ d ℱDγv w⊑v) , (ℱ-⊑ d ℱDγv w⊑v₁) ⟩
  ℱ-⊑ d ℱDγv (⊑-conj-R1 w⊑v) = ℱ-⊑ d (proj₁ ℱDγv) w⊑v
  ℱ-⊑ d ℱDγv (⊑-conj-R2 w⊑v) = ℱ-⊑ d (proj₂ ℱDγv) w⊑v
  ℱ-⊑ d ℱDγv (⊑-trans w⊑v w⊑v₁) = ℱ-⊑ d (ℱ-⊑ d ℱDγv w⊑v₁) w⊑v
  ℱ-⊑ {Γ}{D}{γ}{v ↦ w}{v' ↦ w'} d ℱDγv (⊑-fun v⊑v' w'⊑w) =
    WFDenot.⊑-closed d (WFDenot.⊑-env d ℱDγv b) w'⊑w
    where b : (γ `, v) `⊑ (γ `, v')
          b Z = v⊑v'
          b (S x) = ⊑-refl 
  ℱ-⊑ d ℱDγv ⊑-dist = WFDenot.⊔-closed d (proj₁ ℱDγv) (proj₂ ℱDγv)

  ●-⊑ : ∀{Γ}{D₁ D₂ : Denotation Γ} {γ : Env Γ} {v w : Value}
      → WFDenot Γ D₁ → (D₁ ● D₂) γ v → w ⊑ v
      → (D₁ ● D₂) γ w
  ●-⊑ d (inj₁ x) w⊑v = inj₁ (⊑-trans w⊑v x)
  ●-⊑ {v = v}{w} d (inj₂ ⟨ v' , ⟨ fst₁ , snd ⟩ ⟩) w⊑v =
    inj₂ ⟨ v' , ⟨ WFDenot.⊑-closed d fst₁ lt  , snd ⟩ ⟩
    where lt : v' ↦ w ⊑ v' ↦ v
          lt = ⊑-fun ⊑-refl w⊑v

  ●-⊥ : ∀{Γ}{D₁ D₂ : Denotation Γ} {γ : Env Γ}
      → (D₁ ● D₂) γ ⊥
  ●-⊥ = inj₁ ⊑-⊥

  ℱ-inv : ∀{Γ}{D : Denotation (suc Γ)}{γ : Env Γ}{u : Value}
        → ℱ D γ u
        → u ⊑ ⊥ ⊎ (Σ[ v ∈ Value ] Σ[ w ∈ Value ] D (γ `, v) w × v ↦ w ⊑ u)
  ℱ-inv {u = ⊥} tt = inj₁ ⊑-refl
  ℱ-inv {u = v ↦ w} ℱDγu = inj₂ ⟨ v , ⟨ w , ⟨ ℱDγu , ⊑-refl ⟩ ⟩ ⟩
  ℱ-inv {u = u ⊔ v} ⟨ fst , snd ⟩
      with ℱ-inv{u = u} fst | ℱ-inv{u = v} snd
  ... | inj₁ u⊑⊥ | inj₁ v⊑⊥ = inj₁ (⊑-conj-L u⊑⊥ v⊑⊥)
  ... | inj₁ u⊑⊥ | inj₂ ⟨ v' , ⟨ w' , ⟨ Dγv'w' , v'↦w'⊑v ⟩ ⟩ ⟩ =
        inj₂ ⟨ v' , ⟨ w' , ⟨ Dγv'w' , ⊑-conj-R2 v'↦w'⊑v ⟩ ⟩ ⟩
  ... | inj₂ ⟨ v' , ⟨ w' , ⟨ Dγv'w' , v'↦w'⊑v ⟩ ⟩ ⟩ | _ =
        inj₂ ⟨ v' , ⟨ w' , ⟨ Dγv'w' , ⊑-conj-R1 v'↦w'⊑v ⟩ ⟩ ⟩


  MB : InValueOrder.ModelBasics domain _●_
  MB = (record { Cong = Cong ;
                 ●-⊑ = λ {Γ}{D₁}{D₂} a b c → ●-⊑ {D₂ = D₂} a b c;
                 ℱ-⊑ = ℱ-⊑ ;
                 ●-⊔ = ●-⊔
                 })

  MBot : ModelBot domain_bot _●_
  MBot = (record { MB = MB ;
                 ●-⊥ = λ {Γ}{D₁}{D₂} → ●-⊥ {D₁ = D₁}{D₂} })

  ME : ModelExtra domain_bot _●_
  ME = (record { MBot = MBot ;
                 ●-≡ = refl ;
                 ℱ-inv = ℱ-inv
                 })

  open Reflect domain_bot _●_ ME


module CallByValue where

  infix 4 _⊑_

  data _⊑_ : Value → Value → Set where

    ⊑-⊥-⊥ : ⊥ ⊑ ⊥
    
    ⊑-⊥-fun : ∀ {v w} → ⊥ ⊑ v ↦ w 

    ⊑-conj-L : ∀ {u v w}
        → v ⊑ u
        → w ⊑ u
          -----------
        → (v ⊔ w) ⊑ u

    ⊑-conj-R1 : ∀ {u v w}
       → u ⊑ v
         -----------
       → u ⊑ (v ⊔ w)

    ⊑-conj-R2 : ∀ {u v w}
       → u ⊑ w
         -----------
       → u ⊑ (v ⊔ w)

    ⊑-trans : ∀ {u v w}
       → u ⊑ v
       → v ⊑ w
         -----
       → u ⊑ w

    ⊑-fun : ∀ {v w v′ w′}
         → v′ ⊑ v
         → w ⊑ w′
           -------------------
         → (v ↦ w) ⊑ (v′ ↦ w′)

    ⊑-dist : ∀{v w w′}
           ---------------------------------
         → v ↦ (w ⊔ w′) ⊑ (v ↦ w) ⊔ (v ↦ w′)
  

  ⊑-refl : ∀ {v} → v ⊑ v
  ⊑-refl {⊥} = ⊑-⊥-⊥
  ⊑-refl {v ↦ v′} = ⊑-fun ⊑-refl ⊑-refl
  ⊑-refl {v₁ ⊔ v₂} = ⊑-conj-L (⊑-conj-R1 ⊑-refl) (⊑-conj-R2 ⊑-refl)

  domain : ValueOrder
  domain = record
             { _⊑_ = _⊑_
             ; ⊑-refl = ⊑-refl
             ; ⊑-trans = ⊑-trans
             ; ⊑-conj-L = ⊑-conj-L
             ; ⊑-conj-R1 = ⊑-conj-R1
             ; ⊑-conj-R2 = ⊑-conj-R2
             ; ⊑-fun = ⊑-fun
             ; ⊑-dist = ⊑-dist
             }
             
  open ValueOrderAux domain

  infixl 7 _●_
  _●_ : ∀{Γ} → Denotation Γ → Denotation Γ → Denotation Γ
  _●_ {Γ} D₁ D₂ γ w = Σ[ v ∈ Value ] D₁ γ (v ↦ w) × D₂ γ v 
  
  ●-≲ : ∀{Γ Δ}{γ : Env Γ}{δ : Env  Δ}{D₁ D₂ : Denotation Γ}
            {D₁′ D₂′ : Denotation Δ}
         → D₁ γ ≲ D₁′ δ  →  D₂ γ ≲ D₂′ δ
         → (D₁ ● D₂) γ ≲ (D₁′ ● D₂′) δ
  ●-≲ {γ = γ} {δ} {D₁} {D₂} {D₁′} {D₂′} D₁γ≲D₁′δ D₂γ≲D₂′δ {w}
      ⟨ v , ⟨ fst₁ , snd ⟩ ⟩
      with D₁γ≲D₁′δ {w} | D₂γ≲D₂′δ {w}
  ... | a | b = ⟨ v , ⟨ (D₁γ≲D₁′δ fst₁) , (D₂γ≲D₂′δ snd) ⟩ ⟩

  Cong : ModelCong _●_
  Cong = record { ●-≲ = λ {Γ}{Δ}{γ}{δ}{D₁}{D₂}{D₁′}{D₂′} x y →
                         ●-≲ {D₁ = D₁}{D₂ = D₂}{D₁′ = D₁′}{D₂′ = D₂′} x y }

  module RP = InValueOrder.RenamePreserveReflect domain _●_ Cong
  open RP using (⊑-env)  

  ●-⊔ : ∀{Γ}{D₁ D₂ : Denotation Γ}{γ : Env Γ} {u v : Value}
      → WFDenot Γ D₁ → WFDenot Γ D₂
      → (D₁ ● D₂) γ u → (D₁ ● D₂) γ v → (D₁ ● D₂) γ (u ⊔ v)
  ●-⊔ {Γ}{D₁}{D₂}{γ}{u}{v} wf1 wf2 ⟨ u' , ⟨ fst₁ , snd ⟩ ⟩
                      ⟨ v' , ⟨ fst₃ , snd₁ ⟩ ⟩ =
    let a = WFDenot.⊔-closed wf1 fst₁ fst₃ in                      
    ⟨ (u' ⊔ v') ,
    ⟨ WFDenot.⊑-closed wf1 a Dist⊔↦⊔ ,
      WFDenot.⊔-closed wf2 snd snd₁ ⟩ ⟩

  ℱ-⊑ : ∀{Γ}{D : Denotation (suc Γ)}{γ : Env Γ} {v w : Value}
         → WFDenot (suc Γ) D
         → ℱ D γ v → w ⊑ v → ℱ D γ w
  ℱ-⊑ d ℱDγv ⊑-⊥-⊥ = tt
  ℱ-⊑ d ℱDγv ⊑-⊥-fun = tt
  ℱ-⊑ d ℱDγv (⊑-conj-L w⊑v w⊑v₁) = ⟨ (ℱ-⊑ d ℱDγv w⊑v) , (ℱ-⊑ d ℱDγv w⊑v₁) ⟩
  ℱ-⊑ d ℱDγv (⊑-conj-R1 w⊑v) = ℱ-⊑ d (proj₁ ℱDγv) w⊑v
  ℱ-⊑ d ℱDγv (⊑-conj-R2 w⊑v) = ℱ-⊑ d (proj₂ ℱDγv) w⊑v
  ℱ-⊑ d ℱDγv (⊑-trans w⊑v w⊑v₁) = ℱ-⊑ d (ℱ-⊑ d ℱDγv w⊑v₁) w⊑v
  ℱ-⊑ {Γ}{D}{γ}{v ↦ w}{v' ↦ w'} d ℱDγv (⊑-fun v⊑v' w'⊑w) =
    WFDenot.⊑-closed d (WFDenot.⊑-env d ℱDγv b) w'⊑w
    where b : (γ `, v) `⊑ (γ `, v')
          b Z = v⊑v'
          b (S x) = ⊑-refl 
  ℱ-⊑ d ℱDγv ⊑-dist = WFDenot.⊔-closed d (proj₁ ℱDγv) (proj₂ ℱDγv)

  ●-⊑ : ∀{Γ}{D₁ D₂ : Denotation Γ} {γ : Env Γ} {v w : Value}
      → WFDenot Γ D₁ → (D₁ ● D₂) γ v → w ⊑ v
      → (D₁ ● D₂) γ w
  ●-⊑ {v = v}{w} d ⟨ v' , ⟨ fst₁ , snd ⟩ ⟩ w⊑v =
    ⟨ v' , ⟨ WFDenot.⊑-closed d fst₁ lt  , snd ⟩ ⟩
    where lt : v' ↦ w ⊑ v' ↦ v
          lt = ⊑-fun ⊑-refl w⊑v

  MB : InValueOrder.ModelBasics domain _●_
  MB = (record { Cong = Cong ;
                 ●-⊑ = λ {Γ}{D₁}{D₂} a b c → ●-⊑ {D₂ = D₂} a b c;
                 ℱ-⊑ = ℱ-⊑ ;
                 ●-⊔ = ●-⊔
                 })
  

{-

  This version attaches bindings directly to operators
  so that these low-level AST nodes are 1-1 with the higher level
  AST nodes.

-}

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties
open import Data.Bool
open import Data.List using (List; []; _∷_)
open import Function using (_∘_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong; cong₂; cong-app)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Level using (Level)

import Relation.Binary.HeterogeneousEquality as HEq
open HEq using (_≅_; ≅-to-type-≡) renaming (refl to hrefl; cong to hcong; subst to hsubst)
open HEq.≅-Reasoning using (_≅⟨_⟩_) renaming (begin_ to hbegin_; _≡⟨⟩_ to _≅⟨⟩_; _∎ to _□)

module Syntax2 (Op : Set) (sig : Op → List Bool) where

postulate
  extensionality : ∀ {A B : Set} {f g : A → B}
    → (∀ (x : A) → f x ≡ g x)
      -----------------------
    → f ≡ g

data Var : ℕ → Set where

  Z : ∀ {Γ}
     ---------
   → Var (suc Γ)

  S_ : ∀ {Γ}
    → Var Γ
      ---------
    → Var (suc Γ)

Rename : ℕ → ℕ → Set
Rename Γ Δ = Var Γ → Var Δ

data Args (Γ : ℕ) : (sig : List Bool) → Set

data AST : ℕ → Set where

  `_ : ∀{Γ} → (x : Var Γ) → AST Γ

  _⦅_⦆ : ∀{Γ} → (op : Op) → Args Γ (sig op) → AST Γ

data Args Γ where
  nil : Args Γ []
  bind : ∀{bs} → AST (suc Γ) → Args Γ bs → Args Γ (true ∷ bs)
  cons : ∀{bs} → AST Γ → Args Γ bs → Args Γ (false ∷ bs)

Subst : ℕ → ℕ → Set
Subst Γ Δ = Var Γ → AST Δ

ext : ∀ {Γ Δ} → Rename Γ Δ
    ----------------------
  → Rename (suc Γ) (suc Δ)
ext ρ Z      =  Z
ext ρ (S x)  =  S (ρ x)

rename : ∀ {Γ Δ}
     → Rename Γ  Δ
       -------------
     → AST Γ → AST Δ
renames : ∀ {Γ Δ S}
      → Rename Γ Δ
        -------------------
      → Args Γ S → Args Δ S

rename ρ (` x)          =  ` (ρ x)
rename ρ (o ⦅ Ms ⦆)     =  o ⦅ renames ρ Ms ⦆
renames ρ nil           = nil
renames ρ (cons M Ms) = cons (rename ρ M) (renames ρ Ms)
renames ρ (bind M Ms) = bind (rename (ext ρ) M) (renames ρ Ms)

exts : ∀ {Γ Δ}
   → Subst Γ Δ
     ----------------------
   → Subst (suc Γ) (suc Δ)
exts σ Z      =  ` Z
exts σ (S x)  =  rename S_ (σ x)

⟪_⟫ : ∀ {Γ Δ}
  → Subst Γ Δ
    -------------
  → AST Γ → AST Δ
substs : ∀ {Γ Δ S}
  → Subst Γ Δ
    -------------------
  → Args Γ S → Args Δ S

⟪ σ ⟫ (` x)          =  σ x
⟪ σ ⟫ (o ⦅ Ms ⦆)     =  o ⦅ substs σ Ms ⦆
substs σ nil         = nil
substs σ (bind M Ms) = bind (⟪ exts σ ⟫ M) (substs σ Ms)
substs σ (cons M Ms) = cons (⟪ σ ⟫ M) (substs σ Ms)

subst-zero : ∀ {Γ} → (AST Γ) → Var (suc Γ) → (AST Γ)
subst-zero M Z      = M
subst-zero M (S x)  = ` x

_[_] : ∀ {Γ}
   → AST (suc Γ)
   → AST Γ
     ---------
   → AST Γ
_[_] N M =  ⟪ subst-zero M ⟫ N

ids : ∀{Γ} → Subst Γ Γ
ids x = ` x

↑ : ∀{Γ} → Subst Γ (suc Γ)
↑ x = ` (S x)

infixr 6 _•_
_•_ : ∀{Γ Δ} → (AST Δ) → Subst Γ Δ → Subst (suc Γ) Δ
(M • σ) Z = M
(M • σ) (S x) = σ x


infixr 5 _⨟_
_⨟_ : ∀{Γ Δ Σ} → Subst Γ Δ → Subst Δ Σ → Subst Γ Σ
σ ⨟ τ = ⟪ τ ⟫ ∘ σ


ren : ∀{Γ Δ} → Rename Γ Δ → Subst Γ Δ
ren ρ = ids ∘ ρ


sub-head : ∀ {Γ Δ} {M : AST Δ}{σ : Subst Γ Δ}
         → ⟪ M • σ ⟫ (` Z) ≡ M
sub-head = refl


sub-tail : ∀{Γ Δ} {M : AST Δ} {σ : Subst Γ Δ}
         → (↑ ⨟ M • σ) ≡ σ
sub-tail = extensionality λ x → refl


sub-η : ∀{Γ Δ} {σ : Subst (suc Γ) Δ} 
      → (⟪ σ ⟫ (` Z) • (↑ ⨟ σ)) ≡ σ
sub-η {Γ}{Δ}{σ} = extensionality λ x → lemma
   where 
   lemma : ∀ {x} → ((⟪ σ ⟫ (` Z)) • (↑ ⨟ σ)) x ≡ σ x
   lemma {x = Z} = refl
   lemma {x = S x} = refl


Z-shift : ∀{Γ}
        → ((` Z) • ↑) ≡ ids
Z-shift {Γ} = extensionality lemma 
   where
   lemma : (x : Var (suc Γ)) → ((` Z) • ↑) x ≡ ids x
   lemma Z = refl
   lemma (S y) = refl

sub-idL : ∀{Γ Δ} {σ : Subst Γ Δ}
       → ids ⨟ σ ≡ σ
sub-idL = extensionality λ x → refl

sub-dist :  ∀{Γ Δ Σ} {σ : Subst Γ Δ} {τ : Subst Δ Σ} {M : AST Δ}
         → ((M • σ) ⨟ τ) ≡ ((⟪ τ ⟫ M) • (σ ⨟ τ))
sub-dist {Γ}{Δ}{Σ}{σ}{τ}{M} = extensionality λ x → lemma {x = x}
  where
  lemma : ∀ {x : Var (suc Γ)} → ((M • σ) ⨟ τ) x ≡ ((⟪ τ ⟫ M) • (σ ⨟ τ)) x
  lemma {x = Z} = refl
  lemma {x = S x} = refl


sub-op : ∀{Γ Δ} {σ : Subst Γ Δ} {o : Op}{Ms : Args Γ (sig o)}
        → ⟪ σ ⟫ (o ⦅ Ms ⦆)  ≡ o ⦅ substs σ Ms ⦆
sub-op = refl        


ren-ext : ∀ {Γ Δ} {ρ : Rename Γ Δ}
        → ren (ext ρ) ≡ exts (ren ρ)
ren-ext {Γ}{Δ}{ρ} = extensionality λ x → lemma {x = x}
  where
  lemma : ∀ {x : Var (suc Γ)} → (ren (ext ρ)) x ≡ exts (ren ρ) x
  lemma {x = Z} = refl
  lemma {x = S x} = refl


rename-subst-ren : ∀ {Γ Δ} {ρ : Rename Γ Δ}{M : AST Γ}
                 → rename ρ M ≡ ⟪ ren ρ ⟫ M
renames-subst-ren : ∀ {Γ Δ} {ρ : Rename Γ Δ}{S}{Ms : Args Γ S}
                 → renames ρ Ms ≡ substs (ren ρ) Ms
rename-subst-ren {M = ` x} = refl
rename-subst-ren{Γ}{Δ}{ρ}{o ⦅ Ms ⦆} =
  cong (_⦅_⦆ o) (renames-subst-ren {Ms = Ms})
renames-subst-ren {Ms = nil} = refl
renames-subst-ren {ρ = ρ}{Ms = bind M Ms} =
  let ih1 = rename-subst-ren {ρ = ext ρ}{M = M} in
  let ih2 = renames-subst-ren {ρ = ρ}{Ms = Ms} in
  begin
      renames ρ (bind M Ms)
    ≡⟨⟩
      bind (rename (ext ρ) M) (renames ρ Ms)
    ≡⟨ cong₂ bind ih1 ih2 ⟩
      bind (⟪ ren (ext ρ) ⟫ M) (substs (ren ρ) Ms)
    ≡⟨ cong₂ bind (cong-app (cong ⟪_⟫ (ren-ext{ρ = ρ})) M) refl ⟩
      bind (⟪ exts (ren ρ) ⟫ M) (substs (ren ρ) Ms)
    ≡⟨⟩
      substs (ren ρ) (bind M Ms)
  ∎
renames-subst-ren {ρ = ρ}{Ms = cons M Ms} =
  cong₂ cons (rename-subst-ren{M = M}) (renames-subst-ren{Ms = Ms})

ren-shift : ∀{Γ}
          → ren S_ ≡ ↑ 
ren-shift {Γ} = extensionality λ x → lemma {x = x}
  where
  lemma : ∀ {x : Var Γ} → ren (S_) x ≡ ↑ x
  lemma {x = Z} = refl
  lemma {x = S x} = refl

rename-shift : ∀{Γ} {M : AST Γ}
             → rename (S_) M ≡ ⟪ ↑ ⟫ M
rename-shift{Γ}{M} =
  begin
    rename S_ M
  ≡⟨ rename-subst-ren ⟩
    ⟪ ren S_ ⟫ M
  ≡⟨ cong-app (cong ⟪_⟫ ren-shift) M ⟩
    ⟪ ↑ ⟫ M
  ∎

exts-cons-shift : ∀{Γ Δ} {σ : Subst Γ Δ}
                → exts σ ≡ (` Z • (σ ⨟ ↑))
exts-cons-shift = extensionality λ x → lemma{x = x}
  where
  lemma : ∀{Γ Δ} {σ : Subst Γ Δ} {x : Var (suc Γ)}
                  → exts σ x ≡ (` Z • (σ ⨟ ↑)) x
  lemma {x = Z} = refl
  lemma {x = S y} = rename-subst-ren

ext-cons-Z-shift : ∀{Γ Δ} {ρ : Rename Γ Δ}
                 → ren (ext ρ) ≡ (` Z • (ren ρ ⨟ ↑))
ext-cons-Z-shift {Γ}{Δ}{ρ} =
  begin
    ren (ext ρ)
  ≡⟨ ren-ext ⟩
    exts (ren ρ)
  ≡⟨ exts-cons-shift{σ = ren ρ} ⟩
   ((` Z) • (ren ρ ⨟ ↑))
  ∎

subst-Z-cons-ids : ∀{Γ}{M : AST Γ}
                 → subst-zero M ≡ (M • ids)
subst-Z-cons-ids = extensionality λ x → lemma {x = x}
  where
  lemma : ∀{Γ}{M : AST Γ}{x : Var (suc Γ)}
                      → subst-zero M x ≡ (M • ids) x
  lemma {x = Z} = refl
  lemma {x = S x} = refl

{-
sub-abs : ∀{Γ Δ} {σ : Subst Γ Δ} {N : AST (suc Γ)}
        → ⟪ σ ⟫ (α N) ≡ α ⟪ (` Z) • (σ ⨟ ↑) ⟫ N
sub-abs {σ = σ}{N = N} =
   begin
     ⟪ σ ⟫ (α N)
   ≡⟨⟩
     α ⟪ exts σ ⟫ N
   ≡⟨ cong α_ (cong-app (cong ⟪_⟫ exts-cons-shift) N) ⟩
     α ⟪ (` Z) • (σ ⨟ ↑) ⟫ N
   ∎
-}

exts-ids : ∀{Γ}
         → exts ids ≡ ids
exts-ids {Γ} = extensionality lemma
  where lemma : (x : Var (suc Γ)) → exts ids x ≡ ids x
        lemma Z = refl
        lemma (S x) = refl


sub-id : ∀{Γ} {M : AST Γ}
         → ⟪ ids ⟫ M ≡ M
subs-id : ∀{Γ}{S} {Ms : Args Γ S}
         → substs ids Ms ≡ Ms
sub-id {M = ` x} = refl
sub-id {M = o ⦅ Ms ⦆} = cong (_⦅_⦆ o) (subs-id {Ms = Ms})
subs-id {Ms = nil} = refl
subs-id {Ms = bind M Ms} =
   begin
     bind (⟪ exts ids ⟫ M) (substs ids Ms)
   ≡⟨ cong₂ bind (cong-app (cong ⟪_⟫ exts-ids) M) (subs-id {Ms = Ms})  ⟩
     bind (⟪ ids ⟫ M) Ms
   ≡⟨ cong₂ bind (sub-id {M = M}) refl ⟩
     bind M Ms
   ∎
subs-id {Ms = cons M Ms} = cong₂ cons sub-id subs-id


sub-idR : ∀{Γ Δ} {σ : Subst Γ Δ}
       → (σ ⨟ ids) ≡ σ
sub-idR {Γ}{σ = σ} =
          begin
            σ ⨟ ids
          ≡⟨⟩
            ⟪ ids ⟫ ∘ σ
          ≡⟨ extensionality (λ x → sub-id) ⟩
            σ
          ∎

compose-ext : ∀{Γ Δ Σ}{ρ : Rename Δ Σ} {ρ′ : Rename Γ Δ}
            → ((ext ρ) ∘ (ext ρ′)) ≡ ext (ρ ∘ ρ′)
compose-ext = extensionality λ x → lemma {x = x}
  where
  lemma : ∀{Γ Δ Σ}{ρ : Rename Δ Σ} {ρ′ : Rename Γ Δ} {x : Var (suc Γ)}
              → ((ext ρ) ∘ (ext ρ′)) x ≡ ext (ρ ∘ ρ′) x
  lemma {x = Z} = refl
  lemma {x = S x} = refl

compose-rename : ∀{Γ Δ Σ}{M : AST Γ}{ρ : Rename Δ Σ}{ρ′ : Rename Γ Δ} 
  → rename ρ (rename ρ′ M) ≡ rename (ρ ∘ ρ′) M
compose-renames : ∀{Γ Δ Σ}{S}{Ms : Args Γ S}{ρ : Rename Δ Σ}{ρ′ : Rename Γ Δ} 
  → renames ρ (renames ρ′ Ms) ≡ renames (ρ ∘ ρ′) Ms
compose-rename {M = ` x} = refl
compose-rename {M = o ⦅ Ms ⦆} = cong (_⦅_⦆ o) (compose-renames {Ms = Ms})
compose-renames {Ms = nil} = refl
compose-renames {Ms = bind M Ms}{ρ}{ρ′} =
  let ih1 = compose-rename {M = M}{ext ρ}{ext ρ′} in
  let ih2 = compose-renames {Ms = Ms}{ρ}{ρ′} in
  begin
      bind (rename (ext ρ) (rename (ext ρ′) M))
        (renames ρ (renames ρ′ Ms))
    ≡⟨ cong₂ bind ih1 ih2 ⟩ 
      bind (rename ((ext ρ) ∘ (ext ρ′)) M) (renames (ρ ∘ ρ′) Ms)
    ≡⟨ cong₂ bind (cong₂ rename (compose-ext{ρ = ρ}) refl) refl ⟩ 
      bind (rename (ext (ρ ∘ ρ′)) M) (renames (ρ ∘ ρ′) Ms)
    ∎
compose-renames {Ms = cons M Ms}{ρ}{ρ′} = cong₂ cons compose-rename compose-renames


commute-subst-rename : ∀{Γ Δ}{M : AST Γ}{σ : Subst Γ Δ}
                        {ρ : ∀{Γ} → Rename Γ (suc Γ)}
     → (∀{x : Var Γ} → exts σ (ρ x) ≡ rename ρ (σ x))
     → ⟪ exts σ ⟫ (rename ρ M) ≡ rename ρ (⟪ σ ⟫ M)
commute-subst-renames : ∀{Γ Δ}{S}{Ms : Args Γ S}{σ : Subst Γ Δ}
                        {ρ : ∀{Γ} → Rename Γ (suc Γ)}
     → (∀{x : Var Γ} → exts σ (ρ x) ≡ rename ρ (σ x))
     → substs (exts σ) (renames ρ Ms) ≡ renames ρ (substs σ Ms)
commute-subst-rename {M = ` x} r = r
commute-subst-rename {M = o ⦅ Ms ⦆} r =
  cong (_⦅_⦆ o) (commute-subst-renames {Ms = Ms} r)
commute-subst-renames {Ms = nil} r = refl
commute-subst-renames {Γ}{Δ}{_}{bind M Ms}{σ}{ρ} r =
  begin
    bind (⟪ exts (exts σ) ⟫ (rename (ext ρ) M)) (substs (exts σ) (renames ρ Ms))
  ≡⟨ cong₂ bind (commute-subst-rename{suc Γ}{suc Δ}{M}{exts σ}{ρ′} (λ {x} → H {x}))
                (commute-subst-renames{Ms = Ms} r) ⟩
    bind (rename (ext ρ) (⟪ exts σ ⟫ M)) (renames ρ (substs σ Ms))
  ∎
   where
   ρ′ : ∀ {Γ} → Rename Γ (suc Γ)
   ρ′ {zero} = λ ()
   ρ′ {suc Γ} = ext ρ

   H : {x : Var (suc Γ)} → exts (exts σ) (ext ρ x) ≡ rename (ext ρ) (exts σ x)
   H {Z} = refl
   H {S y} =
     begin
       exts (exts σ) (ext ρ (S y))
     ≡⟨⟩
       rename S_ (exts σ (ρ y)) 
     ≡⟨ cong (rename S_) r ⟩
       rename S_ (rename ρ (σ y))
     ≡⟨ compose-rename ⟩
       rename (S_ ∘ ρ) (σ y)
     ≡⟨⟩
       rename ((ext ρ) ∘ S_) (σ y)
     ≡⟨ sym compose-rename ⟩
       rename (ext ρ) (rename S_ (σ y))
     ≡⟨⟩
       rename (ext ρ) (exts σ (S y))
     ∎
commute-subst-renames {Γ}{Δ}{_}{cons M Ms}{σ}{ρ} r =
  cong₂ cons (commute-subst-rename{M = M} r) (commute-subst-renames{Ms = Ms} r)


exts-seq : ∀{Γ Δ Δ′} {σ₁ : Subst Γ Δ} {σ₂ : Subst Δ Δ′}
         → (exts σ₁ ⨟ exts σ₂) ≡ exts (σ₁ ⨟ σ₂)
exts-seq = extensionality λ x → lemma {x = x}
  where
  lemma : ∀{Γ Δ Δ′}{x : Var (suc Γ)} {σ₁ : Subst Γ Δ}{σ₂ : Subst Δ Δ′}
     → (exts σ₁ ⨟ exts σ₂) x ≡ exts (σ₁ ⨟ σ₂) x
  lemma {x = Z} = refl
  lemma {x = S x}{σ₁}{σ₂} =
     begin
       (exts σ₁ ⨟ exts σ₂) (S x)
     ≡⟨⟩
       ⟪ exts σ₂ ⟫ (rename S_ (σ₁ x))
     ≡⟨ commute-subst-rename{M = σ₁ x}{σ = σ₂}{ρ = S_} refl ⟩
       rename S_ (⟪ σ₂ ⟫ (σ₁ x))
     ≡⟨⟩
       rename S_ ((σ₁ ⨟ σ₂) x)
     ∎

sub-sub : ∀{Γ Δ Σ}{M : AST Γ} {σ₁ : Subst Γ Δ}{σ₂ : Subst Δ Σ} 
            → ⟪ σ₂ ⟫ (⟪ σ₁ ⟫ M) ≡ ⟪ σ₁ ⨟ σ₂ ⟫ M
sub-subs : ∀{Γ Δ Σ}{S}{Ms : Args Γ S} {σ₁ : Subst Γ Δ}{σ₂ : Subst Δ Σ} 
            → substs σ₂ (substs σ₁ Ms) ≡ substs (σ₁ ⨟ σ₂) Ms
sub-sub {M = ` x} = refl
sub-sub {M = op ⦅ Ms ⦆} = cong (op ⦅_⦆) (sub-subs{Ms = Ms})
sub-subs {Ms = nil} = refl
sub-subs {Ms = bind M Ms}{σ₁}{σ₂} =
  let ih1 = sub-sub {M = M}{exts σ₁}{exts σ₂} in
  let ih2 = sub-subs {Ms = Ms}{σ₁}{σ₂} in
  begin
    substs σ₂ (substs σ₁ (bind M Ms))
  ≡⟨⟩
    bind (⟪ exts σ₂ ⟫ (⟪ exts σ₁ ⟫ M)) (substs σ₂ (substs σ₁ Ms))
  ≡⟨ cong₂ bind ih1 ih2 ⟩
    bind (⟪ exts σ₁ ⨟ exts σ₂ ⟫ M) (substs (σ₁ ⨟ σ₂) Ms)
  ≡⟨ cong₂ bind (cong-app (cong ⟪_⟫ exts-seq) M) refl ⟩
    bind (⟪ exts (σ₁ ⨟ σ₂) ⟫ M) (substs (σ₁ ⨟ σ₂) Ms)
  ≡⟨⟩
    substs (σ₁ ⨟ σ₂) (bind M Ms)
  ∎
sub-subs {Ms = cons M Ms} = cong₂ cons (sub-sub{M = M}) (sub-subs{Ms = Ms})

rename-subst : ∀{Γ Δ Δ′}{M : AST Γ}{ρ : Rename Γ Δ}{σ : Subst Δ Δ′}
             → ⟪ σ ⟫ (rename ρ M) ≡ ⟪ σ ∘ ρ ⟫ M
rename-subst {Γ}{Δ}{Δ′}{M}{ρ}{σ} =
   begin
     ⟪ σ ⟫ (rename ρ M)
   ≡⟨ cong ⟪ σ ⟫ (rename-subst-ren{M = M}) ⟩
     ⟪ σ ⟫ (⟪ ren ρ ⟫ M)
   ≡⟨ sub-sub{M = M} ⟩
     ⟪ ren ρ ⨟ σ ⟫ M
   ≡⟨⟩
     ⟪ σ ∘ ρ ⟫ M
   ∎

sub-assoc : ∀{Γ Δ Σ Ψ} {σ : Subst Γ Δ} {τ : Subst Δ Σ}
             {θ : Subst Σ Ψ}
          → (σ ⨟ τ) ⨟ θ ≡ σ ⨟ τ ⨟ θ
sub-assoc {Γ}{Δ}{Σ}{Ψ}{σ}{τ}{θ} = extensionality λ x → lemma{x = x}
  where
  lemma : ∀ {x : Var Γ} → ((σ ⨟ τ) ⨟ θ) x ≡ (σ ⨟ τ ⨟ θ) x
  lemma {x} =
      begin
        ((σ ⨟ τ) ⨟ θ) x
      ≡⟨⟩
        ⟪ θ ⟫ (⟪ τ ⟫ (σ x))
      ≡⟨ sub-sub{M = σ x} ⟩
        ⟪ τ ⨟ θ ⟫ (σ x)
      ≡⟨⟩
        (σ ⨟ τ ⨟ θ) x
      ∎

subst-zero-exts-cons : ∀{Γ Δ}{σ : Subst Γ Δ}{M : AST Δ}
                     → exts σ ⨟ subst-zero M ≡ M • σ
subst-zero-exts-cons {Γ}{Δ}{σ}{M} =
    begin
      exts σ ⨟ subst-zero M
    ≡⟨ cong₂ _⨟_ exts-cons-shift subst-Z-cons-ids ⟩
      (` Z • (σ ⨟ ↑)) ⨟ (M • ids)
    ≡⟨ sub-dist ⟩
      (⟪ M • ids ⟫ (` Z)) • ((σ ⨟ ↑) ⨟ (M • ids))
    ≡⟨ cong₂ _•_ (sub-head{σ = ids}) refl ⟩
      M • ((σ ⨟ ↑) ⨟ (M • ids))
    ≡⟨ cong₂ _•_ refl (sub-assoc{σ = σ}) ⟩
      M • (σ ⨟ (↑ ⨟ (M • ids)))
    ≡⟨ cong₂ _•_ refl (cong₂ _⨟_ {x = σ} refl (sub-tail{M = M}{σ = ids})) ⟩
      M • (σ ⨟ ids)
    ≡⟨ cong₂ _•_ refl (sub-idR{σ = σ}) ⟩
      M • σ
    ∎

subst-commute : ∀{Γ Δ : ℕ}{N : AST (suc Γ)}{M : AST Γ}{σ : Subst Γ Δ }
    → (⟪ exts σ ⟫ N) [ ⟪ σ ⟫ M ] ≡ ⟪ σ ⟫ (N [ M ])
subst-commute {Γ}{Δ}{N}{M}{σ} =
     begin
       ⟪ exts σ ⟫ N [ ⟪ σ ⟫ M ]
     ≡⟨⟩
       ⟪ subst-zero (⟪ σ ⟫ M) ⟫ (⟪ exts σ ⟫ N)
     ≡⟨ cong-app (cong ⟪_⟫ subst-Z-cons-ids) (⟪ exts σ ⟫ N) ⟩
       ⟪ ⟪ σ ⟫ M • ids ⟫ (⟪ exts σ ⟫ N)
     ≡⟨ sub-sub {M = N} ⟩
       ⟪ (exts σ) ⨟ ((⟪ σ ⟫ M) • ids) ⟫ N
     ≡⟨ cong-app (cong ⟪_⟫ (cong₂ _⨟_ exts-cons-shift refl)) N ⟩
       ⟪ (` Z • (σ ⨟ ↑)) ⨟ (⟪ σ ⟫ M • ids) ⟫ N
     ≡⟨ cong-app (cong ⟪_⟫ (sub-dist {M = ` Z})) N ⟩
       ⟪ ⟪ ⟪ σ ⟫ M • ids ⟫ (` Z) • ((σ ⨟ ↑) ⨟ (⟪ σ ⟫ M • ids)) ⟫ N
     ≡⟨⟩
       ⟪ ⟪ σ ⟫ M • ((σ ⨟ ↑) ⨟ (⟪ σ ⟫ M • ids)) ⟫ N
     ≡⟨ cong-app (cong ⟪_⟫ (cong₂ _•_ refl (sub-assoc{σ = σ}))) N ⟩
       ⟪ ⟪ σ ⟫ M • (σ ⨟ ↑ ⨟ ⟪ σ ⟫ M • ids) ⟫ N
     ≡⟨ refl ⟩
       ⟪ ⟪ σ ⟫ M • (σ ⨟ ids) ⟫ N
     ≡⟨ cong-app (cong ⟪_⟫ (cong₂ _•_ refl (sub-idR{σ = σ}))) N ⟩
       ⟪ ⟪ σ ⟫ M • σ ⟫ N
     ≡⟨ cong-app (cong ⟪_⟫ (cong₂ _•_ refl (sub-idL{σ = σ}))) N ⟩
       ⟪ ⟪ σ ⟫ M • (ids ⨟ σ) ⟫ N
     ≡⟨ cong-app (cong ⟪_⟫ (sym sub-dist)) N ⟩
       ⟪ M • ids ⨟ σ ⟫ N
     ≡⟨ sym (sub-sub{M = N}) ⟩
       ⟪ σ ⟫ (⟪ M • ids ⟫ N)
     ≡⟨ cong ⟪ σ ⟫ (sym (cong-app (cong ⟪_⟫ subst-Z-cons-ids) N)) ⟩
       ⟪ σ ⟫ (N [ M ])
     ∎

rename-subst-commute : ∀{Γ Δ}{N : AST (suc Γ)}{M : AST Γ}{ρ : Rename Γ Δ }
    → (rename (ext ρ) N) [ rename ρ M ] ≡ rename ρ (N [ M ])
rename-subst-commute {Γ}{Δ}{N}{M}{ρ} =
     begin
       (rename (ext ρ) N) [ rename ρ M ]
     ≡⟨ cong-app (cong ⟪_⟫ (cong subst-zero rename-subst-ren)) (rename (ext ρ) N) ⟩
       (rename (ext ρ) N) [ ⟪ ren ρ ⟫ M ]
     ≡⟨ cong ⟪ subst-zero (⟪ ren ρ ⟫ M) ⟫ (rename-subst-ren{M = N}) ⟩
       (⟪ ren (ext ρ) ⟫ N) [ ⟪ ren ρ ⟫ M ]
     ≡⟨  cong ⟪ subst-zero (⟪ ren ρ ⟫ M) ⟫ ( cong-app (cong ⟪_⟫ ren-ext) N) ⟩
       (⟪ exts (ren ρ) ⟫ N) [ ⟪ ren ρ ⟫ M ]
     ≡⟨ subst-commute{N = N} ⟩
       ⟪ ren ρ ⟫ (N [ M ])
     ≡⟨ sym rename-subst-ren ⟩
       rename ρ (N [ M ])
     ∎


_〔_〕 : ∀ {Γ}
        → AST (suc (suc Γ))
        → AST Γ
          ------------
        → AST (suc Γ)
_〔_〕 {Γ} N M = ⟪ exts (subst-zero M) ⟫ N

substitution : ∀{Γ}{M : AST (suc (suc Γ))}{N : AST (suc Γ)}{L : AST Γ}
    → (M [ N ]) [ L ] ≡ (M 〔 L 〕) [ (N [ L ]) ]
substitution{M = M}{N = N}{L = L} =
   sym (subst-commute{N = M}{M = N}{σ = subst-zero L})


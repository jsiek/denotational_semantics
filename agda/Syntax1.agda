module Syntax (Op : Set) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Function using (_∘_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong; cong₂; cong-app)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)

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

data AST : ℕ → Set where

  `_ : ∀{Γ} → (x : Var Γ) → AST Γ

  α_ : ∀{Γ} → AST (suc Γ) → AST Γ
  
  _⦅_⦆ : ∀{Γ} → Op → List (AST Γ) → AST Γ

  
ext : ∀ {Γ Δ} → (Var Γ → Var Δ)
    -----------------------------------
  → Var (suc Γ) → Var (suc Δ)
ext ρ Z      =  Z
ext ρ (S x)  =  S (ρ x)


rename : ∀ {Γ Δ}
  → (Var Γ → Var Δ)
    -----------------------
  → (AST Γ → AST Δ)
renames : ∀ {Γ Δ}
  → (Var Γ → Var Δ)
    -------------------------------------
  → (List (AST Γ) → List (AST Δ))

rename ρ (` x)          =  ` (ρ x)
rename ρ (α N)          =  α (rename (ext ρ) N)
rename ρ (o ⦅ Ms ⦆)     =  o ⦅ renames ρ Ms ⦆
renames ρ []            = []
renames ρ (M ∷ Ms)      = rename ρ M ∷ renames ρ Ms


exts : ∀ {Γ Δ} → (Var Γ → AST Δ)
    -----------------------------
  → Var (suc Γ) → AST (suc Δ)
exts σ Z      =  ` Z
exts σ (S x)  =  rename S_ (σ x)

Subst : ℕ → ℕ → Set
Subst Γ Δ = Var Γ → AST Δ

⟪_⟫ : ∀ {Γ Δ}
  → Subst Γ Δ
    -------------
  → AST Γ → AST Δ
substs : ∀ {Γ Δ}
  → Subst Γ Δ
    ---------------------------
  → List (AST Γ) → List (AST Δ)

⟪ σ ⟫ (` k)          =  σ k
⟪ σ ⟫ (α N)          =  α (⟪ exts σ ⟫ N)
⟪ σ ⟫ (o ⦅ Ms ⦆)      =  o ⦅ substs σ Ms ⦆
substs σ []            = []
substs σ (M ∷ Ms)      = ⟪ σ ⟫ M ∷ substs σ Ms

subst-zero : ∀ {Γ} → (AST Γ) → Var (suc Γ) → (AST Γ)
subst-zero M Z      =  M
subst-zero M (S x)  =  ` x

_[_] : ∀ {Γ}
        → AST (suc Γ)
        → AST Γ
          ---------
        → AST Γ
_[_] N M =  ⟪ subst-zero M ⟫ N

Rename : ℕ → ℕ → Set
Rename Γ Δ = Var Γ → Var Δ


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


sub-op : ∀{Γ Δ} {σ : Subst Γ Δ} {o : Op}{Ms : List (AST Γ)}
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
renames-subst-ren : ∀ {Γ Δ} {ρ : Rename Γ Δ}{Ms : List (AST Γ)}
                 → renames ρ Ms ≡ substs (ren ρ) Ms
rename-subst-ren {M = ` x} = refl
rename-subst-ren {ρ = ρ}{M = α N} =
  begin
      rename ρ (α N)
    ≡⟨⟩
      α rename (ext ρ) N
    ≡⟨ cong α_ (rename-subst-ren {ρ = ext ρ}{M = N}) ⟩
      α ⟪ ren (ext ρ) ⟫ N
    ≡⟨ cong α_ (cong-app (cong ⟪_⟫ ren-ext) N) ⟩
      α ⟪ exts (ren ρ) ⟫  N
    ≡⟨⟩
      ⟪ ren ρ ⟫ (α N)
  ∎
rename-subst-ren {M = o ⦅ Ms ⦆} = cong₂ _⦅_⦆ refl renames-subst-ren
renames-subst-ren {Ms = []} = refl
renames-subst-ren {Ms = M ∷ Ms} = cong₂ _∷_ rename-subst-ren renames-subst-ren


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


exts-ids : ∀{Γ}
         → exts ids ≡ ids
exts-ids {Γ} = extensionality lemma
  where lemma : (x : Var (suc Γ)) → exts ids x ≡ ids x
        lemma Z = refl
        lemma (S x) = refl


sub-id : ∀{Γ} {M : AST Γ}
         → ⟪ ids ⟫ M ≡ M
subs-id : ∀{Γ} {Ms : List (AST Γ)}
         → substs ids Ms ≡ Ms
sub-id {M = ` x} = refl
sub-id {M = α N} = 
   begin
     ⟪ ids ⟫ (α N)
   ≡⟨⟩
     α ⟪ exts ids ⟫ N
   ≡⟨ cong α_ (cong-app (cong ⟪_⟫ exts-ids) N)  ⟩
     α ⟪ ids ⟫ N
   ≡⟨ cong α_ sub-id ⟩
     α N
   ∎
sub-id {M = o ⦅ Ms ⦆} = cong₂ _⦅_⦆ refl subs-id
subs-id {Ms = []} = refl
subs-id {Ms = M ∷ Ms} = cong₂ _∷_ sub-id subs-id


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
compose-renames : ∀{Γ Δ Σ}{Ms : List (AST Γ)}{ρ : Rename Δ Σ}{ρ′ : Rename Γ Δ} 
  → renames ρ (renames ρ′ Ms) ≡ renames (ρ ∘ ρ′) Ms
compose-rename {M = ` x} = refl
compose-rename {Γ}{Δ}{Σ}{α N}{ρ}{ρ′} = cong α_ G
  where
  G : rename (ext ρ) (rename (ext ρ′) N) ≡ rename (ext (ρ ∘ ρ′)) N
  G =
      begin
        rename (ext ρ) (rename (ext ρ′) N)
      ≡⟨ compose-rename{ρ = ext ρ}{ρ′ = ext ρ′} ⟩
        rename ((ext ρ) ∘ (ext ρ′)) N
      ≡⟨ cong₂ rename compose-ext refl ⟩
        rename (ext (ρ ∘ ρ′)) N
      ∎        
compose-rename {M = o ⦅ Ms ⦆} = cong₂ _⦅_⦆ refl compose-renames
compose-renames {Ms = []} = refl
compose-renames {Ms = M ∷ Ms} = cong₂ _∷_ compose-rename compose-renames


commute-subst-rename : ∀{Γ Δ}{M : AST Γ}{σ : Subst Γ Δ}
                        {ρ : ∀{Γ} → Rename Γ (suc Γ)}
     → (∀{x : Var Γ} → exts σ (ρ x) ≡ rename ρ (σ x))
     → ⟪ exts σ ⟫ (rename ρ M) ≡ rename ρ (⟪ σ ⟫ M)
commute-subst-renames : ∀{Γ Δ}{Ms : List (AST Γ)}{σ : Subst Γ Δ}
                        {ρ : ∀{Γ} → Rename Γ (suc Γ)}
     → (∀{x : Var Γ} → exts σ (ρ x) ≡ rename ρ (σ x))
     → substs (exts σ) (renames ρ Ms) ≡ renames ρ (substs σ Ms)
commute-subst-rename {M = ` x} r = r
commute-subst-rename{Γ}{Δ}{α N}{σ}{ρ} r =
   cong α_ (commute-subst-rename{suc Γ}{suc Δ}{N}
               {exts σ}{ρ = ρ′} (λ {x} → H {x}))
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
commute-subst-rename {M = o ⦅ Ms ⦆}{ρ = ρ} r =
   cong₂ _⦅_⦆ refl (commute-subst-renames{Ms = Ms}{ρ = ρ} r)
commute-subst-renames {Ms = []} r = refl
commute-subst-renames {Ms = M ∷ Ms} r =
  cong₂ _∷_ (commute-subst-rename{M = M} r) (commute-subst-renames r)


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
sub-subs : ∀{Γ Δ Σ}{Ms : List (AST Γ)} {σ₁ : Subst Γ Δ}{σ₂ : Subst Δ Σ} 
            → substs σ₂ (substs σ₁ Ms) ≡ substs (σ₁ ⨟ σ₂) Ms
sub-sub {M = ` x} = refl
sub-sub {Γ}{Δ}{Σ}{α N}{σ₁}{σ₂} =
   begin
     ⟪ σ₂ ⟫ (⟪ σ₁ ⟫ (α N))
   ≡⟨⟩
     α ⟪ exts σ₂ ⟫ (⟪ exts σ₁ ⟫ N)
   ≡⟨ cong α_ (sub-sub{M = N}{σ₁ = exts σ₁}{σ₂ = exts σ₂}) ⟩
     α ⟪ exts σ₁ ⨟ exts σ₂ ⟫ N
   ≡⟨ cong α_ (cong-app (cong ⟪_⟫ exts-seq) N) ⟩
     α ⟪ exts ( σ₁ ⨟ σ₂) ⟫ N
   ∎
sub-sub {M = o ⦅ Ms ⦆} = cong₂ _⦅_⦆ refl (sub-subs{Ms = Ms})

sub-subs {Ms = []} = refl
sub-subs {Ms = M ∷ Ms} = cong₂ _∷_ (sub-sub{M = M}) sub-subs


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



module ToANF where

open import Lambda
open import ModelISWIM

open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; cong; cong₂)
open import Data.Nat using (ℕ; suc ; zero)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Agda.Primitive using (lzero)
open import Lambda
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using (contradiction)
open import Data.Empty using (⊥-elim) renaming (⊥ to Bot)
open import Relation.Nullary using (Dec; yes; no)
open import Data.Unit


{-

  An intermediate language in administrative-normal form (ANF).

-}

data Op : Set where
  op-lam : Op
  op-app : Op
  op-let : Op
  op-const : (p : Prim) → rep p → Op

sig : Op → List ℕ
sig op-lam = 1 ∷ []
sig op-app = 0 ∷ 0 ∷ []
sig op-let = 0 ∷ 1 ∷ []
sig (op-const p k) = []

import Syntax
module ASTMod = Syntax3 Op sig
open ASTMod using (AST; `_; _⦅_⦆; Subst; Ctx; plug;
                   rename; ⟪_⟫; _[_]; subst-zero; bind; ast; cons; nil; exts;
                   rename-id) public
open ASTMod using (_•_; _⨟_; ↑; exts-cons-shift)

data Simp : Context → Set where
  $_ :  ∀ {Γ}{p : Prim} → rep p → Simp Γ
  
  `_ : ∀ {Γ}
    → Γ ∋ ★
      -----
    → Simp Γ


data ANF : Context → Set where
  s_ : ∀ {Γ}
    → Simp Γ
      ------
    → ANF Γ

  ƛ_  :  ∀ {Γ}
    → ANF (Γ , ★)
      -----------
    → ANF Γ

  _·_ : ∀ {Γ}
    → Simp Γ
    → Simp Γ
      ------
    → ANF Γ
    
  bind_then_ : ∀ {Γ}
    → ANF Γ
    → ANF (Γ , ★)
      ------
    → ANF Γ
  
infix 3 _⊢s_↓_

data _⊢s_↓_ : ∀{Γ} → Env Γ → Simp Γ → Value → Set where
  var : ∀ {Γ} {γ : Env Γ} {x v}
                      → v ⊑ nth x γ
        -------------
      → γ ⊢s (` x) ↓ v

  lit-intro : ∀{Γ}{γ : Env Γ}{P : Prim} {p : rep P} {v : Value}
        → v ∈ P 〚 p 〛
          ----------------------
        → γ ⊢s ($_ {Γ} {P} p) ↓ v


infix 3 _⊢₁_↓_

data _⊢₁_↓_ : ∀{Γ} → Env Γ → ANF Γ → Value → Set where

  eval-simp : ∀ {Γ} {γ : Env Γ} {S' v}
      → γ ⊢s S' ↓ v
        ---------------
      → γ ⊢₁ (s S') ↓ v
      
  ↦-elim : ∀ {Γ} {γ : Env Γ} {S₁ S₂ v v₁ v₂}
        → γ ⊢s S₁ ↓ (v₁ ↦ v₂)  →  γ ⊢s S₂ ↓ v₁  → v ⊑ v₂
          ------------------------------------
        → γ ⊢₁ (S₁ · S₂) ↓ v

  ↦-intro : ∀ {Γ} {γ : Env Γ} {M v₁ v₂}
        → (γ , v₁) ⊢₁ M ↓ v₂
          ---------------------
        → γ ⊢₁ (ƛ M) ↓ (v₁ ↦ v₂)

  ⊥-intro : ∀ {Γ} {γ : Env Γ} {M}
          -------------
        → γ ⊢₁ (ƛ M) ↓ ⊥

  ⊔-intro : ∀ {Γ} {γ : Env Γ} {M v₁ v₂}
        → γ ⊢₁ M ↓ v₁  →  γ ⊢₁ M ↓ v₂
          -------------------------
        → γ ⊢₁ M ↓ (v₁ ⊔ v₂)

  eval-bind : ∀ {Γ} {γ : Env Γ} {M N v₁ v₂}
        → γ ⊢₁ M ↓ v₁  → (γ , v₁) ⊢₁ N ↓ v₂
          ---------------------------------
        → γ ⊢₁ (bind M then N) ↓ v₂


SemANF : ∀{Γ} → ANF Γ → Env Γ → Value → Set
SemANF M γ v = γ ⊢₁ M ↓ v

↦-intro' : ∀{Γ}{γ : Env Γ}{M : Γ , ★ ⊢ ★}{v₁ v₂ : Value}
           → ℒ M (γ , v₁) v₂
           → ℒ (ƛ M) γ (v₁ ↦ v₂)
↦-intro' d = ↦-intro d



rename-Simp : ∀ {Γ Δ}
  → Rename Γ Δ
    ---------------
  → (Simp Γ → Simp Δ)
rename-Simp ρ ($_ {p = P} x) = $_ {p = P} x
rename-Simp ρ (` x)          =  ` (ρ x)

rename-ANF : ∀ {Γ Δ}
  → Rename Γ Δ
    ---------------
  → (ANF Γ → ANF Δ)
rename-ANF ρ (s S')          = s (rename-Simp ρ S')
rename-ANF ρ (ƛ N)           = ƛ (rename-ANF (ext ρ) N)
rename-ANF ρ (S₁ · S₂)       = rename-Simp ρ S₁ · rename-Simp ρ S₂
rename-ANF ρ (bind M then N) = bind rename-ANF ρ M
                               then rename-ANF (ext ρ) N
to-ANF : ∀{Γ} → Γ ⊢ ★ → ANF Γ
to-ANF {Γ} ($_ {p = p} x) = s ($_ {p = p} x)
to-ANF {Γ} (` x) = s (` x)
to-ANF {Γ} (ƛ M) = ƛ (to-ANF M)
to-ANF {Γ} (M₁ · M₂) =
  let x = to-ANF M₁ in
  let y = rename-ANF (λ {A} → λ x → S x) (to-ANF M₂) in 
  bind x then (bind y then ((` (S Z)) · (` Z)))



sub-Simp : ∀ {Γ} {γ : Env Γ} {M v₁ v₂}
  → γ ⊢s M ↓ v₁  →  v₂ ⊑ v₁
    ----------
  → γ ⊢s M ↓ v₂
sub-Simp (var lt1) lt2 = var (Trans⊑ lt2 lt1)
sub-Simp (lit-intro d) lt2 = lit-intro (sub-prim d lt2)

sub-ANF : ∀ {Γ} {γ : Env Γ} {M v₁ v₂}
  → γ ⊢₁ M ↓ v₁  →  v₂ ⊑ v₁
    ----------
  → γ ⊢₁ M ↓ v₂
sub-ANF (eval-simp d) lt = eval-simp (sub-Simp d lt)
sub-ANF (↦-elim d₁ d₂ lt2) lt3 = ↦-elim d₁ d₂ (Trans⊑ lt3 lt2)
sub-ANF (↦-intro d) Bot⊑ = ⊥-intro
sub-ANF (↦-intro d) Fun⊑ = ↦-intro d
sub-ANF (↦-intro d) (ConjL⊑ lt lt₁) =
   ⊔-intro (sub-ANF (↦-intro d) lt) (sub-ANF (↦-intro d) lt₁)
sub-ANF ⊥-intro Bot⊑ = ⊥-intro
sub-ANF ⊥-intro (ConjL⊑ lt lt₁) =
   ⊔-intro (sub-ANF ⊥-intro lt) (sub-ANF ⊥-intro lt₁)
sub-ANF (⊔-intro d d₁) Bot⊑ = sub-ANF d₁ Bot⊑
sub-ANF (⊔-intro d d₁) (ConjL⊑ lt lt₁) =
   ⊔-intro (sub-ANF (⊔-intro d d₁) lt) (sub-ANF (⊔-intro d d₁) lt₁)
sub-ANF (⊔-intro d d₁) (ConjR1⊑ lt) = sub-ANF d lt
sub-ANF (⊔-intro d d₁) (ConjR2⊑ lt) = sub-ANF d₁ lt
sub-ANF (eval-bind d₁ d₂) lt =
   eval-bind (sub-ANF d₁ Refl⊑) (sub-ANF d₂ lt)


rename-Simp-pres : ∀ {Γ Δ v} {γ : Env Γ} {δ : Env Δ} {M : Simp Γ}
  → (ρ : Rename Γ Δ)
  → (∀ {n : Γ ∋ ★} → nth n γ ⊑ nth (ρ n) δ)
  → γ ⊢s M ↓ v
    ----------------------------------------
  → δ ⊢s (rename-Simp ρ M) ↓ v
rename-Simp-pres ρ nth-eq (var{x = x} lt) =  var (Trans⊑ lt (nth-eq {x}))
rename-Simp-pres ρ nth-eq (lit-intro d) =  lit-intro d


rename-ANF-pres : ∀ {Γ Δ v} {γ : Env Γ} {δ : Env Δ} {M : ANF Γ}
  → (ρ : Rename Γ Δ)
  → (∀ {n : Γ ∋ ★} → nth n γ ⊑ nth (ρ n) δ)
  → γ ⊢₁ M ↓ v
    ----------------------------------------
  → δ ⊢₁ (rename-ANF ρ M) ↓ v
rename-ANF-pres ρ nth-eq (eval-simp d) =
   eval-simp (rename-Simp-pres ρ nth-eq d)
rename-ANF-pres ρ nth-eq (↦-elim d d₁ lt2) =
   ↦-elim (rename-Simp-pres ρ nth-eq d) (rename-Simp-pres ρ nth-eq d₁) lt2
rename-ANF-pres ρ nth-eq (↦-intro d) =
   ↦-intro (rename-ANF-pres (ext ρ) (λ {n} → ext-nth ρ nth-eq {n}) d)
rename-ANF-pres ρ nth-eq ⊥-intro = ⊥-intro
rename-ANF-pres ρ nth-eq (⊔-intro d d₁) =
   ⊔-intro (rename-ANF-pres ρ nth-eq d) (rename-ANF-pres ρ nth-eq d₁)
rename-ANF-pres ρ nth-eq (eval-bind d₁ d₂) =
   eval-bind (rename-ANF-pres ρ nth-eq d₁)
       (rename-ANF-pres (ext ρ) ((λ {n} → ext-nth ρ nth-eq {n})) d₂)

to-ANF-pres : ∀{Γ}{γ : Env Γ}{M : Γ ⊢ ★}{v}
            → γ ⊢ M ↓ v
              -----------------
            → γ ⊢₁ to-ANF M ↓ v
to-ANF-pres (var lt) = eval-simp (var lt)
to-ANF-pres (lit-intro d) = eval-simp (lit-intro d)
to-ANF-pres (↦-elim d₁ d₂ lt) =
   let ih2 = to-ANF-pres d₂ in
   let d₂' = rename-ANF-pres S_ (λ {n} → Refl⊑) ih2 in
   let ap = ↦-elim (var Refl⊑) (var Refl⊑) lt in
   eval-bind (to-ANF-pres d₁) (eval-bind d₂' ap)
to-ANF-pres (↦-intro d) = ↦-intro (to-ANF-pres d)
to-ANF-pres ⊥-intro = ⊥-intro
to-ANF-pres (⊔-intro d₁ d₂) = ⊔-intro (to-ANF-pres d₁) (to-ANF-pres d₂)


rename-Simp-reflect : ∀ {Γ Δ v} {γ : Env Γ} {δ : Env Δ} { M : Simp Γ}
  → {ρ : Rename Γ Δ}
  → (∀ {n : Γ ∋ ★} → nth (ρ n) δ ≡ nth n γ)
  → δ ⊢s rename-Simp ρ M ↓ v
    ------------------------------------
  → γ ⊢s M ↓ v
rename-Simp-reflect {M = $ x} all-n (lit-intro d) = lit-intro d
rename-Simp-reflect {M = ` x} all-n (var lt) rewrite all-n {x} = var lt


rename-ANF-reflect : ∀ {Γ Δ v} {γ : Env Γ} {δ : Env Δ} { M : ANF Γ}
  → {ρ : Rename Γ Δ}
  → (∀ {n : Γ ∋ ★} → nth (ρ n) δ ≡ nth n γ)
  → δ ⊢₁ rename-ANF ρ M ↓ v
    ------------------------------------
  → γ ⊢₁ M ↓ v
rename-ANF-reflect {M = s S'} all-n (eval-simp d) =
   eval-simp (rename-Simp-reflect all-n d)
rename-ANF-reflect {M = s S'} all-n (⊔-intro d₁ d₂) =
   let ih1 = rename-ANF-reflect all-n d₁ in 
   let ih2 = rename-ANF-reflect all-n d₂ in 
   ⊔-intro ih1 ih2
rename-ANF-reflect {Γ}{Δ}{v₁ ↦ v₂}{γ}{δ}{ƛ M'}{ρ} all-n (↦-intro d) =
   ↦-intro (rename-ANF-reflect (λ {n} → nth-ext {n}) d)
   where
   nth-ext : {n : Γ , ★ ∋ ★} → nth (ext ρ n) (δ , v₁) ≡ nth n (γ , v₁) 
   nth-ext {Z} = refl
   nth-ext {S n} = all-n
rename-ANF-reflect {M = ƛ M'} all-n ⊥-intro = ⊥-intro
rename-ANF-reflect {M = ƛ M'} all-n (⊔-intro d₁ d₂) =
   ⊔-intro (rename-ANF-reflect all-n d₁) (rename-ANF-reflect all-n d₂)
rename-ANF-reflect {M = M₁ · M₂} all-n (↦-elim d₁ d₂ lt2) =
   ↦-elim (rename-Simp-reflect all-n d₁) (rename-Simp-reflect all-n d₂) lt2
rename-ANF-reflect {M = M₁ · M₂} all-n (⊔-intro d₁ d₂) =
   ⊔-intro (rename-ANF-reflect all-n d₁) (rename-ANF-reflect all-n d₂)
rename-ANF-reflect {Γ}{Δ}{v}{γ}{δ}{bind M₁ then M₂}{ρ} all-n
      (eval-bind {v₁ = v₁} d₁ d₂) =
   let ih1 = rename-ANF-reflect all-n d₁ in 
   let ih2 = rename-ANF-reflect ((λ {n} → nth-ext {n})) d₂ in
   eval-bind ih1 ih2
   where
   nth-ext : {n : Γ , ★ ∋ ★} → nth (ext ρ n) (δ , v₁) ≡ nth n (γ , v₁) 
   nth-ext {Z} = refl
   nth-ext {S n} = all-n
rename-ANF-reflect {M = bind M₁ then M₂} all-n (⊔-intro d₁ d₂) =
   let ih1 = rename-ANF-reflect all-n d₁ in 
   let ih2 = rename-ANF-reflect all-n d₂ in 
   ⊔-intro ih1 ih2

rename-commutes-ANF : ∀{Γ Δ}{ρ : Rename Γ Δ}{M : Γ ⊢ ★} → 
  rename-ANF ρ (to-ANF M) ≡ to-ANF (rename ρ M)
rename-commutes-ANF = {!!}

to-ANF-reflect : ∀{Γ}{γ : Env Γ}{M : Γ ⊢ ★}{L : ANF Γ}{v}
            → γ ⊢₁ L ↓ v  →  to-ANF M ≡ L
              ---------------------------
            → γ ⊢ M ↓ v
to-ANF-reflect {M = $ x} (eval-simp (lit-intro lt)) refl = lit-intro lt
to-ANF-reflect {M = ` x} (eval-simp (var lt)) refl = var lt
to-ANF-reflect {M = ƛ M} (eval-simp d) ()
to-ANF-reflect {M = M · M₁} (eval-simp d) ()
to-ANF-reflect {M = $ x} (↦-elim d₁ d₂ lt) ()
to-ANF-reflect {M = ` x} (↦-elim d₁ d₂ lt) ()
to-ANF-reflect {M = ƛ M} (↦-elim d₁ d₂ lt) ()
to-ANF-reflect {M = M · M₁} (↦-elim d₁ d₂ lt) ()
to-ANF-reflect {M = $ x} (↦-intro d) ()
to-ANF-reflect {M = ` x} (↦-intro d) ()
to-ANF-reflect {M = ƛ M} (↦-intro d) refl = ↦-intro (to-ANF-reflect d refl)
to-ANF-reflect {M = M · M₁} (↦-intro d) ()
to-ANF-reflect {M = $ x} ⊥-intro ()
to-ANF-reflect {M = ` x} ⊥-intro ()
to-ANF-reflect {M = ƛ M} ⊥-intro refl = ⊥-intro
to-ANF-reflect {M = M · M₁} ⊥-intro ()
to-ANF-reflect {M = M} (⊔-intro d₁ d₂) eqL =
   ⊔-intro (to-ANF-reflect d₁ eqL) (to-ANF-reflect d₂ eqL)
to-ANF-reflect {M = $ x} (eval-bind d₁ d₂) ()
to-ANF-reflect {M = ` x} (eval-bind d₁ d₂) ()
to-ANF-reflect {M = ƛ M} (eval-bind d₁ d₂) ()
to-ANF-reflect {Γ}{γ}{M₁ · M₂} (eval-bind d₁ (⊔-intro d₂ d₃)) refl 
   rewrite rename-commutes-ANF {Γ}{Γ , ★}{λ {A} → S_}{M₂} =
   let ih1 = to-ANF-reflect d₁ refl in
   let ih2 = to-ANF-reflect d₂ {!!} in
   {!!}
to-ANF-reflect{Γ}{γ}{M₁ · M₂}
   (eval-bind d₁ (eval-bind d₂ (↦-elim (var lt1) (var lt2) lt3))) refl
   rewrite rename-commutes-ANF {Γ}{Γ , ★}{λ {A} → S_}{M₂} =
   let ih1 = to-ANF-reflect d₁ refl in
   let ih2 = to-ANF-reflect d₂ refl in
   let x = rename-reflect{γ = γ} {ρ = (λ {A} → S_)} (λ {n} → refl) ih2 in
   ↦-elim (sub ih1 lt1) (sub x lt2) lt3

to-ANF-reflect {M = M₁ · M₂} (eval-bind d₁ (eval-bind d₂ (⊔-intro d₃ d₄))) refl = {!!}


{-

 to do: alternate proof that is more equational,
 perhaps doesn't use induction?

-}

ANF-equal : ∀{Γ}{M : Γ ⊢ ★} → (ℒ M) ≃ (SemANF (to-ANF M))
ANF-equal {Γ} {$_ {p = p} x} {γ}{v} = ⟨ G , H ⟩
   where G : ∀{v} → ℒ ($_ {p = p} x) γ v → SemANF (s ($_ {p = p} x)) γ v
         G (lit-intro d) = eval-simp (lit-intro d)
         G (⊔-intro d₁ d₂) = ⊔-intro (G d₁) (G d₂)

         H : ∀{v} → SemANF (s ($ x)) γ v → ℒ ($ x) γ v
         H (eval-simp (lit-intro d)) = lit-intro d
         H (⊔-intro d₁ d₂) = ⊔-intro (H d₁) (H d₂)
ANF-equal {Γ} {` x} {γ}{v} = ⟨ G , H ⟩
   where G : ∀{v} → ℒ (` x) γ v → SemANF (s (` x)) γ v
         G (var lt) = eval-simp (var lt)
         G (⊔-intro d₁ d₂) = ⊔-intro (G d₁) (G d₂)

         H : ∀{v} → SemANF (s (` x)) γ v → ℒ (` x) γ v
         H (eval-simp (var lt)) = var lt
         H (⊔-intro d₁ d₂) = ⊔-intro (H d₁) (H d₂)

ANF-equal {Γ} {ƛ M}{γ}{v} = ⟨ G , H ⟩
   where G : ∀{v} → ℒ (ƛ M) γ v → SemANF (ƛ to-ANF M) γ v
         G (↦-intro d) = ↦-intro ((proj₁ ANF-equal) d)
         G ⊥-intro = ⊥-intro
         G (⊔-intro d₁ d₂) = ⊔-intro (G d₁) (G d₂)

         H : ∀{v} → SemANF (ƛ to-ANF M) γ v → ℒ (ƛ M) γ v
         H (↦-intro d) = ↦-intro ((proj₂ ANF-equal) d)
         H ⊥-intro = ⊥-intro
         H (⊔-intro d₁ d₂) = ⊔-intro (H d₁) (H d₂)

ANF-equal {Γ} {L · M}{γ}{v} = ⟨ G , H ⟩
  where G : ∀{v} → ℒ (L · M) γ v → SemANF (to-ANF (L · M)) γ v
        G (↦-elim d₁ d₂ lt) =
           let ih1 = proj₁ (ANF-equal{M = L}) in
           let ih2 = proj₁ (ANF-equal{M = M}) in
           let d₁' = ih1 d₁ in
           let d₂' = ih2 d₂ in
           eval-bind d₁' (eval-bind (rename-ANF-pres S_ (λ {n} → Refl⊑) d₂')
              (↦-elim (var Refl⊑) (var Refl⊑ ) lt))
        G (⊔-intro d₁ d₂) = ⊔-intro (G d₁) (G d₂)

        H : ∀{v} → SemANF (to-ANF (L · M)) γ v → ℒ (L · M) γ v
        H (⊔-intro d₁ d₂) = ⊔-intro (H d₁) (H d₂)
        H (eval-bind d₁ d₂) = {!!}

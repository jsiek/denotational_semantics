module Denot where

open import Value

open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; cong; cong₂)
open import Data.Nat using (ℕ; suc ; zero)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Agda.Primitive using (lzero)
open import Lambda
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using (contradiction)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (Dec; yes; no)


base-eval : ∀{B : Base} → base-rep B → Value
base-eval {Nat} n = lit n
base-eval {𝔹} b = lit b

data _∈_〚_〛 : Value → (P : Prim) → rep P → Set where
   base-val : ∀{B}{b : base-rep B}
              --------------------------
            → (base-eval b) ∈ (` B)〚 b 〛
   fun-val :  ∀{B}{P}{f : base-rep B → rep P}{k : base-rep B}{v : Value}
            → v ∈ P 〚 f k 〛
              -------------------------------
            → (lit {B} k ↦ v) ∈ (B ⇒ P)〚 f 〛
   ⊔-val :  ∀{P : Prim}{p : rep P}{v₁ v₂ : Value}
            → v₁ ∈ P 〚 p 〛  →   v₂ ∈ P 〚 p 〛
              --------------------------------
            → (v₁ ⊔ v₂) ∈ P 〚 p 〛
   ⊥-val :  ∀{P : Prim}{p : rep P}
              ------------
            → ⊥ ∈ P 〚 p 〛


infix 3 _⊢_↓_

data _⊢_↓_ : ∀{Γ} → Env Γ → (Γ ⊢ ★) → Value → Set where
  var : ∀ {Γ} {γ : Env Γ} {x v}
                      → v ⊑ nth x γ
        -------------
      → γ ⊢ (` x) ↓ v

  lit-intro : ∀{Γ}{γ : Env Γ}{P : Prim} {p : rep P} {v : Value}
        → v ∈ P 〚 p 〛
          ----------------------
        → γ ⊢ ($_ {Γ} {P} p) ↓ v

  ↦-elim : ∀ {Γ} {γ : Env Γ} {M₁ M₂ v v₁ v₂}
        → γ ⊢ M₁ ↓ (v₁ ↦ v₂)  →  γ ⊢ M₂ ↓ v₁  → v ⊑ v₂
          ----------------------------------
        → γ ⊢ (M₁ · M₂) ↓ v

  ↦-intro : ∀ {Γ} {γ : Env Γ} {M v₁ v₂}
        → (γ , v₁) ⊢ M ↓ v₂
          ---------------------
        → γ ⊢ (ƛ M) ↓ (v₁ ↦ v₂)

  ⊥-intro : ∀ {Γ} {γ : Env Γ} {M}
          -------------
        → γ ⊢ (ƛ M) ↓ ⊥

  ⊔-intro : ∀ {Γ} {γ : Env Γ} {M v₁ v₂}
        → γ ⊢ M ↓ v₁  →  γ ⊢ M ↓ v₂
          -------------------------
        → γ ⊢ M ↓ (v₁ ⊔ v₂)


sub-prim : ∀ {P : Prim}{p : rep P}{v₁ v₂ : Value}
  → v₁ ∈ P 〚 p 〛 →  v₂ ⊑ v₁
    -------------
  → v₂ ∈ P 〚 p 〛
sub-prim (base-val {Nat}) Bot⊑ = ⊥-val
sub-prim (base-val {Nat}) Lit⊑ = base-val
sub-prim (base-val {Nat}) (ConjL⊑ lt lt₁) =
    ⊔-val (sub-prim base-val lt) (sub-prim base-val lt₁)
sub-prim (base-val {𝔹}) Bot⊑ = ⊥-val
sub-prim (base-val {𝔹}) Lit⊑ = base-val
sub-prim (base-val {𝔹}) (ConjL⊑ lt lt₁) =
    ⊔-val (sub-prim base-val lt) (sub-prim base-val lt₁)
sub-prim (fun-val d) Bot⊑ = ⊥-val
sub-prim (fun-val d) Fun⊑ = fun-val d
sub-prim (fun-val d) (ConjL⊑ lt lt₁) =
    ⊔-val (sub-prim (fun-val d) lt) (sub-prim (fun-val d) lt₁)
sub-prim (⊔-val d d₁) Bot⊑ = ⊥-val
sub-prim (⊔-val d d₁) (ConjL⊑ lt lt₁) =
    ⊔-val (sub-prim (⊔-val d d₁) lt) (sub-prim (⊔-val d d₁) lt₁)
sub-prim (⊔-val d d₁) (ConjR1⊑ lt) = sub-prim d lt
sub-prim (⊔-val d d₁) (ConjR2⊑ lt) = sub-prim d₁ lt
sub-prim ⊥-val Bot⊑ = ⊥-val
sub-prim ⊥-val (ConjL⊑ lt lt₁) =
    ⊔-val (sub-prim ⊥-val lt) (sub-prim ⊥-val lt₁)


sub : ∀ {Γ} {γ : Env Γ} {M v₁ v₂}
  → γ ⊢ M ↓ v₁  →  v₂ ⊑ v₁
    ----------
  → γ ⊢ M ↓ v₂
sub (var lt1) lt2 = var (Trans⊑ lt2 lt1)
sub (lit-intro d) lt2 = lit-intro (sub-prim d lt2)
sub (↦-elim d₁ d₂ lt2) lt3 = ↦-elim d₁ d₂ (Trans⊑ lt3 lt2)
sub (↦-intro d) Bot⊑ = ⊥-intro
sub (↦-intro d) Fun⊑ = ↦-intro d
sub (↦-intro d) (ConjL⊑ lt lt₁) =
  ⊔-intro (sub (↦-intro d) lt) (sub (↦-intro d) lt₁)
sub ⊥-intro Bot⊑ = ⊥-intro
sub ⊥-intro (ConjL⊑ lt lt₁) = ⊔-intro (sub ⊥-intro lt) (sub ⊥-intro lt₁)
sub (⊔-intro d d₁) Bot⊑ = sub d₁ Bot⊑
sub (⊔-intro d d₁) (ConjL⊑ lt lt₁) =
  ⊔-intro (sub (⊔-intro d d₁) lt) (sub (⊔-intro d d₁) lt₁)
sub (⊔-intro d d₁) (ConjR1⊑ lt) = sub d lt
sub (⊔-intro d d₁) (ConjR2⊑ lt) = sub d₁ lt


denot-any-bot : ∀ {Γ} {γ : Env Γ} {M v₁}
  → γ ⊢ M ↓ v₁
    ----------
  → γ ⊢ M ↓ ⊥
denot-any-bot d = sub d Bot⊑


infix 4 _≅_
_≅_ : ∀ {Γ} → (Γ ⊢ ★) → (Γ ⊢ ★) → Set
_≅_ {Γ} M N = (∀ {γ : Env Γ} → ∀ {v} → (γ ⊢ M ↓ v) iff (γ ⊢ N ↓ v))

equal-refl : ∀ {Γ : Context} → {M : Γ ⊢ ★}
  → M ≅ M
equal-refl = ⟨ (λ x → x) , (λ x → x) ⟩

equal-sym : ∀ {Γ : Context} → {M : Γ ⊢ ★} → {N : Γ ⊢ ★}
  → M ≅ N
    -----
  → N ≅ M
equal-sym eq = ⟨ proj₂ eq , proj₁ eq ⟩

equal-trans : ∀ {Γ : Context} → {M₁ : Γ ⊢ ★} → {M₂ : Γ ⊢ ★} → {M₃ : Γ ⊢ ★}
  → M₁ ≅ M₂ → M₂ ≅ M₃
    -----------------
  → M₁ ≅ M₃
equal-trans eq1 eq3 =
  ⟨ (λ z → proj₁ eq3 (proj₁ eq1 z)) , (λ z → proj₂ eq1 (proj₂ eq3 z)) ⟩

ext-nth : ∀ {Γ Δ v} {γ : Env Γ} {δ : Env Δ}
  → (ρ : ∀ {A} → Γ ∋ A → Δ ∋ A)
  → (∀ {n : Γ ∋ ★} → nth n γ ⊑ nth (ρ n) δ)
    -----------------------------------------------------------------
  → (∀ {n : Γ , ★ ∋ ★} → nth n (γ , v) ⊑ nth ((ext ρ) n) (δ , v))
ext-nth ρ lt {Z} = Refl⊑
ext-nth ρ lt {S n'} = lt

rename-pres : ∀ {Γ Δ v} {γ : Env Γ} {δ : Env Δ} {M : Γ ⊢ ★}
  → (ρ : Rename Γ Δ)
  → (∀ {n : Γ ∋ ★} → nth n γ ⊑ nth (ρ n) δ)
  → γ ⊢ M ↓ v
    ----------------------------------------
  → δ ⊢ (rename ρ M) ↓ v
rename-pres ρ nth-eq (var{x = x} lt) =  var (Trans⊑ lt (nth-eq {x}))
rename-pres ρ nth-eq (lit-intro d) =  lit-intro d
rename-pres ρ nth-eq (↦-elim d d₁ lt2) =
  ↦-elim (rename-pres ρ nth-eq d) (rename-pres ρ nth-eq d₁) lt2
rename-pres ρ nth-eq (↦-intro d) =
  ↦-intro (rename-pres (ext ρ) (λ {n} → ext-nth ρ nth-eq {n}) d)
rename-pres ρ nth-eq ⊥-intro = ⊥-intro
rename-pres ρ nth-eq (⊔-intro d d₁) =
  ⊔-intro (rename-pres ρ nth-eq d) (rename-pres ρ nth-eq d₁)

rename-inc-pres : ∀ {Γ v' v} {γ : Env Γ} {M : Γ ⊢ ★}
    → γ ⊢ M ↓ v
    → γ , v' ⊢ rename (λ {A} → λ k → S k) M ↓ v
rename-inc-pres d = rename-pres (λ {A} → λ k → S k) (λ {n} → Refl⊑) d


Subst : Context → Context → Set
Subst Γ Δ = ∀{A} → Γ ∋ A → Δ ⊢ A

_⊨_↓_ : ∀{Δ Γ} → Env Δ → Subst Γ Δ → Env Γ → Set
_⊨_↓_ {Δ}{Γ} δ σ γ = (∀{k : Γ ∋ ★} → δ ⊢ σ k ↓ nth k γ)

subst-ext : ∀ {Γ Δ v} {γ : Env Γ} {δ : Env Δ}
  → (σ : Subst Γ Δ)  →  δ ⊨ σ ↓ γ
   ------------------------------
  → (δ , v) ⊨ exts σ ↓ (γ , v)
subst-ext{v = v} σ d {Z} = var Refl⊑
subst-ext{Γ}{Δ}{v}{γ}{δ} σ d {S x'} =
  rename-pres (λ {A} → S_) (λ {n} → Refl⊑) (d {x'})

subst-pres : ∀ {Γ Δ v} {γ : Env Γ} {δ : Env Δ} {M : Γ ⊢ ★}
  → (σ : Subst Γ Δ)  →  δ ⊨ σ ↓ γ  →  γ ⊢ M ↓ v
    -------------------------------------------
  → δ ⊢ subst σ M ↓ v
subst-pres σ s (var {x = x} lt) = sub (s {x}) lt
subst-pres σ s (lit-intro d) = (lit-intro d)
subst-pres σ s (↦-elim d₁ d₂ lt2) =
   ↦-elim (subst-pres σ s d₁) (subst-pres σ s d₂) lt2
subst-pres σ s (↦-intro d) =
   ↦-intro (subst-pres (λ {A} → exts σ) (λ {x} → subst-ext σ s {x}) d)
subst-pres σ s ⊥-intro = ⊥-intro
subst-pres σ s (⊔-intro d₁ d₂) =
   ⊔-intro (subst-pres σ s d₁) (subst-pres σ s d₂)

substitution : ∀ {Γ} {γ : Env Γ} {M N v₁ v₂}
   → γ , v₁ ⊢ M ↓ v₂  →  γ ⊢ N ↓ v₁
     ------------------------------
   → γ ⊢ M [ N ] ↓ v₂   
substitution{Γ}{γ}{M}{N}{v₁}{v₂} dm dn =
  subst-pres (subst-zero N) sub-z-ok dm
  where
  sub-z-ok : (∀ {y : Γ , ★ ∋ ★} → γ ⊢ (subst-zero N) y ↓ nth y (γ , v₁))
  sub-z-ok {Z} = dn
  sub-z-ok {S y'} = var Refl⊑

preserve : ∀ {Γ} {γ : Env Γ} {M N v}
  → γ ⊢ M ↓ v  →  M —→ N
    --------------------
  → γ ⊢ N ↓ v
preserve (var lt) ()
preserve (lit-intro d) ()
preserve (↦-elim d₁ d₂ lt2) (ξ₁-rule r) = ↦-elim (preserve d₁ r) d₂ lt2
preserve (↦-elim d₁ d₂ lt2) (ξ₂-rule v r) = ↦-elim d₁ (preserve d₂ r) lt2
preserve (↦-elim (↦-intro d₁) d₂ lt2) (β-rule v) = sub (substitution d₁ d₂) lt2
preserve (↦-elim (lit-intro (fun-val {Nat} d)) (lit-intro base-val) lt) δ-rule =
   lit-intro (sub-prim d lt)
preserve (↦-elim (lit-intro (fun-val {𝔹} d)) (lit-intro base-val) lt) δ-rule =
   lit-intro (sub-prim d lt)
preserve (↦-intro d) ()
preserve ⊥-intro ()
preserve (⊔-intro d d₁) r = ⊔-intro (preserve d r) (preserve d₁ r)

var-inv : ∀ {Γ v x} {γ : Env Γ}
  → γ ⊢ ` x ↓ v
    -------------------
  → v ⊑ nth x γ
var-inv (var lt) = lt
var-inv (⊔-intro d₁ d₂) = ConjL⊑ (var-inv d₁) (var-inv d₂)

rename-reflect : ∀ {Γ Δ v} {γ : Env Γ} {δ : Env Δ} { M : Γ ⊢ ★}
  → {ρ : Rename Γ Δ}
  → (∀ {n : Γ ∋ ★} → nth (ρ n) δ ≡ nth n γ)
  → δ ⊢ rename ρ M ↓ v
    ------------------------------------
  → γ ⊢ M ↓ v
rename-reflect {M = ` x} all-n d with var-inv d
... | lt rewrite all-n {x} = var lt

rename-reflect {M = $ k} all-n (lit-intro x) = lit-intro x
rename-reflect {M = $ k} {ρ = ρ} all-n (⊔-intro d₁ d₂) =
    ⊔-intro (rename-reflect {ρ = ρ} all-n d₁) (rename-reflect {ρ = ρ} all-n d₂)

rename-reflect {Γ}{Δ}{v₁ ↦ v₂}{γ}{δ}{ƛ M'}{ρ} all-n (↦-intro d) =
   ↦-intro (rename-reflect (λ {n} → nth-ext {n}) d)
   where
   nth-ext : {n : Γ , ★ ∋ ★} → nth (ext ρ n) (δ , v₁) ≡ nth n (γ , v₁) 
   nth-ext {Z} = refl
   nth-ext {S n} = all-n
rename-reflect {M = ƛ M'} all-n ⊥-intro = ⊥-intro
rename-reflect {M = ƛ M'} all-n (⊔-intro d₁ d₂) =
   ⊔-intro (rename-reflect all-n d₁) (rename-reflect all-n d₂)

rename-reflect {M = M₁ · M₂} all-n (↦-elim d₁ d₂ lt2) =
   ↦-elim (rename-reflect all-n d₁) (rename-reflect all-n d₂) lt2
rename-reflect {M = M₁ · M₂} all-n (⊔-intro d₁ d₂) =
   ⊔-intro (rename-reflect all-n d₁) (rename-reflect all-n d₂)

rename-inc-reflect : ∀ {Γ v' v} {γ : Env Γ} { M : Γ ⊢ ★}
  → (γ , v') ⊢ rename (λ {A} → S_) M ↓ v
    ------------------------------------
  → γ ⊢ M ↓ v
rename-inc-reflect d = rename-reflect (λ {n} → refl) d

rename-inc-iff : ∀ {Γ v' v} {γ : Env Γ} { M : Γ ⊢ ★}
  → (γ ⊢ M ↓ v) iff ((γ , v') ⊢ rename (λ {A} → S_) M ↓ v)
rename-inc-iff = ⟨ rename-inc-pres , rename-inc-reflect ⟩

is-identity : ∀ {Γ} (id : ∀{A} → Γ ∋ A → Γ ∋ A) → Set
is-identity {Γ} id = (∀ {x : Γ ∋ ★} → id {★} x ≡ x)

rename-id : ∀ {Γ} {M : Γ ⊢ ★} {id : ∀{A} → Γ ∋ A → Γ ∋ A}
  → is-identity id
    ---------------
  → rename id M ≡ M
rename-id {M = ` x} eq = cong `_ (eq {x})
rename-id {M = $_ k} eq = cong $_ refl
rename-id {M = ƛ M₁}{id = id} eq = cong ƛ_ (rename-id {M = M₁} ext-id)
  where
  ext-id : is-identity (ext id)
  ext-id {Z} = refl
  ext-id {S x} = cong S_ eq
rename-id {M = M · M₁} eq = cong₂ _·_ (rename-id eq) (rename-id eq)

var-id : ∀ {Γ A} → (Γ ∋ A) → (Γ ∋ A)
var-id {A} x = x

var-id-id : ∀ {Γ} → is-identity {Γ} var-id
var-id-id = refl

Env⊑ : ∀ {Γ} {γ : Env Γ} {δ : Env Γ} {M v}
  → γ ⊢ M ↓ v  →  γ `⊑ δ
    --------------------
  → δ ⊢ M ↓ v
Env⊑{Γ}{γ}{δ}{M}{v} d lt
      with rename-pres var-id lt d
... | d' rewrite rename-id {Γ}{M}{var-id} (var-id-id {Γ}) = d'

up-env : ∀ {Γ} {γ : Env Γ} {M v u₁ u₂}
  → (γ , u₁) ⊢ M ↓ v  →  u₁ ⊑ u₂
    ----------------------------
  → (γ , u₂) ⊢ M ↓ v
up-env{Γ}{γ}{M}{v}{u₁}{u₂} d lt = Env⊑ d (λ {k} → nth-le lt {k})
  where
  nth-le : u₁ ⊑ u₂ → (γ , u₁) `⊑ (γ , u₂)
  nth-le lt {Z} = lt
  nth-le lt {S n} = Refl⊑

empty-env : ∀ {Γ} → Env Γ
empty-env {∅} = ∅
empty-env {Γ , ★} = (empty-env {Γ}) , ⊥

nth-empty-env : ∀{Γ} {x : Γ ∋ ★} → nth x empty-env ≡ ⊥
nth-empty-env {x = Z} = refl
nth-empty-env {Γ , ★} {S x} = nth-empty-env {Γ} {x}

const-env : ∀{Γ} → (x : Γ ∋ ★) → Value → Env Γ
const-env {∅} x v = ∅
const-env {Γ , ★} Z v = empty-env {Γ} , v
const-env {Γ , ★} (S x) v = (const-env {Γ} x v) , ⊥

nth-const-env : ∀{Γ} {n : Γ ∋ ★} {v}
                 → nth n (const-env n v) ≡ v
nth-const-env {Γ , ★} {Z} = refl
nth-const-env {Γ , ★} {S n} = nth-const-env {Γ} {n}

diff-nth-const-env : ∀{Γ} {n : Γ ∋ ★} {n' : Γ ∋ ★} {v}
    → n ≢ n' → nth n (const-env n' v) ≡ ⊥
diff-nth-const-env {Γ , ★} {n} {Z} {v} neq with n
... | Z = ⊥-elim (neq refl)
... | S n₁ = nth-empty-env {Γ}
diff-nth-const-env {Γ , ★} {n} {S n'} neq with n
... | Z = refl
... | S n₁ = diff-nth-const-env (λ n → neq (cong S_ n))

var-eq? : ∀ {Γ} → (x y : Γ ∋ ★) → Dec (x ≡ y)
var-eq? Z Z = yes refl
var-eq? Z (S y) = no (λ ())
var-eq? (S x) Z = no (λ ())
var-eq? {Γ , ★} (S x) (S y) with var-eq? {Γ} x y
... | yes eq = yes (cong S_ eq)
... | no neq = no g
  where
  g : (S_ {B = ★} x) ≢ (S y)
  g refl = neq refl 

term-value-⊥ : ∀{Γ}{ρ : Env Γ}{M : Γ ⊢ ★} → TermValue M → ρ ⊢ M ↓ ⊥
term-value-⊥ V-ƛ = ⊥-intro
term-value-⊥ V-const = lit-intro ⊥-val
term-value-⊥ V-var = var Bot⊑

data Terminating : ∀{Γ Δ} → Subst Γ Δ → Env Δ → Set where
  valsub : ∀{Γ Δ}{σ : Subst Γ Δ}{δ : Env Δ}
        → (∀{k} → δ ⊢ (σ k) ↓ ⊥)
        → Terminating σ δ

subst-reflect-var : ∀ {Γ Δ} {γ : Env Δ} {x : Γ ∋ ★} {v} {σ : Subst Γ Δ}
  → γ ⊢ σ x ↓ v   →   Terminating σ γ
    ----------------------------------------
  → Σ[ δ ∈ Env Γ ] γ ⊨ σ ↓ δ  ×  δ ⊢ ` x ↓ v
subst-reflect-var {Γ}{Δ}{γ}{x}{v}{σ} sx (valsub allv)
  rewrite sym (nth-const-env {Γ}{x}{v}) =
    ⟨ const-env x v , ⟨ const-env-ok , var Refl⊑ ⟩ ⟩
  where
  const-env-ok : γ ⊨ σ ↓ const-env x v
  const-env-ok {k} with var-eq? k x
  ... | yes k≡x rewrite k≡x | nth-const-env {Γ}{x}{v} = sx
  ... | no k≢x rewrite diff-nth-const-env {Γ}{k}{x}{v} k≢x = allv

subst-empty : ∀{Γ Δ}{γ : Env Δ}{σ : Subst Γ Δ}
            → Terminating σ γ → γ ⊨ σ ↓ empty-env
subst-empty (valsub allv) {k = k} rewrite nth-empty-env {x = k} = allv

subst-⊔ : ∀{Γ Δ}{γ : Env Δ}{γ₁ γ₂ : Env Γ}{σ : Subst Γ Δ}
           → γ ⊨ σ ↓ γ₁  →  γ ⊨ σ ↓ γ₂
             -------------------------
           → γ ⊨ σ ↓ (γ₁ `⊔ γ₂)
subst-⊔{Γ}{Δ}{γ}{γ₁}{γ₂} γ₁-ok γ₂-ok {k}
  rewrite nth-join-env{Γ}{γ₁}{γ₂}{k} = ⊔-intro γ₁-ok γ₂-ok

lambda-inj : ∀ {Γ} {M : Γ , ★ ⊢ ★ } {N : Γ , ★ ⊢ ★ }
  → _≡_ {lzero} {Γ ⊢ ★} (ƛ M) (ƛ N)
    -------------------------------
  → (M ≡ N)
lambda-inj refl = refl

rename-pres-bot : ∀{Γ Δ}{ρ : Rename Γ Δ}
    {M : Γ ⊢ ★}{γ : Env Γ}{δ : Env Δ}
   → (∀{n : Γ ∋ ★} → nth n γ ⊑ nth (ρ n) δ)
   → γ ⊢ M ↓ ⊥
   → δ ⊢ (rename ρ M) ↓ ⊥
rename-pres-bot {ρ = ρ} r d = rename-pres ρ r d

ext-val-subst : ∀{Γ Δ}{σ : Subst Γ Δ}{δ : Env Δ}{v}
              → Terminating σ δ
              → Terminating (exts σ {B = ★}) (δ , v)
ext-val-subst {Γ}{Δ}{σ}{δ}{v} (valsub d) = (valsub λ {k} → G {k})
  where
  G : {k : Γ , ★ ∋ ★} → (δ , v) ⊢ exts σ k ↓ ⊥
  G {Z} = var Bot⊑
  G {S k} = rename-pres-bot {γ = δ}{δ = δ , v} (λ {n} → Refl⊑) d

subst-reflect : ∀ {Γ Δ} {δ : Env Δ} {M : Γ ⊢ ★} {v} {L : Δ ⊢ ★} {σ : Subst Γ Δ}
  → δ ⊢ L ↓ v  →  (subst σ M) ≡ L  → Terminating σ δ
    -------------------------------------------
  → Σ[ γ ∈ Env Γ ] δ ⊨ σ ↓ γ  ×  γ ⊢ M ↓ v

subst-reflect {Γ}{Δ}{M = M}{σ = σ} (lit-intro d) eqL vs with M
... | ` x  with lit-intro{Δ} d
... | d' rewrite sym eqL = subst-reflect-var {σ = σ} d' vs
subst-reflect {M = M} {σ = σ} (lit-intro d) refl vs | $ k' =
  ⟨ empty-env , ⟨ subst-empty vs , (lit-intro d) ⟩ ⟩
subst-reflect {M = M} {σ = σ} (lit-intro d) () vs | ƛ M'
subst-reflect {M = M} {σ = σ} (lit-intro d) () vs | M₁ · M₂

subst-reflect {M = M}{σ = σ} (var {x = y} lt) eqL vs with M 
... | ` x  with (var{x = y} lt)
... | yv  rewrite sym eqL = subst-reflect-var {σ = σ} yv vs
subst-reflect {M = M} (var {x = y} lt) () vs | M₁ · M₂
subst-reflect {M = M} (var {x = y} lt) () vs | ƛ M'
subst-reflect {M = M} (var {x = y} lt) () vs | $ k 

subst-reflect {M = M}{σ = σ} (↦-elim d₁ d₂ lt2) eqL vs
         with M 
...    | ` x with ↦-elim d₁ d₂ lt2
...    | d' rewrite sym eqL = subst-reflect-var {σ = σ} d' vs
subst-reflect (↦-elim d₁ d₂ lt2) () vs | ƛ M'
subst-reflect (↦-elim d₁ d₂ lt2) () vs | $ k
subst-reflect{Γ}{Δ}{γ}{σ = σ} (↦-elim d₁ d₂ lt2) refl vs | M₁ · M₂
     with subst-reflect {M = M₁} d₁ refl vs | subst-reflect {M = M₂} d₂ refl vs
...     | ⟨ δ₁ , ⟨ subst-δ₁ , m1 ⟩ ⟩ | ⟨ δ₂ , ⟨ subst-δ₂ , m2 ⟩ ⟩ =
     ⟨ δ₁ `⊔ δ₂ , ⟨ subst-⊔ {γ₁ = δ₁}{γ₂ = δ₂}{σ = σ} subst-δ₁ subst-δ₂ ,
                    ↦-elim (Env⊑ m1 (EnvConjR1⊑ δ₁ δ₂))
                           (Env⊑ m2 (EnvConjR2⊑ δ₁ δ₂)) lt2 ⟩ ⟩

subst-reflect {M = M}{σ = σ} (↦-intro d) eqL vs with M
...    | ` x with (↦-intro d)
...    | d' rewrite sym eqL = subst-reflect-var {σ = σ} d' vs
subst-reflect {M = _} {σ = σ} (↦-intro d) () vs | $ k
subst-reflect {σ = σ} (↦-intro d) eq vs | ƛ M'
      with subst-reflect{σ = exts σ} d (lambda-inj eq) (ext-val-subst vs)
... | ⟨ (δ' , v') , ⟨ exts-σ-δ'v' , m' ⟩ ⟩ = 
    ⟨ δ' , ⟨ ((λ {k} → rename-inc-reflect (exts-σ-δ'v' {S k}))) ,
             ↦-intro (up-env m' (var-inv (exts-σ-δ'v' {Z} ))) ⟩ ⟩
subst-reflect (↦-intro d) () vs | M₁ · M₂ 

subst-reflect {M = M} {σ = σ} ⊥-intro eq vs with M
...  | ` x = ⟨ empty-env , ⟨ subst-empty{σ = σ} vs , var Bot⊑ ⟩ ⟩
...  | ƛ M' = ⟨ empty-env , ⟨ subst-empty{σ = σ} vs , ⊥-intro ⟩ ⟩
subst-reflect {M = M} {σ = σ} ⊥-intro () vs | $ k
subst-reflect {M = M} {σ = σ} ⊥-intro () vs | M₁ · M₂

subst-reflect {σ = σ} (⊔-intro d₁ d₂) eq vs
  with subst-reflect {σ = σ} d₁ eq vs | subst-reflect {σ = σ} d₂ eq vs
... | ⟨ δ₁ , ⟨ subst-δ₁ , m1 ⟩ ⟩ | ⟨ δ₂ , ⟨ subst-δ₂ , m2 ⟩ ⟩ =
     ⟨ δ₁ `⊔ δ₂ , ⟨ subst-⊔ {γ₁ = δ₁}{γ₂ = δ₂}{σ = σ} subst-δ₁ subst-δ₂ ,
                    ⊔-intro (Env⊑ m1 (EnvConjR1⊑ δ₁ δ₂))
                            (Env⊑ m2 (EnvConjR2⊑ δ₁ δ₂)) ⟩ ⟩

nth-id-le : ∀{Γ}{δ'}{v'}{γ}{N}
      → γ ⊨ subst-zero N ↓ (δ' , v')
        -----------------------------------------------------------
      → {n : Γ , ★ ∋ ★} → nth n (δ' , v') ⊑ nth (var-id n) (γ , v')
nth-id-le γ-sz-δ'v' {Z} = Refl⊑
nth-id-le γ-sz-δ'v' {S n'} = var-inv (γ-sz-δ'v' {S n'})


val-subst-zero : ∀{Γ}{γ : Env Γ}{N : Γ ⊢ ★}
  → γ ⊢ N ↓ ⊥
  → Terminating (subst-zero N) γ
val-subst-zero {Γ}{γ}{N} v = valsub G
  where
  G : ∀{k : Γ , ★ ∋ ★} → γ ⊢ subst-zero N k ↓ ⊥
  G {Z} = v
  G {S k} = var Bot⊑


substitution-reflect : ∀ {Γ} {γ : Env Γ} {M N v}
  → γ ⊢ M [ N ] ↓ v   →  γ ⊢ N ↓ ⊥
    -----------------------------------------------
  → Σ[ v₂ ∈ Value ] γ ⊢ N ↓ v₂  ×  (γ , v₂) ⊢ M ↓ v
substitution-reflect {Γ}{γ}{M}{N} d vn
      with subst-reflect {M = M}{σ = subst-zero N} d refl (val-subst-zero vn)
... | ⟨ (δ' , v') , ⟨ γ-sz-δ'v' , mn ⟩ ⟩
      with rename-pres var-id (λ {n} → nth-id-le γ-sz-δ'v' {n}) mn
... | mn' rewrite rename-id {Γ , ★}{M}{var-id} var-id-id =
      ⟨ v' , ⟨ γ-sz-δ'v' {Z} , mn' ⟩ ⟩

base-eval-lit : ∀{B}{k} → lit k ∈ (` B) 〚 k 〛
base-eval-lit {Nat} {k} = base-val
base-eval-lit {𝔹} {k} = base-val

reflect : ∀ {Γ} {γ : Env Γ} {M N v}
  → γ ⊢ N ↓ v  →  M —→ N
    --------------------
  → γ ⊢ M ↓ v
reflect d (ξ₁-rule r) with d
... | ↦-elim d₁ d₂ lt2 = ↦-elim (reflect d₁ r) d₂ lt2
... | ⊔-intro d₁ d₂ = ⊔-intro (reflect d₁ (ξ₁-rule r)) (reflect d₂ (ξ₁-rule r))
reflect d (ξ₂-rule d' r) with d
... | ↦-elim d₁ d₂ lt2 = ↦-elim d₁ (reflect d₂ r) lt2
... | ⊔-intro d₁ d₂ = ⊔-intro (reflect d₁ (ξ₂-rule d' r))
                              (reflect d₂ (ξ₂-rule d' r))
reflect d (β-rule v) with substitution-reflect d (term-value-⊥ v)
... | ⟨ v₂ , ⟨ d₁ , d₂ ⟩ ⟩ = ↦-elim (↦-intro d₂) d₁ Refl⊑
reflect{v = v} (lit-intro d) (δ-rule{k = k'}) =
    ↦-elim{v₁ = lit k'}{v₂ = v} (lit-intro (fun-val d))
                                (lit-intro base-eval-lit) Refl⊑
reflect (⊔-intro d₁ d₂) δ-rule =
    ⊔-intro (reflect d₁ δ-rule) (reflect d₂ δ-rule)


reduce-equal : ∀ {Γ} {M : Γ ⊢ ★} {N : Γ ⊢ ★}
  → M —→ N
    ------
  → M ≅ N
reduce-equal {Γ}{M}{N} r = ⟨ (λ m → preserve m r) , (λ n → reflect n r) ⟩


beta-equal : ∀ {Γ : Context} → {M : Γ ⊢ ★} → {N : Γ , ★ ⊢ ★} → TermValue M
  → ((ƛ N) · M) ≅ (N [ M ])
beta-equal mv = reduce-equal (β-rule mv)

{-

  Alternative β rule that is application to non-values.  Instead
  requires the lambda's variable (de Bruijn index 0) to occur at least
  once in a place what must evaluate.

-}

data VarMustEval : ∀{Γ : Context} → Γ ⊢ ★ → Set where
  vme-var : ∀{Γ : Context} → VarMustEval (`_ {Γ , ★} Z)
  vme-appL : ∀{Γ}{M N : Γ ⊢ ★} → VarMustEval M → VarMustEval (M · N)
  vme-appR : ∀{Γ}{M N : Γ ⊢ ★} → VarMustEval N → VarMustEval (M · N)

var-must-eval : ∀{Γ}{γ : Env Γ}{N L : Γ ⊢ ★}{M : Γ , ★ ⊢ ★}{v}
               → VarMustEval M
               → γ ⊢ L ↓ v → M [ N ] ≡ L → Σ[ v' ∈ Value ] γ ⊢ N ↓ v'
var-must-eval {v = v} vme-var d eqL rewrite eqL = ⟨ v , d ⟩
var-must-eval {L = $ x} (vme-appL vo) d ()
var-must-eval {L = ` x} (vme-appL vo) d ()
var-must-eval {L = ƛ L} (vme-appL vo) d ()
var-must-eval (vme-appL vo) (↦-elim d₁ d₂ x) refl =
   var-must-eval vo d₁ refl
var-must-eval {L = L₁ · L₂}{M = M₁ · M₂} (vme-appL vo) (⊔-intro d₁ d₂) eqL =
   var-must-eval (vme-appL {N = M₂} vo) d₁ eqL
var-must-eval {L = $ x} (vme-appR vo) d ()
var-must-eval {L = ` x} (vme-appR vo) d ()
var-must-eval {L = ƛ L} (vme-appR vo) d ()
var-must-eval (vme-appR vo) (↦-elim d₁ d₂ x) refl = 
   var-must-eval vo d₂ refl
var-must-eval {L = L · L₁}{M = M₁ · M₂} (vme-appR vo) (⊔-intro d₁ d₂) eqL =
   var-must-eval (vme-appR{M = M₁} vo) d₁ eqL


β-var-must-eval : ∀{Γ}{N : Γ ⊢ ★}{M : Γ , ★ ⊢ ★}
         → VarMustEval M
           --------------------
         → (ƛ M ) · N ≅ M [ N ]
β-var-must-eval {Γ}{N}{M} vo {γ}{v} = ⟨ H , G ⟩
  where
  G : γ ⊢ M [ N ] ↓ v → γ ⊢ (ƛ M) · N ↓ v
  G d
      with var-must-eval vo d refl
  ... | ⟨ v' , N↓v' ⟩
      with substitution-reflect{M = M} d (sub N↓v' Bot⊑)
  ... | ⟨ v₂ , ⟨ N↓v₂ , M↓v ⟩ ⟩ =
    ↦-elim (↦-intro M↓v) N↓v₂ Refl⊑
  
  H : ∀{v} → γ ⊢ (ƛ M) · N ↓ v → γ ⊢ M [ N ] ↓ v
  H (↦-elim (↦-intro d₁) d₂ lt) = sub (substitution d₁ d₂) lt
  H (⊔-intro d₁ d₂) = ⊔-intro (H d₁) (H d₂)

{-

  Congruence

-}


infix 4 _≲_
_≲_ : ∀ {Γ} → (Γ ⊢ ★) → (Γ ⊢ ★) → Set
_≲_ {Γ} M N = (∀ {γ : Env Γ} → ∀ {v} → (γ ⊢ M ↓ v) → (γ ⊢ N ↓ v))

lam-less : ∀{Γ}{M N : Γ , ★ ⊢ ★} → M ≲ N → (ƛ M) ≲ (ƛ N)
lam-less M≲N (↦-intro M↓v) = ↦-intro (M≲N M↓v)
lam-less M≲N ⊥-intro = ⊥-intro
lam-less M≲N (⊔-intro ƛM↓v₁ ƛM↓v₂) =
   ⊔-intro (lam-less M≲N ƛM↓v₁) (lam-less M≲N ƛM↓v₂)

app-less : ∀{Γ}{M₁ M₂ N₁ N₂ : Γ ⊢ ★}
         → M₁ ≲ N₁ → M₂ ≲ N₂ → (M₁ · M₂) ≲ (N₁ · N₂)
app-less M₁≲N₁ M₂≲N₂ {γ} {v} (↦-elim M₁↓v M₂↓v' lt) =
   ↦-elim (M₁≲N₁ M₁↓v) (M₂≲N₂ M₂↓v') lt
app-less M₁≲N₁ M₂≲N₂ {γ} {v₁ ⊔ v₂} (⊔-intro M₁·M₂↓v₁ M₁·M₂↓v₂) =
   ⊔-intro (app-less M₁≲N₁ M₂≲N₂ M₁·M₂↓v₁) (app-less M₁≲N₁ M₂≲N₂ M₁·M₂↓v₂)


lam-cong : ∀{Γ}{M N : Γ , ★ ⊢ ★} → M ≅ N → (ƛ M) ≅ (ƛ N)
lam-cong {Γ}{M}{N} M≅N {γ}{v} = ⟨ lam-less (proj₁ M≅N) , lam-less (proj₂ M≅N) ⟩

app-cong : ∀{Γ}{M₁ M₂ N₁ N₂ : Γ ⊢ ★}
         → M₁ ≅ N₁ → M₂ ≅ N₂ → (M₁ · M₂) ≅ (N₁ · N₂)
app-cong M₁≅N₁ M₂≅N₂ {γ} {v} =
   ⟨ app-less (proj₁ M₁≅N₁) (proj₁ M₂≅N₂) ,
     app-less (proj₂ M₁≅N₁) (proj₂ M₂≅N₂) ⟩


data Ctx : Context → Context → Set where
  CHole : ∀{Γ} → Ctx Γ Γ
  CLam :  ∀{Γ Δ} → Ctx (Γ , ★) (Δ , ★) → Ctx (Γ , ★) Δ
  CAppL : ∀{Γ Δ} → Ctx Γ Δ → Δ ⊢ ★ → Ctx Γ Δ
  CAppR : ∀{Γ Δ} → Δ ⊢ ★ → Ctx Γ Δ → Ctx Γ Δ

plug : ∀{Γ}{Δ} → Ctx Γ Δ → Γ ⊢ ★ → Δ ⊢ ★
plug CHole M = M
plug (CLam C) M = ƛ plug C M
plug (CAppL C N) M = (plug C M) · N
plug (CAppR L C) M = L · (plug C M)

congruence : ∀{Γ Δ}{C : Ctx Γ Δ} {M N : Γ ⊢ ★}
           → M ≅ N → (plug C M) ≅ (plug C N)
congruence {C = CHole} eq = eq
congruence {C = CLam C'} eq = lam-cong (congruence {C = C'} eq)
congruence {C = CAppL C' L} eq =
  app-cong (congruence {C = C'} eq) equal-refl
congruence {C = CAppR L C'} eq =
  app-cong equal-refl (congruence {C = C'} eq) 

_ : ∅ ⊢ inc · ($ 2) ↓ (lit 3)
_ = ↦-elim (lit-intro (fun-val base-val)) (lit-intro base-val) Lit⊑

_ : ∅ ⊢ (ƛ (` Z)) · ($ 1) ↓ (lit 1)
_ = ↦-elim (↦-intro (var Lit⊑)) (lit-intro base-val) Lit⊑


{-

  Inversion (aka Generation) Lemmas

-}

app-inv : ∀{Γ}{γ : Env Γ}{M N : Γ ⊢ ★}{v : Value}
        → γ ⊢ M · N ↓ v
        → Σ[ v₁ ∈ Value ] Σ[ v₂ ∈ Value ] Σ[ v₃ ∈ Value ]  γ ⊢ M ↓ v₁ ↦ v₂ × γ ⊢ N ↓ v₃ × v₁ ⊑ v₃ × v ⊑ v₂
app-inv (↦-elim d₁ d₂ lt) = {!!}
app-inv {Γ}{γ}{M}{N}{v} (⊔-intro d₁ d₂)
    with app-inv d₁
... | ⟨ v₁ , ⟨ v₂ , ⟨ v₃ , ⟨ M↓v12 , ⟨ N↓v3 , ⟨ v13 , vv2 ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ =

      ⟨ {!!} , ⟨ {!!} , ⟨ {!!} , ⟨ M↓v12 , ⟨ N↓v3 , ⟨ v13 , {!!} ⟩ ⟩ ⟩ ⟩ ⟩ ⟩

module SemReduceEquiv where

open import Rename
open import Sem
open import ValueBCD
open import Lambda
open import Inversion
open import Subst

open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; cong; cong₂)
open import Data.Nat using (ℕ; suc ; zero)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum
open import Agda.Primitive using (lzero)
open import Lambda
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using (contradiction)
open import Data.Empty using (⊥-elim) renaming (⊥ to Bot)
open import Relation.Nullary using (Dec; yes; no)
open import Data.Unit


preserve : ∀ {Γ} {γ : Env Γ} {M N v}
  → ℰ M γ v  →  M —→ N
    --------------------
  → ℰ N γ v
preserve (ℰ-var lt) ()
preserve (ℰ-lit d) ()
preserve (ℰ-app d₁ d₂ lt2) (ξ₁-rule r) = ℰ-app (preserve d₁ r) d₂ lt2
preserve (ℰ-app d₁ d₂ lt2) (ξ₂-rule v r) = ℰ-app d₁ (preserve d₂ r) lt2
preserve (ℰ-app d₁ d₂ lt2) (β-rule v) =
   ℰ-⊑ (substitution (lam-inv d₁) d₂) lt2
preserve (ℰ-app{v = v}{v₁ = v₁}{v₂ = v₂} d₁ d₂ lt) (δ-rule{Γ}{B}{P}{f}{k}) =
  let ℘f=v₁↦v₂ = prim-inv d₁ in
  let v₁⊑k = AllLit→⊑lit (base-inv (prim-inv d₂)) in
  let ℘fk=v₂ = prim-fun-inv ℘f=v₁↦v₂ {k} v₁⊑k in 
  ℰ-lit (℘-⊑ ℘fk=v₂ lt)
preserve (ℰ-lam d) ()
preserve ℰ-⊥ ()
preserve (ℰ-⊔ d d₁) r = ℰ-⊔ (preserve d r) (preserve d₁ r)
preserve (ℰ-⊑ d lt) r = ℰ-⊑ (preserve d r) lt


rename-reflect : ∀ {Γ Δ v} {γ : Env Γ} {δ : Env Δ} { M : Γ ⊢ ★}
  → {ρ : Rename Γ Δ}
  → (∀ {n : Γ ∋ ★} → nth (ρ n) δ ≡ nth n γ)
  → ℰ (rename ρ M) δ v
    ------------------------------------
  → ℰ M γ v

rename-reflect {M = ` x} all-n d
    with var-inv d
... | lt rewrite all-n {x} = ℰ-var lt

rename-reflect {M = $ k} all-n d
    with prim-inv d
... | d' = ℰ-lit d'

rename-reflect {Γ}{Δ}{v₁ ↦ v₂}{γ}{δ}{ƛ M'}{ρ} all-n (ℰ-lam d) =
   ℰ-lam (rename-reflect (λ {n} → nth-ext {n}) d)
   where
   nth-ext : {n : Γ , ★ ∋ ★} → nth (ext ρ n) (δ , v₁) ≡ nth n (γ , v₁) 
   nth-ext {Z} = refl
   nth-ext {S n} = all-n
rename-reflect {M = ƛ M'} all-n ℰ-⊥ = ℰ-⊥
rename-reflect {M = ƛ M'} all-n (ℰ-⊔ d₁ d₂) =
   ℰ-⊔ (rename-reflect all-n d₁) (rename-reflect all-n d₂)
{- I'd like to collapse the following 4 into 1 case -}
rename-reflect {v = ⊥} {M = ƛ M} all-n (ℰ-⊑ {v₂ = ⊥} d lt ) = ℰ-⊥
rename-reflect {v = lit x₂} {M = ƛ M} all-n (ℰ-⊑ {v₂ = lit x₂} d lt)
    with sub-Λ (lam-inv d) lt
... | ()
rename-reflect {v = v₂ ↦ v₃} {M = ƛ M} all-n (ℰ-⊑ {v₂ = v₂ ↦ v₃} d lt) =
   ℰ-⊑ (rename-reflect{M = ƛ M} all-n d) lt
rename-reflect {v = v₂ ⊔ v₃} {M = ƛ M} all-n (ℰ-⊑ {v₂ = v₂ ⊔ v₃} d lt) =
   ℰ-⊑ (rename-reflect{M = ƛ M} all-n d) lt

rename-reflect {M = M₁ · M₂} all-n (ℰ-app d₁ d₂ lt2) =
   ℰ-app (rename-reflect all-n d₁) (rename-reflect all-n d₂) lt2
rename-reflect {M = M₁ · M₂} all-n (ℰ-⊔ d₁ d₂) =
   ℰ-⊔ (rename-reflect all-n d₁) (rename-reflect all-n d₂)
rename-reflect {M = M · M₁} all-n (ℰ-⊑ d lt) =
  ℰ-⊑ (rename-reflect {M = M · M₁} all-n d) lt


rename-inc-reflect : ∀ {Γ v' v} {γ : Env Γ} { M : Γ ⊢ ★}
  → ℰ (rename (λ {A} → S_) M) (γ , v') v
    ------------------------------------
  → ℰ M γ v
rename-inc-reflect d = rename-reflect (λ {n} → refl) d


rename-inc-iff : ∀ {Γ v' v} {γ : Env Γ} { M : Γ ⊢ ★}
  → (ℰ M γ v) iff (ℰ (rename (λ {A} → S_) M) (γ , v') v)
rename-inc-iff = ⟨ rename-inc-pres , rename-inc-reflect ⟩


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

term-value-⊥ : ∀{Γ}{ρ : Env Γ}{M : Γ ⊢ ★} → TermValue M → ℰ M ρ ⊥
term-value-⊥ V-ƛ = ℰ-⊥
term-value-⊥ V-const = ℰ-lit ℘-⊥
term-value-⊥ V-var = ℰ-var Bot⊑


data Terminating : ∀{Γ Δ} → Subst Γ Δ → Env Δ → Set where
  valsub : ∀{Γ Δ}{σ : Subst Γ Δ}{δ : Env Δ}
        → (∀{k} → ℰ (σ k) δ ⊥)
        → Terminating σ δ


subst-reflect-var : ∀ {Γ Δ} {γ : Env Δ} {x : Γ ∋ ★} {v} {σ : Subst Γ Δ}
  → ℰ (σ x) γ v   →   Terminating σ γ
    ----------------------------------------
  → Σ[ δ ∈ Env Γ ] γ ⊨ σ ↓ δ  ×  ℰ (` x) δ v
subst-reflect-var {Γ}{Δ}{γ}{x}{v}{σ} sx (valsub allv)
  rewrite sym (nth-const-env {Γ}{x}{v}) =
    ⟨ const-env x v , ⟨ const-env-ok , ℰ-var Refl⊑ ⟩ ⟩
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
  rewrite nth-join-env{Γ}{γ₁}{γ₂}{k} = ℰ-⊔ γ₁-ok γ₂-ok


lambda-inj : ∀ {Γ} {M : Γ , ★ ⊢ ★ } {N : Γ , ★ ⊢ ★ }
  → _≡_ {lzero} {Γ ⊢ ★} (ƛ M) (ƛ N)
    -------------------------------
  → (M ≡ N)
lambda-inj refl = refl


rename-pres-bot : ∀{Γ Δ}{ρ : Rename Γ Δ}
    {M : Γ ⊢ ★}{γ : Env Γ}{δ : Env Δ}
   → (∀{n : Γ ∋ ★} → nth n γ ⊑ nth (ρ n) δ)
   → ℰ M γ ⊥
   → ℰ (rename ρ M) δ ⊥
rename-pres-bot {ρ = ρ} r d = rename-pres ρ r d


ext-val-subst : ∀{Γ Δ}{σ : Subst Γ Δ}{δ : Env Δ}{v}
              → Terminating σ δ
              → Terminating (exts σ {B = ★}) (δ , v)
ext-val-subst {Γ}{Δ}{σ}{δ}{v} (valsub d) = (valsub λ {k} → G {k})
  where
  G : {k : Γ , ★ ∋ ★} → ℰ (exts σ k) (δ , v) ⊥
  G {Z} = ℰ-var Bot⊑
  G {S k} = rename-pres-bot {γ = δ}{δ = δ , v} (λ {n} → Refl⊑) d


subst-reflect : ∀ {Γ Δ} {δ : Env Δ} {M : Γ ⊢ ★} {v} {L : Δ ⊢ ★} {σ : Subst Γ Δ}
  → ℰ L δ v  →  (subst σ M) ≡ L  → Terminating σ δ
    -------------------------------------------
  → Σ[ γ ∈ Env Γ ] δ ⊨ σ ↓ γ  ×  ℰ M γ v

subst-reflect {Γ}{Δ}{M = M}{σ = σ} (ℰ-lit d) eqL vs with M
... | ` x  with ℰ-lit{Δ} d
... | d' rewrite sym eqL = subst-reflect-var {σ = σ} d' vs
subst-reflect {M = M} {σ = σ} (ℰ-lit d) refl vs | $ k' =
  ⟨ empty-env , ⟨ subst-empty vs , (ℰ-lit d) ⟩ ⟩
subst-reflect {M = M} {σ = σ} (ℰ-lit d) () vs | ƛ M'
subst-reflect {M = M} {σ = σ} (ℰ-lit d) () vs | M₁ · M₂

subst-reflect {M = M}{σ = σ} (ℰ-var {x = y} lt) eqL vs with M 
... | ` x  with (ℰ-var{x = y} lt)
... | yv  rewrite sym eqL = subst-reflect-var {σ = σ} yv vs
subst-reflect {M = M} (ℰ-var {x = y} lt) () vs | M₁ · M₂
subst-reflect {M = M} (ℰ-var {x = y} lt) () vs | ƛ M'
subst-reflect {M = M} (ℰ-var {x = y} lt) () vs | $ k 

subst-reflect {M = M}{σ = σ} (ℰ-app d₁ d₂ lt2) eqL vs
         with M 
...    | ` x with ℰ-app d₁ d₂ lt2
...    | d' rewrite sym eqL = subst-reflect-var {σ = σ} d' vs
subst-reflect (ℰ-app d₁ d₂ lt2) () vs | ƛ M'
subst-reflect (ℰ-app d₁ d₂ lt2) () vs | $ k
subst-reflect{Γ}{Δ}{γ}{σ = σ} (ℰ-app d₁ d₂ lt2) refl vs | M₁ · M₂
     with subst-reflect {M = M₁} d₁ refl vs | subst-reflect {M = M₂} d₂ refl vs
...     | ⟨ δ₁ , ⟨ subst-δ₁ , m1 ⟩ ⟩ | ⟨ δ₂ , ⟨ subst-δ₂ , m2 ⟩ ⟩ =
     ⟨ δ₁ `⊔ δ₂ , ⟨ subst-⊔ {γ₁ = δ₁}{γ₂ = δ₂}{σ = σ} subst-δ₁ subst-δ₂ ,
                    ℰ-app (Env⊑ m1 (EnvConjR1⊑ δ₁ δ₂))
                           (Env⊑ m2 (EnvConjR2⊑ δ₁ δ₂)) lt2 ⟩ ⟩

subst-reflect {M = M}{σ = σ} (ℰ-lam d) eqL vs with M
...    | ` x with (ℰ-lam d)
...    | d' rewrite sym eqL = subst-reflect-var {σ = σ} d' vs
subst-reflect {M = _} {σ = σ} (ℰ-lam d) () vs | $ k
subst-reflect {σ = σ} (ℰ-lam d) eq vs | ƛ M'
      with subst-reflect{σ = exts σ} d (lambda-inj eq) (ext-val-subst vs)
... | ⟨ (δ' , v') , ⟨ exts-σ-δ'v' , m' ⟩ ⟩ = 
    ⟨ δ' , ⟨ ((λ {k} → rename-inc-reflect (exts-σ-δ'v' {S k}))) ,
             ℰ-lam (up-env m' (var-inv (exts-σ-δ'v' {Z} ))) ⟩ ⟩
subst-reflect (ℰ-lam d) () vs | M₁ · M₂ 

subst-reflect {M = M} {σ = σ} ℰ-⊥ eq vs with M
...  | ` x = ⟨ empty-env , ⟨ subst-empty{σ = σ} vs , ℰ-var Bot⊑ ⟩ ⟩
...  | ƛ M' = ⟨ empty-env , ⟨ subst-empty{σ = σ} vs , ℰ-⊥ ⟩ ⟩
subst-reflect {M = M} {σ = σ} ℰ-⊥ () vs | $ k
subst-reflect {M = M} {σ = σ} ℰ-⊥ () vs | M₁ · M₂

subst-reflect {σ = σ} (ℰ-⊔ d₁ d₂) eq vs
    with subst-reflect {σ = σ} d₁ eq vs | subst-reflect {σ = σ} d₂ eq vs
... | ⟨ δ₁ , ⟨ subst-δ₁ , m1 ⟩ ⟩ | ⟨ δ₂ , ⟨ subst-δ₂ , m2 ⟩ ⟩ =
     ⟨ δ₁ `⊔ δ₂ , ⟨ subst-⊔ {γ₁ = δ₁}{γ₂ = δ₂}{σ = σ} subst-δ₁ subst-δ₂ ,
                    ℰ-⊔ (Env⊑ m1 (EnvConjR1⊑ δ₁ δ₂))
                        (Env⊑ m2 (EnvConjR2⊑ δ₁ δ₂)) ⟩ ⟩

subst-reflect{M = M} (ℰ-⊑ d lt) eq vs
    with subst-reflect{M = M} d eq vs
... | ⟨ δ , ⟨ subst-δ , m ⟩ ⟩ = ⟨ δ , ⟨ subst-δ , ℰ-⊑ m lt ⟩ ⟩


nth-id-le : ∀{Γ}{δ'}{v'}{γ}{N}
      → γ ⊨ subst-zero N ↓ (δ' , v')
        -----------------------------------------------------------
      → {n : Γ , ★ ∋ ★} → nth n (δ' , v') ⊑ nth (var-id n) (γ , v')
nth-id-le γ-sz-δ'v' {Z} = Refl⊑
nth-id-le γ-sz-δ'v' {S n'} = var-inv (γ-sz-δ'v' {S n'})


val-subst-zero : ∀{Γ}{γ : Env Γ}{N : Γ ⊢ ★}
  → ℰ N γ ⊥
  → Terminating (subst-zero N) γ
val-subst-zero {Γ}{γ}{N} v = valsub G
  where
  G : ∀{k : Γ , ★ ∋ ★} → ℰ (subst-zero N k) γ ⊥
  G {Z} = v
  G {S k} = ℰ-var Bot⊑


substitution-reflect : ∀ {Γ} {γ : Env Γ} {M N v}
  → ℰ (M [ N ]) γ v   →  ℰ N γ ⊥
    -----------------------------------------------
  → Σ[ v₂ ∈ Value ] ℰ N γ v₂  ×  ℰ M (γ , v₂) v
substitution-reflect {Γ}{γ}{M}{N} d vn
      with subst-reflect {M = M}{σ = subst-zero N} d refl (val-subst-zero vn)
... | ⟨ (δ' , v') , ⟨ γ-sz-δ'v' , mn ⟩ ⟩
      with rename-pres var-id (λ {n} → nth-id-le γ-sz-δ'v' {n}) mn
... | mn' rewrite rename-id {Γ , ★}{M}{var-id} var-id-id =
      ⟨ v' , ⟨ γ-sz-δ'v' {Z} , mn' ⟩ ⟩

infix 2 _—→'_

data _—→'_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where

  ξ₁-rule' : ∀ {Γ} {L L′ M : Γ ⊢ ★}
    → L —→' L′
      ----------------
    → L · M —→' L′ · M

  ξ₂-rule' : ∀ {Γ} {L M M′ : Γ ⊢ ★}
    → TermValue L
    → M —→' M′
      ----------------
    → L · M —→' L · M′

  β-rule' : ∀ {Γ} {N : Γ , ★ ⊢ ★} {M : Γ ⊢ ★} {L : Γ ⊢ ★}
    → TermValue M → N [ M ] ≡ L
      ---------------------------------
    → (ƛ N) · M —→' L

  δ-rule' : ∀ {Γ}{B}{P} {f : base-rep B → rep P} {k : base-rep B}
      ---------------------------------------------------------
    → ($_ {Γ} {B ⇒ P} f) · ($_ {Γ}{` B} k) —→' ($_ {Γ}{P} (f k))


reflect-app-beta : ∀{Γ}{γ : Env Γ}{M N}{v}
    → TermValue M  →  ℰ (N [ M ]) γ v
    → ℰ ((ƛ N) · M) γ v
reflect-app-beta mv d12 
    with substitution-reflect d12 (term-value-⊥ mv)
... | ⟨ v₂' , ⟨ d₁' , d₂' ⟩ ⟩ = ℰ-app (ℰ-lam d₂') d₁' Refl⊑


reflect : ∀ {Γ} {γ : Env Γ} {M N v}
  → ℰ N γ v  →  M —→' N
    --------------------
  → ℰ M γ v
{- by induction on ℰ N γ v -}
reflect{γ = γ} (ℰ-var lt) r
    with r
... | β-rule' v leq
    with (ℰ-var{γ = γ} lt)
... | d' rewrite sym leq = reflect-app-beta v d'
reflect{γ = γ} (ℰ-lit pv) r
    with r
... | β-rule' v leq
    with (ℰ-lit{γ = γ} pv)
... | d' rewrite sym leq = reflect-app-beta v d'
reflect{v = v} (ℰ-lit d) r | (δ-rule'{k = k'}) =
   ℰ-app (ℰ-lit (℘-fun d Refl⊑ Refl⊑)) (ℰ-lit ℘k-litk) Refl⊑
reflect{Γ}{γ} (ℰ-app d₁ d₂ lt) r
    with r
... | ξ₁-rule' r' = ℰ-app (reflect d₁ r') d₂ lt
... | ξ₂-rule' vm1 r' = ℰ-app d₁ (reflect d₂ r') lt
reflect{Γ}{γ} (ℰ-app d₁ d₂ lt) r | β-rule' vv leq
    with ℰ-app d₁ d₂ lt
... | d12 rewrite sym leq = reflect-app-beta vv d12
reflect (ℰ-lam d) r
    with r
... | β-rule' v leq
    with (ℰ-lam d)
... | d' rewrite sym leq = reflect-app-beta v d'
reflect ℰ-⊥ r = {!!}


reflect (ℰ-⊔ d₁ d₂) r = {!!}
reflect (ℰ-⊑ d lt) r = ℰ-⊑ (reflect d r) lt

{-

{- by induction on the reduction relation -}
reflect : ∀ {Γ} {γ : Env Γ} {M N v}
  → ℰ N γ v  →  M —→ N
    --------------------
  → ℰ M γ v
reflect d (ξ₁-rule r) with d
... | ℰ-app d₁ d₂ lt2 = ℰ-app (reflect d₁ r) d₂ lt2
... | ℰ-⊔ d₁ d₂ = ℰ-⊔ (reflect d₁ (ξ₁-rule r)) (reflect d₂ (ξ₁-rule r))
... | ℰ-⊑ d₁ lt =
   {!!}
reflect d (ξ₂-rule d' r) with d
... | ℰ-app d₁ d₂ lt2 = ℰ-app d₁ (reflect d₂ r) lt2
... | ℰ-⊔ d₁ d₂ = ℰ-⊔ (reflect d₁ (ξ₂-rule d' r))
                      (reflect d₂ (ξ₂-rule d' r))
... | ℰ-⊑ d₁ lt = {!!}
reflect d (β-rule v) with substitution-reflect d (term-value-⊥ v)
... | ⟨ v₂ , ⟨ d₁ , d₂ ⟩ ⟩ = ℰ-app (ℰ-lam d₂) d₁ Refl⊑
reflect{v = v} (ℰ-lit d) (δ-rule{k = k'}) =
    ℰ-app{v₁ = lit k'}{v₂ = v} (ℰ-lit (℘-fun d Refl⊑ Refl⊑))
                                (ℰ-lit base-eval-lit) Refl⊑
reflect{v = v} (ℰ-⊑ d lt) (δ-rule{k = k'}) = {!!}

reflect (ℰ-⊔ d₁ d₂) δ-rule =
    ℰ-⊔ (reflect d₁ δ-rule) (reflect d₂ δ-rule)
-}

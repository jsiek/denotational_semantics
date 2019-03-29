module Sem where

open import Lambda
open import ValueBCD

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

Sem : Context → Set₁
Sem Γ = (Env Γ → Value → Set)

infix 3 _≃_

_≃_ : ∀ {Γ} → (Sem Γ) → (Sem Γ) → Set
_≃_ {Γ} D₁ D₂ = ∀{γ : Env Γ} {v} → D₁ γ v iff D₂ γ v

ℬ : ∀{B : Base} → base-rep B → Value
ℬ {Nat} n = lit n
ℬ {𝔹} b = lit b

data ℘ : ∀{P : Prim} → rep P → Value → Set where
   ℘-base : ∀{B}{b : base-rep B}
              ---------------
            → ℘ {` B} b (ℬ b)
   ℘-fun :  ∀{B}{P}{f : base-rep B → rep P}{k : base-rep B}{v : Value}
            → ℘ {P} (f k) v
              ---------------------------
            → ℘ {B ⇒ P} f (lit {B} k ↦ v)
   ℘-⊔ :  ∀{P : Prim}{p : rep P}{v₁ v₂ : Value}
            → ℘ {P} p v₁  →  ℘ {P} p v₂
              -------------------------
            → ℘ {P} p (v₁ ⊔ v₂)
   ℘-⊥ :  ∀{P : Prim}{p : rep P}
              ---------
            → ℘ {P} p ⊥
   ℘-⊑ :  ∀{P : Prim}{p : rep P}{v₁ v₂ : Value}
            → ℘ {P} p v₁  →  v₂ ⊑ v₁
              ----------------------
            → ℘ {P} p v₂


data ℰ : ∀{Γ} → Γ ⊢ ★ → Env Γ → Value → Set where
  ℰ-var : ∀ {Γ} {γ : Env Γ} {x v}
                   → v ⊑ nth x γ
        -----------
      → ℰ (` x) γ v
  ℰ-lit : ∀{Γ}{γ : Env Γ}{P : Prim} {p : rep P} {v : Value}
        → ℘ {P} p v
          --------------------
        → ℰ ($_ {Γ} {P} p) γ v
  ℰ-app : ∀ {Γ} {γ : Env Γ} {M₁ M₂ v v₁ v₂}
        → ℰ M₁ γ (v₁ ↦ v₂)  →  ℰ M₂ γ v₁   → v ⊑ v₂
          ----------------------------------
        → ℰ (M₁ · M₂) γ v

  ℰ-lam : ∀ {Γ} {γ : Env Γ} {M v₁ v₂}
        → ℰ M (γ , v₁) v₂
          -------------------
        → ℰ (ƛ M) γ (v₁ ↦ v₂)

  ℰ-⊥ : ∀ {Γ} {γ : Env Γ} {M}
          -----------
        → ℰ (ƛ M) γ ⊥

  ℰ-⊔ : ∀ {Γ} {γ : Env Γ} {M v₁ v₂}
        → ℰ M γ v₁  →  ℰ M γ v₂
          ---------------------
        → ℰ M γ (v₁ ⊔ v₂)

  ℰ-⊑ : ∀ {Γ} {γ : Env Γ} {M v₁ v₂}
        → ℰ M γ v₁  →  v₂ ⊑ v₁
          ---------------------
        → ℰ M γ v₂

rename-pres : ∀ {Γ Δ v} {γ : Env Γ} {δ : Env Δ} {M : Γ ⊢ ★}
  → (ρ : Rename Γ Δ)
  → (∀ {n : Γ ∋ ★} → nth n γ ⊑ nth (ρ n) δ)
  → ℰ M γ v
    ----------------------------------------
  → ℰ (rename ρ M) δ v
rename-pres ρ nth-eq (ℰ-var{x = x} lt) =  ℰ-var (Trans⊑ lt (nth-eq {x}))
rename-pres ρ nth-eq (ℰ-lit d) = ℰ-lit d
rename-pres ρ nth-eq (ℰ-app d d₁ lt2) =
  ℰ-app (rename-pres ρ nth-eq d) (rename-pres ρ nth-eq d₁) lt2
rename-pres ρ nth-eq (ℰ-lam d) =
  ℰ-lam (rename-pres (ext ρ) (λ {n} → ext-nth ρ nth-eq {n}) d)
rename-pres ρ nth-eq ℰ-⊥ = ℰ-⊥
rename-pres ρ nth-eq (ℰ-⊔ d d₁) =
  ℰ-⊔ (rename-pres ρ nth-eq d) (rename-pres ρ nth-eq d₁)
rename-pres ρ nth-eq (ℰ-⊑ d lt) =
  ℰ-⊑ (rename-pres ρ nth-eq d) lt

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
  → ℰ M γ v  →  γ `⊑ δ
    --------------------
  → ℰ M δ v
Env⊑{Γ}{γ}{δ}{M}{v} d lt
      with rename-pres var-id lt d
... | d' rewrite rename-id {Γ}{M}{var-id} (var-id-id {Γ}) = d'


up-env : ∀ {Γ} {γ : Env Γ} {M v u₁ u₂}
  → ℰ M (γ , u₁) v  →  u₁ ⊑ u₂
    ----------------------------
  → ℰ M (γ , u₂) v
up-env{Γ}{γ}{M}{v}{u₁}{u₂} d lt = Env⊑ d (λ {k} → nth-le lt {k})
  where
  nth-le : u₁ ⊑ u₂ → (γ , u₁) `⊑ (γ , u₂)
  nth-le lt {Z} = lt
  nth-le lt {S n} = Refl⊑

{-

  Inversion (aka Generation) Lemmas

-}

app-inv : ∀{Γ}{γ : Env Γ}{M N : Γ ⊢ ★}{v : Value}
        → ℰ (M · N) γ v
        → Σ[ v₁ ∈ Value ] Σ[ v₂ ∈ Value ] Σ[ v₃ ∈ Value ]  ℰ M γ (v₁ ↦ v₂) × ℰ N γ v₃ × v₁ ⊑ v₃ × v ⊑ v₂
app-inv (ℰ-app{v₁ = v₁}{v₂ = v₂} d₁ d₂ lt) =
   ⟨ v₁ , ⟨ v₂ , ⟨ v₁ , ⟨ d₁ , ⟨ d₂ , ⟨ Refl⊑ , lt ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
app-inv {Γ}{γ}{M}{N}{v} (ℰ-⊔ d₁ d₂)
    with app-inv d₁ | app-inv d₂
... | ⟨ v₁ , ⟨ v₂ , ⟨ v₃ , ⟨ M↓v12 , ⟨ N↓v3 , ⟨ v13 , vv2 ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
    | ⟨ v₁' , ⟨ v₂' , ⟨ v₃' , ⟨ M↓v12' , ⟨ N↓v3' , ⟨ v13' , vv2' ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ =
      let M↓⊔ = ℰ-⊔ M↓v12 M↓v12' in
      let N↓⊔ = ℰ-⊔ N↓v3 N↓v3' in
      ⟨ v₁ ⊔ v₁' , ⟨ v₂ ⊔ v₂' , ⟨ v₃ ⊔ v₃' , ⟨ ℰ-⊑ M↓⊔ G , ⟨ N↓⊔ , ⟨ H , I ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
      where
      G : (v₁ ⊔ v₁') ↦ (v₂ ⊔ v₂') ⊑ (v₁ ↦ v₂) ⊔ (v₁' ↦ v₂')
      G = Trans⊑ (Dist⊑{v₁ = v₁ ⊔ v₁'}{v₂ = v₂}{v₃ = v₂'})
                 (Conj⊑Conj (Fun⊑ (ConjR1⊑ Refl⊑) Refl⊑) (Fun⊑ (ConjR2⊑ Refl⊑) Refl⊑))
      H = Conj⊑Conj v13 v13'
      I = Conj⊑Conj vv2 vv2'
app-inv {Γ}{γ}{M}{N}{v} (ℰ-⊑ d lt)
    with app-inv d
... | ⟨ v₁ , ⟨ v₂ , ⟨ v₃ , ⟨ M↓v12 , ⟨ N↓v3 , ⟨ v13 , vv2 ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ =
      ⟨ v₁ , ⟨ v₂ , ⟨ v₃ , ⟨ M↓v12 , ⟨ N↓v3 , ⟨ v13 , Trans⊑ lt vv2 ⟩ ⟩ ⟩ ⟩ ⟩ ⟩

infixl 7 _●_

_●_ : ∀{Γ} → Sem Γ → Sem Γ → Sem Γ
(F ● E) γ v = Σ[ v₁ ∈ Value ] Σ[ v₂ ∈ Value ] Σ[ v₃ ∈ Value ] F γ (v₁ ↦ v₂) × E γ v₃ × v₁ ⊑ v₃ × v ⊑ v₂


Λ : ∀{Γ} → Sem (Γ , ★) → Sem Γ
Λ S' γ ⊥ = ⊤
Λ S' γ (lit x) = Bot
Λ S' γ (v₁ ↦ v₂) = S' (γ , v₁) v₂
Λ S' γ (v₁ ⊔ v₂) = (Λ S' γ v₁) × (Λ S' γ v₂)

sub-Λ : ∀{Γ}{M : Γ , ★ ⊢ ★}{γ v v'} → (Λ (ℰ M)) γ v → v' ⊑ v → (Λ (ℰ M)) γ v'
sub-Λ d Bot⊑ = tt
sub-Λ d Lit⊑ = d
sub-Λ d (Fun⊑ lt lt') = ℰ-⊑ (up-env d lt) lt'
sub-Λ d (ConjL⊑ lt lt₁) = ⟨ sub-Λ d lt , sub-Λ d lt₁ ⟩
sub-Λ d (ConjR1⊑ lt) = sub-Λ (proj₁ d) lt
sub-Λ d (ConjR2⊑ lt) = sub-Λ (proj₂ d) lt
sub-Λ {v = v₁ ↦ v₂ ⊔ v₁ ↦ v₃} {v₁ ↦ (v₂ ⊔ v₃)} ⟨ M2 , M3 ⟩ Dist⊑ =
   ℰ-⊔ M2 M3
sub-Λ d (Trans⊑ x₁ x₂) = sub-Λ (sub-Λ d x₂) x₁


lam-inv : ∀{Γ}{γ : Env Γ}{M : Γ , ★ ⊢ ★}{v : Value}
        → ℰ (ƛ M) γ v → Λ (ℰ M) γ v
lam-inv (ℰ-lam d) = d
lam-inv ℰ-⊥ = tt
lam-inv (ℰ-⊔ d₁ d₂) = ⟨ lam-inv d₁ , lam-inv d₂ ⟩
lam-inv {Γ}{γ}{M}{v = v₂} (ℰ-⊑{v₁ = v₁}{v₂ = v₂} d lt) = sub-Λ (lam-inv d) lt

inv-lam : ∀{Γ}{γ : Env Γ}{M : Γ , ★ ⊢ ★}{v : Value}
        → Λ (ℰ M) γ v
        → ℰ (ƛ M) γ v
inv-lam {v = ⊥} d = ℰ-⊥
inv-lam {v = lit x} ()
inv-lam {v = v₁ ↦ v₂} d = ℰ-lam d
inv-lam {v = v₁ ⊔ v₂} ⟨ d1 , d2 ⟩ =
    let ih1 = inv-lam{v = v₁} d1 in
    let ih2 = inv-lam{v = v₂} d2 in
    ℰ-⊔ (inv-lam d1) (inv-lam d2)

lam-inv2 : ∀{Γ}{γ : Env Γ}{M : Γ , ★ ⊢ ★}{v : Value}
        → Λ (ℰ M) γ v
        → (v ⊑ ⊥)
          ⊎ (Σ[ v₁ ∈ Value ] Σ[ v₂ ∈ Value ] ℰ M (γ , v₁) v₂ × v₁ ↦ v₂ ⊑ v)
lam-inv2 {v = ⊥} d = inj₁ Bot⊑
lam-inv2 {v = lit x} ()
lam-inv2 {v = v₁ ↦ v₂} d = inj₂ ⟨ v₁ , ⟨ v₂ , ⟨ d , Refl⊑ ⟩ ⟩ ⟩
lam-inv2 {v = v₁ ⊔ v₂} ⟨ d1 , d2 ⟩
    with lam-inv2{v = v₁} d1 | lam-inv2{v = v₂} d2
... | inj₁ d1' | inj₁ d2' = inj₁ (ConjL⊑ d1' d2')
... | inj₁ lt1 | inj₂ ⟨ v₁' , ⟨ v₂' , ⟨ d' , lt2 ⟩ ⟩ ⟩ =
      inj₂ ⟨ v₁' , ⟨ v₂' , ⟨ d' , ConjR2⊑ lt2 ⟩ ⟩ ⟩
... | inj₂  ⟨ v₁' , ⟨ v₂' , ⟨ d' , lt2 ⟩ ⟩ ⟩ | _ =
      inj₂ ⟨ v₁' , ⟨ v₂' , ⟨ d' , ConjR1⊑ lt2 ⟩ ⟩ ⟩


var-inv : ∀ {Γ v x} {γ : Env Γ}
  → ℰ (` x) γ v
    -------------------
  → v ⊑ nth x γ
var-inv (ℰ-var lt) = lt
var-inv (ℰ-⊔ d₁ d₂) = ConjL⊑ (var-inv d₁) (var-inv d₂)
var-inv (ℰ-⊑ d lt) = Trans⊑ lt (var-inv d)

prim-inv : ∀ {Γ v} {γ : Env Γ}{P : Prim}{p : rep P}
  → ℰ ($_ {Γ}{P} p) γ v
    -----------------------------------
  → ℘ {P} p v
prim-inv (ℰ-lit{v = v} d) = d
prim-inv (ℰ-⊔ d d₁) = ℘-⊔ (prim-inv d) (prim-inv d₁)
prim-inv (ℰ-⊑ d x) = ℘-⊑ (prim-inv d) x


{-

  Equational and compositional presentation of the semantics

-}

var-equiv : ∀{Γ}{γ : Env Γ}{x : Γ ∋ ★}
          → ℰ (` x) ≃ (λ γ v → v ⊑ nth x γ)
var-equiv = ⟨ var-inv , (λ lt → ℰ-var lt) ⟩

lit-equiv : ∀{Γ}{γ : Env Γ}{P : Prim}{p : rep P}
          → ℰ ($_ {Γ} {P} p) ≃ λ γ v → ℘ {P} p v
lit-equiv = ⟨ prim-inv , ℰ-lit ⟩

app-equiv : ∀{Γ}{γ : Env Γ}{M N : Γ ⊢ ★}
          → ℰ (M · N) ≃ (ℰ M) ● (ℰ N)
app-equiv{Γ}{γ}{M}{N} = ⟨ app-inv , G ⟩
   where G : ∀{γ v} → (ℰ M ● ℰ N) γ v → ℰ (M · N) γ v
         G {γ}{v} ⟨ v₁ , ⟨ v₂ , ⟨ v₃ , ⟨ d1 , ⟨ d2 , ⟨ lt1 , lt2 ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ =
           ℰ-app d1 (ℰ-⊑ d2 lt1) lt2

lam-equiv : ∀{Γ}{γ : Env Γ}{M : Γ , ★ ⊢ ★}
          → ℰ (ƛ M) ≃ Λ (ℰ M)
lam-equiv {Γ}{γ}{M}{v} = ⟨ lam-inv , inv-lam ⟩



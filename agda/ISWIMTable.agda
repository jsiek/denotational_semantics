
module ISWIMTable where

open import Primitives
open import Syntax using (Rename; extensionality)
open import ISWIM hiding (subst-zero; _[_]; id; _—→_)
open import Fold2 Op sig
open import ValueTable
open import ScopedTuple hiding (𝒫)
open import Sig

open import Data.Nat using (ℕ; zero; suc; _+_; _≤_)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
    renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; sym; cong; cong₂; cong-app; subst)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Empty using (⊥-elim) renaming (⊥ to False)
open import Data.List using (List ; _∷_ ; []; _++_) 

interp  : (op : Op) → Tuple (sig op) (ArgTy (𝒫 Value)) → 𝒫 Value
interp lam ⟨ F , _ ⟩ = Λ F
interp app ⟨ D₁ , ⟨ D₂ , _ ⟩ ⟩ = D₁ ▪ D₂
interp (lit P k) _ = ℘ {P} k

infix 10 ⟦_⟧_
⟦_⟧_ : Term → (Var → 𝒫 Value) → 𝒫 Value
⟦ M ⟧ ρ = fold interp ∅ ρ M


{- Substitution Lemma -}

⟦⟧-rename : ∀ {M : Term}{σ : Rename}{ρ : Var → 𝒫 Value}
  → ⟦ rename σ M ⟧ ρ ≡ ⟦ M ⟧ (λ x → ⟦ ` σ x ⟧ ρ)
⟦⟧-rename {M}{ρ} = fold-rename-fusion M

⟦⟧-subst : ∀ {M : Term}{σ : Subst}{ρ : Var → 𝒫 Value}
  → ⟦ ⟪ σ ⟫ M ⟧ ρ ≡ ⟦ M ⟧ (λ x → ⟦ σ x ⟧ ρ)
⟦⟧-subst {M}{ρ} = fold-subst-fusion M

id : Subst
id = (λ x → ` x)

_[_] : Term → Term → Term
N [ M ] =  ⟪ M • id ⟫ N

⟦⟧-substitution : ∀ {M N : Term}{ρ : Var → 𝒫 Value}
  → ⟦ M [ N ] ⟧ ρ ≡ ⟦ M ⟧ ((⟦ N ⟧ ρ) • ρ)
⟦⟧-substitution {M}{N}{ρ} =
  subst (λ X → ⟦ M [ N ] ⟧ ρ ≡ ⟦ M ⟧ X) (extensionality EQ)
        (⟦⟧-subst {M}{N • id})
  where 
  EQ : (x : Var) → ⟦ (N • id) x ⟧ ρ ≡ (⟦ N ⟧ ρ • ρ) x
  EQ zero = refl
  EQ (suc x) = refl

{- Consistent -}

data _~̸_ : Value → Value → Set 

data _~_ : Value → Value → Set where 
  ~const : ∀ {B k} → const {B} k ~ const {B} k
  ~fun : ∀{t₁ t₂}
      → (∀ {v₁ w₁ v₂ w₂}
         → v₁ ↦ w₁ ∈ mem t₁  →  v₂ ↦ w₂ ∈ mem t₂
         → (v₁ ~ v₂ × w₁ ~ w₂) ⊎ v₁ ~̸ v₂)
      → fun t₁ ~ fun t₂

data _~̸_ where
  ~̸const-B : ∀ {B B′ k k′} → B ≢ B′ → const {B} k ~̸ const {B′} k′
  ~̸const-k : ∀ {B k k′} → k ≢ k′ → const {B} k ~̸ const {B} k′
  ~̸fun : ∀{t₁ t₂ v₁ w₁ v₂ w₂}
     → v₁ ↦ w₁ ∈ mem t₁  →  v₂ ↦ w₂ ∈ mem t₂
     → v₁ ~ v₂  →  w₁ ~̸ w₂
     → fun t₁ ~̸ fun t₂

table-size : Table → ℕ

size : Value → ℕ
size (const k) = 0
size (fun t) = suc (table-size t)

table-size [] = 0
table-size (⟨ v , w ⟩ ∷ ts) = size v + size w + table-size ts

mem-size : ∀{t v w} → mem t ⟨ v , w ⟩ →  size v ≤ table-size t
      ×  size w ≤ table-size t
mem-size {.(⟨ v , w ⟩ ∷ _)} {v} {w} mem-here = ⟨ {!!} , {!!} ⟩
mem-size {.(_ ∷ _)} {v} {w} (mem-there vwt)
    with mem-size vwt
... | ⟨ a , b ⟩  = ⟨ {!!} , {!!} ⟩

~̸⇒¬~-aux : ∀{u v n} → size u + size v ≤ n → u ~̸ v → ¬ (u ~ v)
~̸⇒¬~-aux m (~̸const-B B≠B′) ~const = ⊥-elim (B≠B′ refl)
~̸⇒¬~-aux m (~̸const-k k≠k′) ~const = ⊥-elim (k≠k′ refl)
~̸⇒¬~-aux {fun t₁} {fun t₂}{n} m (~̸fun {t₁}{t₂}{v₁}{w₁}{v₂}{w₂} vw₁∈ vw₂∈ v₁~v₂ w₁~̸w₂)
   (~fun t₁~t₂)
    with t₁~t₂ vw₁∈ vw₂∈
... | inj₁ ⟨ _ , w₁~w₂ ⟩ = ~̸⇒¬~-aux {n = suc (suc n)} {!!} w₁~̸w₂ w₁~w₂
... | inj₂ v₁~̸v₂ = ~̸⇒¬~-aux {n = suc (suc n)} {!!} v₁~̸v₂ v₁~v₂

~̸⇒¬~ : ∀{u v} → u ~̸ v → ¬ (u ~ v)
~̸⇒¬~ {u}{v} u~̸v = ~̸⇒¬~-aux {n = size u + size v} ≤-refl u~̸v

¬~⇒~̸ : ∀{u v} → ¬ (u ~ v) → u ~̸ v
¬~⇒~̸ {u}{v} ¬uv = {!!}

~-refl : ∀{u} → u ~ u
~-refl {u} = {!!}

~-sym : ∀{u v} → u ~ v → v ~ u
~-sym {u}{v} uv = {!!}

~-decidable-aux : ∀ (u v : Value) → ∀{n} → size u + size v ≤ n → Dec (u ~ v)
~-decidable-aux (const {B} k) (const {B′} k′) {n} m
    with base-eq? B B′
... | no neq = no λ { ~const → ⊥-elim (neq refl) }
... | yes refl
    with base-rep-eq? k k′
... | no neq  = no λ { ~const → neq refl }
... | yes refl = yes ~const
~-decidable-aux (const {B} k) (fun t₁) {n} m = no λ ()
~-decidable-aux (fun t₁) (const x) {n} m = no λ ()
~-decidable-aux (fun t₁) (fun t₂) {n} m = {!!}

~-decidable : ∀ (u v : Value) → Dec (u ~ v)
~-decidable u v = ~-decidable-aux u v {size u + size v} ≤-refl

consistent : 𝒫 Value → Set
consistent D = ∀ {u v} → u ∈ D → v ∈ D → u ~ v

⟦⟧-monotone : ∀{M : Term}{ρ ρ′}
  → (∀ x → ρ x ≲ ρ′ x)
  → ⟦ M ⟧ ρ ≲ ⟦ M ⟧ ρ′ 
⟦⟧-monotone {` x} ρ<ρ′ = ρ<ρ′ x
⟦⟧-monotone {L · M} ρ<ρ′ w ⟨ t , ⟨ t∈ , ⟨ v , ⟨ vw∈ , v∈ ⟩ ⟩ ⟩ ⟩ =
  let t∈L = ⟦⟧-monotone {L} ρ<ρ′ (fun t) t∈ in
  let v∈M = ⟦⟧-monotone {M} ρ<ρ′ v v∈ in
  ⟨ t , ⟨ t∈L , ⟨ v , ⟨ vw∈ , v∈M ⟩ ⟩ ⟩ ⟩
⟦⟧-monotone {ƛ N}{ρ}{ρ′} ρ<ρ′ (fun t) ft v w vw∈ =
  let w∈⟦N⟧ = ft v w vw∈ in
  ⟦⟧-monotone {N} G w w∈⟦N⟧
  where
  G : (x : Var) → (⌈ v ⌉ • ρ) x ≲ (⌈ v ⌉ • ρ′) x
  G zero = λ v z → z
  G (suc x) = ρ<ρ′ x
⟦⟧-monotone {$ p k} ρ<ρ′ = {!!}

⟦⟧-consistent : ∀{M : Term}{ρ}
  → (∀ x → consistent (ρ x))
  → consistent (⟦ M ⟧ ρ)
⟦⟧-consistent {` x}{ρ} ρ~ = ρ~ x  
⟦⟧-consistent {L · M}{ρ} ρ~ {w₁}{w₂}
   ⟨ t₁ , ⟨ t₁∈ , ⟨ v₁ , ⟨ v₁w₁∈ , v₁∈ ⟩ ⟩ ⟩ ⟩
   ⟨ t₂ , ⟨ t₂∈ , ⟨ v₂ , ⟨ v₂w₂∈ , v₂∈ ⟩ ⟩ ⟩ ⟩
    with ⟦⟧-consistent {L}{ρ} ρ~ t₁∈ t₂∈
... | ~fun t₁~t₂ 
    with t₁~t₂ v₁w₁∈ v₂w₂∈
... | inj₁ ⟨ v₁∼v₂ , w₁∼w₂ ⟩ = w₁∼w₂    
... | inj₂ v₁~̸v₂ =
    let v₁~v₂ = ⟦⟧-consistent {M}{ρ} ρ~ v₁∈ v₂∈ in
    ⊥-elim (~̸⇒¬~ v₁~̸v₂ v₁~v₂)  
⟦⟧-consistent {ƛ N}{ρ} ρ~ {fun t₁}{fun t₂} t1∈λN t2∈λN =
    ~fun G
    where
    G : {v₁ w₁ v₂ w₂ : Value} →
         v₁ ↦ w₁ ∈ mem t₁ →
         v₂ ↦ w₂ ∈ mem t₂ → (v₁ ~ v₂) × (w₁ ~ w₂) ⊎ (v₁ ~̸ v₂)
    G {v₁}{w₁}{v₂}{w₂} vwt1 vwt2
        with ~-decidable v₁ v₂ 
    ... | no ¬v₁~v₂ = inj₂ (¬~⇒~̸ ¬v₁~v₂)
    ... | yes v₁~v₂ =        
       let w1∈Nρ = t1∈λN v₁ w₁ vwt1 in
       let w1∈Nρ′ = ⟦⟧-monotone {N} v₁•ρ≲ρ′ w₁ w1∈Nρ in
       let w2∈Nρ = t2∈λN v₂ w₂ vwt2 in       
       let w2∈Nρ′ = ⟦⟧-monotone {N} v₂•ρ≲ρ′ w₂ w2∈Nρ in
       let w₁~w₂ = ⟦⟧-consistent {N}{ρ′} ρ′-consis {w₁}{w₂} w1∈Nρ′ w2∈Nρ′ in
       inj₁ ⟨ v₁~v₂ , w₁~w₂ ⟩
       where
       ρ′ = (λ v → v ≡ v₁ ⊎ v ≡ v₂) • ρ
       
       v₁•ρ≲ρ′ : ∀ x →  ((λ v → v ≡ v₁) • ρ) x ≲ ρ′ x
       v₁•ρ≲ρ′ zero u refl = inj₁ refl
       v₁•ρ≲ρ′ (suc x) = λ v z → z
       
       v₂•ρ≲ρ′ : ∀ x →  ((λ v → v ≡ v₂) • ρ) x ≲ ρ′ x
       v₂•ρ≲ρ′ zero a b = inj₂ b
       v₂•ρ≲ρ′ (suc x) a b = b
    
       ρ′-consis : ∀ x → consistent (ρ′ x)
       ρ′-consis zero (inj₁ refl) (inj₁ refl) = ~-refl
       ρ′-consis zero (inj₁ refl) (inj₂ refl) = v₁~v₂
       ρ′-consis zero (inj₂ refl) (inj₁ refl) = ~-sym v₁~v₂
       ρ′-consis zero (inj₂ refl) (inj₂ refl) = ~-refl
       ρ′-consis (suc x) a b = ρ~ x a b
⟦⟧-consistent {$ p k}{ρ} ρ~ u∈M v∈M = {!!}  


{- Join Closed -}

⟦⟧-join-closed : ∀ {M : Term}{ρ}
   → (∀ x → join-closed (ρ x) )
   → join-closed (⟦ M ⟧ ρ)
⟦⟧-join-closed {` x} {ρ} ρ-closed = ρ-closed x
⟦⟧-join-closed {L · M} {ρ} ρ-closed V V≢[] V<⟦L·M⟧ = {!!}
{-

  nts. ∃ w. w ∈ ⟦ L · M ⟧ and V<v
     w ∈ ⟦ L ⟧ ρ ▪ ⟦ M ⟧ ρ
     ∃ t. fun t ∈ ⟦ L ⟧ ρ
     ∃ v. v ↦ w ∈ t   and v ∈ ⟦ M ⟧ ρ
     
  have 
     mem V ≲ ⟦ L · M ⟧ ρ
-}
{-
    with ⟦⟧-join-closed{L} ρ-closed V {!!}
... | ⟨ u , ⟨ u∈D , V<u ⟩ ⟩ = 

  let IH2 = ⟦⟧-join-closed{M} ρ-closed in
  {!!}
-}
⟦⟧-join-closed {ƛ N} {ρ} ρ-closed = {!!}
⟦⟧-join-closed {$ p k} {ρ} ρ-closed = {!!}


infix 2 _—→_

data _—→_ : Term → Term → Set where

  ξ₁-rule : ∀  {L L′ M : Term}
    → L —→ L′
      ----------------
    → L · M —→ L′ · M

  ξ₂-rule : ∀  {L M M′ : Term}
    → TermValue L
    → M —→ M′
      ----------------
    → L · M —→ L · M′

  β-rule : ∀  {N : Term} {M : Term}
    → TermValue M
      ---------------------------------
    → (ƛ N) · M —→ N [ M ]

  δ-rule : ∀ {B}{P} {f : base-rep B → rep P} {k : base-rep B}
      ------------------------------------------------------------
    → _—→_  (($ (B ⇒ P) f) · ($ (base B) k)) ($ P (f k))


⟦⟧—→ : ∀{M N : Term}{ρ : Var → 𝒫 Value}
   → M —→ N
   → ⟦ M ⟧ ρ ≃ ⟦ N ⟧ ρ
   
⟦⟧—→ {L · M} {L′ · M} {ρ} (ξ₁-rule L—→L′) =
  let IH = ⟦⟧—→{ρ = ρ} L—→L′ in
    ⟦ L · M ⟧ ρ
  ≃⟨ ≃-refl ⟩
    (⟦ L ⟧ ρ) ▪ (⟦ M ⟧ ρ)
  ≃⟨ ▪-cong IH ≃-refl ⟩
    (⟦ L′ ⟧ ρ) ▪ (⟦ M ⟧ ρ)
  ≃⟨ ≃-refl ⟩
    ⟦ L′ · M ⟧ ρ
  ∎
  where open ≃-Reasoning  
⟦⟧—→ {V · M} {.(_ · _)} {ρ} (ξ₂-rule {M′ = M′} v M—→M′) =
  let IH = ⟦⟧—→{ρ = ρ} M—→M′ in
    ⟦ V · M ⟧ ρ
  ≃⟨ ≃-refl ⟩
    (⟦ V ⟧ ρ) ▪ (⟦ M ⟧ ρ)
  ≃⟨ ▪-cong (≃-refl{D = ⟦ V ⟧ ρ}) IH ⟩
    (⟦ V ⟧ ρ) ▪ (⟦ M′ ⟧ ρ)
  ≃⟨ ≃-refl ⟩
    ⟦ V · M′ ⟧ ρ
  ∎
  where open ≃-Reasoning  
⟦⟧—→ {ƛ N · V} {_} {ρ} (β-rule v) =
    ⟦ ƛ N · V ⟧ ρ
  ≃⟨ {!!} ⟩
     (Λ (λ D → ⟦ N ⟧ (D • ρ))) ▪ (⟦ V ⟧ ρ)
  ≃⟨ {!!} ⟩
     ⟦ N ⟧ (⟦ V ⟧ ρ • ρ)
  ≃⟨ {!!} {- sym (⟦⟧-substitution {N} {V} {ρ}) -} ⟩
    ⟦ N [ V ] ⟧ ρ
  ∎
  where open ≃-Reasoning
⟦⟧—→ {($ (B ⇒ P) f · $ (base B) k)} {_} {ρ} δ-rule = {!!}

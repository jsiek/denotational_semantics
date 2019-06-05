open import Primitives
open import Variables
open import Structures
import Lambda
open Lambda.ASTMod
   using (`_; _⦅_⦆; Subst;
          exts; cons; bind; nil; rename; ⟪_⟫; subst-zero; _[_]; rename-id)

open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; cong; cong₂)
open import Data.Nat using (ℕ; suc ; zero)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Agda.Primitive using (lzero)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using (contradiction)
open import Data.Empty using (⊥-elim) renaming (⊥ to Bot)
open import Relation.Nullary using (Dec; yes; no)
open import Data.Unit using (⊤; tt)


module ValueBCDConst where

infixr 7 _↦_
infixl 5 _⊔_

data Value : Set where
  ⊥ : Value
  const : {B : Base} → base-rep B → Value
  _↦_ : Value → Value → Value
  _⊔_ : Value → Value → Value

domain : Domain
domain = record { Value = Value ; ⊥ = ⊥ ; _↦_ = _↦_ ; _⊔_ = _⊔_ }

open DomainAux domain

ℱ : ∀{Γ} → Denotation (suc Γ) → Denotation Γ
ℱ D γ (v ↦ w) = D (γ `, v) w
ℱ D γ ⊥ = ⊤
ℱ D γ (const k) = Bot
ℱ D γ (u ⊔ v) = (ℱ D γ u) × (ℱ D γ v)

ℱ-⊔ : ∀{Γ}{D : Denotation (suc Γ)}{γ : Env Γ} {u v : Value}
    → ℱ D γ u → ℱ D γ v → ℱ D γ (u ⊔ v)
ℱ-⊔ d1 d2 = ⟨ d1 , d2 ⟩

ℱ-⊥ : ∀{Γ}{D : Denotation (suc Γ)}{γ : Env Γ}
    → ℱ D γ ⊥
ℱ-⊥ = tt

ℱ-≲ : ∀{Γ Δ}{γ : Env Γ}{δ : Env Δ}{D : Denotation (suc Γ)}
          {D′ : Denotation (suc Δ)}
       → (∀{v : Value} → D (γ `, v) ≲ D′ (δ `, v))
       → ℱ D γ ≲ ℱ D′ δ
ℱ-≲ D≲D′ {⊥} = λ _ → tt
ℱ-≲ D≲D′ {const k} = λ x → x
ℱ-≲ D≲D′ {v ↦ w} = D≲D′
ℱ-≲ {D = D}{D′} D≲D′ {u ⊔ v} ℱDγ
    with ℱ-≲{D = D}{D′} D≲D′ {u} | ℱ-≲{D = D}{D′} D≲D′ {v}
... | a | b =
    ⟨ (a (proj₁ ℱDγ)) , (b (proj₂ ℱDγ)) ⟩

infix 4 _⊑_

data _⊑_ : Value → Value → Set where

  ⊑-⊥ : ∀ {v} → ⊥ ⊑ v

  ⊑-const : ∀ {B}{k} → const {B} k ⊑ const {B} k

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
⊑-refl {const k} = ⊑-const
⊑-refl {v ↦ v′} = ⊑-fun ⊑-refl ⊑-refl
⊑-refl {v₁ ⊔ v₂} = ⊑-conj-L (⊑-conj-R1 ⊑-refl) (⊑-conj-R2 ⊑-refl)

ordering : ValueOrdering domain
ordering = record
             { _⊑_ = _⊑_
             ; ⊑-⊥ = ⊑-⊥
             ; ⊑-conj-L = ⊑-conj-L
             ; ⊑-conj-R1 = ⊑-conj-R1
             ; ⊑-conj-R2 = ⊑-conj-R2
             ; ⊑-trans = ⊑-trans
             ; ⊑-fun = ⊑-fun
             ; ⊑-dist = ⊑-dist
             ; ⊑-refl = ⊑-refl
             }

open OrderingAux domain ordering

ℱ-⊑ : ∀{Γ}{D : Denotation (suc Γ)}{γ : Env Γ} {v w : Value}
       → WFDenot (suc Γ) D
       → ℱ D γ v → w ⊑ v → ℱ D γ w
ℱ-⊑ d ℱDγv ⊑-⊥ = tt
ℱ-⊑ d () ⊑-const
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

model_curry : ModelCurry ℱ
model_curry = record { ℱ-≲ = ℱ-≲ ; ℱ-⊑ = ℱ-⊑ ;
                       ℱ-⊔ = λ {Γ}{D}{γ}{u}{v} → ℱ-⊔{D = D}{γ}{u}{v} ;
                       ℱ-⊥ = λ {Γ}{D}{γ} → ℱ-⊥ {Γ}{D}{γ} }


℘ : ∀{P : Prim} → rep P → Value → Set
℘ {P} k (const {B′} k′)
    with P
... | B ⇒ P′ = Bot
... | base B 
    with base-eq? B B′
... | yes eq rewrite eq = k ≡ k′
... | no neq = Bot
℘ {P} k ⊥ = ⊤
℘ {P} f (v ↦ w)
    with P
... | base B = Bot
{-
... | B ⇒ P′ = ∀{k : base-rep B} → v ⊑ const {B} k → ℘ {P′} (f k) w
-}
... | B ⇒ P′ = Σ[ k ∈ base-rep B ] (const {B} k ⊑ v × ℘ {P′} (f k) w)
℘ {P} f (u ⊔ v) = ℘ {P} f u × ℘ {P} f v


{- need consistency for this to be true! -Jeremy -}
postulate k⊑v→k′⊑v→k′≡k : ∀{B : Base}{k : base-rep B}{k′ : base-rep B} {v : Value} → const k ⊑ v → const k′ ⊑ v → k′ ≡ k


℘-⊑ : ∀{P}{k : rep P}{v w : Value}
   → ℘ {P} k v
   → w ⊑ v
     ------------
   → ℘ {P} k w
℘-⊑ {P} {k} {v} {.⊥} ℘kv ⊑-⊥ =
   tt
℘-⊑ {P} {k} {.(const _)} {.(const _)} ℘kv ⊑-const =
   ℘kv
℘-⊑ {P} {k} {v} {.(_ ⊔ _)} ℘kv (⊑-conj-L w⊑v w⊑v₁) =
   ⟨ ℘-⊑ ℘kv w⊑v , ℘-⊑ ℘kv w⊑v₁ ⟩
℘-⊑ {P} {k} {.(_ ⊔ _)} {w} ℘kv (⊑-conj-R1 w⊑v) =
   ℘-⊑ (proj₁ ℘kv) w⊑v
℘-⊑ {P} {k} {.(_ ⊔ _)} {w} ℘kv (⊑-conj-R2 w⊑v) =
   ℘-⊑ (proj₂ ℘kv) w⊑v
℘-⊑ {P} {k} {v} {w} ℘kv (⊑-trans w⊑v w⊑v₁) =
   ℘-⊑ (℘-⊑ ℘kv w⊑v₁) w⊑v
℘-⊑ {P} {f} {v ↦ w} {v′ ↦ w′} ℘fv (⊑-fun v⊑v′ w′⊑w)
    with P
... | base B = ℘fv
{-
... | B ⇒ P′ = G
    where G : ∀{k} → v′ ⊑ const k → ℘ {P′} (f k) w′
          G {k} v′⊑k = ℘-⊑ {P′} (℘fv {k} (⊑-trans v⊑v′ v′⊑k)) w′⊑w
-}
... | B ⇒ P′
    with ℘fv
... | ⟨ k , ⟨ k⊑v , ℘fkw ⟩ ⟩ = G
    where G : Σ[ k ∈ base-rep B ] (const k ⊑ v′ × ℘ (f k) w′)
          G = ⟨ k , ⟨ (⊑-trans k⊑v v⊑v′) , (℘-⊑ ℘fkw w′⊑w) ⟩ ⟩


℘-⊑ {P} {f} {(v ↦ w ⊔ v ↦ w′)} {(v ↦ (w ⊔ w′))} ℘fv ⊑-dist
    with P
... | base B = proj₁ ℘fv
{-
... | B ⇒ P′ = G
    where G : ∀{k} → v ⊑ const k → ℘ {P′} (f k) w × ℘ {P′} (f k) w′
          G {k} v⊑k = ⟨ (proj₁ ℘fv v⊑k) , (proj₂ ℘fv v⊑k) ⟩
-}
... | B ⇒ P′
    with ℘fv
... | ⟨ ⟨ k , ⟨ k⊑v , ℘fkw ⟩ ⟩ , ⟨ k′ , ⟨ k′⊑v , ℘fk′w ⟩ ⟩ ⟩ = G
    where G : Σ[ k ∈ base-rep B ] (const k ⊑ v × ℘ (f k) w × ℘ (f k) w′)
          G
              with k⊑v→k′⊑v→k′≡k k⊑v k′⊑v
          ... | eq rewrite eq =
             ⟨ k , ⟨ k⊑v , ⟨ ℘fkw , ℘fk′w ⟩ ⟩ ⟩

℘-⊔ : ∀{P : Prim} {k : rep P} {u v : Value}
    → ℘ {P} k u → ℘ {P} k v → ℘ {P} k (u ⊔ v)
℘-⊔ ℘u ℘v = ⟨ ℘u , ℘v ⟩


Below⊥ : Value → Set
Below⊥ ⊥ = ⊤
Below⊥ (const x) = Bot
Below⊥ (v ↦ v₁) = Bot
Below⊥ (u ⊔ v) = Below⊥ u × Below⊥ v

Below⊥-⊑ : ∀{v w : Value} → Below⊥ v → w ⊑ v → Below⊥ w
Below⊥-⊑ bv ⊑-⊥ = tt
Below⊥-⊑ bv ⊑-const = bv
Below⊥-⊑ bv (⊑-conj-L w⊑v w⊑v₁) = ⟨ Below⊥-⊑ bv w⊑v , Below⊥-⊑ bv w⊑v₁ ⟩
Below⊥-⊑ bv (⊑-conj-R1 w⊑v) = Below⊥-⊑ (proj₁ bv) w⊑v
Below⊥-⊑ bv (⊑-conj-R2 w⊑v) = Below⊥-⊑ (proj₂ bv) w⊑v
Below⊥-⊑ bv (⊑-trans w⊑v w⊑v₁) = Below⊥-⊑ (Below⊥-⊑ bv w⊑v₁) w⊑v
Below⊥-⊑ bv (⊑-fun w⊑v w⊑v₁) = bv
Below⊥-⊑ bv ⊑-dist = proj₁ bv

v⊑⊥→Below⊥ : ∀{v : Value} → v ⊑ ⊥ → Below⊥ v
v⊑⊥→Below⊥ ⊑-⊥ = tt
v⊑⊥→Below⊥ (⊑-conj-L v⊑⊥ v⊑⊥₁) = ⟨ v⊑⊥→Below⊥ v⊑⊥ , v⊑⊥→Below⊥ v⊑⊥₁ ⟩
v⊑⊥→Below⊥ (⊑-trans v⊑⊥ v⊑⊥₁) = Below⊥-⊑ (v⊑⊥→Below⊥ v⊑⊥₁) v⊑⊥



BelowConst : ∀{B : Base} → (k : base-rep B) → Value → Set
BelowConst k ⊥ = ⊤
BelowConst {B} k (const {B′} k′)
    with base-eq? B B′
... | yes eq rewrite eq = k ≡ k′ 
... | no neg = Bot
BelowConst k (v ↦ w) = Bot
BelowConst k (u ⊔ v) = BelowConst k u × BelowConst k v

Below⊥→BelowConst : ∀{B : Base}{k : base-rep B}{v : Value}
   → Below⊥ v
   → BelowConst k v
Below⊥→BelowConst {v = ⊥} b⊥v = tt
Below⊥→BelowConst {B}{k}{const {B′} k′} b⊥v
    with base-eq? B B′ 
... | yes eq rewrite eq = ⊥-elim b⊥v
... | no neq = b⊥v
Below⊥→BelowConst {v = v ↦ w} b⊥v = b⊥v
Below⊥→BelowConst {v = v₁ ⊔ v₂} ⟨ fst , snd ⟩ =
  ⟨ Below⊥→BelowConst fst , Below⊥→BelowConst snd ⟩

BelowConst-⊥ : ∀{B : Base}{k : base-rep B}{v : Value}
   → v ⊑ ⊥
   → BelowConst k v
BelowConst-⊥ v⊑⊥ = Below⊥→BelowConst (v⊑⊥→Below⊥ v⊑⊥)

BelowConst-⊑ : ∀{B : Base}{k : base-rep B}{v w : Value}
   → BelowConst k v
   → w ⊑ v
   → BelowConst k w
BelowConst-⊑ bkv ⊑-⊥ = tt
BelowConst-⊑ {B} bkv (⊑-const{B′})
    with base-eq? B B′
... | yes eq rewrite eq = bkv
... | no neq = bkv
BelowConst-⊑ bkv (⊑-conj-L w⊑v w⊑v₁) =
  ⟨ BelowConst-⊑ bkv w⊑v , BelowConst-⊑ bkv w⊑v₁ ⟩
BelowConst-⊑ bkv (⊑-conj-R1 w⊑v) = BelowConst-⊑ (proj₁ bkv) w⊑v
BelowConst-⊑ bkv (⊑-conj-R2 w⊑v) = BelowConst-⊑ (proj₂ bkv) w⊑v
BelowConst-⊑ bkv (⊑-trans w⊑v w⊑v₁) = BelowConst-⊑ (BelowConst-⊑ bkv w⊑v₁) w⊑v
BelowConst-⊑ bkv (⊑-fun w⊑v w⊑v₁) = bkv
BelowConst-⊑ bkv ⊑-dist = proj₁ bkv

⊑k→BelowConstk : ∀{B : Base}{k : base-rep B}{v : Value}
   → v ⊑ const {B} k
   → BelowConst k v
⊑k→BelowConstk ⊑-⊥ = tt
⊑k→BelowConstk {B} (⊑-const{B′})
    with base-eq? B B′
... | yes eq rewrite eq = refl
... | no neq = neq refl
⊑k→BelowConstk (⊑-conj-L v⊑k v⊑k₁) =
   ⟨ ⊑k→BelowConstk v⊑k , ⊑k→BelowConstk v⊑k₁ ⟩
⊑k→BelowConstk (⊑-trans v⊑k v⊑k₁) =
  let ih = ⊑k→BelowConstk v⊑k₁ in
  BelowConst-⊑ ih v⊑k

BelowConstk→⊑k : ∀{B : Base}{k : base-rep B}{v : Value}
   → BelowConst k v
   → v ⊑ const {B} k
BelowConstk→⊑k {v = ⊥} bkv = ⊑-⊥
BelowConstk→⊑k {B}{k}{v = const {B′} k′} bkv
     with base-eq? B B′
... | yes eq rewrite eq | bkv = ⊑-const
... | no neq = ⊥-elim bkv
BelowConstk→⊑k {v = v ↦ v₁} ()
BelowConstk→⊑k {v = v₁ ⊔ v₂} ⟨ fst , snd ⟩ =
  ⊑-conj-L (BelowConstk→⊑k fst) (BelowConstk→⊑k snd)

℘k→BelowConstk : ∀{B : Base}{k : base-rep B}{v : Value}
    → ℘ {base B} k v
    → BelowConst k v
℘k→BelowConstk {B} {k} {⊥} ℘kv = tt
℘k→BelowConstk {B} {k} {const {B′} k′} ℘kv
    with base-eq? B B′
... | yes eq rewrite eq = ℘kv
... | no neq = ℘kv
℘k→BelowConstk {B} {k} {v ↦ v₁} ℘kv = ℘kv
℘k→BelowConstk {B} {k} {v ⊔ v₁} ℘kv =
  ⟨ (℘k→BelowConstk {B}{k}{v} (proj₁ ℘kv)) ,
    (℘k→BelowConstk {B}{k}{v₁} (proj₂ ℘kv)) ⟩


{------------------------------
  Function Inversion
 -------------------------------}

infix 5 _∈_

_∈_ : Value → Value → Set
u ∈ ⊥ = u ≡ ⊥
u ∈ const {B} k = u ≡ const {B} k
u ∈ v ↦ w = u ≡ v ↦ w
u ∈ (v ⊔ w) = u ∈ v ⊎ u ∈ w

infix 5 _⊆_

_⊆_ : Value → Value → Set
v ⊆ w = ∀{u} → u ∈ v → u ∈ w

not-u₁⊔u₂∈v : ∀{v u₁ u₂} → ¬ (u₁ ⊔ u₂) ∈ v
not-u₁⊔u₂∈v {⊥} ()
not-u₁⊔u₂∈v {const x} ()
not-u₁⊔u₂∈v {v ↦ v₁} ()
not-u₁⊔u₂∈v {v ⊔ v₁} (inj₁ x) = not-u₁⊔u₂∈v x
not-u₁⊔u₂∈v {v ⊔ v₁} (inj₂ y) = not-u₁⊔u₂∈v y


∈→⊑ : ∀{u v : Value}
    → u ∈ v
      -----
    → u ⊑ v
∈→⊑ {⊥} {⊥} u∈v = ⊑-⊥
∈→⊑ {⊥} {v} u∈v = ⊑-⊥
∈→⊑ {u} {⊥} u∈v rewrite u∈v = ⊑-⊥
∈→⊑ {const {B} k} {const {B′} k′} u∈v rewrite u∈v = ⊑-refl
∈→⊑ {const {B} k} {v ↦ w} ()
∈→⊑ {v ↦ w} {const k} ()
∈→⊑ {v ↦ w} {v ↦ w} refl = ⊑-refl
∈→⊑ {u} {v ⊔ w} (inj₁ x) = ⊑-conj-R1 (∈→⊑ x)
∈→⊑ {u} {v ⊔ w} (inj₂ y) = ⊑-conj-R2 (∈→⊑ y)
∈→⊑ {u₁ ⊔ u₂} {v} u∈v = ⊥-elim (contradiction u∈v not-u₁⊔u₂∈v)

⊆→⊑ : ∀{u v : Value}
    → u ⊆ v
      -----
    → u ⊑ v
⊆→⊑ {⊥} s with s {⊥} refl
... | x = ⊑-⊥
⊆→⊑ {const {B} k} s with s {const {B} k} refl
... | x = ∈→⊑ x
⊆→⊑ {u ↦ u′} s with s {u ↦ u′} refl
... | x = ∈→⊑ x
⊆→⊑ {u ⊔ u′} s = ⊑-conj-L (⊆→⊑ (λ z → s (inj₁ z))) (⊆→⊑ (λ z → s (inj₂ z)))

⊔⊆-inv : ∀{u v w : Value}
       → (u ⊔ v) ⊆ w
         ---------------
       → u ⊆ w  ×  v ⊆ w
⊔⊆-inv uvw = ⟨ (λ x → uvw (inj₁ x)) , (λ x → uvw (inj₂ x)) ⟩

↦⊆→∈ : ∀{v w u : Value}
     → v ↦ w ⊆ u
       ---------
     → v ↦ w ∈ u
↦⊆→∈ incl = incl refl 

data Fun : Value → Set where
  fun : ∀{u v w} → u ≡ (v ↦ w) → Fun u

not-Fun-k : ∀{B : Base}{k : base-rep B} → ¬ Fun (const {B} k)
not-Fun-k {B} {k} (fun ())

Funs : Value → Set
Funs v = ∀{u} → u ∈ v → Fun u

¬Fun⊥ : ¬ (Fun ⊥)
¬Fun⊥ (fun ())

Funs∈ : ∀{u}
      → Funs u
      → Σ[ v ∈ Value ] Σ[ w ∈ Value ] v ↦ w ∈ u
Funs∈ {⊥} f with f {⊥} refl
... | fun ()
Funs∈ {const {B} k} f = ⊥-elim (not-Fun-k (f refl))
Funs∈ {v ↦ w} f = ⟨ v , ⟨ w , refl ⟩ ⟩
Funs∈ {u ⊔ u′} f
    with Funs∈ λ z → f (inj₁ z)
... | ⟨ v , ⟨ w , m ⟩ ⟩ = ⟨ v , ⟨ w , (inj₁ m) ⟩ ⟩


dom : (u : Value) → Value
dom ⊥  = ⊥
dom (const {B} k) = ⊥
dom (v ↦ w) = v
dom (u ⊔ u′) = dom u ⊔ dom u′

cod : (u : Value) → Value
cod ⊥  = ⊥
cod (const {B} k) = ⊥
cod (v ↦ w) = w
cod (u ⊔ u′) = cod u ⊔ cod u′


↦∈→⊆dom : ∀{u v w : Value}
          → Funs u  →  (v ↦ w) ∈ u
            ----------------------
          → v ⊆ dom u
↦∈→⊆dom {⊥} fg () u∈v
↦∈→⊆dom {const {B} k} fu ()
↦∈→⊆dom {v ↦ w} fg refl u∈v = u∈v
↦∈→⊆dom {u ⊔ u′} fg (inj₁ v↦w∈u) u∈v =
   let ih = ↦∈→⊆dom (λ z → fg (inj₁ z)) v↦w∈u in
   inj₁ (ih u∈v)
↦∈→⊆dom {u ⊔ u′} fg (inj₂ v↦w∈u′) u∈v =
   let ih = ↦∈→⊆dom (λ z → fg (inj₂ z)) v↦w∈u′ in
   inj₂ (ih u∈v)


⊆↦→cod⊆ : ∀{u v w : Value}
        → u ⊆ v ↦ w
          ---------
        → cod u ⊆ w
⊆↦→cod⊆ {⊥} s refl with s {⊥} refl
... | ()
⊆↦→cod⊆ {const {B} k} u⊆v↦w
    with u⊆v↦w refl
... | ()
⊆↦→cod⊆ {C ↦ C′} s m with s {C ↦ C′} refl
... | refl = m
⊆↦→cod⊆ {u ⊔ u′} s (inj₁ x) = ⊆↦→cod⊆ (λ {C} z → s (inj₁ z)) x
⊆↦→cod⊆ {u ⊔ u′} s (inj₂ y) = ⊆↦→cod⊆ (λ {C} z → s (inj₂ z)) y


factor : (u : Value) → (u′ : Value) → (v : Value) → (w : Value) → Set
factor u u′ v w = Funs u′ × u′ ⊆ u × dom u′ ⊑ v × w ⊑ cod u′

sub-inv-trans : ∀{u′ u₂ u : Value}
    → Funs u′  →  u′ ⊆ u
    → (∀{v′ w′} → v′ ↦ w′ ∈ u → Σ[ u₃ ∈ Value ] factor u₂ u₃ v′ w′)
      ---------------------------------------------------------------
    → Σ[ u₃ ∈ Value ] factor u₂ u₃ (dom u′) (cod u′)
sub-inv-trans {⊥} {u₂} {u} fu′ u′⊆u IH =
   ⊥-elim (contradiction (fu′ refl) ¬Fun⊥)
sub-inv-trans {const {B} k} fu′ u′⊆u IH = ⊥-elim (not-Fun-k (fu′ refl))
sub-inv-trans {u₁′ ↦ u₂′} {u₂} {u} fg u′⊆u IH = IH (↦⊆→∈ u′⊆u)
sub-inv-trans {u₁′ ⊔ u₂′} {u₂} {u} fg u′⊆u IH
    with ⊔⊆-inv u′⊆u
... | ⟨ u₁′⊆u , u₂′⊆u ⟩
    with sub-inv-trans {u₁′} {u₂} {u} (λ {v′} z → fg (inj₁ z)) u₁′⊆u IH
       | sub-inv-trans {u₂′} {u₂} {u} (λ {v′} z → fg (inj₂ z)) u₂′⊆u IH
... | ⟨ u₃₁ , ⟨ fu21' , ⟨ u₃₁⊆u₂ , ⟨ du₃₁⊑du₁′ , cu₁′⊑cu₃₁ ⟩ ⟩ ⟩ ⟩
    | ⟨ u₃₂ , ⟨ fu22' , ⟨ u₃₂⊆u₂ , ⟨ du₃₂⊑du₂′ , cu₁′⊑cu₃₂ ⟩ ⟩ ⟩ ⟩ =
      ⟨ (u₃₁ ⊔ u₃₂) , ⟨ fu₂′ , ⟨ u₂′⊆u₂ ,
      ⟨ ⊔⊑⊔ du₃₁⊑du₁′ du₃₂⊑du₂′ ,
        ⊔⊑⊔ cu₁′⊑cu₃₁ cu₁′⊑cu₃₂ ⟩ ⟩ ⟩ ⟩
    where fu₂′ : {v′ : Value} → v′ ∈ u₃₁ ⊎ v′ ∈ u₃₂ → Fun v′
          fu₂′ {v′} (inj₁ x) = fu21' x
          fu₂′ {v′} (inj₂ y) = fu22' y
          u₂′⊆u₂ : {C : Value} → C ∈ u₃₁ ⊎ C ∈ u₃₂ → C ∈ u₂
          u₂′⊆u₂ {C} (inj₁ x) = u₃₁⊆u₂ x
          u₂′⊆u₂ {C} (inj₂ y) = u₃₂⊆u₂ y


sub-inv : ∀{u₁ u₂ : Value}
        → u₁ ⊑ u₂
        → ∀{v w} → v ↦ w ∈ u₁
          -------------------------------------
        → Σ[ u₃ ∈ Value ] factor u₂ u₃ v w
sub-inv {⊥} {u₂} ⊑-⊥ {v} {w} ()
sub-inv {const {B} k} ⊑-const {v} {w} ()
sub-inv {u₁₁ ⊔ u₁₂} {u₂} (⊑-conj-L lt1 lt2) {v} {w} (inj₁ x) = sub-inv lt1 x
sub-inv {u₁₁ ⊔ u₁₂} {u₂} (⊑-conj-L lt1 lt2) {v} {w} (inj₂ y) = sub-inv lt2 y
sub-inv {u₁} {u₂₁ ⊔ u₂₂} (⊑-conj-R1 lt) {v} {w} m
    with sub-inv lt m  
... | ⟨ u₃₁ , ⟨ fu₃₁ , ⟨ u₃₁⊆u₂₁ , ⟨ domu₃₁⊑v , w⊑codu₃₁ ⟩ ⟩ ⟩ ⟩ =
      ⟨ u₃₁ , ⟨ fu₃₁ , ⟨ (λ {w} z → inj₁ (u₃₁⊆u₂₁ z)) ,
                                   ⟨ domu₃₁⊑v , w⊑codu₃₁ ⟩ ⟩ ⟩ ⟩
sub-inv {u₁} {u₂₁ ⊔ u₂₂} (⊑-conj-R2 lt) {v} {w} m
    with sub-inv lt m  
... | ⟨ u₃₂ , ⟨ fu₃₂ , ⟨ u₃₂⊆u₂₂ , ⟨ domu₃₂⊑v , w⊑codu₃₂ ⟩ ⟩ ⟩ ⟩ =
      ⟨ u₃₂ , ⟨ fu₃₂ , ⟨ (λ {C} z → inj₂ (u₃₂⊆u₂₂ z)) ,
                                   ⟨ domu₃₂⊑v , w⊑codu₃₂ ⟩ ⟩ ⟩ ⟩
sub-inv {u₁} {u₂} (⊑-trans{v = u} u₁⊑u u⊑u₂) {v} {w} v↦w∈u₁
    with sub-inv u₁⊑u v↦w∈u₁
... | ⟨ u′ , ⟨ fu′ , ⟨ u′⊆u , ⟨ domu′⊑v , w⊑codu′ ⟩ ⟩ ⟩ ⟩ 
    with sub-inv-trans {u′} fu′ u′⊆u (sub-inv u⊑u₂) 
... | ⟨ u₃ , ⟨ fu₃ , ⟨ u₃⊆u₂ , ⟨ domu₃⊑domu′ , codu′⊑codu₃ ⟩ ⟩ ⟩ ⟩ =
      ⟨ u₃ , ⟨ fu₃ , ⟨ u₃⊆u₂ , ⟨ ⊑-trans domu₃⊑domu′ domu′⊑v ,
                                    ⊑-trans w⊑codu′ codu′⊑codu₃ ⟩ ⟩ ⟩ ⟩
sub-inv {u₁₁ ↦ u₁₂} {u₂₁ ↦ u₂₂} (⊑-fun lt1 lt2) refl =
    ⟨ u₂₁ ↦ u₂₂ , ⟨ (λ {w} → fun) , ⟨ (λ {C} z → z) , ⟨ lt1 , lt2 ⟩ ⟩ ⟩ ⟩
sub-inv {u₂₁ ↦ (u₂₂ ⊔ u₂₃)} {u₂₁ ↦ u₂₂ ⊔ u₂₁ ↦ u₂₃} ⊑-dist
    {.u₂₁} {.(u₂₂ ⊔ u₂₃)} refl =
    ⟨ u₂₁ ↦ u₂₂ ⊔ u₂₁ ↦ u₂₃ , ⟨ f , ⟨ g ,
    ⟨ ⊑-conj-L ⊑-refl ⊑-refl , ⊑-refl ⟩ ⟩ ⟩ ⟩
  where f : Funs (u₂₁ ↦ u₂₂ ⊔ u₂₁ ↦ u₂₃)
        f (inj₁ x) = fun x
        f (inj₂ y) = fun y
        g : (u₂₁ ↦ u₂₂ ⊔ u₂₁ ↦ u₂₃) ⊆ (u₂₁ ↦ u₂₂ ⊔ u₂₁ ↦ u₂₃)
        g (inj₁ x) = inj₁ x
        g (inj₂ y) = inj₂ y

sub-inv-fun : ∀{v w u₁ : Value}
    → (v ↦ w) ⊑ u₁
      -----------------------------------------------------
    → Σ[ u₂ ∈ Value ] Funs u₂ × u₂ ⊆ u₁
        × (∀{v′ w′} → (v′ ↦ w′) ∈ u₂ → v′ ⊑ v) × w ⊑ cod u₂
sub-inv-fun{v}{w}{u₁} abc
    with sub-inv abc {v}{w} refl
... | ⟨ u₂ , ⟨ f , ⟨ u₂⊆u₁ , ⟨ db , cc ⟩ ⟩ ⟩ ⟩ =
      ⟨ u₂ , ⟨ f , ⟨ u₂⊆u₁ , ⟨ G , cc ⟩ ⟩ ⟩ ⟩
   where G : ∀{D E} → (D ↦ E) ∈ u₂ → D ⊑ v
         G{D}{E} m = ⊑-trans (⊆→⊑ (↦∈→⊆dom f m)) db


↦⊑↦-inv : ∀{v w v′ w′}
        → v ↦ w ⊑ v′ ↦ w′
          -----------------
        → v′ ⊑ v × w ⊑ w′
↦⊑↦-inv{v}{w}{v′}{w′} lt
    with sub-inv-fun lt  
... | ⟨ Γ , ⟨ f , ⟨ Γ⊆v34 , ⟨ lt1 , lt2 ⟩ ⟩ ⟩ ⟩
    with Funs∈ f
... | ⟨ u , ⟨ u′ , u↦u′∈Γ ⟩ ⟩
    with Γ⊆v34 u↦u′∈Γ
... | refl =    
  let codΓ⊆w′ = ⊆↦→cod⊆ Γ⊆v34 in
  ⟨ lt1 u↦u′∈Γ , ⊑-trans lt2 (⊆→⊑ codΓ⊆w′) ⟩


AboveFun : Value → Set
AboveFun u = Σ[ v ∈ Value ] Σ[ w ∈ Value ] v ↦ w ⊑ u

AboveFun-⊑ : ∀{u u' : Value}
      → AboveFun u → u ⊑ u'
        -------------------
      → AboveFun u'
AboveFun-⊑ ⟨ v , ⟨ w , lt' ⟩ ⟩ lt = ⟨ v , ⟨ w , ⊑-trans lt' lt ⟩ ⟩

AboveFun⊥ : ¬ AboveFun ⊥
AboveFun⊥ ⟨ v , ⟨ w , lt ⟩ ⟩
    with sub-inv-fun lt
... | ⟨ Γ , ⟨ f , ⟨ Γ⊆⊥ , ⟨ lt1 , lt2 ⟩ ⟩ ⟩ ⟩
    with Funs∈ f
... | ⟨ A , ⟨ B , m ⟩ ⟩
    with Γ⊆⊥ m
... | ()

AboveFun-⊔ : ∀{u u'}
           → AboveFun (u ⊔ u')
           → AboveFun u ⊎ AboveFun u'
AboveFun-⊔{u}{u'} ⟨ v , ⟨ w , v↦w⊑u⊔u' ⟩ ⟩ 
    with sub-inv-fun v↦w⊑u⊔u'
... | ⟨ Γ , ⟨ f , ⟨ Γ⊆u⊔u' , ⟨ lt1 , lt2 ⟩ ⟩ ⟩ ⟩
    with Funs∈ f
... | ⟨ A , ⟨ B , m ⟩ ⟩
    with Γ⊆u⊔u' m
... | inj₁ x = inj₁ ⟨ A , ⟨ B , (∈→⊑ x) ⟩ ⟩
... | inj₂ x = inj₂ ⟨ A , ⟨ B , (∈→⊑ x) ⟩ ⟩

not-AboveFun-⊔ : ∀{u u' : Value}
               → ¬ AboveFun u → ¬ AboveFun u'
               → ¬ AboveFun (u ⊔ u')
not-AboveFun-⊔ naf1 naf2 af12
    with AboveFun-⊔ af12
... | inj₁ af1 = contradiction af1 naf1
... | inj₂ af2 = contradiction af2 naf2

not-AboveFun-⊔-inv : ∀{u u' : Value} → ¬ AboveFun (u ⊔ u')
              → ¬ AboveFun u × ¬ AboveFun u'
not-AboveFun-⊔-inv af = ⟨ f af , g af ⟩
  where
    f : ∀{u u' : Value} → ¬ AboveFun (u ⊔ u') → ¬ AboveFun u
    f{u}{u'} af12 ⟨ v , ⟨ w , lt ⟩ ⟩ =
        contradiction ⟨ v , ⟨ w , ⊑-conj-R1 lt ⟩ ⟩ af12
    g : ∀{u u' : Value} → ¬ AboveFun (u ⊔ u') → ¬ AboveFun u'
    g{u}{u'} af12 ⟨ v , ⟨ w , lt ⟩ ⟩ =
        contradiction ⟨ v , ⟨ w , ⊑-conj-R2 lt ⟩ ⟩ af12

AboveFun? : (v : Value) → Dec (AboveFun v)
AboveFun? ⊥ = no AboveFun⊥
AboveFun? (const {B} k) = no G
  where
  G : ¬ AboveFun (const k)
  G ⟨ v , ⟨ w , v↦w⊑k ⟩ ⟩ = ⊥-elim (⊑k→BelowConstk v↦w⊑k)
AboveFun? (v ↦ w) = yes ⟨ v , ⟨ w , ⊑-refl ⟩ ⟩
AboveFun? (u ⊔ u')
    with AboveFun? u | AboveFun? u'
... | yes ⟨ v , ⟨ w , lt ⟩ ⟩ | _ = yes ⟨ v , ⟨ w , (⊑-conj-R1 lt) ⟩ ⟩
... | no _ | yes ⟨ v , ⟨ w , lt ⟩ ⟩ = yes ⟨ v , ⟨ w , (⊑-conj-R2 lt) ⟩ ⟩
... | no x | no y = no (not-AboveFun-⊔ x y)


{------------------------------
  Consistency
 -------------------------------}

infix 4 _~_

_~_ : Value → Value → Set
⊥ ~ v = ⊤
const {B} k ~ ⊥ = ⊤
const {B} k ~ const {B′} k′
    with base-eq? B B′
... | yes eq rewrite eq = k ≡ k′ 
... | no neq = Bot
const {B} k ~ v ↦ w = Bot
const {B} k ~ u ⊔ v = const {B} k ~ u × const {B} k ~ v
v ↦ w ~ ⊥ = ⊤
v ↦ w ~ const k = Bot
v ↦ w ~ v′ ↦ w′ = (v ~ v′ × w ~ w′) ⊎ ¬ (v ~ v′)
v ↦ w ~ (u₁ ⊔ u₂) = v ↦ w ~ u₁ × v ↦ w ~ u₂
v₁ ⊔ v₂ ~ u = v₁ ~ u × v₂ ~ u


~⊔R : ∀{v u₁ u₂} → v ~ u₁ → v ~ u₂ 
    → v ~ u₁ ⊔ u₂
~⊔R {⊥} v~u₁ v~u₂ = tt
~⊔R {const k} v~u₁ v~u₂ = ⟨ v~u₁ , v~u₂ ⟩
~⊔R {v ↦ w} v~u₁ v~u₂ = ⟨ v~u₁ , v~u₂ ⟩
~⊔R {v₁ ⊔ v₂} v~u₁ v~u₂ =
    ⟨ (~⊔R {v = v₁} (proj₁ v~u₁) (proj₁ v~u₂)) ,
      (~⊔R {v = v₂} (proj₂ v~u₁) (proj₂ v~u₂)) ⟩


data wf : Value → Set where
  wf-bot : wf ⊥
  wf-const : ∀{B}{k : base-rep B} → wf (const {B} k)
  wf-fun : ∀{v w} → wf v → wf w → wf (v ↦ w)
  wf-⊔ : ∀{u v} → u ~ v → wf u → wf v → wf (u ⊔ v)


~-sym : ∀{u v} → u ~ v → v ~ u
~-sym {⊥} {⊥} u~v = tt
~-sym {⊥} {const k} u~v = tt
~-sym {⊥} {v ↦ w} u~v = tt
~-sym {⊥} {v₁ ⊔ v₂} u~v = ⟨ ~-sym {v = v₁} tt , ~-sym {v = v₂} tt ⟩
~-sym {const k} {⊥} u~v = tt
~-sym {const {B} k} {const {B′} k′} u~v
    with base-eq? B B′
... | no neq = ⊥-elim u~v
... | yes eq
    rewrite eq
    with base-eq? B′ B′
... | no neq = neq refl
... | yes refl = sym u~v
~-sym {const k} {v ↦ w} ()
~-sym {const k} {u ⊔ v} ⟨ k~u , k~v ⟩ =
  ⟨ (~-sym{v = u} k~u) , (~-sym{v = v} k~v) ⟩
~-sym {v ↦ w} {⊥} u~v = tt
~-sym {v ↦ w} {const k} ()
~-sym {v ↦ w} {v′ ↦ w′} (inj₁ ⟨ fst , snd ⟩) =
   inj₁ ⟨ (~-sym{v = v′} fst) , (~-sym{v = w′} snd) ⟩
~-sym {v ↦ w} {v′ ↦ w′} (inj₂ ¬v~v′) =
   inj₂ λ x → ⊥-elim (contradiction (~-sym{u = v′} x) ¬v~v′)
~-sym {v ↦ w} {u₁ ⊔ u₂} ⟨ fst , snd ⟩ =
   ⟨ ~-sym{v = u₁} fst , ~-sym{v = u₂} snd ⟩
~-sym {u₁ ⊔ u₂} {⊥} ⟨ fst , snd ⟩ = tt
~-sym {u₁ ⊔ u₂} {const k} ⟨ fst , snd ⟩ =
   ⟨ ~-sym{u = u₁} fst , ~-sym{u = u₂} snd ⟩
~-sym {u₁ ⊔ u₂} {v ↦ v₁} ⟨ fst , snd ⟩ =
   ⟨ ~-sym{u = u₁} fst , ~-sym{u = u₂} snd ⟩
~-sym {u₁ ⊔ u₂} {v₁ ⊔ v₂} ⟨ fst , snd ⟩ 
    with ~-sym {u₁} {v₁ ⊔ v₂} fst
       | ~-sym {u₂} {v₁ ⊔ v₂} snd
... | ⟨ v₁~u₁ , v₂~u₁ ⟩ | ⟨ v₁~u₂ , v₂~u₂ ⟩ =
      ⟨ ~⊔R{v = v₁} v₁~u₁ v₁~u₂ , ~⊔R{v = v₂} v₂~u₁ v₂~u₂ ⟩

~-refl : ∀{v} → wf v → v ~ v
~-refl {.⊥} wf-bot = tt
~-refl {const {B} k} wf-const
    with base-eq? B B
... | yes eq rewrite eq = refl
... | no neq = neq refl
~-refl {.(_ ↦ _)} (wf-fun wfv wfv₁) = inj₁ ⟨ ~-refl wfv , ~-refl wfv₁ ⟩
~-refl {v₁ ⊔ v₂} (wf-⊔ v₁~v₂ wfv₁ wfv₂) =
    ⟨ ~⊔R{v₁} (~-refl{v₁} wfv₁) v₁~v₂ ,
      ~⊔R{v₂} (~-sym{v₁} v₁~v₂) (~-refl wfv₂) ⟩


consistent→atoms : ∀ {u v u′ v′} → u ~ v → u′ ∈ u → v′ ∈ v → u′ ~ v′
consistent→atoms {⊥} {v} {u′} {v′} u~v u′∈u v′∈v rewrite u′∈u = tt
consistent→atoms {const {B} k} {⊥} {u′} {v′} u~v u′∈u v′∈v
    rewrite u′∈u | v′∈v = tt
consistent→atoms {const {B} k} {const {B′} k′} {u′} {v′} u~v u′∈u v′∈v
    rewrite u′∈u | v′∈v
    with base-eq? B B′
... | yes refl = u~v
... | no neq = u~v
consistent→atoms {const {B} k} {v ↦ w} {u′} {v′} () u′∈u v′∈v
consistent→atoms {const {B} k} {v₁ ⊔ v₂} {u′} {v′} ⟨ fst , snd ⟩ u′∈u
    (inj₁ v′∈v₁) rewrite u′∈u = consistent→atoms{const {B} k} fst refl v′∈v₁
consistent→atoms {const {B} k} {v₁ ⊔ v₂} {u′} {v′} ⟨ fst , snd ⟩ u′∈u
    (inj₂ v′∈v₂) rewrite u′∈u =  consistent→atoms{const {B} k} snd refl v′∈v₂
consistent→atoms {u ↦ w} {⊥} {u′} {v′} u~v u′∈u v′∈v rewrite u′∈u | v′∈v = tt
consistent→atoms {u ↦ w} {const x} {u′} {v′} () u′∈u v′∈v
consistent→atoms {u ↦ w} {v₁ ↦ v₂} {u′} {v′} (inj₁ ⟨ fst , snd ⟩) u′∈u v′∈v
    rewrite u′∈u | v′∈v = inj₁ ⟨ fst , snd ⟩
consistent→atoms {u ↦ w} {v₁ ↦ v₂} {u′} {v′} (inj₂ y) u′∈u v′∈v
    rewrite u′∈u | v′∈v = inj₂ y
consistent→atoms {u ↦ w} {v₁ ⊔ v₂} {u′} {v′} ⟨ fst , snd ⟩ u′∈u (inj₁ x)
    rewrite u′∈u = consistent→atoms {u ↦ w}{v₁} fst refl x
consistent→atoms {u ↦ w} {v₁ ⊔ v₂} {u′} {v′} ⟨ fst , snd ⟩ u′∈u (inj₂ y)
    rewrite u′∈u = consistent→atoms {u ↦ w}{v₂} snd refl y
consistent→atoms {u₁ ⊔ u₂} {v} {u′} {v′} ⟨ u₁~v , u₂~v ⟩ (inj₁ u′∈u₁) v′∈v =
    consistent→atoms u₁~v u′∈u₁ v′∈v
consistent→atoms {u₁ ⊔ u₂} {v} {u′} {v′} ⟨ u₁~v , u₂~v ⟩ (inj₂ u′∈u₂) v′∈v =
    consistent→atoms u₂~v u′∈u₂ v′∈v

atoms→consistent : ∀{u v}
                 → (∀{u′ v′} → u′ ∈ u → v′ ∈ v → u′ ~ v′)
                 → u ~ v
atoms→consistent {⊥} {v} atoms = tt
atoms→consistent {const k} {⊥} atoms = tt
atoms→consistent {const k} {const k′} atoms =
    atoms {const k} {const k′} refl refl
atoms→consistent {const k} {v ↦ w} atoms =
    ⊥-elim (atoms {const k} {v ↦ w} refl refl)
atoms→consistent {const k} {v₁ ⊔ v₂} atoms =
    ⟨ atoms→consistent{const k}{v₁} (λ {u′} {v′} z z₁ → atoms z (inj₁ z₁)) ,
      atoms→consistent{const k}{v₂} (λ {u′} {v′} z z₁ → atoms z (inj₂ z₁)) ⟩
atoms→consistent {u ↦ w} {⊥} atoms = tt
atoms→consistent {u ↦ w} {const k} atoms =
    ⊥-elim (atoms {u ↦ w}{const k} refl refl)
atoms→consistent {u ↦ w} {v₁ ↦ v₂} atoms =
    atoms {u ↦ w} {v₁ ↦ v₂ } refl refl
atoms→consistent {u ↦ w} {v₁ ⊔ v₂} atoms =
    ⟨ atoms→consistent{u ↦ w}{v₁}(λ {u′}{v′} z z₁ → atoms z (inj₁ z₁)) ,
      atoms→consistent{u ↦ w}{v₂} (λ {u′} {v′} z z₁ → atoms z (inj₂ z₁)) ⟩
atoms→consistent {u₁ ⊔ u₂} {v} atoms =
    ⟨ atoms→consistent (λ {u′} {v′} z → atoms (inj₁ z)) ,
      atoms→consistent (λ {u′} {v′} z → atoms (inj₂ z)) ⟩


BelowFun : Value → Set
BelowFun ⊥ = ⊤
BelowFun (const {B} k) = Bot
BelowFun (v ↦ w) = ⊤
BelowFun (u ⊔ v) = BelowFun u × BelowFun v

Below⊥→BelowFun : ∀{v : Value}
   → Below⊥ v
   → BelowFun v
Below⊥→BelowFun {⊥} b⊥v = tt
Below⊥→BelowFun {const {B′} k′} ()
Below⊥→BelowFun {v ↦ w} ()
Below⊥→BelowFun {v₁ ⊔ v₂} ⟨ fst , snd ⟩ =
  ⟨ Below⊥→BelowFun fst , Below⊥→BelowFun snd ⟩


BelowFun-⊑ : ∀{u v} → BelowFun v → u ⊑ v → BelowFun u
BelowFun-⊑ {.⊥} {v} bv ⊑-⊥ = tt
BelowFun-⊑ {.(const _)} {.(const _)} () ⊑-const
BelowFun-⊑ {.(_ ⊔ _)} {v} bv (⊑-conj-L u⊑v u⊑v₁) =
    ⟨ BelowFun-⊑ bv u⊑v , BelowFun-⊑ bv u⊑v₁ ⟩
BelowFun-⊑ {u} {.(_ ⊔ _)} bv (⊑-conj-R1 u⊑v) =
    BelowFun-⊑ (proj₁ bv) u⊑v
BelowFun-⊑ {u} {.(_ ⊔ _)} bv (⊑-conj-R2 u⊑v) =
    BelowFun-⊑ (proj₂ bv) u⊑v
BelowFun-⊑ {u} {v} bv (⊑-trans u⊑v u⊑v₁) =
    BelowFun-⊑ (BelowFun-⊑ bv u⊑v₁) u⊑v
BelowFun-⊑ {.(_ ↦ _)} {.(_ ↦ _)} bv (⊑-fun u⊑v u⊑v₁) = tt
BelowFun-⊑ {.(_ ↦ (_ ⊔ _))} {.(_ ↦ _ ⊔ _ ↦ _)} bv ⊑-dist = tt

⊑↦→BelowFun : ∀{u v w} → u ⊑ v ↦ w → BelowFun u
⊑↦→BelowFun {.⊥} {v} {w} ⊑-⊥ = tt
⊑↦→BelowFun {.(_ ⊔ _)} {v} {w} (⊑-conj-L u⊑v↦w u⊑v↦w₁) =
    ⟨ ⊑↦→BelowFun u⊑v↦w , ⊑↦→BelowFun u⊑v↦w₁ ⟩
⊑↦→BelowFun {u} {v} {w} (⊑-trans u⊑v↦w u⊑v↦w₁) =
  let ih = ⊑↦→BelowFun u⊑v↦w₁ in
  BelowFun-⊑ ih u⊑v↦w
⊑↦→BelowFun {.(_ ↦ _)} {v} {w} (⊑-fun u⊑v↦w u⊑v↦w₁) = tt


{-
below-fun-funs : ∀{u v}
    → Funs v
    → u ⊑ v
    → Funs u ⊎ u ⊑ ⊥
below-fun-funs {u} {⊥} fv u⊑v = inj₂ u⊑v
below-fun-funs {u} {const k} fv u⊑v
    with fv {const k} refl
... | fun ()   
below-fun-funs {⊥} {v ↦ w} fv u⊑v = inj₂ ⊑-⊥
below-fun-funs {const k} {v ↦ w} fv u⊑v = {!!}
below-fun-funs {u ↦ u₁} {v ↦ w} fv u⊑v = inj₁ λ {u₂} → fun
below-fun-funs {u₁ ⊔ u₂} {v ↦ w} fv u⊑v = {!!}
below-fun-funs {u} {v₁ ⊔ v₂} fv u⊑v = {!!}

-}




k⊑A→k∈A : ∀{B}{k : base-rep B}{A : Value}
        → const k ⊑ A
        → const k ∈ A
k⊑A→k∈A {B} {k} {⊥} k⊑A =
    ⊥-elim (v⊑⊥→Below⊥ k⊑A)
k⊑A→k∈A {B} {k} {const {B′} k′} k⊑A
    with base-eq? B′ B | ⊑k→BelowConstk k⊑A
... | yes eq1 | eq2 rewrite eq1 | eq2 = refl
... | no neq | ()
k⊑A→k∈A {B} {k} {A₁ ↦ A₂} k⊑A 
    with ⊑↦→BelowFun k⊑A
... | ()  
k⊑A→k∈A {B} {k} {A₁ ⊔ A₂} k⊑A = {!!}





consistent-⊑ : ∀{A B C D}
    → A ~ B  →  C ⊑ A  → D ⊑ B
    → C ~ D
consistent-⊑ {A}{B}{C}{D} A~B C⊑A D⊑B = atoms→consistent {C}{D} G
    where
    G : ∀ {C′ D′} → C′ ∈ C → D′ ∈ D → C′ ~ D′
    G {⊥} {D′} C′∈C D′∈D = tt
    G {const k} {D′} C′∈C D′∈D =
       let k⊑A : const k ⊑ A
           k⊑A = ⊑-trans (∈→⊑ C′∈C) C⊑A  in
       let k∈A : const k ∈ A
           k∈A = {!!} in
       {!!}
    G {C′ ↦ C₂} {D′} C′∈C D′∈D = {!!}
    G {C′ ⊔ C₂} {D′} C′∈C D′∈D = ⊥-elim (not-u₁⊔u₂∈v C′∈C)

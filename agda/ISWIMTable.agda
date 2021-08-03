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
open import Data.Empty.Irrelevant renaming (⊥-elim to ⊥-elimi)
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

_≈_ : Table → Table → Set
t₁ ≈ t₂ = (∀ {v₁ w₁ v₂ w₂}
         → v₁ ↦ w₁ ∈ mem t₁  →  v₂ ↦ w₂ ∈ mem t₂
         → (v₁ ~ v₂ × w₁ ~ w₂) ⊎ v₁ ~̸ v₂)

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

~-relevant : ∀{u v} → .(c : u ~ v) → u ~ v
~-relevant {u}{v} c
    with ~-decidable u v
... | yes u~v = u~v
... | no ¬u~v = ⊥-elimi (¬u~v c)

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
⟦⟧-monotone {$ p k} ρ<ρ′ v v∈℘k = v∈℘k

℘-consistent : ∀{P}{k}
  → consistent (℘ {P} k)
℘-consistent {base B} {k} {const {B1} k1} {const {B2} k2} u∈ v∈
  with base-eq? B B1
... | no xx = ⊥-elim u∈
... | yes refl
    with base-eq? B B2
... | no xx = ⊥-elim v∈
... | yes refl rewrite u∈ | v∈ = ~const
℘-consistent {B ⇒ P} {k} {fun t₁}{fun t₂} u∈ v∈ = ~fun G
  where
  G : {v₁ w₁ v₂ w₂ : Value} →
      v₁ ↦ w₁ ∈ mem t₁ →
      v₂ ↦ w₂ ∈ mem t₂ → (v₁ ~ v₂) × (w₁ ~ w₂) ⊎ (v₁ ~̸ v₂)
  G {v₁}{w₁}{v₂}{w₂} vw₁∈t₁ vw₂∈t₂
      with u∈ v₁ w₁ vw₁∈t₁
  ... | ⟨ k1 , ⟨ refl , p1 ⟩ ⟩
      with v∈ v₂ w₂ vw₂∈t₂
  ... | ⟨ k2 , ⟨ refl , p2 ⟩ ⟩
      with ~-decidable v₁ v₂ 
  ... | no ¬v₁~v₂ = inj₂ (¬~⇒~̸ ¬v₁~v₂)
  ... | yes ~const =
      inj₁ ⟨ ~const , ℘-consistent {P} p1 p2 ⟩

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
⟦⟧-consistent {$ P k}{ρ} ρ~ = ℘-consistent {P}{k}

join : (u : Value) → (v : Value) → .(c : u ~ v) → Value

inner-cross : (t₂ : Table) (v₁ w₁ : Value) 
  → (∀ {v₂ w₂} → v₂ ↦ w₂ ∈ mem t₂ → (v₁ ~ v₂ × w₁ ~ w₂) ⊎ v₁ ~̸ v₂)
  → Table
inner-cross [] v₁ w₁ c = []
inner-cross (⟨ v₂ , w₂ ⟩ ∷ t₂) v₁ w₁ c 
    with ~-decidable v₁ v₂
... | no ¬v1~̸v2 = inner-cross t₂ v₁ w₁ λ z → c (mem-there z) 
... | yes v1~v2
    with c mem-here
... | inj₁ ⟨ _ , w1~w2 ⟩ =
    ⟨ join v₁ v₂ v1~v2 , join w₁ w₂ w1~w2 ⟩
    ∷ inner-cross t₂ v₁ w₁ λ z → c (mem-there z) 
... | inj₂ v₁~̸v₂ = ⊥-elim (~̸⇒¬~ v₁~̸v₂ v1~v2)

cross : (t₁ t₂ : Table) (c : t₁ ≈ t₂) → Table
cross [] t₂ c = []
cross (⟨ v₁ , w₁ ⟩ ∷ t₁) t₂ c =
  (inner-cross t₂ v₁ w₁ (c mem-here)) ++ (cross t₁ t₂ λ z → c (mem-there z))

join (const {B} k) (const {B′} k′) c
    with base-eq? B B′
... | yes refl
    with base-rep-eq? k k′
... | yes refl = const k
... | no neq = ⊥-elimi (G c neq)
    where
    G : const {B} k ~ const {B′} k′ → ¬ k ≡ k′ → False
    G ~const ne = ne refl
join (const {B} k) (const {B′} k′) c | no neq = ⊥-elimi (G c neq)
    where
    G : const {B} k ~ const {B′} k′ → ¬ B ≡ B′ → False
    G ~const ne = ne refl
join (fun t₁) (fun t₂) c = fun (t₁ ++ t₂ ++ cross t₁ t₂ {!!})

{-
mem++ : ∀{T : Set} (t₁ t₂ : List T) → mem (t₁ ++ t₂) ≃ mem t1 ∪ mem t2
-}

mem++-left : ∀{T : Set} (t₁ t₂ : List T) → mem t₁ ⊆ mem (t₁ ++ t₂)
mem++-left {T} [] t₂ = λ d ()
mem++-left {T} (x ∷ t₁) t₂ .x mem-here = mem-here
mem++-left {T} (x ∷ t₁) t₂ d (mem-there y) = mem-there (mem++-left t₁ t₂ d y)

mem++-right : ∀{T : Set} (t₁ t₂ : List T) → mem t₂ ⊆ mem (t₁ ++ t₂)
mem++-right {T} [] t₂ = λ d z → z
mem++-right {T} (x ∷ t₁) t₂ d x₁ = mem-there (mem++-right t₁ t₂ d x₁)

{-

⊑-join-left : ∀{w1 w2}{c} → w1 ⊑ join w1 w2 c
⊑-join-left {.(const _)} {.(const _)} {~const} = ⊑-const
⊑-join-left {(fun t₁)} {(fun t₂)} {~fun t₁~t₂} =
  ⊑-fun (mem++-left t₁ (t₂ ++ cross t₁ t₂ t₁~t₂))

⊑-join-right : ∀{w1 w2}{c} → w2 ⊑ join w1 w2 c
⊑-join-right {.(const _)} {.(const _)} {~const} = ⊑-const
⊑-join-right {(fun t₁)} {(fun t₂)} {~fun t₁~t₂} =
  let xx = (mem++-right t₁ (t₂ ++ cross t₁ t₂ t₁~t₂))  in
  let yy = (mem++-left t₂ (cross t₁ t₂ t₁~t₂)) in
  ⊑-fun (⊆-trans yy xx)

mem-inner-cross : ∀{t₂ : Table}{v₁ w₁ v₂ w₂ : Value}
  → v₂ ↦ w₂ ∈ mem t₂
  → (v₁~v₂ : v₁ ~ v₂) → (w₁~w₂ : w₁ ~ w₂)
  → (c : (∀ {v₂ w₂} → v₂ ↦ w₂ ∈ mem t₂ → (v₁ ~ v₂ × w₁ ~ w₂) ⊎ v₁ ~̸ v₂))
  → mem (inner-cross t₂ v₁ w₁ c) ⟨ join v₁ v₂ v₁~v₂ , join w₁ w₂ w₁~w₂ ⟩
mem-inner-cross {⟨ v₂ , w₂ ⟩ ∷ t₂}{v₁}{w₁}{v₂}{w₂} mem-here v₁~v₂ w₁~w₂ c
    with ~-decidable v₁ v₂
... | no ¬v₁~v₂ = ⊥-elim (¬v₁~v₂ v₁~v₂)
... | yes _
    with c mem-here
... | inj₁ ⟨ _ , _ ⟩ = {!!}
... | inj₂ v₁~̸v₂ = ⊥-elim (~̸⇒¬~ v₁~̸v₂ v₁~v₂)
mem-inner-cross {x ∷ t₂} (mem-there v₂↦w₂∈t₂) v₁~v₂ w₁~w₂ c = {!!}

mem-cross-join : ∀{v₁ v₂ w₁ w₂ t₁ t₂}
  → (v₁~v₂ : v₁ ~ v₂) → (w₁~w₂ : w₁ ~ w₂) → (t₁≈t₂ : t₁ ≈ t₂)
  → v₁ ↦ w₁ ∈ mem t₁ → v₂ ↦ w₂ ∈ mem t₂
  → mem (cross t₁ t₂ t₁≈t₂) ⟨ join v₁ v₂ v₁~v₂ , join w₁ w₂ w₁~w₂ ⟩
mem-cross-join {t₁ = (⟨ v₁ , w₁ ⟩) ∷ t₁} v₁~v₂ w₁~w₂ t₁≈t₂ mem-here vw₂∈t₂ = {!!}
mem-cross-join {t₁ = x ∷ t₁} v₁~v₂ w₁~w₂ t₁≈t₂ (mem-there vw₁∈t₁) vw₂∈t₂ = {!!}

joinable : 𝒫 Value → Set
joinable D = ∀ u v → u ∈ D → v ∈ D → (c : u ~ v) → join u v c ∈ D

▪-joinable : ∀{E D : 𝒫 Value}
  → consistent E → consistent D
  → joinable E → joinable D
  → joinable (E ▪ D)
▪-joinable{E}{D} cE cD jE jD w1 w2 ⟨ t1 , ⟨ t1∈E , ⟨ v1 , ⟨ vw1∈ , v1∈D ⟩ ⟩ ⟩ ⟩
                             ⟨ t2 , ⟨ t2∈E , ⟨ v2 , ⟨ vw2∈ , v2∈D ⟩ ⟩ ⟩ ⟩ w1~w2
    with cE t1∈E t2∈E
... | ~fun t1~t2
    with t1~t2 vw1∈ vw2∈ 
... | inj₂ v1~̸v2 = ⊥-elim (~̸⇒¬~ v1~̸v2 (cD v1∈D v2∈D))     
... | inj₁ ⟨ v₁~v₂ , w₁~w₂ ⟩ =
    let t12 = join (fun t1) (fun t2) (~fun t1~t2) in
    let v12 = join v1 v2 v₁~v₂ in
    let t12∈E = jE (fun t1) (fun t2) t1∈E t2∈E (~fun t1~t2) in
    let v12∈D = jD v1 v2 v1∈D v2∈D v₁~v₂ in
    let w12 = join w1 w2 w₁~w₂ in
    ⟨ t1 ++ t2 ++ cross t1 t2 t1~t2 ,
    ⟨ t12∈E , ⟨ v12 , ⟨ {!!} , v12∈D ⟩ ⟩ ⟩ ⟩
{-

    with jD v1 v2 v1∈D v2∈D
... | ⟨ v12 , ⟨ v12∈D , ⟨ v1⊑v12 , v2⊑v12 ⟩ ⟩ ⟩ =
    let w12 = join w1 w2 {w₁~w₂} in
    let w12∈ED : w12 ∈ (E ▪ D)
        w12∈ED = ⟨ t12 , ⟨ t12∈E , ⟨ {!!} , ⟨ {!!} , {!!} ⟩ ⟩ ⟩ ⟩ in
    ⟨ w12 , ⟨ w12∈ED , ⟨ ⊑-join-left , ⊑-join-right ⟩ ⟩ ⟩  
-}

⟦⟧-joinable : ∀ {M : Term}{ρ}
   → (∀ x → consistent (ρ x) )
   → (∀ x → joinable (ρ x) )
   → joinable (⟦ M ⟧ ρ)
⟦⟧-joinable {` x}{ρ} ρ~ ρ⊔ = ρ⊔ x
⟦⟧-joinable {L · M}{ρ} ρ~ ρ⊔ =
  ▪-joinable (⟦⟧-consistent{L} ρ~) (⟦⟧-consistent{M} ρ~)
             (⟦⟧-joinable{L} ρ~ ρ⊔) (⟦⟧-joinable{M} ρ~ ρ⊔)
⟦⟧-joinable {ƛ N}{ρ} ρ⊔ = {!!}
⟦⟧-joinable {$ p k}{ρ} ρ⊔ = {!!}


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


-}

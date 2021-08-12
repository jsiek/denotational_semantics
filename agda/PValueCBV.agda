module PValueCBV where

{-

  This is an adaptation of the call-by-name models P(ω) of Scott
  (1976) and Dₐ of Engeler (1981) to call-by-value.

-}

open import Primitives
open import Utilities using (extensionality)
open import SetsAsPredicates
open import Var
open import Substitution using (_•_)
open import ScopedTuple hiding (𝒫)
open import Syntax using (Sig; ext; ν; ■; Var; _•_; ↑; id; _⨟_) public
open import Sig

open import Data.Empty using (⊥-elim) renaming (⊥ to False)
open import Data.List using (List ; _∷_ ; []; _++_; length; replicate)
open import Data.List.Properties using (++-conicalˡ)
open import Data.List.Membership.Propositional renaming (_∈_ to _⋵_)
open import Data.List.Membership.Propositional.Properties
  using (∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any using (here; there) 
open import Data.Nat using (ℕ; zero; suc; _≟_; _<_; s≤s; _+_)
open import Data.Product using (_×_; Σ; Σ-syntax; proj₁; proj₂)
    renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt) renaming (⊤ to True)
open import Data.Unit.Polymorphic using (⊤) renaming (tt to ptt)
open import Relation.Binary.PropositionalEquality
    using (_≡_; _≢_; refl; sym; subst)
open import Level using (Level; Lift; lift)
    renaming (zero to lzero; suc to lsuc)
open import Relation.Nullary using (¬_; Dec; yes; no)

{- Finite Sets represented by Lists -------------------------------------------}

mem : ∀{T : Set} → List T → T → Set
mem {T} ls x = x ⋵ ls

E≢[]⇒nonempty-mem : ∀{T}{E : List T}
  → E ≢ [] → nonempty (mem E)
E≢[]⇒nonempty-mem {T} {[]} E≢[] = ⊥-elim (E≢[] refl)
E≢[]⇒nonempty-mem {T} {x ∷ E} E≢[] = ⟨ x , here refl ⟩


{- Denotational Values --------------------------------------------------------}

data Value : Set where
  const : {B : Base} → base-rep B → Value  {- A primitive constant of type B. -}
  _↦_ : List Value → Value → Value        {- An entry in a function's graph. -}
  ν : Value      {- A function. Needed for CBV to distinguish from diverging. -}
  ❲_,_❳ : Value → Value → Value
  ⟬_⟭ : List Value → Value 

{- Abstraction and Application ------------------------------------------------}

Λ : (𝒫 Value → 𝒫 Value) → 𝒫 Value
Λ f (const k) = False
Λ f (V ↦ w) = w ∈ f (mem V)  ×  V ≢ []
Λ f ν = True
Λ f ❲ u , v ❳ = False
Λ f ⟬ vs ⟭ = False

infix 10 _▪_
_▪_ : 𝒫 Value → 𝒫 Value → 𝒫 Value
D₁ ▪ D₂ = λ w → Σ[ V ∈ List Value ] (V ↦ w ∈ D₁)  ×  (mem V ⊆ D₂)  ×  V ≢ []

℘ : (P : Prim) → rep P → 𝒫 Value
℘ (base B) k (const {B′} k′)
    with base-eq? B B′
... | yes refl = k ≡ k′
... | no neq = False
℘ (base B) k (V ↦ w) = False
℘ (base B) k ν = False
℘ (base B) k ❲ u , v ❳ = False
℘ (base B) k ⟬ vs ⟭ = False
℘ (B ⇒ P) f (const k) = False
℘ (B ⇒ P) f (V ↦ w) =
   Σ[ k ∈ base-rep B ] V ≡ (const {B} k) ∷ []  ×  w ∈ ℘ P (f k)
℘ (B ⇒ P) f ν = True
℘ (B ⇒ P) k ❲ u , v ❳ = False
℘ (B ⇒ P) k ⟬ vs ⟭ = False

k∈℘k : ∀{B}{k} → const {B} k ∈ ℘ (base B) k
k∈℘k {B}{k}
    with base-eq? B B
... | yes refl = refl
... | no neq = neq refl

k′∈℘k⇒P≡B : ∀{P B}{k}{k′} → const {B} k′ ∈ ℘ P k → P ≡ base B
k′∈℘k⇒P≡B {base B′} {B} {k} {k′} k′∈℘k
    with base-eq? B′ B
... | yes refl = refl
... | no neq = ⊥-elim k′∈℘k

k′∈℘k⇒k′≡k : ∀{B}{k}{k′} → const {B} k′ ∈ ℘ (base B) k → k′ ≡ k
k′∈℘k⇒k′≡k {B}{k}{k′} m
    with base-eq? B B
... | yes refl = sym m
... | no neq = ⊥-elim m

〘_,_〙 : 𝒫 Value → 𝒫 Value → 𝒫 Value
〘 D₁ , D₂ 〙 ❲ u , v ❳ = u ∈ D₁ × v ∈ D₂
〘 D₁ , D₂ 〙 _ = False

car : 𝒫 Value → 𝒫 Value
car D u = Σ[ v ∈ Value ] ❲ u , v ❳ ∈ D

cdr : 𝒫 Value → 𝒫 Value
cdr D v = Σ[ u ∈ Value ] ❲ u , v ❳ ∈ D

∏ : ℕ → Set₁ → Set₁
∏ n T = Tuple (replicate n ■) (Result T)

𝒯 : ∀ n → ∏ n (𝒫 Value) → 𝒫 Value
𝒯 zero _ ⟬ [] ⟭ = True
𝒯 (suc n) ⟨ D , Ds ⟩ ⟬ v ∷ vs ⟭ = v ∈ D  ×  𝒯 n Ds ⟬ vs ⟭
𝒯 n Ds _ = False

v∈𝒯⇒v≡⟬vs⟭ : ∀{n}{Ds}{v}
  → v ∈ 𝒯 n Ds
  → Σ[ vs ∈ List Value ] v ≡ ⟬ vs ⟭
v∈𝒯⇒v≡⟬vs⟭ {zero} {Ds} {⟬ x ⟭} v∈ = ⟨ x , refl ⟩
v∈𝒯⇒v≡⟬vs⟭ {suc n} {Ds} {⟬ x ⟭} v∈ = ⟨ x , refl ⟩

nth : List Value → ℕ → Value
nth [] i = const 0
nth (v ∷ vs) 0 = v
nth (v ∷ vs) (suc i) = nth vs i

proj : 𝒫 Value → ℕ → 𝒫 Value
proj D i u = Σ[ vs ∈ List Value ] ⟬ vs ⟭ ∈ D  ×  u ≡ nth vs i

all-∏ : ∀{n}{T : Set₁}{ℓ : Level} → (T → Set ℓ) → ∏ n T → Set ℓ
all-∏ {zero}{T}{ℓ} P (lift tt) = ⊤
all-∏ {suc n}{T}{ℓ} P ⟨ x , xs ⟩ = P x  ×  all-∏ P xs

rel-∏ : ∀{n}{T : Set₁} → (T → T → Set) → ∏ n T → ∏ n T → Set
rel-∏ {zero} R (lift tt) (lift tt) = True
rel-∏ {suc n} R ⟨ x , xs ⟩ ⟨ y , ys ⟩ = R x y  ×  rel-∏ R xs ys

rel-∏-refl : ∀{n}{T : Set₁}{R : T → T → Set}{Ds : ∏ n T}
   → (∀ {x} → R x x) → rel-∏ R Ds Ds
rel-∏-refl {zero} {T} {R} {Ds} R-refl = tt
rel-∏-refl {suc n} {T} {R} {⟨ D , Ds ⟩} R-refl =
    ⟨ R-refl , (rel-∏-refl R-refl) ⟩

rel-∏-sym : ∀{n}{T : Set₁}{R : T → T → Set}{Ds Es : ∏ n T}
   → (∀ {x y} → R x y → R y x) → rel-∏ R Ds Es → rel-∏ R Es Ds
rel-∏-sym {zero} {T} {R} {lift tt} {lift tt} R-sym tt = tt
rel-∏-sym {suc n} {T} {R} {⟨ D , Ds ⟩} {⟨ E , Es ⟩} R-sym ⟨ RDE , R[Ds,Es] ⟩ =
    ⟨ (R-sym RDE) , (rel-∏-sym R-sym R[Ds,Es]) ⟩

rel-∏-⇒ : ∀{n}{T : Set₁}{xs ys : ∏ n T}{R R′ : T → T → Set}
   → (∀ x y → R x y → R′ x y) → rel-∏ R xs ys → rel-∏ R′ xs ys
rel-∏-⇒ {zero} R⇒R′ tt = tt
rel-∏-⇒ {suc n}{T}{⟨ x , xs ⟩}{⟨ y , ys ⟩} R⇒R′ ⟨ Rxy , R[xs,ys] ⟩ =
    ⟨ R⇒R′ x y Rxy , rel-∏-⇒ R⇒R′ R[xs,ys] ⟩

NE-∏ = λ {n} → all-∏{n}{𝒫 Value} nonempty

NE-∏⇒𝒯 : ∀{n}{Ds : ∏ n (𝒫 Value)}
   → NE-∏ Ds
   → Σ[ vs ∈ List Value ] 𝒯 n Ds ⟬ vs ⟭
NE-∏⇒𝒯 {zero} {ptt} NE-Ds = ⟨ [] , tt ⟩
NE-∏⇒𝒯 {suc n} {⟨ D , Ds ⟩} ⟨ ⟨ v , v∈D ⟩ , NE-Ds ⟩
    with NE-∏⇒𝒯 {n} {Ds} NE-Ds
... | ⟨ vs , vs⊆ ⟩ = ⟨ v ∷ vs , ⟨ v∈D , vs⊆ ⟩ ⟩

NE-∏⇒NE-𝒯 : ∀{n}{Ds : ∏ n (𝒫 Value)}
   → NE-∏ Ds
   → nonempty (𝒯 n Ds)
NE-∏⇒NE-𝒯{n}{Ds} NE-Ds
    with NE-∏⇒𝒯 NE-Ds
... | ⟨ vs , vs∈𝒯Ds ⟩ = ⟨ ⟬ vs ⟭ , vs∈𝒯Ds ⟩

𝒯-nth-0 : ∀{n}{D}{Ds}
   → NE-∏ Ds
   → proj (𝒯 (suc n) ⟨ D , Ds ⟩) 0 ≃ D
𝒯-nth-0 {n}{D}{Ds} NE-Ds = ⟨ G , H ⟩
  where
  G : proj (𝒯 (suc n) ⟨ D , Ds ⟩) 0 ⊆ D
  G .v ⟨ v ∷ vs , ⟨ ⟨ v∈D , ⟬vs⟭∈𝒯Ds ⟩ , refl ⟩ ⟩ = v∈D
  H : D ⊆ proj (𝒯 (suc n) ⟨ D , Ds ⟩) 0
  H v v∈D
      with NE-∏⇒𝒯 NE-Ds
  ... | ⟨ vs , vs⊆ ⟩ = ⟨ (v ∷ vs) , ⟨ ⟨ v∈D , vs⊆ ⟩ , refl ⟩ ⟩

𝒯-nth-suc : ∀{i}{n}{D}{Ds}
   → nonempty D → NE-∏ Ds
   → proj (𝒯 (suc n) ⟨ D , Ds ⟩) (suc i)
   ≃ proj (𝒯 n Ds) i
𝒯-nth-suc {i}{n}{D}{Ds} ⟨ u , u∈D ⟩ NE-Ds = ⟨ G , H ⟩
  where
  G : proj (𝒯 (suc n) ⟨ D , Ds ⟩) (suc i) ⊆ proj (𝒯 n Ds) i
  G u ⟨ v ∷ vs , ⟨ ⟨ v∈D , ⟬vs⟭∈𝒯Ds ⟩ , refl ⟩ ⟩ = ⟨ vs , ⟨ ⟬vs⟭∈𝒯Ds , refl ⟩ ⟩
  H : proj (𝒯 n Ds) i ⊆ proj (𝒯 (suc n) ⟨ D , Ds ⟩) (suc i)
  H v ⟨ vs , ⟨ vs⊆Ds , eq ⟩ ⟩ = ⟨ u ∷ vs , ⟨ ⟨ u∈D , vs⊆Ds ⟩ , eq ⟩ ⟩

∏-append : ∀{n}{m} → ∏ n (𝒫 Value) → ∏ m (𝒫 Value) → ∏ (n + m) (𝒫 Value)
∏-append {zero} {m} Ds Es = Es
∏-append {suc n} {m} ⟨ D , Ds ⟩ Es = ⟨ D , (∏-append Ds Es) ⟩

{- Application is a Congruence ------------------------------------------------}

▪-cong-⊆ : ∀{D₁ D₂ D₃ D₄ : 𝒫 Value}
  → D₁ ⊆ D₃  →  D₂ ⊆ D₄
  → D₁ ▪ D₂ ⊆ D₃ ▪ D₄
▪-cong-⊆ D13 D24 w ⟨ V , ⟨ wv∈D1 , ⟨ V<D2 , V≢[] ⟩ ⟩ ⟩ =
   ⟨ V , ⟨ (D13 (V ↦ w) wv∈D1) , ⟨ (λ d z → D24 d (V<D2 d z)) , V≢[] ⟩ ⟩ ⟩
     
▪-cong : ∀{D₁ D₂ D₃ D₄ : 𝒫 Value}
  → D₁ ≃ D₃  →  D₂ ≃ D₄
  → D₁ ▪ D₂ ≃ D₃ ▪ D₄
▪-cong ⟨ d13 , d31 ⟩ ⟨ d24 , d42 ⟩ = ⟨ (▪-cong-⊆ d13 d24) , (▪-cong-⊆ d31 d42) ⟩


{- Abstraction is Extensional ---- --------------------------------------------}

Λ-ext-⊆ : ∀{F₁ F₂ : (𝒫 Value) → (𝒫 Value)}
  → (∀ {X} → F₁ X ⊆ F₂ X)
  → Λ F₁ ⊆ Λ F₂
Λ-ext-⊆ {F₁} {F₂} F₁⊆F₂ (V ↦ w) ⟨ w∈F₁X , V≢[] ⟩ = ⟨ F₁⊆F₂ w w∈F₁X , V≢[] ⟩
Λ-ext-⊆ {F₁} {F₂} F₁⊆F₂ ν v∈ = tt

Λ-ext : ∀{F₁ F₂ : (𝒫 Value) → (𝒫 Value)}
  → (∀ {X} → F₁ X ≃ F₂ X)
  → Λ F₁ ≃ Λ F₂
Λ-ext {F₁}{F₂} F₁≃F₂ = ⟨ Λ-ext-⊆ (proj₁ F₁≃F₂) , Λ-ext-⊆ (proj₂ F₁≃F₂) ⟩


{- Abstraction followed by Application is the identity ------------------------}

continuous : (F : 𝒫 Value → 𝒫 Value) → Set₁
continuous F = ∀ X E → mem E ⊆ F X → nonempty X
    → Σ[ D ∈ List Value ] mem D ⊆ X  ×  mem E ⊆ F (mem D)  ×  D ≢ []

monotone : (F : 𝒫 Value → 𝒫 Value) → Set₁
monotone F = ∀ D₁ D₂ → D₁ ⊆ D₂ → F D₁ ⊆ F D₂

Λ-▪-id : ∀ {F : 𝒫 Value → 𝒫 Value}{X : 𝒫 Value}
  → continuous F → monotone F → nonempty X
  → (Λ F) ▪ X ≃ F X
Λ-▪-id {F}{X} Fcont Fmono NE-X = ⟨ (Λ-▪-⊆ Fmono) , (⊆-Λ-▪ Fcont NE-X) ⟩
  where
  Λ-▪-⊆ : ∀ {F : 𝒫 Value → 𝒫 Value}{X : 𝒫 Value}
    → monotone F  →  (Λ F) ▪ X ⊆ F X
  Λ-▪-⊆ {F} {X} Fmono w ⟨ V , ⟨ ⟨ w∈FV , _ ⟩ , ⟨ V<X , V≢[] ⟩ ⟩ ⟩ =
      Fmono (mem V) X V<X w w∈FV

  ⊆-Λ-▪ : ∀ {F : 𝒫 Value → 𝒫 Value}{X : 𝒫 Value}
    → continuous F  → nonempty X →  F X ⊆ (Λ F) ▪ X
  ⊆-Λ-▪ {F}{X} Fcont NE-X w w∈FX 
      with Fcont X (w ∷ []) (λ { d (here refl) → w∈FX }) NE-X
  ... | ⟨ D , ⟨ D<X , ⟨ w∈FD , NE-D ⟩ ⟩ ⟩ =
        ⟨ D , ⟨ ⟨ w∈FD w (here refl) , NE-D ⟩ , ⟨ D<X , NE-D ⟩ ⟩ ⟩

  
{- Primitive Abstraction followed by Application is the identity --------------}

℘-▪-≃ : ∀{B}{P}{f}{k}  →  (℘ (B ⇒ P) f) ▪ (℘ (base B) k) ≃ ℘ P (f k)
℘-▪-≃ {B}{P}{f}{k} = ⟨ fwd , back ⟩
  where
  fwd : ℘ (B ⇒ P) f ▪ ℘ (base B) k ⊆ ℘ P (f k)
  fwd w ⟨ V , ⟨ ⟨ k′ , ⟨ refl , w∈fk′ ⟩ ⟩ , ⟨ k′∈pk , _ ⟩ ⟩ ⟩
      with k′∈pk (const k′) (here refl)
  ... | pkk′ rewrite k′∈℘k⇒k′≡k pkk′ = w∈fk′
  back : ℘ P (f k) ⊆ ℘ (B ⇒ P) f ▪ ℘ (base B) k
  back w w∈fk = ⟨ (const k ∷ []) , ⟨ ⟨ k , ⟨ refl , w∈fk ⟩ ⟩ ,
                ⟨ (λ {d (here refl) → k∈℘k}) , (λ ()) ⟩ ⟩ ⟩

{- Cons is a Congruence  ------------------------------------------------------}

cons-cong-⊆ : ∀{D₁ D₂ D₃ D₄ : 𝒫 Value} → D₁ ⊆ D₃  →  D₂ ⊆ D₄
  → 〘 D₁ , D₂ 〙 ⊆ 〘 D₃ , D₄ 〙
cons-cong-⊆ D13 D24 ❲ u , v ❳ ⟨ u∈D₁ , v∈D₂ ⟩ = ⟨ D13 u u∈D₁ , D24 v v∈D₂ ⟩

cons-cong : ∀{D₁ D₂ D₃ D₄ : 𝒫 Value} → D₁ ≃ D₃  →  D₂ ≃ D₄
   → 〘 D₁ , D₂ 〙 ≃ 〘 D₃ , D₄ 〙
cons-cong ⟨ d13 , d31 ⟩ ⟨ d24 , d42 ⟩ =
    ⟨ (cons-cong-⊆ d13 d24) , (cons-cong-⊆ d31 d42) ⟩

car-cong-⊆ : ∀{D₁ D₃ : 𝒫 Value} → D₁ ⊆ D₃ → car D₁ ⊆ car D₃
car-cong-⊆ D13 u ⟨ v , uv∈D₁ ⟩ = ⟨ v , D13 ❲ u , v ❳ uv∈D₁ ⟩

car-cong : ∀{D₁ D₃ : 𝒫 Value} → D₁ ≃ D₃ → car D₁ ≃ car D₃
car-cong ⟨ d13 , d31 ⟩  =
    ⟨ (car-cong-⊆ d13) , (λ { u ⟨ v , uv∈D₃ ⟩  → ⟨ v , d31 ❲ u , v ❳ uv∈D₃ ⟩}) ⟩

cdr-cong-⊆ : ∀{D₁ D₃ : 𝒫 Value} → D₁ ⊆ D₃ → cdr D₁ ⊆ cdr D₃
cdr-cong-⊆ D13 v ⟨ u , uv∈D₁ ⟩ = ⟨ u , D13 ❲ u , v ❳ uv∈D₁ ⟩

cdr-cong : ∀{D₁ D₃ : 𝒫 Value} → D₁ ≃ D₃ → cdr D₁ ≃ cdr D₃
cdr-cong ⟨ d13 , d31 ⟩  =
    ⟨ (cdr-cong-⊆ d13) , (λ { v ⟨ u , uv∈D₃ ⟩ → ⟨ u , d31 ❲ u , v ❳ uv∈D₃ ⟩}) ⟩

_⫃_ : ∀{n} → ∏ n (𝒫 Value) → ∏ n (𝒫 Value) → Set
_⫃_ {n} = rel-∏ {n} _⊆_

𝒯-cong-⊆ : ∀{n}{Ds Es : ∏ n (𝒫 Value)} → Ds ⫃ Es → 𝒯 n Ds ⊆ 𝒯 n Es
𝒯-cong-⊆ {zero} {lift tt} {lift tt} Ds⊆Es v v∈ = v∈
𝒯-cong-⊆ {suc n} {⟨ D , Ds ⟩} {⟨ E , Es ⟩} ⟨ D⊆E , Ds⊆Es ⟩ ⟬ v ∷ vs ⟭
    ⟨ v∈D , vs∈𝒯Ds ⟩ = ⟨ (D⊆E v v∈D) , (𝒯-cong-⊆ Ds⊆Es ⟬ vs ⟭ vs∈𝒯Ds) ⟩

_⩭_ : ∀{n} → ∏ n (𝒫 Value) → ∏ n (𝒫 Value) → Set
_⩭_ {n} = rel-∏ {n} _≃_

⩭-refl = λ {n}{Ds} → rel-∏-refl {n}{𝒫 Value}{R = _≃_}{Ds} ≃-refl

⩭-sym = λ {n}{Ds}{Es} → rel-∏-sym {n}{𝒫 Value}{R = _≃_}{Ds}{Es} ≃-sym 

⩭⇒⊆ : ∀{n}{Ds Es : ∏ n (𝒫 Value)} → Ds ⩭ Es → Ds ⫃ Es  ×  Es ⫃ Ds
⩭⇒⊆ {n}{Ds}{Es} Ds=Es =
    ⟨ rel-∏-⇒ (λ x y → proj₁) Ds=Es , rel-∏-⇒ (λ x y → proj₁) (⩭-sym Ds=Es) ⟩
    
𝒯-cong-≃ : ∀{n}{Ds Es : ∏ n (𝒫 Value)} → Ds ⩭ Es → 𝒯 n Ds ≃ 𝒯 n Es
𝒯-cong-≃ {n}{Ds}{Es} Ds=Es
    with ⩭⇒⊆ Ds=Es
... | ⟨ Ds⊆Es , Es⊆Ds ⟩ =    
  ⟨ 𝒯-cong-⊆ Ds⊆Es , 𝒯-cong-⊆ Es⊆Ds ⟩

proj-cong-⊆ : ∀{D E : 𝒫 Value}{i} → D ⊆ E → proj D i ⊆ proj E i
proj-cong-⊆ D⊆E v ⟨ vs , ⟨ vs∈D , refl ⟩ ⟩ =
                  ⟨ vs , ⟨ (D⊆E ⟬ vs ⟭ vs∈D) , refl ⟩ ⟩

proj-cong-≃ : ∀{D E : 𝒫 Value}{i} → D ≃ E → proj D i ≃ proj E i
proj-cong-≃ D≃E = ⟨ (proj-cong-⊆ (proj₁ D≃E)) , (proj-cong-⊆ (proj₂ D≃E)) ⟩  

∏-append-⊆ : ∀{n}{m}{Ds Ds′ : ∏ n (𝒫 Value)}{Es Es′ : ∏ m (𝒫 Value)}
   → Ds ⫃ Ds′ → Es ⫃ Es′
   → ∏-append Ds Es ⫃ ∏-append Ds′ Es′
∏-append-⊆ {zero} {m} {Ds} {Ds′} {Es} {Es′} Ds⊆Ds′ Es⊆Es′ = Es⊆Es′
∏-append-⊆ {suc n} {m} {⟨ D , Ds ⟩} {⟨ D′ , Ds′ ⟩} {Es} {Es′} ⟨ D⊆D′ , Ds⊆Ds′ ⟩
    Es⊆Es′ = ⟨ D⊆D′ , ∏-append-⊆ Ds⊆Ds′ Es⊆Es′ ⟩

∏-append-⩭ : ∀{n}{m}{Ds Ds′ : ∏ n (𝒫 Value)}{Es Es′ : ∏ m (𝒫 Value)}
   → Ds ⩭ Ds′ → Es ⩭ Es′
   → ∏-append Ds Es ⩭ ∏-append Ds′ Es′
∏-append-⩭ {zero} {m} {Ds} {Ds′} Ds=Ds′ Es=Es′ = Es=Es′
∏-append-⩭ {suc n} {m} {⟨ D , Ds ⟩} {⟨ D′ , Ds′ ⟩} ⟨ D=D′ , Ds=Ds′ ⟩ Es=Es′ =
    ⟨ D=D′ , ∏-append-⩭ Ds=Ds′ Es=Es′ ⟩

{- Cons and Car  --------------------------------------------------------------}

car-of-cons-⊆ : ∀{D₁ D₂ : 𝒫 Value}
  → car (〘 D₁ , D₂ 〙) ⊆ D₁
car-of-cons-⊆ {D₁} {D₂} u ⟨ v , ⟨ u∈D₁ , v∈D₂ ⟩ ⟩ = u∈D₁

car-of-cons : ∀{D₁ D₂ : 𝒫 Value}
  → nonempty D₂
  → car (〘 D₁ , D₂ 〙) ≃ D₁
car-of-cons {D₁}{D₂} ⟨ v , v∈D₂ ⟩ =
    ⟨ car-of-cons-⊆ , (λ u u∈D₁ → ⟨ v , ⟨ u∈D₁ , v∈D₂ ⟩ ⟩) ⟩

cdr-of-cons-⊆ : ∀{D₁ D₂ : 𝒫 Value}
  → cdr 〘 D₁ , D₂ 〙 ⊆ D₂
cdr-of-cons-⊆ {D₁} {D₂} v ⟨ u , ⟨ u∈D₁ , v∈D₂ ⟩ ⟩ = v∈D₂

cdr-of-cons : ∀{D₁ D₂ : 𝒫 Value}
  → nonempty D₁
  → cdr 〘 D₁ , D₂ 〙 ≃ D₂
cdr-of-cons {D₁}{D₂} ⟨ u , u∈D₁ ⟩ =
    ⟨ cdr-of-cons-⊆ , (λ v v∈D₂ → ⟨ u , ⟨ u∈D₁ , v∈D₂ ⟩ ⟩) ⟩

{- Environments ---------------------------------------------------------------}

Env : Set₁
Env = Var → 𝒫 Value

nonempty-env : Env → Set
nonempty-env ρ = ∀ x → nonempty (ρ x)

infix 5 _⊆ₑ_
_⊆ₑ_ : Env → Env → Set
ρ₁ ⊆ₑ ρ₂ = ∀ x → ρ₁ x ⊆ ρ₂ x

⊆ₑ-trans : ∀{ρ₁ ρ₂ ρ₃} → ρ₁ ⊆ₑ ρ₂ → ρ₂ ⊆ₑ ρ₃ → ρ₁ ⊆ₑ ρ₃
⊆ₑ-trans {ρ₁}{ρ₂}{ρ₃} r12 r23 x = λ d z → r23 x d (r12 x d z)

extend-nonempty-env : ∀{ρ}{X}
   → nonempty-env ρ  →  nonempty X  →  nonempty-env (X • ρ)
extend-nonempty-env {ρ} {X} NE-ρ NE-X zero = NE-X
extend-nonempty-env {ρ} {X} NE-ρ V≢[] (suc x) = NE-ρ x

env-ext : ∀{ρ ρ′}{X} → ρ ⊆ₑ ρ′ → (x : Var) → (X • ρ) x ⊆ (X • ρ′) x
env-ext ρ<ρ′ zero d d∈ = d∈
env-ext ρ<ρ′ (suc x) = ρ<ρ′ x

{- environments whose codomain are finite nonempty sets -}
finite-env : Env → Set
finite-env ρ = ∀ x → Σ[ E ∈ List Value ] ρ x ≃ mem E × E ≢ []

infix 6 _⊔ₑ_
_⊔ₑ_ : Env → Env → Env
(ρ₁ ⊔ₑ ρ₂) x v = ρ₁ x v ⊎ ρ₂ x v

join-finite-env : ∀{ρ₁ ρ₂}  → finite-env ρ₁  →  finite-env ρ₂
   → finite-env (ρ₁ ⊔ₑ ρ₂)
join-finite-env {ρ₁}{ρ₂} f1 f2 x
    with f1 x
... | ⟨ E1 , ⟨ ρ₁=E1 , NE-E1 ⟩ ⟩
    with f2 x
... | ⟨ E2 , ⟨ ρ₂=E2 , NE-E2 ⟩ ⟩ =
    ⟨ (E1 ++ E2) , ⟨ ⟨ G , (H {E1} λ d z → z) ⟩ ,
      (λ E12=[] → NE-E1 (++-conicalˡ E1 E2 E12=[])) ⟩ ⟩
    where
    G : (v : Value) → ρ₁ x v ⊎ ρ₂ x v → mem (E1 ++ E2) v
    G v (inj₁ ρ1x) = ∈-++⁺ˡ ((proj₁ ρ₁=E1) v ρ1x)
    G v (inj₂ ρ2x) = ∈-++⁺ʳ E1 ((proj₁ ρ₂=E2) v ρ2x)

    H : ∀{E} → mem E ⊆ mem E1 → mem (E ++ E2) ⊆ (λ v → ρ₁ x v ⊎ ρ₂ x v)
    H {[]} E<E1 v v∈E++E2 = inj₂ ((proj₂ ρ₂=E2) v v∈E++E2)
    H {x ∷ E} E<E1 .x (here refl) = inj₁ ((proj₂ ρ₁=E1) x (E<E1 x (here refl)))
    H {x ∷ E} E<E1 v (there v∈E++E2) =
       H (λ v z → E<E1 v (there z)) v v∈E++E2

join-lub : ∀{ρ ρ₁ ρ₂} → ρ₁ ⊆ₑ ρ → ρ₂ ⊆ₑ ρ → ρ₁ ⊔ₑ ρ₂ ⊆ₑ ρ
join-lub {ρ} {ρ₁} {ρ₂} ρ₁⊆ρ ρ₂⊆ρ x v (inj₁ v∈ρ₁x) = ρ₁⊆ρ x v v∈ρ₁x
join-lub {ρ} {ρ₁} {ρ₂} ρ₁⊆ρ ρ₂⊆ρ x v (inj₂ v∈ρ₂x) = ρ₂⊆ρ x v v∈ρ₂x

join-⊆-left : ∀{ρ₁ ρ₂} → ρ₁ ⊆ₑ ρ₁ ⊔ₑ ρ₂
join-⊆-left {ρ₁}{ρ₂} = λ x d z → inj₁ z

join-⊆-right : ∀{ρ₁ ρ₂} → ρ₂ ⊆ₑ ρ₁ ⊔ₑ ρ₂
join-⊆-right {ρ₁}{ρ₂} = λ x d z → inj₂ z

monotone-env : (Env → 𝒫 Value) → Set₁
monotone-env D = ∀ {ρ ρ′} → (∀ x → ρ x ⊆ ρ′ x)  →  D ρ ⊆ D ρ′

{- Needs a name ---------------------------------------------------------------}

rel-results : ∀{ℓ}{T : Set ℓ}
   → (∀ b → Result T b → Result T b → Set₁)
   → ∀ bs → Tuple bs (Result T) → Tuple bs (Result T) → Set₁
rel-results R [] xs ys = Lift (lsuc lzero) True
rel-results R (b ∷ bs) ⟨ x , xs ⟩ ⟨ y , ys ⟩ =
    (R b x y) × (rel-results R bs xs ys)

⊆-result : ∀ b → Result (𝒫 Value) b → Result (𝒫 Value) b → Set₁
⊆-result ■ x y = Lift (lsuc lzero) (x ⊆ y)
⊆-result (ν b) f g = ∀ X → ⊆-result b (f X) (g X)
⊆-result (∁ b) x y = ⊆-result b x y

⊆-results = rel-results ⊆-result

⊆-result⇒⊆ : ∀ D E → ⊆-result ■ D E → D ⊆ E
⊆-result⇒⊆ D E (lift D⊆E) = D⊆E

rel-results⇒rel-∏ : ∀{n}{xs ys : ∏ n (𝒫 Value)}
    {R : ∀ b → Result (𝒫 Value) b → Result (𝒫 Value) b → Set₁}
    {R′ : 𝒫 Value → 𝒫 Value → Set}
  → (∀ x y → R ■ x y → R′ x y)
  → rel-results R (replicate n ■) xs ys
  → rel-∏ R′ xs ys
rel-results⇒rel-∏ {zero} R⇒R′ (lift tt) = tt
rel-results⇒rel-∏ {suc n}{⟨ x , xs ⟩}{⟨ y , ys ⟩} R⇒R′ ⟨ Rxy , R[xs,ys] ⟩ =
    ⟨ R⇒R′ x y Rxy , (rel-results⇒rel-∏ R⇒R′ R[xs,ys]) ⟩

{- Continuous -----------------------------------------------------------------}

continuous-∈ : (Env → 𝒫 Value) → Env → Value → Set₁
continuous-∈ D ρ v = v ∈ D ρ
   → Σ[ ρ′ ∈ Env ] finite-env ρ′ × ρ′ ⊆ₑ ρ  × v ∈ D ρ′

continuous-env : (Env → 𝒫 Value) → Env → Set₁
continuous-env D ρ = ∀ v → v ∈ D ρ
                     → Σ[ ρ′ ∈ Env ] finite-env ρ′ × ρ′ ⊆ₑ ρ  × v ∈ D ρ′

{- creates an environment that maps each variable x to
   a singleton set of some element in ρ x.  -}
initial-finite-env : (ρ : Env) → (NE-ρ : nonempty-env ρ) → Env
initial-finite-env ρ NE-ρ x
    with NE-ρ x
... | ⟨ v , v∈ρx ⟩ = ⌈ v ⌉

initial-fin : (ρ : Env) → (NE-ρ : nonempty-env ρ)
   → finite-env (initial-finite-env ρ NE-ρ)
initial-fin ρ NE-ρ x
    with NE-ρ x
... | ⟨ v , v∈ρx ⟩ =
      ⟨ v ∷ [] ,
      ⟨ ⟨ (λ {w refl → (here refl)}) , (λ {w (here refl) → refl}) ⟩ , (λ ()) ⟩ ⟩

initial-fin-⊆ : (ρ : Env) → (NE-ρ : nonempty-env ρ)
  → initial-finite-env ρ NE-ρ ⊆ₑ ρ
initial-fin-⊆ ρ NE-ρ x v v∈initial
    with NE-ρ x
... | ⟨ w , w∈ρx ⟩ rewrite v∈initial = w∈ρx

{- single-env maps x to D and any other variable y to something in ρ y. -}
single-env : Var → 𝒫 Value → (ρ : Env) → (NE-ρ : nonempty-env ρ) → Env
single-env x D ρ NE-ρ y
    with x ≟ y
... | yes refl = D
... | no neq
    with NE-ρ y
... | ⟨ v , v∈ρy ⟩ = ⌈ v ⌉    

single-fin : ∀{v}{x}{ρ}{NE-ρ} → finite-env (single-env x ⌈ v ⌉ ρ NE-ρ)
single-fin {v}{x}{ρ}{NE-ρ} y
    with x ≟ y
... | yes refl =
    ⟨ v ∷ [] ,
    ⟨ ⟨ (λ{v₁ refl → (here refl)}) , (λ{v₁ (here refl) → refl}) ⟩ , (λ ()) ⟩ ⟩
... | no neq
    with NE-ρ y
... | ⟨ w , w∈ρy ⟩ =
    ⟨ w ∷ [] ,
    ⟨ ⟨ (λ{v₁ refl → here refl}) , (λ{v₁ (here refl) → refl}) ⟩ , (λ ()) ⟩ ⟩

single-⊆ : ∀{ρ x v}{NE-ρ : nonempty-env ρ}
  →  v ∈ ρ x  →  single-env x ⌈ v ⌉ ρ NE-ρ ⊆ₑ ρ
single-⊆ {ρ}{x}{v}{NE-ρ} v∈ρx y w sing 
    with x ≟ y
... | yes refl rewrite sing = v∈ρx
... | no neq
    with NE-ρ y
... | ⟨ u , u∈ρy ⟩ rewrite sing = u∈ρy

v∈single[xv]x : ∀{v}{x}{ρ}{NE-ρ} → v ∈ single-env x ⌈ v ⌉ ρ NE-ρ x
v∈single[xv]x {v}{x}
    with x ≟ x
... | yes refl = refl
... | no neq = ⊥-elim (neq refl)

continuous-∈⇒⊆ : ∀ E ρ (NE-ρ : nonempty-env ρ)
   → monotone-env E
   → ∀ V → mem V ⊆ E ρ
   → (∀ v → v ∈ mem V → continuous-∈ E ρ v)
   → Σ[ ρ′ ∈ Env ] finite-env ρ′ × ρ′ ⊆ₑ ρ  × mem V ⊆ E ρ′
continuous-∈⇒⊆ E ρ NE-ρ mE [] V⊆E ∀v∈V⇒cont =
   ⟨ initial-finite-env ρ NE-ρ , ⟨ initial-fin ρ NE-ρ ,
   ⟨ initial-fin-⊆ ρ NE-ρ , (λ d ()) ⟩ ⟩ ⟩
continuous-∈⇒⊆ E ρ NE-ρ mE (v ∷ V) v∷V⊆Eρ v∈V⇒cont
    with continuous-∈⇒⊆ E ρ NE-ρ mE V (λ d z → v∷V⊆Eρ d (there z))
                (λ w w∈V w∈Mρ → v∈V⇒cont w (there w∈V) w∈Mρ)
... | ⟨ ρ₁ , ⟨ fρ₁ , ⟨ ρ₁⊆ρ , V⊆Eρ₁ ⟩ ⟩ ⟩
    with v∈V⇒cont v (here refl) (v∷V⊆Eρ v (here refl))
... | ⟨ ρ₂ , ⟨ fρ₂ , ⟨ ρ₂⊆ρ , v∈Eρ₂ ⟩ ⟩ ⟩ =    
    ⟨ ρ₃ , ⟨ (join-finite-env fρ₁ fρ₂) , ⟨ (join-lub ρ₁⊆ρ ρ₂⊆ρ) ,
    G ⟩ ⟩ ⟩
    where
    ρ₃ = ρ₁ ⊔ₑ ρ₂
    G : (d : Value) → mem (v ∷ V) d → d ∈ E ρ₃
    G d (here refl) = mE {ρ₂}{ρ₃} join-⊆-right v v∈Eρ₂
    G d (there m) = mE {ρ₁}{ρ₃} join-⊆-left d (V⊆Eρ₁ d m)

▪-continuous : ∀{D E : Env → 𝒫 Value}{ρ}{NE-ρ : nonempty-env ρ}{w}
  → w ∈ (D ρ) ▪ (E ρ)
  → continuous-env D ρ → continuous-env E ρ
  → monotone-env D → monotone-env E
  → Σ[ ρ₃ ∈ Env ] finite-env ρ₃ × ρ₃ ⊆ₑ ρ × w ∈ (D ρ₃) ▪ (E ρ₃)
▪-continuous {D}{E}{ρ}{NE-ρ}{w} ⟨ V , ⟨ V↦w∈Dρ , ⟨ V⊆Eρ , V≢[] ⟩ ⟩ ⟩
    IH-D IH-E mD mE
    with IH-D (V ↦ w) V↦w∈Dρ 
... | ⟨ ρ₁ , ⟨ fρ₁ , ⟨ ρ₁⊆ρ , V↦w∈Dρ₁ ⟩ ⟩ ⟩
    with ((continuous-∈⇒⊆ E ρ NE-ρ mE) V V⊆Eρ (λ v v∈V → IH-E v))
... | ⟨ ρ₂ , ⟨ fρ₂ , ⟨ ρ₂⊆ρ , V⊆Eρ₂ ⟩ ⟩ ⟩ =
   ⟨ ρ₃ , ⟨ join-finite-env fρ₁ fρ₂ , ⟨ join-lub ρ₁⊆ρ ρ₂⊆ρ , w∈D▪Eρ₃ ⟩ ⟩ ⟩ 
    where
    ρ₃ = ρ₁ ⊔ₑ ρ₂
    ρ₁⊆ρ₃ = λ x v z → inj₁ z
    V↦w∈Dρ₃ : V ↦ w ∈ D ρ₃
    V↦w∈Dρ₃ = mD ρ₁⊆ρ₃ (V ↦ w) V↦w∈Dρ₁
    ρ₂⊆ρ₄ = λ x v z → inj₂ z
    V⊆Eρ₃ : mem V ⊆ E ρ₃
    V⊆Eρ₃ v v∈V = mE ρ₂⊆ρ₄ v (V⊆Eρ₂ v v∈V)
    w∈D▪Eρ₃ : w ∈ (D ρ₃) ▪ (E ρ₃)
    w∈D▪Eρ₃ = ⟨ V , ⟨ V↦w∈Dρ₃ , ⟨ V⊆Eρ₃ , V≢[] ⟩ ⟩ ⟩

Λ-continuous : ∀{E : Env  → 𝒫 Value}{ρ}{NE-ρ}{v}
  → v ∈ Λ (λ D → E (D • ρ))
  → (∀ V → V ≢ [] → continuous-env E (mem V • ρ))
  → monotone-env E
  → Σ[ ρ′ ∈ Env ] finite-env ρ′ × ρ′ ⊆ₑ ρ × v ∈ Λ (λ D → E (D • ρ′))
Λ-continuous {E}{ρ}{NE-ρ}{V ↦ w} ⟨ w∈EV•ρ , V≢[] ⟩ IH mE
    with IH V V≢[] w w∈EV•ρ
... | ⟨ ρ′ , ⟨ fρ′ , ⟨ ρ′⊆V•ρ , w∈Eρ′ ⟩ ⟩ ⟩ =
    ⟨ (λ x → ρ′ (suc x)) , ⟨ (λ x → fρ′ (suc x)) , ⟨ (λ x → ρ′⊆V•ρ (suc x)) ,
    ⟨ mE{ρ′}{mem V • (λ x → ρ′ (suc x))} G w w∈Eρ′ , V≢[] ⟩ ⟩ ⟩ ⟩
    where G : (x : Var) → ρ′ x ⊆ (mem V • (λ x₁ → ρ′ (suc x₁))) x
          G zero v v∈ρ′x = ρ′⊆V•ρ 0 v v∈ρ′x
          G (suc x) v v∈ρ′x = v∈ρ′x
Λ-continuous {E}{ρ}{NE-ρ}{ν} v∈Λ IH mE =
  ⟨ initial-finite-env ρ NE-ρ , ⟨ initial-fin ρ NE-ρ , ⟨ initial-fin-⊆ ρ NE-ρ ,
      tt ⟩ ⟩ ⟩

cons-continuous : ∀{D E : Env → 𝒫 Value}{ρ}{NE-ρ : nonempty-env ρ}{w : Value}
  → w ∈ 〘 D ρ , E ρ 〙
  → continuous-env D ρ → continuous-env E ρ → monotone-env D → monotone-env E
  → Σ[ ρ₃ ∈ Env ] finite-env ρ₃ × ρ₃ ⊆ₑ ρ × w ∈ 〘 D ρ₃ , E ρ₃ 〙
cons-continuous {D} {E} {ρ} {NE-ρ} {❲ u , v ❳} ⟨ u∈Dρ , v∈Eρ ⟩ cD cE mD mE
    with cD u u∈Dρ 
... | ⟨ ρ₁ , ⟨ fρ₁ , ⟨ ρ₁⊆ρ , u∈Dρ₁ ⟩ ⟩ ⟩
    with cE v v∈Eρ 
... | ⟨ ρ₂ , ⟨ fρ₂ , ⟨ ρ₂⊆ρ , v∈Eρ₂ ⟩ ⟩ ⟩ =
    ⟨ ρ₃ , ⟨ join-finite-env fρ₁ fρ₂ , ⟨ join-lub ρ₁⊆ρ ρ₂⊆ρ ,
    ⟨ u∈Dρ₃ , v∈Dρ₃ ⟩ ⟩ ⟩ ⟩
    where
    ρ₃ = ρ₁ ⊔ₑ ρ₂
    ρ₁⊆ρ₃ = λ x v z → inj₁ z
    u∈Dρ₃ = mD ρ₁⊆ρ₃ u u∈Dρ₁
    ρ₂⊆ρ₃ = λ x v z → inj₂ z
    v∈Dρ₃ = mE ρ₂⊆ρ₃ v v∈Eρ₂

car-continuous : ∀{D : Env → 𝒫 Value}{ρ}{NE-ρ : nonempty-env ρ}{u : Value}
  → u ∈ car (D ρ) → continuous-env D ρ → monotone-env D
  → Σ[ ρ₃ ∈ Env ] finite-env ρ₃ × ρ₃ ⊆ₑ ρ × u ∈ car (D ρ₃)
car-continuous {D} {ρ} {NE-ρ} {u} ⟨ v , uv∈Dρ ⟩ cD mD
    with cD ❲ u , v ❳ uv∈Dρ 
... | ⟨ ρ₁ , ⟨ fρ₁ , ⟨ ρ₁⊆ρ , uv∈Dρ₁ ⟩ ⟩ ⟩ =
      ⟨ ρ₁ , ⟨ fρ₁ , ⟨ ρ₁⊆ρ , ⟨ v , mD (λ x d z → z) ❲ u , v ❳ uv∈Dρ₁ ⟩ ⟩ ⟩ ⟩

cdr-continuous : ∀{D : Env → 𝒫 Value}{ρ}{NE-ρ : nonempty-env ρ}{u : Value}
  → u ∈ cdr (D ρ) → continuous-env D ρ → monotone-env D
  → Σ[ ρ₃ ∈ Env ] finite-env ρ₃ × ρ₃ ⊆ₑ ρ × u ∈ cdr (D ρ₃)
cdr-continuous {D} {ρ} {NE-ρ} {v} ⟨ u , uv∈Dρ ⟩ cD mD
    with cD ❲ u , v ❳ uv∈Dρ 
... | ⟨ ρ₁ , ⟨ fρ₁ , ⟨ ρ₁⊆ρ , uv∈Dρ₁ ⟩ ⟩ ⟩ =
      ⟨ ρ₁ , ⟨ fρ₁ , ⟨ ρ₁⊆ρ , ⟨ u , mD (λ x d z → z) ❲ u , v ❳ uv∈Dρ₁ ⟩ ⟩ ⟩ ⟩

mono-envs : ∀{n} → (Env → ∏ n (𝒫 Value)) → Set₁
mono-envs {n} Ds = ∀{ρ ρ′} → ρ ⊆ₑ ρ′ → ⊆-results (replicate n ■) (Ds ρ) (Ds ρ′)

continuous-envs : ∀{n} → (Env → ∏ n (𝒫 Value)) → Env → Set₁
continuous-envs {n} Ds ρ = ∀ v → v ∈ 𝒯 n (Ds ρ)
                     → Σ[ ρ′ ∈ Env ] finite-env ρ′ × ρ′ ⊆ₑ ρ  × v ∈ 𝒯 n (Ds ρ′)

next-Ds : ∀{n} → (Env → ∏ (suc n) (𝒫 Value)) → (Env → ∏ n (𝒫 Value))
next-Ds Ds ρ
    with Ds ρ
... | ⟨ D , Ds′ ⟩ = Ds′

next-Ds-proj₂ : ∀{n}{Ds : Env → ∏ (suc n) (𝒫 Value)}{ρ}
   → next-Ds Ds ρ ≡ proj₂ (Ds ρ)
next-Ds-proj₂ {n} {Ds} {ρ}
    with Ds ρ
... | ⟨ a , b ⟩ = refl

next-mono-envs : ∀{n}{Ds : Env → ∏ (suc n) (𝒫 Value)}
   → mono-envs Ds → mono-envs (next-Ds Ds)
next-mono-envs {zero} {Ds} mDs {ρ} {ρ′} _ = lift tt
next-mono-envs {suc n} {Ds} mDs {ρ} {ρ′} ρ⊆ρ′
    with Ds ρ | Ds ρ′ | mDs {ρ} {ρ′} ρ⊆ρ′
... | ⟨ Dρ , Dsρ ⟩ | ⟨ Dρ′ , Dsρ′ ⟩ | ⟨ _ , mDs′ ⟩ = mDs′

proj₁-mono-envs : ∀{n}{Ds : Env → ∏ (suc n) (𝒫 Value)}{ρ}{ρ′}
   → ρ ⊆ₑ ρ′  → mono-envs Ds → proj₁ (Ds ρ) ⊆ proj₁ (Ds ρ′)
proj₁-mono-envs {n}{Ds}{ρ}{ρ′} ρ⊆ρ′ mDs
    with Ds ρ | mDs {ρ}{ρ′} ρ⊆ρ′
... | ⟨ Dρ , Dsρ ⟩ | ⟨ lift mD , _ ⟩ = mD

next-NE-Ds : ∀{n}{Ds : Env → ∏ (suc n) (𝒫 Value)}{ρ}
  → NE-∏ (Ds ρ)
  → NE-∏ (next-Ds Ds ρ)
next-NE-Ds{n}{Ds}{ρ} NE-Ds
    with Ds ρ | NE-Ds
... | ⟨ Dρ , Dsρ ⟩ | ⟨ NE-D , NE-Ds′ ⟩ = NE-Ds′

next-cont-envs : ∀{n}{Ds : Env → ∏ (suc n) (𝒫 Value)}
     {ρ}{NE-ρ : nonempty-env ρ}{w}
   → proj₁ (Ds ρ) w
   → continuous-envs Ds ρ
   → continuous-envs (next-Ds Ds) ρ
next-cont-envs {n} {Ds} {ρ}{NE-ρ}{w} w∈Dsρ cDs u u∈
    with Ds ρ | cDs | u∈ 
... | ⟨ D , Ds′ ⟩ | cDDs | u∈′ 
    with v∈𝒯⇒v≡⟬vs⟭ u∈′
... | ⟨ vs , refl ⟩
    with cDDs ⟬ w ∷ vs ⟭ ⟨ w∈Dsρ , u∈′ ⟩
... | ⟨ ρ′ , ⟨ fρ′ , ⟨ ρ′⊆ρ , ⟨ aaa , vs∈Dsρ′ ⟩ ⟩ ⟩ ⟩ =
    ⟨ ρ′ , ⟨ fρ′ , ⟨ ρ′⊆ρ , vs∈Dsρ′ ⟩ ⟩ ⟩

𝒯-continuous : ∀{n}{Ds : Env → ∏ n (𝒫 Value)}{ρ}{NE-ρ : nonempty-env ρ}
    {u : Value}
  → u ∈ 𝒯 n (Ds ρ) → continuous-envs Ds ρ → mono-envs Ds
  → Σ[ ρ₃ ∈ Env ] finite-env ρ₃ × ρ₃ ⊆ₑ ρ × u ∈ 𝒯 n (Ds ρ₃)
𝒯-continuous {zero} {Ds} {ρ} {NE-ρ} {u} u∈𝒯Ds cDs mDs 
    with Ds (initial-finite-env ρ NE-ρ) | u
... | lift tt | ⟬ [] ⟭ =
  ⟨ (initial-finite-env ρ NE-ρ) , ⟨ initial-fin ρ NE-ρ ,
  ⟨ initial-fin-⊆ ρ NE-ρ , tt ⟩ ⟩ ⟩
𝒯-continuous {suc n} {Ds} {ρ} {NE-ρ} {⟬ v ∷ vs ⟭} ⟨ v∈Dρ , vs∈𝒯Dsρ ⟩ cDs mDs 
    with 𝒯-continuous{n}{next-Ds Ds}{ρ}{NE-ρ}{⟬ vs ⟭}
       (subst (λ X → ⟬ vs ⟭ ∈ 𝒯 n X) (sym (next-Ds-proj₂{n}{Ds}{ρ})) vs∈𝒯Dsρ)
       (next-cont-envs{NE-ρ = NE-ρ}{w = v} v∈Dρ cDs)
       (λ {ρ}{ρ′} → next-mono-envs mDs {ρ}{ρ′})
... | ⟨ ρ₁ , ⟨ fρ₁ , ⟨ ρ₁⊆ρ , vs∈𝒯Dsρ₁ ⟩ ⟩ ⟩
    with cDs ⟬ v ∷ vs ⟭ ⟨ v∈Dρ , vs∈𝒯Dsρ ⟩ 
... | ⟨ ρ₂ , ⟨ fρ₂ , ⟨ ρ₂⊆ρ , ⟨ v∈Dρ₂ , vs∈Dsρ₂ ⟩ ⟩ ⟩ ⟩
    with  mDs {ρ₁}{ρ₁ ⊔ₑ ρ₂} λ x d z → inj₁ z
... | ⟨ _ , Dsρ₁⊆Dsρ₃ ⟩ 
    with  mDs {ρ₂}{ρ₁ ⊔ₑ ρ₂} λ x d z → inj₂ z
... | ⟨ lift Dρ₂⊆Dρ₃ , _ ⟩ =
    let v∈Dρ₃ = Dρ₂⊆Dρ₃ v v∈Dρ₂ in
    let vs∈Dsρ₃ = 𝒯-cong-⊆ (rel-results⇒rel-∏ ⊆-result⇒⊆ Dsρ₁⊆Dsρ₃)
                            ⟬ vs ⟭ vs∈𝒯Dsρ₁ in
    ⟨ ρ₃ , ⟨ (join-finite-env fρ₁ fρ₂) , ⟨ (join-lub ρ₁⊆ρ ρ₂⊆ρ) ,
    ⟨ v∈Dρ₃ , vs∈Dsρ₃ ⟩ ⟩ ⟩ ⟩
    where
    ρ₃ = ρ₁ ⊔ₑ ρ₂

proj-continuous : ∀{D : Env → 𝒫 Value}{ρ}{NE-ρ : nonempty-env ρ}{u : Value}{i}
  → u ∈ proj (D ρ) i → continuous-env D ρ → monotone-env D
  → Σ[ ρ₃ ∈ Env ] finite-env ρ₃ × ρ₃ ⊆ₑ ρ × u ∈ proj (D ρ₃) i
proj-continuous {D} {ρ} {NE-ρ} {u} {i} ⟨ vs , ⟨ vs∈Dρ , refl ⟩ ⟩ cD mD
    with cD ⟬ vs ⟭ vs∈Dρ
... | ⟨ ρ′ , ⟨ fρ′ , ⟨ ρ′⊆ρ , vs∈Dρ′ ⟩ ⟩ ⟩ =     
    ⟨ ρ′ , ⟨ fρ′ , ⟨ ρ′⊆ρ ,
    ⟨ vs , ⟨ mD (λ x d z → z) ⟬ vs ⟭ vs∈Dρ′ , refl ⟩ ⟩ ⟩ ⟩ ⟩

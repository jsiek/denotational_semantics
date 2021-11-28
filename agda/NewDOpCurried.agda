{-# OPTIONS --allow-unsolved-metas #-}

module NewDOpCurried where

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
open import NewResultsCurried

open import Data.Empty using (⊥-elim) renaming (⊥ to False)
open import Data.List using (List ; _∷_ ; []; _++_; length; replicate)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Relation.Unary.All 
  using (All; []; _∷_; head; tail; lookup; tabulate; all?)
  renaming (map to allmap)
open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_)
open import Data.List.Properties using (++-conicalˡ)
open import Data.List.Membership.Propositional renaming (_∈_ to _⋵_)
open import Data.List.Membership.Propositional.Properties
  using (∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.Nat using (ℕ; zero; suc; _≟_; _<_; z≤n; s≤s; _+_)
open import Data.Nat.Properties
open import Data.Product using (_×_; Σ; Σ-syntax; proj₁; proj₂)
    renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Unit using (tt) renaming (⊤ to True)
open import Data.Unit.Polymorphic using (⊤) renaming (tt to ptt)
open import Relation.Binary.PropositionalEquality
    using (_≡_; _≢_; refl; sym; trans; subst)
open import Level using (Level; Lift; lift; lower)
    renaming (zero to lzero; suc to lsuc)
open import Relation.Nullary using (¬_; Dec; yes; no)




{- Products (flat tuples) -----------------------------------------------------}
{- Thought: just do this with full tuples with flat tuples as a special case -}

Π : ∀ {ℓ} → ℕ → Set ℓ → Set ℓ
Π n T = Tuple (replicate n ■) (Result T)

Π-map : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} {n}
  → (f : A → B) → Π n A → Π n B
Π-map {n = zero} f (lift lower) = lift tt
Π-map {n = suc n} f ⟨ fst , snd ⟩ = ⟨ f fst , Π-map f snd ⟩

toΠ : ∀ {ℓ} {A : Set ℓ} (xs : List A) → Π (length xs) A
toΠ [] = lift tt
toΠ (x ∷ xs) = ⟨ x , toΠ xs ⟩

toList : ∀ {ℓ} {A : Set ℓ} {n} → Π n A → List A
toList {n = zero} _ = []
toList {n = suc n} ⟨ x , xs ⟩ = x ∷ toList xs

all-Π : ∀{ℓ}{ℓ'}{n}{T : Set ℓ} → (T → Set ℓ') → Π n T → Set ℓ'
all-Π {n = zero} P (lift tt) = ⊤
all-Π {n = suc n} P ⟨ x , xs ⟩ = P x  ×  all-Π P xs

rel-Π : ∀{ℓ}{n}{T : Set ℓ} → (T → T → Set) → Π n T → Π n T → Set
rel-Π {n = zero} R (lift tt) (lift tt) = True
rel-Π {n = suc n} R ⟨ x , xs ⟩ ⟨ y , ys ⟩ = R x y  ×  rel-Π R xs ys

NE-Π : ∀ {n}{T} → Π n (𝒫 T) → Set
NE-Π {n}{T} = all-Π {n = n}{T = 𝒫 T} nonempty

Π-append : ∀{ℓ}{A : Set ℓ}{n}{m} → Π n A → Π m A → Π (n + m) A
Π-append {n = zero} {m} Ds Es = Es
Π-append {n = suc n} {m} ⟨ D , Ds ⟩ Es = ⟨ D , (Π-append Ds Es) ⟩

rel-Π-refl : ∀{ℓ}{n}{T : Set ℓ}{R : T → T → Set}{Ds : Π n T}
   → (∀ {x} → R x x) → rel-Π R Ds Ds
rel-Π-refl {n = zero} {T} {R} {Ds} R-refl = tt
rel-Π-refl {n = suc n} {T} {R} {⟨ D , Ds ⟩} R-refl =
    ⟨ R-refl , (rel-Π-refl R-refl) ⟩

rel-Π-sym : ∀{ℓ}{n}{T : Set ℓ}{R : T → T → Set}{Ds Es : Π n T}
   → (∀ {x y} → R x y → R y x) → rel-Π R Ds Es → rel-Π R Es Ds
rel-Π-sym {n = zero} {T} {R} {lift tt} {lift tt} R-sym tt = tt
rel-Π-sym {n = suc n} {T} {R} {⟨ D , Ds ⟩} {⟨ E , Es ⟩} R-sym ⟨ RDE , R[Ds,Es] ⟩ =
    ⟨ (R-sym RDE) , (rel-Π-sym R-sym R[Ds,Es]) ⟩

rel-Π-⇒ : ∀{ℓ}{n}{T : Set ℓ}{xs ys : Π n T}{R R′ : T → T → Set}
   → (∀ x y → R x y → R′ x y) → rel-Π R xs ys → rel-Π R′ xs ys
rel-Π-⇒ {n = zero} R⇒R′ tt = tt
rel-Π-⇒ {n = suc n}{T}{⟨ x , xs ⟩}{⟨ y , ys ⟩} R⇒R′ ⟨ Rxy , R[xs,ys] ⟩ =
    ⟨ R⇒R′ x y Rxy , rel-Π-⇒ R⇒R′ R[xs,ys] ⟩

_⫃_ : ∀{A : Set}{n} → Π n (𝒫 A) → Π n (𝒫 A) → Set
_⫃_ {A}{n} = rel-Π {n = n}{T = 𝒫 A} _⊆_

_⩭_ : ∀{A : Set}{n} → Π n (𝒫 A) → Π n (𝒫 A) → Set
_⩭_ {A}{n} = rel-Π {n = n}{T = 𝒫 A} _≃_

⩭-refl = λ {A}{n}{Ds} → rel-Π-refl {n = n}{T = 𝒫 A}{R = _≃_}{Ds} ≃-refl

⩭-sym = λ {A}{n}{Ds}{Es} → rel-Π-sym {n = n}{T = 𝒫 A}{R = _≃_}{Ds}{Es} ≃-sym 

⩭⇒⊆ : ∀{A}{n}{Ds Es : Π n (𝒫 A)} → Ds ⩭ Es → Ds ⫃ Es  ×  Es ⫃ Ds
⩭⇒⊆ {n}{Ds}{Es} Ds=Es =
    ⟨ rel-Π-⇒ (λ x y → proj₁) Ds=Es , rel-Π-⇒ (λ x y → proj₁) (⩭-sym Ds=Es) ⟩


curry-rel : ∀ {ℓ} {A : Set ℓ} n R (𝒻 ℊ : Π n A → A)
  → (∀ (Ds Es : Π n A) → rel-Π R Ds Es → R (𝒻 Ds) (ℊ Es)) 
  → fun-rel-pres R (replicate n ■) ■ (curryFun 𝒻) (curryFun ℊ)
curry-rel zero R 𝒻 ℊ H = lift (H (lift tt) (lift tt) tt)
curry-rel (suc n) R 𝒻 ℊ H D E (lift D~E) = 
  curry-rel n R (λ z → 𝒻 ⟨ D , z ⟩) (λ z → ℊ ⟨ E , z ⟩) 
            (λ Ds Es z → H ⟨ D , Ds ⟩ ⟨ E , Es ⟩ ⟨ D~E , z ⟩)

uncurry-rel : ∀ {ℓ}{A : Set ℓ} n R (𝒻 ℊ : DenotOp A (replicate n ■))
  → fun-rel-pres R (replicate n ■) ■ 𝒻 ℊ
  → (∀ (Ds Es : Π n A) → rel-Π R Ds Es → R ((uncurryFun 𝒻) Ds) ((uncurryFun ℊ) Es))
uncurry-rel zero R 𝒻 ℊ H D E _ = lower H
uncurry-rel (suc n) R 𝒻 ℊ H ⟨ D , Ds ⟩ ⟨ E , Es ⟩ ⟨ D~E , Ds~Es ⟩ = 
   uncurry-rel n R (𝒻 D) (ℊ E) (H D E (lift D~E)) Ds Es Ds~Es


{- Denotational Values --------------------------------------------------------}

data Value : Set where
  const : {B : Base} → base-rep B → Value  {- A primitive constant of type B. -}
  _⊢_↦_ : List Value → List Value → Value → Value
      {- An entry in a function's graph. -}
  ν : Value      {- The empty function -}
  ω : Value      {- An error value, to serve as a default value in Envs and
                    to differentiate from converging -}
  ⦅_,_⦆ : Value → Value → Value            {- Pairs -}
  ∥_∥ : List Value → Value                 {- Tuples -}
  left : List Value → Value                {- Sums -}
  right : List Value → Value               {- Sums -}


{- Consistency ----------------------------------------------------------------}

infix 5 _~_
infix 5 _≈_

_≈_ : List Value → List Value → Set
_~_ : Value → Value → Set
const {B} x ~ const {B₁} x₁ with base-eq? B B₁
... | yes refl = x ≡ x₁
... | no neq = False
const x ~ (x₁ ⊢ x₂ ↦ v) = False
const x ~ ν = False
const x ~ ω = False  
const x ~ ⦅ v , v₁ ⦆ = False
const x ~ ∥ x₁ ∥ = False
const x ~ left x₁ = False
const x ~ right x₁ = False
(x ⊢ x₁ ↦ u) ~ const x₂ = False
(us ⊢ v ↦ w) ~ (us₁ ⊢ v₁ ↦ w₁) = (¬ v ≈ v₁) ⊎ ( v ≈ v₁ × w ~ w₁ )
(x ⊢ x₁ ↦ u) ~ ν = True
(x ⊢ x₁ ↦ u) ~ ω = False
(x ⊢ x₁ ↦ u) ~ ⦅ v , v₁ ⦆ = False
(x ⊢ x₁ ↦ u) ~ ∥ x₂ ∥ = False
(x ⊢ x₁ ↦ u) ~ left x₂ = False
(x ⊢ x₁ ↦ u) ~ right x₂ = False
ν ~ const x = False
ν ~ (x ⊢ x₁ ↦ v) = True
ν ~ ν = True
ν ~ ω = False
ν ~ ⦅ v , v₁ ⦆ = False
ν ~ ∥ x ∥ = False
ν ~ left x = False
ν ~ right x = False
ω ~ const x = False
ω ~ (x ⊢ x₁ ↦ v) = False
ω ~ ν = False
ω ~ ω = True {- starting with ω related with just itself -}
ω ~ ⦅ v , v₁ ⦆ = False
ω ~ ∥ x ∥ = False
ω ~ left x = False
ω ~ right x = False
⦅ u , u₁ ⦆ ~ const x = False
⦅ u , u₁ ⦆ ~ (x ⊢ x₁ ↦ v) = False
⦅ u , u₁ ⦆ ~ ν = False
⦅ u , u₁ ⦆ ~ ω = False
⦅ u , u₁ ⦆ ~ ⦅ v , v₁ ⦆ = u ~ v × u₁ ~ v₁
⦅ u , u₁ ⦆ ~ ∥ x ∥ = False
⦅ u , u₁ ⦆ ~ left x = False
⦅ u , u₁ ⦆ ~ right x = False
∥ x ∥ ~ const x₁ = False
∥ x ∥ ~ (x₁ ⊢ x₂ ↦ v) = False
∥ x ∥ ~ ν = False
∥ x ∥ ~ ω = False
∥ x ∥ ~ ⦅ v , v₁ ⦆ = False
∥ [] ∥ ~ ∥ [] ∥ = True
∥ [] ∥ ~ ∥ x ∷ x₁ ∥ = False
∥ x ∷ x₂ ∥ ~ ∥ [] ∥ = False
∥ x ∷ xs ∥ ~ ∥ x₁ ∷ xs₁ ∥ = x ~ x₁ × ∥ xs ∥ ~ ∥ xs₁ ∥
∥ x ∥ ~ left x₁ = False
∥ x ∥ ~ right x₁ = False
left x ~ const x₁ = False
left x ~ (x₁ ⊢ x₂ ↦ v) = False
left x ~ ν = False
left x ~ ω = False
left x ~ ⦅ v , v₁ ⦆ = False
left x ~ ∥ x₁ ∥ = False
left x ~ left x₁ = x ≈ x₁
left x ~ right x₁ = False
right x ~ const x₁ = False
right x ~ (x₁ ⊢ x₂ ↦ v) = False
right x ~ ν = False
right x ~ ω = False
right x ~ ⦅ v , v₁ ⦆ = False
right x ~ ∥ x₁ ∥ = False
right x ~ left x₁ = False
right x ~ right x₁ = x ≈ x₁

[] ≈ vs = True 
(u ∷ us) ≈ vs = All (u ~_) vs × us ≈ vs

≈[] : ∀ V → V ≈ []
≈[] [] = tt
≈[] (x ∷ V) = ⟨ All.[] , ≈[] V ⟩

≈head : ∀ U v V → U ≈ (v ∷ V) → All (_~ v) U
≈head [] v V U~vV = []
≈head (x ∷ U) v V ⟨ x~v ∷ x~V , snd ⟩ = x~v ∷ ≈head U v V snd

≈tail : ∀ U v V → U ≈ (v ∷ V) → U ≈ V
≈tail [] v V U~vV = tt
≈tail (x ∷ U) v V ⟨ x~v ∷ x~V , snd ⟩ = 
  ⟨ x~V , ≈tail U v V snd ⟩


≈-sym : ∀ U V → U ≈ V → V ≈ U
~-sym-All : ∀ u V → All (_~ u) V → All (_~_ u) V
~-sym : ∀ u v → u ~ v → v ~ u
~-sym (const {B} x) (const {B₁} x₁) u~v 
  with base-eq? B B₁ | u~v
... | yes refl | refl = u~v
... | no neq | ()
~-sym (fvs ⊢ V ↦ w) (fvs' ⊢ V' ↦ w') (inj₁ ¬V~V') = 
  inj₁ λ z → ¬V~V' (≈-sym V' V z)
~-sym (fvs ⊢ V ↦ w) (fvs' ⊢ V' ↦ w') (inj₂ ⟨ V~V' , w~w' ⟩) = 
  inj₂ ⟨ ≈-sym V V' V~V' , ~-sym w w' w~w' ⟩
~-sym (x ⊢ x₁ ↦ u) ν u~v = tt
~-sym ν (x ⊢ x₁ ↦ v) u~v = tt
~-sym ν ν u~v = tt
~-sym ω ω u~v = tt
~-sym ⦅ u , u₁ ⦆ ⦅ v , v₁ ⦆ ⟨ fst , snd ⟩ = 
  ⟨ ~-sym u v fst , ~-sym u₁ v₁ snd ⟩
~-sym ∥ [] ∥ ∥ [] ∥ u~v = tt
~-sym ∥ x ∷ x₂ ∥ ∥ x₁ ∷ x₃ ∥ ⟨ fst , rst ⟩ = 
  ⟨ ~-sym x x₁ fst , ~-sym ∥ x₂ ∥ ∥ x₃ ∥ rst ⟩
~-sym (left x) (left x₁) u~v = ≈-sym x x₁ u~v
~-sym (right x) (right x₁) u~v = ≈-sym x x₁ u~v

~-sym-All u [] [] = []
~-sym-All u (x ∷ xs) (px ∷ V~u) = 
  ~-sym x u px ∷ ~-sym-All u xs V~u

≈-sym U [] U≈V = tt
≈-sym U (x ∷ V) U≈V = 
  ⟨ ~-sym-All x U (≈head U x V U≈V) 
  , ≈-sym U V (≈tail U x V U≈V) ⟩

_×dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A × B)
(yes a) ×dec (yes b) = yes ⟨ a , b ⟩
(yes a) ×dec (no b) = no (λ z → b (proj₂ z))
(no a) ×dec decb = no (λ z → a (proj₁ z))

_≈?_ : (U V : List Value) → Dec (U ≈ V)
_~>?_ : (u : Value) (V : List Value) → Dec (All (u ~_) V)
_~?_ : (u v : Value) → Dec (u ~ v)
const {B} x ~? const {B'} x₁ with base-eq? B B'
... | no neq = no (λ z → z)
... | yes refl = base-rep-eq? x x₁
const x ~? (x₁ ⊢ x₂ ↦ v) = no (λ z → z)
const x ~? ν = no (λ z → z)
const x ~? ω = no (λ z → z)
const x ~? ⦅ v , v₁ ⦆ = no (λ z → z)
const x ~? ∥ x₁ ∥ = no (λ z → z)
const x ~? left x₁ = no (λ z → z)
const x ~? right x₁ = no (λ z → z)
(x ⊢ x₁ ↦ u) ~? const x₂ = no (λ z → z)
(fvs ⊢ V ↦ w) ~? (fvs' ⊢ V' ↦ w') with V ≈? V'
... | no ¬V~V' = yes (inj₁ ¬V~V')
... | yes V~V' with w ~? w'
... | no ¬w~w' = no (λ z → [ (λ x → x V~V') 
                           , (λ x → ¬w~w' (proj₂ x)) ] z )
... | yes w~w' = yes (inj₂ ⟨ V~V' , w~w' ⟩)
(x ⊢ x₁ ↦ u) ~? ν = yes tt
(x ⊢ x₁ ↦ u) ~? ω = no (λ z → z)
(x ⊢ x₁ ↦ u) ~? ⦅ v , v₁ ⦆ = no (λ z → z)
(x ⊢ x₁ ↦ u) ~? ∥ x₂ ∥ = no (λ z → z)
(x ⊢ x₁ ↦ u) ~? left x₂ = no (λ z → z)
(x ⊢ x₁ ↦ u) ~? right x₂ = no (λ z → z)
ν ~? const x = no (λ z → z)
ν ~? (x ⊢ x₁ ↦ v) = yes tt
ν ~? ν = yes tt
ν ~? ω = no (λ z → z)
ν ~? ⦅ v , v₁ ⦆ = no (λ z → z)
ν ~? ∥ x ∥ = no (λ z → z)
ν ~? left x = no (λ z → z)
ν ~? right x = no (λ z → z)
ω ~? const x = no (λ z → z)
ω ~? (x ⊢ x₁ ↦ v) = no (λ z → z)
ω ~? ν = no (λ z → z)
ω ~? ω = yes tt
ω ~? ⦅ v , v₁ ⦆ = no (λ z → z)
ω ~? ∥ x ∥ = no (λ z → z)
ω ~? left x = no (λ z → z)
ω ~? right x = no (λ z → z)
⦅ u , u₁ ⦆ ~? const x = no (λ z → z)
⦅ u , u₁ ⦆ ~? (x ⊢ x₁ ↦ v) = no (λ z → z)
⦅ u , u₁ ⦆ ~? ν = no (λ z → z)
⦅ u , u₁ ⦆ ~? ω = no (λ z → z)
⦅ u , u₁ ⦆ ~? ⦅ v , v₁ ⦆ = (u ~? v) ×dec (u₁ ~? v₁)
⦅ u , u₁ ⦆ ~? ∥ x ∥ = no (λ z → z)
⦅ u , u₁ ⦆ ~? left x = no (λ z → z)
⦅ u , u₁ ⦆ ~? right x = no (λ z → z)
∥ x ∥ ~? const x₁ = no (λ z → z)
∥ x ∥ ~? (x₁ ⊢ x₂ ↦ v) = no (λ z → z)
∥ x ∥ ~? ν = no (λ z → z)
∥ x ∥ ~? ω = no (λ z → z)
∥ x ∥ ~? ⦅ v , v₁ ⦆ = no (λ z → z)
∥ [] ∥ ~? ∥ [] ∥ = yes tt
∥ [] ∥ ~? ∥ x ∷ x₁ ∥ = no (λ z → z)
∥ x ∷ x₂ ∥ ~? ∥ [] ∥ = no (λ z → z)
∥ x ∷ x₂ ∥ ~? ∥ x₁ ∷ x₃ ∥ = (x ~? x₁) ×dec (∥ x₂ ∥ ~? ∥ x₃ ∥)
∥ x ∥ ~? left x₁ = no (λ z → z)
∥ x ∥ ~? right x₁ = no (λ z → z)
left x ~? const x₁ = no (λ z → z)
left x ~? (x₁ ⊢ x₂ ↦ v) = no (λ z → z)
left x ~? ν = no (λ z → z)
left x ~? ω = no (λ z → z)
left x ~? ⦅ v , v₁ ⦆ = no (λ z → z)
left x ~? ∥ x₁ ∥ = no (λ z → z)
left x ~? left x₁ = x ≈? x₁
left x ~? right x₁ = no (λ z → z)
right x ~? const x₁ = no (λ z → z)
right x ~? (x₁ ⊢ x₂ ↦ v) = no (λ z → z)
right x ~? ν = no (λ z → z)
right x ~? ω = no (λ z → z)
right x ~? ⦅ v , v₁ ⦆ = no (λ z → z)
right x ~? ∥ x₁ ∥ = no (λ z → z)
right x ~? left x₁ = no (λ z → z)
right x ~? right x₁ = x ≈? x₁

u ~>? [] = yes All.[]
u ~>? (x ∷ V) with u ~? x
... | no ¬u~x = no (λ z → ¬u~x (head z))
... | yes u~x with u ~>? V 
... | no ¬u~V = no λ z → ¬u~V (tail z)
... | yes U~V = yes (u~x All.∷ U~V)

[] ≈? V = yes tt
(x ∷ U) ≈? V with x ~>? V
... | no ¬x~V = no (λ z → ¬x~V (proj₁ z))
... | yes x~V with U ≈? V
... | no ¬U~V = no (λ z → ¬U~V (proj₂ z))
... | yes U~V = yes ⟨ x~V , U~V ⟩



≈⇒Every : ∀ A B → A ≈ B → Every _~_ (mem A) (mem B)
≈⇒Every (x ∷ A) B ⟨ x~B , A~B ⟩ a b (here refl) b∈B = 
  lookup x~B b∈B
≈⇒Every (x ∷ A) B ⟨ x~B , A~B ⟩ a b (there a∈A) b∈B = 
  ≈⇒Every A B A~B a b a∈A b∈B

Every⇒≈ : ∀ A B → Every _~_ (mem A) (mem B) → A ≈ B
Every⇒≈ [] B A~B = tt
Every⇒≈ (x ∷ A) B A~B = 
  ⟨ tabulate (λ {b} b∈B → A~B x b (here refl) b∈B) 
  , Every⇒≈ A B (λ a b a∈A b∈B → A~B a b (there a∈A) b∈B) ⟩

{- Denotational Operators -----------------------------------------------------}

{-
_⋆_  Λ  cons  car  cdr  ℒ  ℛ  𝒞  (proj i)  (𝒯' n)  (𝒯 n)  Λ'  Λ′
-}

infix 10 _⋆_  {- \st -}
_⋆_ : DenotOp (𝒫 Value) (■ ∷ ■ ∷ [])
D₁ ⋆ D₂ = λ w → Σ[ V ∈ List Value ] Σ[ fvs ∈ List Value ] (fvs ⊢ V ↦ w ∈ D₁)
                  ×  (mem V ⊆ D₂)  ×  V ≢ []

ℬ : (B : Base) → base-rep B → DenotOp (𝒫 Value) []
ℬ B k (const {B′} k′)
    with base-eq? B B′
... | yes refl = k ≡ k′
... | no neq = False
ℬ B k _ = False

𝓅 : (P : Prim) → rep P → DenotOp (𝒫 Value) []
𝓅 (base B) k v = ℬ B k v
𝓅 (B ⇒ P) f (const k) = False
𝓅 (B ⇒ P) f (fvs ⊢ V ↦ w) =
   Σ[ k ∈ base-rep B ] V ≡ (const {B} k) ∷ []  ×  w ∈ 𝓅 P (f k)
𝓅 (B ⇒ P) f ν = True
𝓅 (B ⇒ P) f ω = False
𝓅 (B ⇒ P) k ⦅ u , v ⦆ = False
𝓅 (B ⇒ P) k ∥ vs ∥ = False
𝓅 (B ⇒ P) k (left V) = False
𝓅 (B ⇒ P) k (right V) = False


⟪_,_⟫ : DenotOp (𝒫 Value) (■ ∷ ■ ∷ [])
⟪ D₁ , D₂ ⟫ ⦅ u , v ⦆ = u ∈ D₁ × v ∈ D₂
⟪ D₁ , D₂ ⟫ _ = False

car : DenotOp (𝒫 Value) (■ ∷ [])
car D u = Σ[ v ∈ Value ] ⦅ u , v ⦆ ∈ D

cdr : DenotOp (𝒫 Value) (■ ∷ [])
cdr D v = Σ[ u ∈ Value ] ⦅ u , v ⦆ ∈ D

𝒯-cons : DenotOp (𝒫 Value) (■ ∷ ■ ∷ [])
𝒯-cons D 𝒯Ds ∥ d ∷ ds ∥ = d ∈ D × ∥ ds ∥ ∈ 𝒯Ds
𝒯-cons D 𝒯Ds d = False

𝒯 : ∀ n → DenotOp (𝒫 Value) (replicate n ■)
𝒯 n = Dfold ■ ■ n 𝒯-cons ⌈ ∥ [] ∥ ⌉

{-
𝒯 : ∀ n → DenotOp (𝒫 Value) (replicate n ■)
𝒯 zero ∥ [] ∥ = True
𝒯 zero d = False
𝒯 (suc n) D = DComp-n-1 (replicate n ■) ■ ■ (𝒯 n) (𝒯-cons D)
-}

𝒜-cons : DenotOp (𝒫 Value) (■ ∷ ■ ∷ [])
𝒜-cons D F ((fv ∷ fvs) ⊢ V ↦ w) = fv ∈ D × fvs ⊢ V ↦ w ∈ F
𝒜-cons D F d = False

{-
𝒜 : ∀ (n : ℕ) → DenotOp (𝒫 Value) (■ ∷ replicate n ■)
𝒜 zero F = F
𝒜 (suc n) F D = DComp-n-1 (replicate n ■) ■ ■ (𝒜 n F) (𝒜-cons D)
-}

𝒜 : ∀ n → DenotOp (𝒫 Value) (■ ∷ replicate n ■)
𝒜 n F = Dfold ■ ■ n 𝒜-cons F

nth : List Value → ℕ → Value
nth [] i = ω
nth (v ∷ vs) 0 = v
nth (v ∷ vs) (suc i) = nth vs i

proj : ℕ → DenotOp (𝒫 Value) (■ ∷ [])
proj i D u = Σ[ vs ∈ List Value ]
    i < length vs  ×  ∥ vs ∥ ∈ D  ×  u ≡ nth vs i

ℒ : DenotOp (𝒫 Value) (■ ∷ [])
ℒ D (left V) = V ≢ []  ×  mem V ⊆ D
ℒ D _ = False

ℛ : DenotOp (𝒫 Value) (■ ∷ [])
ℛ D (right V) = V ≢ []  ×  mem V ⊆ D
ℛ D _ = False

𝒞 : DenotOp (𝒫 Value) (■ ∷ ■ ∷ ■ ∷ [])
𝒞 D E F w = (Σ[ V ∈ List Value ] Σ[ fvs ∈ List Value ]
                 left V ∈ D  ×  fvs ⊢ V ↦ w ∈ E)
          ⊎ (Σ[ V ∈ List Value ] Σ[ fvs ∈ List Value ]
                 right V ∈ D  ×  fvs ⊢ V ↦ w ∈ F)

𝒞-new : DenotOp (𝒫 Value) (■ ∷ ν ■ ∷ ν ■ ∷ [])
𝒞-new D E F w = Σ[ V ∈ List Value ] left V ∈ D × w ∈ E (mem V) 
          ⊎ (Σ[ V ∈ List Value ] right V ∈ D × w ∈ F (mem V))

Λ : DenotOp (𝒫 Value) (ν ■ ∷ [])
Λ f (const k) = False
Λ f ([] ⊢ V ↦ w) = w ∈ f (mem V)  ×  V ≢ []
Λ f ((b ∷ bs) ⊢ V ↦ w) = False
Λ f ν = True
Λ f ω = False
Λ f ⦅ u , v ⦆ = False
Λ f ∥ vs ∥ = False
Λ f (left V) = False
Λ f (right V) = False



{-

Λ' : ∀ (n : ℕ) → (𝒫 Value → 𝒫 Value) → Π n (𝒫 Value)
               → 𝒫 Value
Λ' n ⟦fvs⟧ f (const k) = False
Λ' n ⟦fvs⟧ f (fvs ⊢ V ↦ w) = w ∈ f (mem V) × V ≢ [] × Σ[ n≡ ∈ n ≡ length fvs ]
                            rel-Π (_⊆_) (Π-map mem (toΠ fvs)) 
                                        (subst (λ z → Π z (𝒫 Value)) n≡ ⟦fvs⟧)
Λ' n ⟦fvs⟧ f ν = True
Λ' n ⟦fvs⟧ f ω = False
Λ' n ⟦fvs⟧ f ⦅ v , v₁ ⦆ = False
Λ' n ⟦fvs⟧ f ∥ x ∥ = False
Λ' n ⟦fvs⟧ f (left x) = False
Λ' n ⟦fvs⟧ f (right x) = False

Λ′ : ∀ (n : ℕ) → DenotOp (𝒫 Value) (ν ■ ∷ replicate n ■)
Λ′ n f = curryFun (Λ' n f)

-}

{- Monotonicity and congruence of operators --------------------------------------------------}

⋆-mono : monotone (■ ∷ ■ ∷ []) ■ _⋆_
⋆-mono D D' (lift D⊆) E E' (lift E⊆) = lift G
  where
  G : D ⋆ E ⊆ D' ⋆ E'
  G d ⟨ V , ⟨ fvs , ⟨ wv∈D , ⟨ V<E , Vne ⟩ ⟩ ⟩ ⟩ =
     ⟨ V , ⟨ fvs , ⟨ D⊆ (fvs ⊢ V ↦ d) wv∈D , ⟨ (λ d z → E⊆ d (V<E d z)) , Vne ⟩ ⟩ ⟩ ⟩

⋆-cong : congruent (■ ∷ ■ ∷ []) ■ _⋆_
⋆-cong D D' (lift ⟨ D<D' , D'<D ⟩) E E' (lift ⟨ E<E' , E'<E ⟩) = lift G
  where
  G : D ⋆ E ≃ D' ⋆ E'
  G = ⟨ lower (⋆-mono D D' (lift D<D') E E' (lift E<E')) 
      , lower (⋆-mono D' D (lift D'<D) E' E (lift E'<E)) ⟩

Λ-mono : monotone (ν ■ ∷ []) ■ Λ
Λ-mono F F' F⊆ = lift G
  where 
  G : Λ F ⊆ Λ F'
  G ([] ⊢ V ↦ w) ⟨ w∈F₁X , V≢[] ⟩ = 
    ⟨ lower (F⊆ (mem V) (mem V) (λ d z → z)) w w∈F₁X , V≢[] ⟩
  G ν v∈ = tt

Λ-ext-⊆ : ∀{F₁ F₂ : (𝒫 Value) → (𝒫 Value)}
  → (∀ {X} → F₁ X ⊆ F₂ X)
  → Λ F₁ ⊆ Λ F₂
Λ-ext-⊆ {F₁} {F₂} F₁⊆F₂ ([] ⊢ V ↦ w) ⟨ w∈F₁X , V≢[] ⟩ =
    ⟨ F₁⊆F₂ w w∈F₁X , V≢[] ⟩
Λ-ext-⊆ {F₁} {F₂} F₁⊆F₂ ν v∈ = tt

Λ-ext : ∀{F₁ F₂ : (𝒫 Value) → (𝒫 Value)}
  → (∀ {X} → F₁ X ≃ F₂ X)
  → Λ F₁ ≃ Λ F₂
Λ-ext {F₁}{F₂} F₁≃F₂ = ⟨ Λ-ext-⊆ (proj₁ F₁≃F₂) , Λ-ext-⊆ (proj₂ F₁≃F₂) ⟩

Λ-cong : congruent (ν ■ ∷ []) ■ Λ
Λ-cong F F' F≃ = lift ⟨ G1 , G2 ⟩
  where
  G1 : Λ F ⊆ Λ F'
  G1 ([] ⊢ V ↦ w) ⟨ w∈FV , Vne ⟩ = ⟨ proj₁ (lower
     (F≃ (mem V) (mem V)
          ⟨ (λ x x₁ → x₁) , (λ x x₁ → x₁) ⟩))
             w w∈FV , Vne ⟩
  G1 ν tt = tt
  G2 : Λ F' ⊆ Λ F
  G2 ([] ⊢ V ↦ w) ⟨ w∈F'V , Vne ⟩ = ⟨  proj₂ (lower 
     (F≃ (mem V) (mem V) 
         ⟨ (λ x x₁ → x₁) , (λ x x₁ → x₁) ⟩)) 
         w w∈F'V  , Vne  ⟩
  G2 ν tt = tt

cons-mono : monotone (■ ∷ ■ ∷ []) ■ ⟪_,_⟫
cons-mono D D' (lift D⊆) E E' (lift E⊆) = lift G
  where
  G : ⟪ D , E ⟫ ⊆ ⟪ D' , E' ⟫
  G ⦅ u , v ⦆ ⟨ u∈D , v∈E ⟩ = ⟨ D⊆ u u∈D , E⊆ v v∈E ⟩

cons-cong : congruent (■ ∷ ■ ∷ []) ■ ⟪_,_⟫
cons-cong D D' (lift ⟨ D<D' , D'<D ⟩) E E' (lift ⟨ E<E' , E'<E ⟩) = lift G
  where
  G : ⟪ D , E ⟫ ≃ ⟪ D' , E' ⟫
  G = ⟨ lower (cons-mono D D' (lift D<D') E E' (lift E<E')) 
      , lower (cons-mono D' D (lift D'<D) E' E (lift E'<E)) ⟩

car-mono : monotone (■ ∷ []) ■ car
car-mono D D' (lift D⊆) = lift G
  where
  G : car D ⊆ car D'
  G u ⟨ v , uv∈D ⟩ = ⟨ v , D⊆ ⦅ u , v ⦆ uv∈D ⟩

car-cong : congruent (■ ∷ []) ■ car
car-cong D D' (lift ⟨ D<D' , D'<D ⟩) = lift G
  where
  G : car D ≃ car D'
  G = ⟨ lower (car-mono D D' (lift D<D')) 
      , lower (car-mono D' D (lift D'<D)) ⟩

cdr-mono : monotone (■ ∷ []) ■ cdr
cdr-mono D D' (lift D⊆) = lift G
  where
  G : cdr D ⊆ cdr D'
  G v ⟨ u , uv∈D ⟩ = ⟨ u , D⊆ ⦅ u , v ⦆ uv∈D ⟩

cdr-cong : congruent (■ ∷ []) ■ cdr
cdr-cong D D' (lift ⟨ D<D' , D'<D ⟩) = lift G
  where
  G : cdr D ≃ cdr D'
  G = ⟨ lower (cdr-mono D D' (lift D<D')) 
      , lower (cdr-mono D' D (lift D'<D)) ⟩


ℒ-mono : monotone (■ ∷ []) ■ ℒ
ℒ-mono D D' (lift D⊆) = lift G
  where
  G : ℒ D ⊆ ℒ D'
  G (left V) ⟨ Vne , V∈ ⟩ = ⟨ Vne , (λ d z → D⊆ d (V∈ d z)) ⟩

ℒ-cong : congruent (■ ∷ []) ■ ℒ
ℒ-cong D D' (lift ⟨ D<D' , D'<D ⟩) = lift G
  where
  G : ℒ D ≃ ℒ D'
  G = ⟨ lower (ℒ-mono D D' (lift D<D')) 
      , lower (ℒ-mono D' D (lift D'<D)) ⟩

ℛ-mono : monotone (■ ∷ []) ■ ℛ
ℛ-mono D D' (lift D⊆) = lift G
  where
  G : ℛ D ⊆ ℛ D'
  G (right V) ⟨ Vne , V∈ ⟩ = ⟨ Vne , (λ d z → D⊆ d (V∈ d z)) ⟩

ℛ-cong : congruent (■ ∷ []) ■ ℛ
ℛ-cong D D' (lift ⟨ D<D' , D'<D ⟩) = lift G
  where
  G : ℛ D ≃ ℛ D'
  G = ⟨ lower (ℛ-mono D D' (lift D<D')) 
      , lower (ℛ-mono D' D (lift D'<D)) ⟩

𝒞-mono : monotone (■ ∷ ■ ∷ ■ ∷ []) ■ 𝒞
𝒞-mono D D' (lift D⊆) FL FL' (lift FL⊆) FR FR' (lift FR⊆) = lift G
  where
  G : 𝒞 D FL FR ⊆ 𝒞 D' FL' FR'
  G d (inj₁ ⟨ V , ⟨ fvs , ⟨ inlV∈ , v∈ ⟩ ⟩ ⟩) = 
    inj₁ ⟨ V , ⟨ fvs , ⟨ D⊆ (left V) inlV∈ , FL⊆ (fvs ⊢ V ↦ d) v∈ ⟩ ⟩ ⟩
  G d (inj₂ ⟨ V , ⟨ fvs , ⟨ inrV∈ , v∈ ⟩ ⟩ ⟩) = 
    inj₂ ⟨ V , ⟨ fvs , ⟨ D⊆ (right V) inrV∈ , FR⊆ (fvs ⊢ V ↦ d) v∈ ⟩ ⟩ ⟩

𝒞-new-mono : monotone (■ ∷ ν ■ ∷ ν ■ ∷ []) ■ 𝒞-new
𝒞-new-mono D D' (lift D⊆) FL FL' FL⊆ FR FR' FR⊆ = lift G
  where 
  G : 𝒞-new D FL FR ⊆ 𝒞-new D' FL' FR'
  G d (inj₁ ⟨ V , ⟨ V∈ , d∈ ⟩ ⟩) = 
    inj₁ ⟨ V , ⟨ D⊆ (left V) V∈ 
         , lower (FL⊆ (mem V) (mem V) (λ d z → z)) d d∈ ⟩ ⟩
  G d (inj₂ ⟨ V , ⟨ V∈ , d∈ ⟩ ⟩) = 
    inj₂ ⟨ V , ⟨ D⊆ (right V) V∈ 
         , lower (FR⊆ (mem V) (mem V) (λ d z → z)) d d∈ ⟩ ⟩

𝒞-cong : congruent (■ ∷ ■ ∷ ■ ∷ []) ■ 𝒞
𝒞-cong D D' (lift ⟨ D<D' , D'<D ⟩) FL FL' (lift ⟨ FL<FL' , FL'<FL ⟩)
                                  FR FR' (lift ⟨ FR<FR' , FR'<FR ⟩) = lift G
  where
  G : 𝒞 D FL FR ≃ 𝒞 D' FL' FR'
  G = ⟨ lower (𝒞-mono D D' (lift D<D') FL FL' (lift FL<FL') FR FR' (lift FR<FR')) 
      , lower (𝒞-mono D' D (lift D'<D) FL' FL (lift FL'<FL) FR' FR (lift FR'<FR)) ⟩

proj-mono : ∀ i → monotone (■ ∷ []) ■ (proj i)
proj-mono i D D' (lift D⊆) = lift G
  where
  G : proj i D ⊆ proj i D'
  G d ⟨ vs , ⟨ i< , ⟨ vs∈ , refl ⟩ ⟩ ⟩ = ⟨ vs , ⟨ i< , ⟨ D⊆ ∥ vs ∥ vs∈ , refl ⟩ ⟩ ⟩

proj-cong : ∀ i → congruent (■ ∷ []) ■ (proj i)
proj-cong i D D' (lift ⟨ D<D' , D'<D ⟩) = lift G
  where
  G : proj i D ≃ proj i D'
  G = ⟨ lower (proj-mono i D D' (lift D<D')) 
      , lower (proj-mono i D' D (lift D'<D)) ⟩

𝒯-cons-mono : monotone (■ ∷ ■ ∷ []) ■ 𝒯-cons
𝒯-cons-mono D D' (lift D⊆) E E' (lift E⊆) = lift G
  where
  G : 𝒯-cons D E ⊆ 𝒯-cons D' E'
  G ∥ d ∷ ds ∥ ⟨ d∈ , ds∈ ⟩ = ⟨ D⊆ d d∈ , E⊆ ∥ ds ∥ ds∈ ⟩

𝒯-mono : ∀ n → monotone (replicate n ■) ■ (𝒯 n)
𝒯-mono n = Dfold-pres _⊆_ ■ ■ n 𝒯-cons 𝒯-cons ⌈ ∥ [] ∥ ⌉ ⌈ ∥ [] ∥ ⌉  
           𝒯-cons-mono (lift (λ d z → z))

{-
𝒯-mono : ∀ n → monotone (replicate n ■) ■ (𝒯 n)
𝒯-mono zero = lift (λ d z → z)
𝒯-mono (suc n) D D' (lift D⊆) = 
  DComp-n-1-pres _⊆_ (replicate n ■) ■ ■ (𝒯 n) (𝒯 n) (𝒯-cons D) (𝒯-cons D') 
                 (𝒯-mono n) (𝒯-cons-mono D D' (lift D⊆))
-}

𝒜-cons-mono : monotone (■ ∷ ■ ∷ []) ■ 𝒜-cons
𝒜-cons-mono D D' (lift D⊆) E E' (lift E⊆) = lift G
  where
  G : 𝒜-cons D E ⊆ 𝒜-cons D' E'
  G ((fv ∷ fvs) ⊢ V ↦ w) ⟨ fv∈ , d∈ ⟩ = 
    ⟨ D⊆ fv fv∈ , E⊆ (fvs ⊢ V ↦ w) d∈ ⟩

𝒜-mono : ∀ n → monotone (■ ∷ replicate n ■) ■ (𝒜 n)
𝒜-mono n F F' (lift F⊆) = Dfold-pres _⊆_ ■ ■ n 𝒜-cons 𝒜-cons F F' 
  𝒜-cons-mono (lift F⊆)

{-
𝒜-mono : ∀ n → monotone (■ ∷ replicate n ■) ■ (𝒜 n)
𝒜-mono zero F F' F⊆ = F⊆
𝒜-mono (suc n) F F' (lift F⊆) D D' (lift D⊆) = 
  DComp-n-1-pres _⊆_ (replicate n ■) ■ ■ (𝒜 n F) (𝒜 n F') (𝒜-cons D) (𝒜-cons D') 
    (𝒜-mono n F F' (lift F⊆)) (𝒜-cons-mono D D' (lift D⊆))
-}


{-

𝒯'-mono : ∀{n}(Ds Es : Π n (𝒫 Value)) → Ds ⫃ Es → 𝒯' n Ds ⊆ 𝒯' n Es
𝒯'-mono {zero} _ _ Ds⊆Es v v∈ = v∈
𝒯'-mono {suc n} ⟨ D , Ds ⟩ ⟨ E , Es ⟩ ⟨ D⊆E , Ds⊆Es ⟩ ∥ v ∷ vs ∥
    ⟨ v∈D , vs∈𝒯Ds ⟩ = ⟨ (D⊆E v v∈D) , (𝒯'-mono Ds Es Ds⊆Es ∥ vs ∥ vs∈𝒯Ds) ⟩

𝒯-mono : ∀ n → monotone (replicate n ■) ■ (𝒯 n)
𝒯-mono n = curry-rel n _⊆_ (𝒯' n) (𝒯' n) (𝒯'-mono {n})

𝒯'-cong : ∀ {n} (Ds Es : Π n (𝒫 Value)) → Ds ⩭ Es → 𝒯' n Ds ≃ 𝒯' n Es
𝒯'-cong {n} Ds Es Ds=Es with ⩭⇒⊆ Ds=Es
... | ⟨ Ds⊆Es , Es⊆Ds ⟩ =    
  ⟨ 𝒯'-mono Ds Es Ds⊆Es , 𝒯'-mono Es Ds Es⊆Ds ⟩

𝒯-cong : ∀ n → congruent (replicate n ■) ■ (𝒯 n)
𝒯-cong n = curry-rel n _≃_ (𝒯' n) (𝒯' n) (𝒯'-cong {n})

Λ'-mono : ∀ n F G → result-rel-pres _⊆_ (ν ■) F G → ∀ (Ds Es : Π n (𝒫 Value)) 
                  → rel-Π _⊆_ Ds Es → Λ' n Ds F ⊆ Λ' n Es G
Λ'-mono n F G F⊆ Ds Es Ds⊆ ν d∈ = d∈
Λ'-mono n F G F⊆ Ds Es Ds⊆ (fvs ⊢ V ↦ w) ⟨ w∈ , ⟨ Vne , ⟨ refl , fvs⊆Ds ⟩ ⟩ ⟩ = 
      ⟨ lower (F⊆ (mem V) (mem V) (λ x z → z)) w w∈ 
      , ⟨ Vne , ⟨ refl , helper fvs Ds Es Ds⊆ fvs⊆Ds ⟩ ⟩ ⟩
  where
  helper : ∀ fvs (Ds Es : Π (length fvs) (𝒫 Value))
      → rel-Π _⊆_ Ds Es
      → rel-Π _⊆_ (Π-map mem (toΠ fvs)) Ds
      → rel-Π _⊆_ (Π-map mem (toΠ fvs)) Es
  helper [] Ds Es Ds⊆Es fvs⊆Ds = tt
  helper (fv ∷ fvs) ⟨ D , Ds ⟩ ⟨ E , Es ⟩ ⟨ D⊆E , Ds⊆Es ⟩ ⟨ fv⊆D , fvs⊆Ds ⟩ = 
    ⟨ (λ d z → D⊆E d (fv⊆D d z)) , helper fvs Ds Es Ds⊆Es fvs⊆Ds ⟩

Λ′-mono : ∀ n → monotone (ν ■ ∷ replicate n ■) ■ (Λ′ n)
Λ′-mono n F G F⊆ = curry-rel n _⊆_ (λ z → Λ' n z F) (λ z → Λ' n z G) (Λ'-mono n F G F⊆)

-}



{- Consistency ----------------------------------------------------------------}

⋆-consis : fun-consistent _~_ (■ ∷ ■ ∷ []) ■ _⋆_
⋆-consis D D' (lift D~) E E' (lift E~) = lift G
  where
  G : Every _~_ (D ⋆ E) (D' ⋆ E')
  G u v ⟨ V , ⟨ fvs , ⟨ wv∈D , ⟨ V<E , Vne ⟩ ⟩ ⟩ ⟩ 
        ⟨ V' , ⟨ fvs' , ⟨ wv∈D' , ⟨ V<E' , Vne' ⟩ ⟩ ⟩ ⟩ 
        with D~ (fvs ⊢ V ↦ u) (fvs' ⊢ V' ↦ v) wv∈D wv∈D'
  ... | inj₁ x = ⊥-elim (x (Every⇒≈ V V' (Every-⊆ E~ V<E V<E')))
  ... | inj₂ y = proj₂ y

Λ-consis : fun-consistent _~_ (ν ■ ∷ []) ■ Λ
Λ-consis F F' F~ = lift G
  where
  G : Every _~_ (Λ F) (Λ F')
  G ν (x ⊢ x₁ ↦ v) tt _ = tt
  G ν ν tt _ = tt
  G ([] ⊢ V ↦ w) ν ⟨ w∈F₁X , V≢[] ⟩ tt = tt
  G ([] ⊢ V ↦ w) ([] ⊢ V' ↦ w') 
    ⟨ w∈F₁X , V≢[] ⟩ ⟨ w∈F₁X' , V≢[]' ⟩ with V ≈? V'
  ... | yes V≈V' = 
    inj₂ ⟨ V≈V' , lower (F~ (mem V) (mem V') (≈⇒Every V V' V≈V')) w w' w∈F₁X w∈F₁X' ⟩
  ... | no ¬V≈V' = inj₁ ¬V≈V'

cons-consis : fun-consistent _~_ (■ ∷ ■ ∷ []) ■ ⟪_,_⟫
cons-consis D D' (lift D~) E E' (lift E~) = lift G
  where
  G : Every _~_ ⟪ D , E ⟫  ⟪ D' , E' ⟫
  G ⦅ u , v ⦆ ⦅ u' , v' ⦆ ⟨ u∈D , v∈D ⟩ ⟨ u'∈D' , v'∈D' ⟩
    = ⟨ D~ u u' u∈D u'∈D' , E~ v v' v∈D v'∈D' ⟩

car-consis : fun-consistent _~_ (■ ∷ []) ■ car
car-consis D D' (lift D~) = lift G
  where
  G : Every _~_ (car D) (car D')
  G u u' ⟨ v , uv∈D ⟩ ⟨ v' , u'v'∈D' ⟩ 
    with D~ ⦅ u , v ⦆ ⦅ u' , v' ⦆ uv∈D u'v'∈D'
  ... | ⟨ u~ , v~ ⟩ = u~

cdr-consis : fun-consistent _~_ (■ ∷ []) ■ cdr
cdr-consis D D' (lift D~) = lift G
  where
  G : Every _~_ (cdr D) (cdr D')
  G v v' ⟨ u , uv∈D ⟩ ⟨ u' , u'v'∈D' ⟩ 
    with D~ ⦅ u , v ⦆ ⦅ u' , v' ⦆ uv∈D u'v'∈D'
  ... | ⟨ u~ , v~ ⟩ = v~

ℒ-consis : fun-consistent _~_ (■ ∷ []) ■ ℒ
ℒ-consis D D' (lift D~) = lift G
  where
  G : Every _~_ (ℒ D) (ℒ D')
  G (left U) (left V) ⟨ Une , U∈ ⟩ ⟨ Vne , V∈ ⟩ 
    = Every⇒≈ U V (Every-⊆  D~ U∈ V∈)

ℛ-consis : fun-consistent _~_ (■ ∷ []) ■ ℛ
ℛ-consis D D' (lift D~) = lift G
  where
  G : Every _~_ (ℛ D) (ℛ D')
  G (right U) (right V) ⟨ Une , U∈ ⟩ ⟨ Vne , V∈ ⟩ 
    = Every⇒≈ U V (Every-⊆  D~ U∈ V∈)

𝒞-consis : fun-consistent _~_ (■ ∷ ■ ∷ ■ ∷ []) ■ 𝒞
𝒞-consis D D' (lift D~) FL FL' (lift FL~) FR FR' (lift FR~) = lift G
  where
  G : Every _~_ (𝒞 D FL FR) (𝒞 D' FL' FR')
  G u v (inj₁ ⟨ V , ⟨ fvs , ⟨ inlV∈ , v∈ ⟩ ⟩ ⟩)
        (inj₁ ⟨ V' , ⟨ fvs' , ⟨ inlV∈' , v∈' ⟩ ⟩ ⟩) 
    with FL~ (fvs ⊢ V ↦ u) (fvs' ⊢ V' ↦ v) v∈ v∈'
  ... | inj₂ y = proj₂ y
  ... | inj₁ x with D~ (left V) (left V') inlV∈ inlV∈' 
  ... | q = ⊥-elim (x q)
  G u v (inj₁ ⟨ V , ⟨ fvs , ⟨ inlV∈ , u∈ ⟩ ⟩ ⟩) 
        (inj₂ ⟨ V' , ⟨ fvs' , ⟨ inrV∈' , v∈ ⟩ ⟩ ⟩) = 
        ⊥-elim (D~ (left V) (right V') inlV∈ inrV∈')
  G u v (inj₂ ⟨ V , ⟨ fvs , ⟨ inrV∈ , u∈ ⟩ ⟩ ⟩) 
        (inj₁ ⟨ V' , ⟨ fvs' , ⟨ inlV∈' , v∈ ⟩ ⟩ ⟩) = 
        ⊥-elim (D~ (right V) (left V') inrV∈ inlV∈')
  G u v (inj₂ ⟨ V , ⟨ fvs , ⟨ inrV∈ , u∈ ⟩ ⟩ ⟩) 
        (inj₂ ⟨ V' , ⟨ fvs' , ⟨ inrV∈' , v∈ ⟩ ⟩ ⟩) 
    with FR~ (fvs ⊢ V ↦ u) (fvs' ⊢ V' ↦ v) u∈ v∈ 
  ... | inj₂ y = proj₂ y
  ... | inj₁ x with D~ (right V) (right V') inrV∈ inrV∈'
  ... | q = ⊥-elim (x q)


𝒞-new-consis : fun-consistent _~_ (■ ∷ ν ■ ∷ ν ■ ∷ []) ■ 𝒞-new
𝒞-new-consis D D' (lift D~) FL FL' FL~ FR FR' FR~ = lift G
  where 
  G : Every _~_ (𝒞-new D FL FR) (𝒞-new D' FL' FR')
  G u v (inj₁ ⟨ V , ⟨ V∈ , u∈ ⟩ ⟩) (inj₁ ⟨ V' , ⟨ V∈' , v∈ ⟩ ⟩)
   with D~ (left V) (left V') V∈ V∈'
  ... | V≈V' with FL~ (mem V) (mem V') (≈⇒Every V V' V≈V')
  ... | lift FL-V~ = FL-V~ u v u∈ v∈
  G u v (inj₁ ⟨ V , ⟨ V∈ , u∈ ⟩ ⟩) (inj₂ ⟨ V' , ⟨ V∈' , v∈ ⟩ ⟩) = 
    ⊥-elim (D~ (left V) (right V') V∈ V∈')
  G u v (inj₂ ⟨ V , ⟨ V∈ , u∈ ⟩ ⟩) (inj₁ ⟨ V' , ⟨ V∈' , v∈ ⟩ ⟩) = 
    ⊥-elim (D~ (right V) (left V') V∈ V∈')
  G u v (inj₂ ⟨ V , ⟨ V∈ , u∈ ⟩ ⟩) (inj₂ ⟨ V' , ⟨ V∈' , v∈ ⟩ ⟩) 
   with D~ (right V) (right V') V∈ V∈' 
  ... | V≈V' with FR~ (mem V) (mem V') (≈⇒Every V V' V≈V')
  ... | lift FR-V~ = FR-V~ u v u∈ v∈

nth-~ : ∀ i us vs → ∥ us ∥ ~ ∥ vs ∥ → 
    i < length us → i < length vs → 
    nth us i ~ nth vs i
nth-~ zero (x ∷ us) (x₁ ∷ vs) us~vs i<us i<vs = proj₁ us~vs
nth-~ (suc i) (x ∷ us) (x₁ ∷ vs) ⟨ fst , snd ⟩ i<us i<vs = 
  nth-~ i us vs snd (≤-pred i<us) (≤-pred i<vs)

proj-consis : ∀ i → fun-consistent _~_ (■ ∷ []) ■ (proj i)
proj-consis i D D' (lift D~) = lift G
  where
  G : Every _~_ (proj i D) (proj i D')
  G u v ⟨ us , ⟨ i< , ⟨ us∈ , refl ⟩ ⟩ ⟩ 
       ⟨ vs , ⟨ i<' , ⟨ vs∈ , refl ⟩ ⟩ ⟩ 
    with D~ ∥ us ∥ ∥ vs ∥ us∈ vs∈ 
  ... | q = nth-~ i us vs q i< i<'

𝓅-consis : ∀ P f → fun-consistent _~_ [] ■ (𝓅 P f)
𝓅-consis P f = lift (G P f)
  where
  G : ∀ P f → Every _~_ (𝓅 P f) (𝓅 P f)
  G (base x) f (const {B} k) (const {B'} k') u∈ v∈ with base-eq? x B | base-eq? x B'
  ... | yes refl | yes refl with base-eq? x x
  ... | yes refl = trans (sym u∈) v∈
  ... | no neq = ⊥-elim (neq refl)
  G (x ⇒ P) f (x₁ ⊢ .(const k ∷ []) ↦ u) (x₃ ⊢ .(const k' ∷ []) ↦ v) 
    ⟨ k , ⟨ refl , u∈ ⟩ ⟩ ⟨ k' , ⟨ refl , v∈ ⟩ ⟩ with base-eq? x x | base-rep-eq? k k' 
  ... | no neq | q = ⊥-elim (neq refl )
  ... | yes refl | no neq = inj₁ (λ z → H (head (proj₁ z)))
    where
    H : const k ~ const k' → False
    H z with base-eq? x x | z
    ... | no neq | q = ⊥-elim (neq refl)
    ... | yes refl | q = neq q
  ... | yes refl | yes refl = inj₂ ⟨ ⟨ H ∷ [] , tt ⟩ , G P (f k) u v u∈ v∈ ⟩
    where
    H : const k ~ const k
    H with base-eq? x x
    ... | no neq = ⊥-elim (neq refl)
    ... | yes refl = refl
  G (x ⇒ P) f (x₁ ⊢ x₂ ↦ u) ν u∈ v∈ = tt
  G (x ⇒ P) f ν (x₁ ⊢ x₂ ↦ v) u∈ v∈ = tt
  G (x ⇒ P) f ν ν u∈ v∈ = tt


𝒯-cons-consis : fun-consistent _~_ (■ ∷ ■ ∷ []) ■ 𝒯-cons
𝒯-cons-consis D D' (lift D~) E E' (lift E~) = lift G
  where
  G : Every _~_ (𝒯-cons D E) (𝒯-cons D' E')
  G ∥ u ∷ us ∥ ∥ v ∷ vs ∥ ⟨ u∈ , us∈ ⟩ ⟨ v∈ , vs∈ ⟩ = ⟨ D~ u v u∈ v∈ , E~ ∥ us ∥ ∥ vs ∥ us∈ vs∈ ⟩


𝒯-consis : ∀ n → fun-consistent _~_ (replicate n ■) ■ (𝒯 n)
𝒯-consis n = Dfold-pres (Every _~_) ■ ■ n 𝒯-cons 𝒯-cons ⌈ ∥ [] ∥ ⌉ ⌈ ∥ [] ∥ ⌉  
           𝒯-cons-consis (lift G)
  where
  G : (x x₁ : Value) (x₂ : x ≡ ∥ [] ∥) (x₃ : x₁ ≡ ∥ [] ∥) → x ~ x₁ 
  G .(∥ [] ∥) .(∥ [] ∥) refl refl = tt


𝒜-cons-consis : fun-consistent _~_ (■ ∷ ■ ∷ []) ■ 𝒜-cons
𝒜-cons-consis D D' (lift D~) E E' (lift E~) = lift G
  where
  G : Every _~_ (𝒜-cons D E) (𝒜-cons D' E')
  G ((fv ∷ fvs) ⊢ V ↦ w) ((fv' ∷ fvs') ⊢ V' ↦ w') ⟨ fvs⊆ , u∈ ⟩ ⟨ fvs'⊆ , v∈ ⟩
     = E~ (fvs ⊢ V ↦ w) (fvs' ⊢ V' ↦ w') u∈ v∈

𝒜-consis : ∀ n → fun-consistent _~_ (■ ∷ replicate n ■) ■ (𝒜 n)
𝒜-consis n F F' F~ = Dfold-pres (Every _~_) ■ ■ n 𝒜-cons 𝒜-cons F F' 
        𝒜-cons-consis F~


{-
𝒜-cons-mono : monotone (■ ∷ ■ ∷ []) ■ 𝒜-cons
𝒜-cons-mono D D' (lift D⊆) E E' (lift E⊆) = lift G
  where
  G : 𝒜-cons D E ⊆ 𝒜-cons D' E'
  G ((fv ∷ fvs) ⊢ V ↦ w) ⟨ fv∈ , d∈ ⟩ = 
    ⟨ (λ d z → D⊆ d (fv∈ d z)) , E⊆ (fvs ⊢ V ↦ w) d∈ ⟩

𝒜-mono : ∀ n → monotone (■ ∷ replicate n ■) ■ (𝒜 n)
𝒜-mono zero F F' F⊆ = F⊆
𝒜-mono (suc n) F F' (lift F⊆) D D' (lift D⊆) = 
  DComp-n-1-pres _⊆_ (replicate n ■) ■ ■ (𝒜 n F) (𝒜 n F') (𝒜-cons D) (𝒜-cons D') 
    (𝒜-mono n F F' (lift F⊆)) (𝒜-cons-mono D D' (lift D⊆))
-}



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


{- Continuity -----------------------------------------------------------------}

{- Bear in mind that Continuity is a property related to environments.
   That is, it involves some  evaluation function  
   
   continuity is the property that whenever a value is in a denotation,
   then there exists a finite environment for which that value is still in the denotation.
   -}






{-

-}

{- More Equations -------------------------------------------------------------}

{-

-}


{- 



{- Basic Properties of Denotational Operators ---------------------------------}

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

v∈ℬk⇒v≡k : ∀{v}{B}{k} → v ∈ ℬ B k → v ≡ const {B} k
v∈ℬk⇒v≡k {const {B′} k′} {B} {k} v∈
    with base-eq? B B′
... | yes refl rewrite v∈ = refl
... | no neq = ⊥-elim v∈

v∈℘k⇒v≡k : ∀{v}{B}{k} → v ∈ ℘ (base B) k → v ≡ const {B} k
v∈℘k⇒v≡k {const {B′} k′} {B} {k} v∈ = v∈ℬk⇒v≡k v∈ 

v∈𝒯⇒v≡∥vs∥ : ∀{n}{Ds}{v}
  → v ∈ 𝒯 n Ds
  → Σ[ vs ∈ List Value ] v ≡ ∥ vs ∥
v∈𝒯⇒v≡∥vs∥ {zero} {Ds} {∥ x ∥} v∈ = ⟨ x , refl ⟩
v∈𝒯⇒v≡∥vs∥ {suc n} {Ds} {∥ x ∥} v∈ = ⟨ x , refl ⟩

NE-Π⇒𝒯 : ∀{n}{Ds : Π n (𝒫 Value)}
   → NE-Π Ds
   → Σ[ vs ∈ List Value ] 𝒯 n Ds ∥ vs ∥
NE-Π⇒𝒯 {zero} {ptt} NE-Ds = ⟨ [] , tt ⟩
NE-Π⇒𝒯 {suc n} {⟨ D , Ds ⟩} ⟨ ⟨ v , v∈D ⟩ , NE-Ds ⟩
    with NE-Π⇒𝒯 {n} {Ds} NE-Ds
... | ⟨ vs , vs⊆ ⟩ = ⟨ v ∷ vs , ⟨ v∈D , vs⊆ ⟩ ⟩

NE-Π⇒NE-𝒯 : ∀{n}{Ds : Π n (𝒫 Value)}
   → NE-Π Ds
   → nonempty (𝒯 n Ds)
NE-Π⇒NE-𝒯{n}{Ds} NE-Ds
    with NE-Π⇒𝒯 NE-Ds
... | ⟨ vs , vs∈𝒯Ds ⟩ = ⟨ ∥ vs ∥ , vs∈𝒯Ds ⟩



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
  Λ-▪-⊆ {F} {X} Fmono w ⟨ V , ⟨ fvs , ⟨ ⟨ w∈FV , _ ⟩ , ⟨ V<X , V≢[] ⟩ ⟩ ⟩ ⟩ =
      Fmono (mem V) X V<X w w∈FV

  ⊆-Λ-▪ : ∀ {F : 𝒫 Value → 𝒫 Value}{X : 𝒫 Value}
    → continuous F  → nonempty X →  F X ⊆ (Λ F) ▪ X
  ⊆-Λ-▪ {F}{X} Fcont NE-X w w∈FX 
      with Fcont X (w ∷ []) (λ { d (here refl) → w∈FX }) NE-X
  ... | ⟨ D , ⟨ D<X , ⟨ w∈FD , NE-D ⟩ ⟩ ⟩ = {!!}
  {-
        ⟨ D , ⟨ [] , ⟨ ⟨ w∈FD w (here refl) , NE-D ⟩ , ⟨ D<X , NE-D ⟩ ⟩ ⟩ ⟩
  -}
  
{- Primitive Abstraction followed by Application is the identity --------------}

℘-▪-≃ : ∀{B}{P}{f}{k}  →  (℘ (B ⇒ P) f) ▪ (℘ (base B) k) ≃ ℘ P (f k)
℘-▪-≃ {B}{P}{f}{k} = ⟨ fwd , back ⟩
  where
  fwd : ℘ (B ⇒ P) f ▪ ℘ (base B) k ⊆ ℘ P (f k)
  fwd w ⟨ V , ⟨ fvs , ⟨ ⟨ k′ , ⟨ refl , w∈fk′ ⟩ ⟩ , ⟨ k′∈pk , _ ⟩ ⟩ ⟩ ⟩
      with k′∈pk (const k′) (here refl)
  ... | pkk′ rewrite k′∈℘k⇒k′≡k pkk′ = w∈fk′
  back : ℘ P (f k) ⊆ ℘ (B ⇒ P) f ▪ ℘ (base B) k
  back w w∈fk = ⟨ (const k ∷ []) , ⟨ [] , ⟨ ⟨ k , ⟨ refl , w∈fk ⟩ ⟩ ,
                ⟨ (λ {d (here refl) → k∈℘k}) , (λ ()) ⟩ ⟩ ⟩ ⟩

{- Cons is a Congruence  ------------------------------------------------------}



Π-append-⊆ : ∀{n}{m}{Ds Ds′ : Π n (𝒫 Value)}{Es Es′ : Π m (𝒫 Value)}
   → Ds ⫃ Ds′ → Es ⫃ Es′
   → Π-append Ds Es ⫃ Π-append Ds′ Es′
Π-append-⊆ {zero} {m} {Ds} {Ds′} {Es} {Es′} Ds⊆Ds′ Es⊆Es′ = Es⊆Es′
Π-append-⊆ {suc n} {m} {⟨ D , Ds ⟩} {⟨ D′ , Ds′ ⟩} {Es} {Es′} ⟨ D⊆D′ , Ds⊆Ds′ ⟩
    Es⊆Es′ = ⟨ D⊆D′ , Π-append-⊆ Ds⊆Ds′ Es⊆Es′ ⟩

Π-append-⩭ : ∀{n}{m}{Ds Ds′ : Π n (𝒫 Value)}{Es Es′ : Π m (𝒫 Value)}
   → Ds ⩭ Ds′ → Es ⩭ Es′
   → Π-append Ds Es ⩭ Π-append Ds′ Es′
Π-append-⩭ {zero} {m} {Ds} {Ds′} Ds=Ds′ Es=Es′ = Es=Es′
Π-append-⩭ {suc n} {m} {⟨ D , Ds ⟩} {⟨ D′ , Ds′ ⟩} ⟨ D=D′ , Ds=Ds′ ⟩ Es=Es′ =
    ⟨ D=D′ , Π-append-⩭ Ds=Ds′ Es=Es′ ⟩

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

{- Project from a Tuple -------------------------------------------------------}

𝒯-nth-0 : ∀{n}{D}{Ds}
   → NE-Π Ds
   → proj (𝒯 (suc n) ⟨ D , Ds ⟩) 0 ≃ D
𝒯-nth-0 {n}{D}{Ds} NE-Ds = ⟨ G , H ⟩
  where
  G : proj (𝒯 (suc n) ⟨ D , Ds ⟩) 0 ⊆ D
  G .v ⟨ v ∷ vs , ⟨ lt , ⟨ ⟨ v∈D , ∥vs∥∈𝒯Ds ⟩ , refl ⟩ ⟩ ⟩ = v∈D

  H : D ⊆ proj (𝒯 (suc n) ⟨ D , Ds ⟩) 0
  H v v∈D
      with NE-Π⇒𝒯 NE-Ds
  ... | ⟨ vs , vs⊆ ⟩ = ⟨ (v ∷ vs) , ⟨ s≤s z≤n , ⟨ ⟨ v∈D , vs⊆ ⟩ , refl ⟩ ⟩ ⟩

𝒯-nth-suc : ∀{i}{n}{D}{Ds}
   → nonempty D → NE-Π Ds
   → proj (𝒯 (suc n) ⟨ D , Ds ⟩) (suc i)
   ≃ proj (𝒯 n Ds) i
𝒯-nth-suc {i}{n}{D}{Ds} ⟨ u , u∈D ⟩ NE-Ds = ⟨ G , H ⟩
  where
  G : proj (𝒯 (suc n) ⟨ D , Ds ⟩) (suc i) ⊆ proj (𝒯 n Ds) i
  G u ⟨ v ∷ vs , ⟨ s≤s lt , ⟨ ⟨ v∈D , ∥vs∥∈𝒯Ds ⟩ , refl ⟩ ⟩ ⟩ =
      ⟨ vs , ⟨ lt , ⟨ ∥vs∥∈𝒯Ds , refl ⟩ ⟩ ⟩
  H : proj (𝒯 n Ds) i ⊆ proj (𝒯 (suc n) ⟨ D , Ds ⟩) (suc i)
  H v ⟨ vs , ⟨ lt , ⟨ vs⊆Ds , eq ⟩ ⟩ ⟩ =
    ⟨ (u ∷ vs) , ⟨ s≤s lt , ⟨ ⟨ u∈D , vs⊆Ds ⟩ , eq ⟩ ⟩ ⟩

{- Case, Left, and Right ------------------------------------------------------}



ℒ-𝒞 : ∀{D : 𝒫 Value}{F G : 𝒫 Value → 𝒫 Value}
   → continuous F → monotone F → nonempty D
   → 𝒞 (ℒ D) (Λ F) (Λ G) ≃ F D
ℒ-𝒞 {D}{F}{G} Fcont Fmono NE-D = ⟨ fwd , back ⟩
  where
  fwd : 𝒞 (ℒ D) (Λ F) (Λ G) ⊆ F D
  fwd v (inj₁ ⟨ V , ⟨ fvs , ⟨ ⟨ _ , V⊆D ⟩ , ⟨ v∈F[V] , V≢[] ⟩ ⟩ ⟩ ⟩) =
      Fmono (mem V) D V⊆D v v∈F[V]

  back : F D ⊆ 𝒞 (ℒ D) (Λ F) (Λ G)
  back v v∈F[D]
      with Fcont D (v ∷ []) (λ{d (here refl) → v∈F[D]}) NE-D
  ... | ⟨ E , ⟨ E⊆D , ⟨ v∈FE , NE-E ⟩ ⟩ ⟩ = {!!}
  {-
      inj₁ ⟨ E , ⟨ [] , ⟨ ⟨ NE-E , E⊆D ⟩ , ⟨ v∈FE v (here refl) , NE-E ⟩ ⟩ ⟩ ⟩
-}

ℛ-𝒞 : ∀{D : 𝒫 Value}{F G : 𝒫 Value → 𝒫 Value}
   → continuous G → monotone G → nonempty D
   → 𝒞 (ℛ D) (Λ F) (Λ G) ≃ G D
ℛ-𝒞 {D}{F}{G} Gcont Gmono NE-D = ⟨ fwd , back ⟩
  where
  fwd : 𝒞 (ℛ D) (Λ F) (Λ G) ⊆ G D
  fwd v (inj₂ ⟨ V , ⟨ fvs , ⟨ ⟨ _ , V⊆D ⟩ , ⟨ v∈G[V] , V≢[] ⟩ ⟩ ⟩ ⟩) =
      Gmono (mem V) D V⊆D v v∈G[V]

  back : G D ⊆ 𝒞 (ℛ D) (Λ F) (Λ G)
  back v v∈G[D]
      with Gcont D (v ∷ []) (λ{d (here refl) → v∈G[D]}) NE-D
  ... | ⟨ E , ⟨ E⊆D , ⟨ v∈GE , NE-E ⟩ ⟩ ⟩ = {!!}
  {-
      inj₂ ⟨ E , ⟨ [] , ⟨ ⟨ NE-E , E⊆D ⟩ , ⟨ v∈GE v (here refl) , NE-E ⟩ ⟩ ⟩ ⟩
  -}














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

{- Relations on Results and Products ------------------------------------------}

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

rel-results⇒rel-Π : ∀{n}{xs ys : Π n (𝒫 Value)}
    {R : ∀ b → Result (𝒫 Value) b → Result (𝒫 Value) b → Set₁}
    {R′ : 𝒫 Value → 𝒫 Value → Set}
  → (∀ x y → R ■ x y → R′ x y)
  → rel-results R (replicate n ■) xs ys
  → rel-Π R′ xs ys
rel-results⇒rel-Π {zero} R⇒R′ (lift tt) = tt
rel-results⇒rel-Π {suc n}{⟨ x , xs ⟩}{⟨ y , ys ⟩} R⇒R′ ⟨ Rxy , R[xs,ys] ⟩ =
    ⟨ R⇒R′ x y Rxy , (rel-results⇒rel-Π R⇒R′ R[xs,ys]) ⟩


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
▪-continuous {D}{E}{ρ}{NE-ρ}{w} ⟨ V , ⟨ fvs , ⟨ V↦w∈Dρ , ⟨ V⊆Eρ , V≢[] ⟩ ⟩ ⟩ ⟩
    IH-D IH-E mD mE
    with IH-D (fvs ⊢ V ↦ w) V↦w∈Dρ 
... | ⟨ ρ₁ , ⟨ fρ₁ , ⟨ ρ₁⊆ρ , V↦w∈Dρ₁ ⟩ ⟩ ⟩
    with ((continuous-∈⇒⊆ E ρ NE-ρ mE) V V⊆Eρ (λ v v∈V → IH-E v))
... | ⟨ ρ₂ , ⟨ fρ₂ , ⟨ ρ₂⊆ρ , V⊆Eρ₂ ⟩ ⟩ ⟩ =
   ⟨ ρ₃ , ⟨ join-finite-env fρ₁ fρ₂ , ⟨ join-lub ρ₁⊆ρ ρ₂⊆ρ , w∈D▪Eρ₃ ⟩ ⟩ ⟩ 
    where
    ρ₃ = ρ₁ ⊔ₑ ρ₂
    ρ₁⊆ρ₃ = λ x v z → inj₁ z
    V↦w∈Dρ₃ : fvs ⊢ V ↦ w ∈ D ρ₃
    V↦w∈Dρ₃ = mD ρ₁⊆ρ₃ (fvs ⊢ V ↦ w) V↦w∈Dρ₁
    ρ₂⊆ρ₄ = λ x v z → inj₂ z
    V⊆Eρ₃ : mem V ⊆ E ρ₃
    V⊆Eρ₃ v v∈V = mE ρ₂⊆ρ₄ v (V⊆Eρ₂ v v∈V)
    w∈D▪Eρ₃ : w ∈ (D ρ₃) ▪ (E ρ₃)
    w∈D▪Eρ₃ = ⟨ V , ⟨ fvs , ⟨ V↦w∈Dρ₃ , ⟨ V⊆Eρ₃ , V≢[] ⟩ ⟩ ⟩ ⟩

Λ-continuous : ∀{E : Env  → 𝒫 Value}{ρ}{NE-ρ}{v}
  → v ∈ Λ (λ D → E (D • ρ))
  → (∀ V → V ≢ [] → continuous-env E (mem V • ρ))
  → monotone-env E
  → Σ[ ρ′ ∈ Env ] finite-env ρ′ × ρ′ ⊆ₑ ρ × v ∈ Λ (λ D → E (D • ρ′))
Λ-continuous {E}{ρ}{NE-ρ}{fvs ⊢ V ↦ w} ⟨ w∈EV•ρ , ⟨ V≢[] , fvs≡[] ⟩ ⟩ IH mE
    with IH V V≢[] w w∈EV•ρ
... | ⟨ ρ′ , ⟨ fρ′ , ⟨ ρ′⊆V•ρ , w∈Eρ′ ⟩ ⟩ ⟩ =
    ⟨ (λ x → ρ′ (suc x)) , ⟨ (λ x → fρ′ (suc x)) , ⟨ (λ x → ρ′⊆V•ρ (suc x)) ,
    ⟨ mE{ρ′}{mem V • (λ x → ρ′ (suc x))} G w w∈Eρ′ , ⟨ V≢[] , {!!} ⟩ ⟩ ⟩ ⟩ ⟩
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
cons-continuous {D} {E} {ρ} {NE-ρ} {⦅ u , v ⦆} ⟨ u∈Dρ , v∈Eρ ⟩ cD cE mD mE
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
    with cD ⦅ u , v ⦆ uv∈Dρ 
... | ⟨ ρ₁ , ⟨ fρ₁ , ⟨ ρ₁⊆ρ , uv∈Dρ₁ ⟩ ⟩ ⟩ =
      ⟨ ρ₁ , ⟨ fρ₁ , ⟨ ρ₁⊆ρ , ⟨ v , mD (λ x d z → z) ⦅ u , v ⦆ uv∈Dρ₁ ⟩ ⟩ ⟩ ⟩

cdr-continuous : ∀{D : Env → 𝒫 Value}{ρ}{NE-ρ : nonempty-env ρ}{u : Value}
  → u ∈ cdr (D ρ) → continuous-env D ρ → monotone-env D
  → Σ[ ρ₃ ∈ Env ] finite-env ρ₃ × ρ₃ ⊆ₑ ρ × u ∈ cdr (D ρ₃)
cdr-continuous {D} {ρ} {NE-ρ} {v} ⟨ u , uv∈Dρ ⟩ cD mD
    with cD ⦅ u , v ⦆ uv∈Dρ 
... | ⟨ ρ₁ , ⟨ fρ₁ , ⟨ ρ₁⊆ρ , uv∈Dρ₁ ⟩ ⟩ ⟩ =
      ⟨ ρ₁ , ⟨ fρ₁ , ⟨ ρ₁⊆ρ , ⟨ u , mD (λ x d z → z) ⦅ u , v ⦆ uv∈Dρ₁ ⟩ ⟩ ⟩ ⟩

mono-envs : ∀{n} → (Env → Π n (𝒫 Value)) → Set₁
mono-envs {n} Ds = ∀{ρ ρ′} → ρ ⊆ₑ ρ′ → ⊆-results (replicate n ■) (Ds ρ) (Ds ρ′)

continuous-envs : ∀{n} → (Env → Π n (𝒫 Value)) → Env → Set₁
continuous-envs {n} Ds ρ = ∀ v → v ∈ 𝒯 n (Ds ρ)
                     → Σ[ ρ′ ∈ Env ] finite-env ρ′ × ρ′ ⊆ₑ ρ  × v ∈ 𝒯 n (Ds ρ′)

next-Ds : ∀{n} → (Env → Π (suc n) (𝒫 Value)) → (Env → Π n (𝒫 Value))
next-Ds Ds ρ
    with Ds ρ
... | ⟨ D , Ds′ ⟩ = Ds′

next-Ds-proj₂ : ∀{n}{Ds : Env → Π (suc n) (𝒫 Value)}{ρ}
   → next-Ds Ds ρ ≡ proj₂ (Ds ρ)
next-Ds-proj₂ {n} {Ds} {ρ}
    with Ds ρ
... | ⟨ a , b ⟩ = refl

next-mono-envs : ∀{n}{Ds : Env → Π (suc n) (𝒫 Value)}
   → mono-envs Ds → mono-envs (next-Ds Ds)
next-mono-envs {zero} {Ds} mDs {ρ} {ρ′} _ = lift tt
next-mono-envs {suc n} {Ds} mDs {ρ} {ρ′} ρ⊆ρ′
    with Ds ρ | Ds ρ′ | mDs {ρ} {ρ′} ρ⊆ρ′
... | ⟨ Dρ , Dsρ ⟩ | ⟨ Dρ′ , Dsρ′ ⟩ | ⟨ _ , mDs′ ⟩ = mDs′

proj₁-mono-envs : ∀{n}{Ds : Env → Π (suc n) (𝒫 Value)}{ρ}{ρ′}
   → ρ ⊆ₑ ρ′  → mono-envs Ds → proj₁ (Ds ρ) ⊆ proj₁ (Ds ρ′)
proj₁-mono-envs {n}{Ds}{ρ}{ρ′} ρ⊆ρ′ mDs
    with Ds ρ | mDs {ρ}{ρ′} ρ⊆ρ′
... | ⟨ Dρ , Dsρ ⟩ | ⟨ lift mD , _ ⟩ = mD

next-NE-Ds : ∀{n}{Ds : Env → Π (suc n) (𝒫 Value)}{ρ}
  → NE-Π (Ds ρ)
  → NE-Π (next-Ds Ds ρ)
next-NE-Ds{n}{Ds}{ρ} NE-Ds
    with Ds ρ | NE-Ds
... | ⟨ Dρ , Dsρ ⟩ | ⟨ NE-D , NE-Ds′ ⟩ = NE-Ds′

next-cont-envs : ∀{n}{Ds : Env → Π (suc n) (𝒫 Value)}
     {ρ}{NE-ρ : nonempty-env ρ}{w}
   → proj₁ (Ds ρ) w
   → continuous-envs Ds ρ
   → continuous-envs (next-Ds Ds) ρ
next-cont-envs {n} {Ds} {ρ}{NE-ρ}{w} w∈Dsρ cDs u u∈
    with Ds ρ | cDs | u∈ 
... | ⟨ D , Ds′ ⟩ | cDDs | u∈′ 
    with v∈𝒯⇒v≡∥vs∥ u∈′
... | ⟨ vs , refl ⟩
    with cDDs ∥ w ∷ vs ∥ ⟨ w∈Dsρ , u∈′ ⟩
... | ⟨ ρ′ , ⟨ fρ′ , ⟨ ρ′⊆ρ , ⟨ aaa , vs∈Dsρ′ ⟩ ⟩ ⟩ ⟩ =
    ⟨ ρ′ , ⟨ fρ′ , ⟨ ρ′⊆ρ , vs∈Dsρ′ ⟩ ⟩ ⟩

𝒯-continuous : ∀{n}{Ds : Env → Π n (𝒫 Value)}{ρ}{NE-ρ : nonempty-env ρ}
    {u : Value}
  → u ∈ 𝒯 n (Ds ρ) → continuous-envs Ds ρ → mono-envs Ds
  → Σ[ ρ₃ ∈ Env ] finite-env ρ₃ × ρ₃ ⊆ₑ ρ × u ∈ 𝒯 n (Ds ρ₃)
𝒯-continuous {zero} {Ds} {ρ} {NE-ρ} {u} u∈𝒯Ds cDs mDs 
    with Ds (initial-finite-env ρ NE-ρ) | u
... | lift tt | ∥ [] ∥ =
  ⟨ (initial-finite-env ρ NE-ρ) , ⟨ initial-fin ρ NE-ρ ,
  ⟨ initial-fin-⊆ ρ NE-ρ , tt ⟩ ⟩ ⟩
𝒯-continuous {suc n} {Ds} {ρ} {NE-ρ} {∥ v ∷ vs ∥} ⟨ v∈Dρ , vs∈𝒯Dsρ ⟩ cDs mDs 
    with 𝒯-continuous{n}{next-Ds Ds}{ρ}{NE-ρ}{∥ vs ∥}
       (subst (λ X → ∥ vs ∥ ∈ 𝒯 n X) (sym (next-Ds-proj₂{n}{Ds}{ρ})) vs∈𝒯Dsρ)
       (next-cont-envs{NE-ρ = NE-ρ}{w = v} v∈Dρ cDs)
       (λ {ρ}{ρ′} → next-mono-envs mDs {ρ}{ρ′})
... | ⟨ ρ₁ , ⟨ fρ₁ , ⟨ ρ₁⊆ρ , vs∈𝒯Dsρ₁ ⟩ ⟩ ⟩
    with cDs ∥ v ∷ vs ∥ ⟨ v∈Dρ , vs∈𝒯Dsρ ⟩ 
... | ⟨ ρ₂ , ⟨ fρ₂ , ⟨ ρ₂⊆ρ , ⟨ v∈Dρ₂ , vs∈Dsρ₂ ⟩ ⟩ ⟩ ⟩
    with  mDs {ρ₁}{ρ₁ ⊔ₑ ρ₂} (λ x d z → inj₁ z)
... | ⟨ _ , Dsρ₁⊆Dsρ₃ ⟩ 
    with  mDs {ρ₂}{ρ₁ ⊔ₑ ρ₂} (λ x d z → inj₂ z)
... | ⟨ lift Dρ₂⊆Dρ₃ , _ ⟩ =
    let v∈Dρ₃ = Dρ₂⊆Dρ₃ v v∈Dρ₂ in
    let vs∈Dsρ₃ = 𝒯-mono-⊆ (rel-results⇒rel-Π ⊆-result⇒⊆ Dsρ₁⊆Dsρ₃)
                            ∥ vs ∥ vs∈𝒯Dsρ₁ in
    ⟨ ρ₃ , ⟨ (join-finite-env fρ₁ fρ₂) , ⟨ (join-lub ρ₁⊆ρ ρ₂⊆ρ) ,
    ⟨ v∈Dρ₃ , vs∈Dsρ₃ ⟩ ⟩ ⟩ ⟩
    where
    ρ₃ = ρ₁ ⊔ₑ ρ₂

proj-continuous : ∀{D : Env → 𝒫 Value}{ρ}{NE-ρ : nonempty-env ρ}{u : Value}{i}
  → u ∈ proj (D ρ) i → continuous-env D ρ → monotone-env D
  → Σ[ ρ₃ ∈ Env ] finite-env ρ₃ × ρ₃ ⊆ₑ ρ × u ∈ proj (D ρ₃) i
proj-continuous {D} {ρ} {NE-ρ} {u} {i} ⟨ vs , ⟨ lt , ⟨ vs∈Dρ , refl ⟩ ⟩ ⟩ cD mD
    with cD ∥ vs ∥ vs∈Dρ
... | ⟨ ρ′ , ⟨ fρ′ , ⟨ ρ′⊆ρ , vs∈Dρ′ ⟩ ⟩ ⟩ =     
    ⟨ ρ′ , ⟨ fρ′ , ⟨ ρ′⊆ρ ,
    ⟨ vs , ⟨ lt , ⟨ mD (λ x d z → z) ∥ vs ∥ vs∈Dρ′ , refl ⟩ ⟩ ⟩ ⟩ ⟩ ⟩

ℒ-continuous : ∀{D : Env → 𝒫 Value}{ρ}{NE-ρ : nonempty-env ρ}{u : Value}
  → u ∈ ℒ (D ρ)  →  continuous-env D ρ  →  monotone-env D
  → Σ[ ρ₃ ∈ Env ] finite-env ρ₃ × ρ₃ ⊆ₑ ρ × u ∈ ℒ (D ρ₃)
ℒ-continuous {D} {ρ} {NE-ρ} {left U} ⟨ U≢[] , U⊆Dρ ⟩ cD mD
    with continuous-∈⇒⊆ D ρ NE-ρ mD U U⊆Dρ (λ v v∈Dρ → cD v)
... | ⟨ ρ₁ , ⟨ fρ₁ , ⟨ ρ₁⊆ρ , U⊆Dρ₁ ⟩ ⟩ ⟩ =
    ⟨ ρ₁ , ⟨ fρ₁ , ⟨ ρ₁⊆ρ , ⟨ U≢[] , U⊆Dρ₁ ⟩ ⟩ ⟩ ⟩

ℛ-continuous : ∀{D : Env → 𝒫 Value}{ρ}{NE-ρ : nonempty-env ρ}{u : Value}
  → u ∈ ℛ (D ρ)  →  continuous-env D ρ  →  monotone-env D
  → Σ[ ρ₃ ∈ Env ] finite-env ρ₃ × ρ₃ ⊆ₑ ρ × u ∈ ℛ (D ρ₃)
ℛ-continuous {D} {ρ} {NE-ρ} {right U} ⟨ U≢[] , U⊆Dρ ⟩ cD mD
    with continuous-∈⇒⊆ D ρ NE-ρ mD U U⊆Dρ (λ v v∈Dρ → cD v)
... | ⟨ ρ₁ , ⟨ fρ₁ , ⟨ ρ₁⊆ρ , U⊆Dρ₁ ⟩ ⟩ ⟩ =
    ⟨ ρ₁ , ⟨ fρ₁ , ⟨ ρ₁⊆ρ , ⟨ U≢[] , U⊆Dρ₁ ⟩ ⟩ ⟩ ⟩

𝒞-continuous : ∀{D E F : Env → 𝒫 Value}{ρ : Env}{NE-ρ : nonempty-env ρ}{u}
  → u ∈ 𝒞 (D ρ) (Λ (λ X → E (X • ρ))) (Λ (λ X → F (X • ρ)))
  → continuous-env D ρ → monotone-env D
  → (∀ V → V ≢ [] → continuous-env E (mem V • ρ)) → monotone-env E
  → (∀ V → V ≢ [] → continuous-env F (mem V • ρ)) → monotone-env F
  → Σ[ ρ′ ∈ Env ] finite-env ρ′ × ρ′ ⊆ₑ ρ
      × u ∈ 𝒞 (D ρ′) (Λ (λ X → E (X • ρ′))) (Λ (λ X → F (X • ρ′)))
𝒞-continuous {D}{E}{F} {ρ} {NE-ρ} {w}
    (inj₁ ⟨ V , ⟨ fvs , ⟨ inlV∈D , ⟨ w∈EV•ρ , ⟨ V≢[] , fvs≡[] ⟩ ⟩ ⟩ ⟩ ⟩)
    cD mD cE mE cF mF 
    with cD (left V) inlV∈D
... | ⟨ ρ₁ , ⟨ fρ₁ , ⟨ ρ₁⊆ρ , inlV∈Dρ₁ ⟩ ⟩ ⟩
    with cE V V≢[] w w∈EV•ρ
... | ⟨ ρ₂ , ⟨ fρ₂ , ⟨ ρ₂⊆V•ρ , w∈Eρ₂ ⟩ ⟩ ⟩ =
    ⟨ ρ₃ , ⟨ join-finite-env fρ₁ fρ₂′ , ⟨ join-lub ρ₁⊆ρ ρ₂′⊆ρ , u∈𝒞ρ₃ ⟩ ⟩ ⟩
    where
    ρ₂′ = (λ x → ρ₂ (suc x))
    ρ₃ = ρ₁ ⊔ₑ ρ₂′ 
    fρ₂′ : finite-env ρ₂′
    fρ₂′ x = fρ₂ (suc x)
    ρ₂′⊆ρ : ρ₂′ ⊆ₑ ρ
    ρ₂′⊆ρ x = ρ₂⊆V•ρ (suc x)
    G : (x : ℕ) (d : Value) → ρ₂ x d → (mem V • ρ₃) x d
    G zero d d∈ρ₂x = ρ₂⊆V•ρ zero d d∈ρ₂x
    G (suc x) d d∈ρ₂x = inj₂ d∈ρ₂x
    u∈𝒞ρ₃ = inj₁ ⟨ V , ⟨ fvs , ⟨ (mD (λ x d z → inj₁ z) (left V) inlV∈Dρ₁) ,
                  ⟨ (mE G w w∈Eρ₂) ,
                    ⟨ V≢[] , {!!} ⟩ ⟩ ⟩ ⟩ ⟩
𝒞-continuous {D}{E}{F} {ρ} {NE-ρ} {w}
    (inj₂ ⟨ V , ⟨ fvs , ⟨ inrV∈D , ⟨ w∈FV•ρ , ⟨ V≢[] , fvs≡[] ⟩ ⟩ ⟩ ⟩ ⟩)
    cD mD cE mE cF mF 
    with cD (right V) inrV∈D
... | ⟨ ρ₁ , ⟨ fρ₁ , ⟨ ρ₁⊆ρ , inrV∈Dρ₁ ⟩ ⟩ ⟩
    with cF V V≢[] w w∈FV•ρ
... | ⟨ ρ₂ , ⟨ fρ₂ , ⟨ ρ₂⊆V•ρ , w∈Fρ₂ ⟩ ⟩ ⟩ =
    ⟨ ρ₃ , ⟨ join-finite-env fρ₁ fρ₂′ , ⟨ join-lub ρ₁⊆ρ ρ₂′⊆ρ , u∈𝒞ρ₃ ⟩ ⟩ ⟩
    where
    ρ₂′ = (λ x → ρ₂ (suc x))
    ρ₃ = ρ₁ ⊔ₑ ρ₂′ 
    fρ₂′ : finite-env ρ₂′
    fρ₂′ x = fρ₂ (suc x)
    ρ₂′⊆ρ : ρ₂′ ⊆ₑ ρ
    ρ₂′⊆ρ x = ρ₂⊆V•ρ (suc x)
    G : (x : ℕ) (d : Value) → ρ₂ x d → (mem V • ρ₃) x d
    G zero d d∈ρ₂x = ρ₂⊆V•ρ zero d d∈ρ₂x
    G (suc x) d d∈ρ₂x = inj₂ d∈ρ₂x
    u∈𝒞ρ₃ = inj₂ ⟨ V , ⟨ fvs , ⟨ (mD (λ x d z → inj₁ z) (right V) inrV∈Dρ₁) ,
                  ⟨ (mF G w w∈Fρ₂) ,
                    ⟨ V≢[] , {!!} ⟩ ⟩ ⟩ ⟩ ⟩



-}

module DomainMultiAnnPair where

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
open import NewSigUtil
open import NewDOpSig
open import NewDenotProperties

open import Data.Empty using (⊥-elim) renaming (⊥ to False)
open import Data.List using (List ; _∷_ ; []; _++_; length; replicate)
open import Data.List.Relation.Unary.Any using (Any; here; there; any?)
open import Data.List.Relation.Unary.All 
  using (All; []; _∷_; head; tail; lookup; tabulate; all?)
  renaming (map to allmap)
open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_)
open import Data.List.Relation.Binary.Subset.Propositional using ()
  renaming (_⊆_ to _l⊆_)
open import Data.List.Properties using (++-conicalˡ; ∷-dec)
open import Data.List.Membership.Propositional renaming (_∈_ to _⋵_)
open import Data.List.Membership.Propositional.Properties
  using (∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.Nat using (ℕ; zero; suc; _≟_; _<_; z≤n; s≤s; _+_)
open import Data.Product using (_×_; Σ; Σ-syntax; proj₁; proj₂; ∃; ∃-syntax; uncurry)
    renaming (_,_ to ⟨_,_⟩)
open import Data.Product.Properties using (,-injective)
open import Relation.Nullary.Product using (_×-dec_)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Unit using (tt) renaming (⊤ to True)
open import Data.Unit.Polymorphic using (⊤) renaming (tt to ptt)
open import Relation.Binary.PropositionalEquality
    using (_≡_; _≢_; refl; sym; trans; subst; cong; cong₂)
open import Level using (Level; Lift; lift; lower)
    renaming (zero to lzero; suc to lsuc)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable using (map′)
open import Data.Bool using (Bool; true; false)
  renaming (_≟_ to _b≟_)


{- Denotational Values --------------------------------------------------------}

data Value : Set where
  const : {B : Base} → (k : base-rep B) → Value  {- A primitive constant of type B. -}
  _↦_ : (V : List Value) → (w : Value) → Value
      {- An entry in a function's graph. -}
  ν : Value      {- The empty function -}
  ω : Value          {- An error value, to serve as a default value in Envs and
                        to differentiate from converging -}
  ⦅_,_⦆⊢_ :             {- Closure Representations are just pairs -}
      (d₁ : Value) → (d₂ : List Value) → (b : Bool) → Value
  ∥_∥ : (ds : List Value) → Value                 {- Tuples -}
  left : (d : Value) → Value                      {- Sums -}
  right : (d : Value) → Value                     {- Sums -}

{- Equality -------------------------------------------------------------------}

l⊆→All∈ : ∀ {A : Set} (U V : List A) → U l⊆ V → All (λ z → Any (z ≡_) V) U
l⊆→All∈ U V = tabulate

All∈→l⊆ : ∀ {A : Set} {U V : List A} → All (λ z → Any (z ≡_) V) U → U l⊆ V
All∈→l⊆ = lookup

_⊢_l⊆?_ : ∀ {A : Set} (≡? : ∀ (a b : A) → Dec (a ≡ b)) (U V : List A) → Dec (U l⊆ V)
≡? ⊢ U l⊆? V = map′ All∈→l⊆ (l⊆→All∈ U V) (all? (λ x → any? (λ y → ≡? x y) V) U)

l⊆→⊆ : ∀ {A : Set} (U V : List A) → U l⊆ V → mem U ⊆ mem V
l⊆→⊆ U V Ul⊆V d = Ul⊆V {d}

⊆→l⊆ : ∀ {A : Set} (U V : List A) → mem U ⊆ mem V → U l⊆ V
⊆→l⊆ U V U⊆V {d} = U⊆V d

const-inj-base : ∀ {B B' k k'} → const {B} k ≡ const {B'} k' → B ≡ B'
const-inj-base {B}{B'} refl = refl

const-inj : ∀ {B k k'} → const {B} k ≡ const {B} k' → k ≡ k'
const-inj refl = refl

clos-inj : ∀ {d₁ d₂ d₁' d₂' b b'} → (⦅ d₁ , d₂ ⦆⊢ b) ≡ (⦅ d₁' , d₂' ⦆⊢ b') 
            → d₁ ≡ d₁' × d₂ ≡ d₂' × b ≡ b'
clos-inj refl = ⟨ refl , ⟨ refl , refl ⟩ ⟩

clos-inj-uncurried : ∀ {d₁ d₂ d₁' d₂' b b'} → (⦅ d₁ , d₂ ⦆⊢ b) ≡ (⦅ d₁' , d₂' ⦆⊢ b') 
  → ⟨ d₁ , ⟨ d₂ , b ⟩ ⟩ ≡ ⟨ d₁' , ⟨ d₂' , b' ⟩ ⟩
clos-inj-uncurried refl = refl

tup-inj : ∀ {ds ds'} → ∥ ds ∥ ≡ ∥ ds' ∥ → ds ≡ ds'
tup-inj refl = refl

left-inj : ∀ {v v'} → (left v) ≡ left v' → v ≡ v'
left-inj refl = refl

right-inj : ∀ {v v'} → (right v) ≡ right v' → v ≡ v'
right-inj refl = refl

↦-inj : ∀ {V V' w w'} → V ↦ w ≡ V' ↦ w'
      → V ≡ V' × w ≡ w'
↦-inj refl = ⟨ refl , refl ⟩

↦-inj-uncurried : ∀ {V V' w w'} → V ↦ w ≡ V' ↦ w'
      → ⟨ V , w ⟩ ≡ ⟨ V' , w' ⟩
↦-inj-uncurried refl = refl

_d≟_ : (d₁ : Value) → (d₂ : Value) → Dec (d₁ ≡ d₂)
_ds≟_ : (ds₁ : List Value) → (ds₂ : List Value) → Dec (ds₁ ≡ ds₂)
const {B} k d≟ const {B'} k₁ with base-eq? B B'
... | no neq = no λ z → neq (const-inj-base z)
... | yes refl = map′ (cong (const {B})) const-inj (base-rep-eq? k k₁)
const k d≟ ν = no (λ ())
const k d≟ (V ↦ w) = no (λ ())
const k d≟ ω = no (λ ())
const k d≟ (⦅ d₁' , d₂' ⦆⊢ b') = no (λ ())
const k d≟ ∥ ds ∥ = no (λ ())
const k d≟ (left v₁) = no (λ ())
const k d≟ (right v₁) = no (λ ())
(V ↦ w) d≟ const k = no (λ ())
(V ↦ w) d≟ (V' ↦ w') = map′ (uncurry (cong₂ _↦_)) ↦-inj ((V ds≟ V') ×-dec (w d≟ w'))
(V ↦ w) d≟ ν = no (λ ())
(V ↦ w) d≟ ω = no (λ ())
(V ↦ w) d≟ (⦅ d₁' , d₂' ⦆⊢ b') = no (λ ())
(V ↦ w) d≟ ∥ ds ∥ = no (λ ())
(V ↦ w) d≟ (left v₁) = no (λ ())
(V ↦ w) d≟ (right v₁) = no (λ ())
ν d≟ const k = no (λ ())
ν d≟ (V ↦ d₃) = no (λ ())
ν d≟ ν = yes refl
ν d≟ ω = no (λ ())
ν d≟ (⦅ d₁' , d₂' ⦆⊢ b') = no (λ ())
ν d≟ ∥ ds ∥ = no (λ ())
ν d≟ (left v) = no (λ ())
ν d≟  (right v) = no (λ ())
ω d≟ const k = no (λ ())
ω d≟ (V ↦ d₃) = no (λ ())
ω d≟ ν = no (λ ())
ω d≟ ω = yes refl
ω d≟ (⦅ d₁ , d₂ ⦆⊢ b) = no (λ ())
ω d≟ ∥ ds ∥ = no (λ ())
ω d≟ (left v) = no (λ ())
ω d≟  (right v) = no (λ ())
(⦅ d₁ , d₂ ⦆⊢ b) d≟ const k = no (λ ())
(⦅ d₁ , d₂ ⦆⊢ b) d≟ (V ↦ d₃) = no (λ ())
(⦅ d₁ , d₂ ⦆⊢ b) d≟ ν = no (λ ())
(⦅ d₁ , d₂ ⦆⊢ b) d≟ ω = no (λ ())
(⦅ d₁ , d₂ ⦆⊢ b) d≟ (⦅ d₁' , d₂' ⦆⊢ b') = 
   map′ (cong (λ z → ⦅ proj₁ z , proj₁ (proj₂ z) ⦆⊢ (proj₂ (proj₂ z))))
        clos-inj-uncurried 
        (map′ (uncurry (cong₂ ⟨_,_⟩)) ,-injective ((d₁ d≟ d₁') ×-dec 
        map′ (uncurry (cong₂ ⟨_,_⟩)) ,-injective ((d₂ ds≟ d₂') ×-dec (b b≟ b'))))
(⦅ d₁ , d₂ ⦆⊢ b) d≟ ∥ ds ∥ = no (λ ())
(⦅ d₁ , d₂ ⦆⊢ b) d≟ (left v) = no (λ ())
(⦅ d₁ , d₂ ⦆⊢ b) d≟  (right v) = no (λ ())
∥ ds ∥ d≟ const k = no (λ ())
∥ ds ∥ d≟ (V ↦ d₃) = no (λ ())
∥ ds ∥ d≟ ν = no (λ ())
∥ ds ∥ d≟ ω = no (λ ())
∥ ds ∥ d≟ (⦅ d₁ , d₂ ⦆⊢ b) = no (λ ())
∥ ds ∥ d≟ ∥ ds₁ ∥ = map′ (cong ∥_∥) tup-inj (ds ds≟ ds₁)
∥ ds ∥ d≟ (left v) = no (λ ())
∥ ds ∥ d≟  (right v) = no (λ ())
(left v) d≟ const k = no (λ ())
(left v) d≟ (V₁ ↦ d₃) = no (λ ())
(left v) d≟ ν = no (λ ())
(left v) d≟ ω = no (λ ())
(left v) d≟ (⦅ d₁ , d₂ ⦆⊢ b) = no (λ ())
(left v) d≟ ∥ ds ∥ = no (λ ())
(left v) d≟ (left v₁) = map′ (cong left) left-inj (v d≟ v₁)
(left v) d≟ (right v₁) = no (λ ())
(right v) d≟ const k = no (λ ())
(right v) d≟ (V₁ ↦ d₃) = no (λ ())
(right v) d≟ ν = no (λ ())
(right v) d≟ ω = no (λ ())
(right v) d≟ (⦅ d₁ , d₂ ⦆⊢ b) = no (λ ())
(right v) d≟ ∥ ds ∥ = no (λ ())
(right v) d≟ (left v₁) = no (λ ())
(right v) d≟ (right v₁) = map′ (cong right) right-inj (v d≟ v₁)
[] ds≟ [] = yes refl
[] ds≟ (x ∷ ds₂) = no (λ ())
(x ∷ ds₁) ds≟ [] = no (λ ())
(x ∷ ds₁) ds≟ (x₁ ∷ ds₂) = ∷-dec (x d≟ x₁) (ds₁ ds≟ ds₂)

_l⊆?_ : ∀ (U V : List Value) → Dec (U l⊆ V)
U l⊆? V = _d≟_ ⊢ U l⊆? V

_mem⊆?_ : ∀ (U V : List Value) → Dec (mem U ⊆ mem V)
U mem⊆? V = map′ (l⊆→⊆ U V) (⊆→l⊆ U V) (U l⊆? V)

{- Consistency ----------------------------------------------------------------}

infix 5 _~_
infix 5 _≈_

_≈_ : List Value → List Value → Set
_~_ : Value → Value → Set
const {B} x ~ const {B₁} x₁ with base-eq? B B₁
... | yes refl = x ≡ x₁
... | no neq = False
const x ~ (V₁ ↦ v) = False
const x ~ ν = False
const x ~ ω = False  
const x ~ (⦅ d₁ , d₂ ⦆⊢ b) = False
const x ~ ∥ x₁ ∥ = False
const x ~ (left x₁) = False
const x ~ (right x₁) = False
(V' ↦ w') ~ const x₂ = False
(V ↦ w) ~ (V' ↦ w') = (¬ V ≈ V') ⊎ (V ≈ V' × w ~ w')
(V' ↦ u) ~ ν = True
(V' ↦ w') ~ ω = False
(V' ↦ w') ~ (⦅ d₁' , d₂' ⦆⊢ b') = False
(V' ↦ w') ~ ∥ x₂ ∥ = False
(V' ↦ w') ~ (left x) = False
(V' ↦ w') ~ (right x) = False
ν ~ const x = False
ν ~ (V' ↦ v) = True
ν ~ ν = True
ν ~ ω = False
ν ~ (⦅ d₁' , d₂' ⦆⊢ b') = False
ν ~ ∥ x ∥ = False
ν ~ (left x) = False
ν ~ (right x) = False
ω ~ const x = False
ω ~ (V' ↦ v) = False
ω ~ ν = False
ω ~ ω = True {- starting with ω related with just itself -}
ω ~ (⦅ d₁' , d₂' ⦆⊢ b') = False
ω ~ ∥ x ∥ = False
ω ~ (left x) = False
ω ~ (right x) = False
(⦅ d₁ , d₂ ⦆⊢ b) ~ const x = False
(⦅ d₁ , d₂ ⦆⊢ b) ~ (V' ↦ v) = False
(⦅ d₁ , d₂ ⦆⊢ b) ~ ν = False
(⦅ d₁ , d₂ ⦆⊢ b) ~ ω = False
(⦅ d₁ , d₂ ⦆⊢ b) ~ (⦅ d₁' , d₂' ⦆⊢ b') = d₁ ~ d₁' × d₂ ≈ d₂'
(⦅ d₁ , d₂ ⦆⊢ b) ~ ∥ x ∥ = False
(⦅ d₁ , d₂ ⦆⊢ b) ~ (left x) = False
(⦅ d₁ , d₂ ⦆⊢ b) ~ (right x) = False
∥ x ∥ ~ const x₁ = False
∥ x ∥ ~ (V₁ ↦ v) = False
∥ x ∥ ~ ν = False
∥ x ∥ ~ ω = False
∥ x ∥ ~ (⦅ d₁' , d₂' ⦆⊢ b') = False
∥ [] ∥ ~ ∥ [] ∥ = True
∥ [] ∥ ~ ∥ x ∷ x₁ ∥ = False
∥ x ∷ x₂ ∥ ~ ∥ [] ∥ = False
∥ x ∷ xs ∥ ~ ∥ x₁ ∷ xs₁ ∥ = x ~ x₁ × ∥ xs ∥ ~ ∥ xs₁ ∥
∥ x ∥ ~ (left x₁) = False
∥ x ∥ ~ (right x₁) = False
(left x) ~ const x₁ = False
(left x) ~ (V₁ ↦ v) = False
(left x) ~ ν = False
(left x) ~ ω = False
(left x) ~ (⦅ d₁' , d₂' ⦆⊢ b') = False
(left x) ~ ∥ x₁ ∥ = False
(left x) ~ (left x₁) = x ~ x₁
(left x) ~ (right x₁) = False
(right x) ~ const x₁ = False
(right x) ~ (V₁ ↦ v) = False
(right x) ~ ν = False
(right x) ~ ω = False
(right x) ~ (⦅ d₁' , d₂' ⦆⊢ b') = False
(right x) ~ ∥ x₁ ∥ = False
(right x) ~ (left x₁) = False
(right x) ~ (right x₁) = x ~ x₁

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
~-sym (V ↦ w) (V' ↦ w') (inj₁ ¬V~V') = 
  inj₁ λ z → ¬V~V' (≈-sym V' V z)
~-sym (V ↦ w) (V' ↦ w') (inj₂ ⟨ V~V' , w~w' ⟩) = 
  inj₂ ⟨ ≈-sym V V' V~V' , ~-sym w w' w~w' ⟩
~-sym (V' ↦ u) ν u~v = tt
~-sym ν (V' ↦ v) u~v = tt
~-sym ν ν u~v = tt
~-sym ω ω u~v = tt
~-sym (⦅ d₁ , d₂ ⦆⊢ b) (⦅ d₁' , d₂' ⦆⊢ b') ⟨ fst , snd ⟩ = 
  ⟨ ~-sym d₁ d₁' fst , ≈-sym d₂ d₂' snd ⟩
~-sym ∥ [] ∥ ∥ [] ∥ u~v = tt
~-sym ∥ x ∷ x₂ ∥ ∥ x₁ ∷ x₃ ∥ ⟨ fst , rst ⟩ = 
  ⟨ ~-sym x x₁ fst , ~-sym ∥ x₂ ∥ ∥ x₃ ∥ rst ⟩
~-sym (left x) (left x₁) u~v = ~-sym x x₁ u~v
~-sym (right x) (right x₁) u~v = ~-sym x x₁ u~v

~-sym-All u [] [] = []
~-sym-All u (x ∷ xs) (px ∷ V~u) = 
  ~-sym x u px ∷ ~-sym-All u xs V~u

≈-sym U [] U≈V = tt
≈-sym U (x ∷ V) U≈V = 
  ⟨ ~-sym-All x U (≈head U x V U≈V) 
  , ≈-sym U V (≈tail U x V U≈V) ⟩

_≈?_ : (U V : List Value) → Dec (U ≈ V)
_~>?_ : (u : Value) (V : List Value) → Dec (All (u ~_) V)
_~?_ : (u v : Value) → Dec (u ~ v)
const {B} x ~? const {B'} x₁ with base-eq? B B'
... | no neq = no (λ z → z)
... | yes refl = base-rep-eq? x x₁
const x ~? (V₁ ↦ v) = no (λ z → z)
const x ~? ν = no (λ z → z)
const x ~? ω = no (λ z → z)
const x ~? (⦅ d₁' , d₂' ⦆⊢ b') = no (λ z → z)
const x ~? ∥ x₁ ∥ = no (λ z → z)
const x ~? (left x₁) = no (λ z → z)
const x ~? (right x₁) = no (λ z → z)
(V' ↦ u) ~? const x₂ = no (λ z → z)
(V ↦ w) ~? (V' ↦ w') with V ≈? V'
... | no ¬V~V' = yes (inj₁ ¬V~V')
... | yes V~V' with w ~? w'
... | no ¬w~w' = no (λ z → [ (λ x → x V~V') 
                           , (λ x → ¬w~w' (proj₂ x)) ] z )
... | yes w~w' = yes (inj₂ ⟨ V~V' , w~w' ⟩)
(V' ↦ w') ~? ν = yes tt
(V' ↦ w') ~? ω = no (λ z → z)
(V' ↦ w') ~? (⦅ d₁' , d₂' ⦆⊢ b') = no (λ z → z)
(V' ↦ w') ~? ∥ x₂ ∥ = no (λ z → z)
(V' ↦ w') ~? (left x) = no (λ z → z)
(V' ↦ w') ~? (right x) = no (λ z → z)
ν ~? const x = no (λ z → z)
ν ~? (V' ↦ v) = yes tt
ν ~? ν = yes tt
ν ~? ω = no (λ z → z)
ν ~? (⦅ d₁' , d₂' ⦆⊢ b') = no (λ z → z)
ν ~? ∥ x ∥ = no (λ z → z)
ν ~? (left x) = no (λ z → z)
ν ~? (right x) = no (λ z → z)
ω ~? const x = no (λ z → z)
ω ~? (V' ↦ v) = no (λ z → z)
ω ~? ν = no (λ z → z)
ω ~? ω = yes tt
ω ~? (⦅ d₁' , d₂' ⦆⊢ b') = no (λ z → z)
ω ~? ∥ x ∥ = no (λ z → z)
ω ~? (left x) = no (λ z → z)
ω ~? (right x) = no (λ z → z)
(⦅ d₁ , d₂ ⦆⊢ b) ~? const x = no (λ z → z)
(⦅ d₁ , d₂ ⦆⊢ b) ~? (V' ↦ v) = no (λ z → z)
(⦅ d₁ , d₂ ⦆⊢ b) ~? ν = no (λ z → z)
(⦅ d₁ , d₂ ⦆⊢ b) ~? ω = no (λ z → z)
(⦅ d₁ , d₂ ⦆⊢ b) ~? (⦅ d₁' , d₂' ⦆⊢ b') = (d₁ ~? d₁') ×-dec (d₂ ≈? d₂')
(⦅ d₁ , d₂ ⦆⊢ b) ~? ∥ x ∥ = no (λ z → z)
(⦅ d₁ , d₂ ⦆⊢ b) ~? (left x) = no (λ z → z)
(⦅ d₁ , d₂ ⦆⊢ b) ~? (right x) = no (λ z → z)
∥ x ∥ ~? const x₁ = no (λ z → z)
∥ x ∥ ~? (V₁ ↦ v) = no (λ z → z)
∥ x ∥ ~? ν = no (λ z → z)
∥ x ∥ ~? ω = no (λ z → z)
∥ x ∥ ~? (⦅ d₁' , d₂' ⦆⊢ b') = no (λ z → z)
∥ [] ∥ ~? ∥ [] ∥ = yes tt
∥ [] ∥ ~? ∥ x ∷ x₁ ∥ = no (λ z → z)
∥ x ∷ x₂ ∥ ~? ∥ [] ∥ = no (λ z → z)
∥ x ∷ x₂ ∥ ~? ∥ x₁ ∷ x₃ ∥ = (x ~? x₁) ×-dec (∥ x₂ ∥ ~? ∥ x₃ ∥)
∥ x ∥ ~? (left x₁) = no (λ z → z)
∥ x ∥ ~? (right x₁) = no (λ z → z)
(left x) ~? const x₁ = no (λ z → z)
(left x) ~? (V₁ ↦ v) = no (λ z → z)
(left x) ~? ν = no (λ z → z)
(left x) ~? ω = no (λ z → z)
(left x) ~? (⦅ d₁' , d₂' ⦆⊢ b') = no (λ z → z)
(left x) ~? ∥ x₁ ∥ = no (λ z → z)
(left x) ~? (left x₁) = x ~? x₁
(left x) ~? (right x₁) = no (λ z → z)
(right x) ~? const x₁ = no (λ z → z)
(right x) ~? (V₁ ↦ v) = no (λ z → z)
(right x) ~? ν = no (λ z → z)
(right x) ~? ω = no (λ z → z)
(right x) ~? (⦅ d₁' , d₂' ⦆⊢ b') = no (λ z → z)
(right x) ~? ∥ x₁ ∥ = no (λ z → z)
(right x) ~? (left x₁) = no (λ z → z)
(right x) ~? (right x₁) = x ~? x₁

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



module GraphModel.Domain where

{-

  This is an adaptation of the call-by-name models P(ω) of Scott
  (1976) and Dₐ of Engeler (1981) to call-by-value.

-}

open import Primitives
open import Utilities using (extensionality)
open import SetsAsPredicates
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


{- Denotational Values --------------------------------------------------------}

data Value : Set where
  const : {B : Base} → (k : base-rep B) → Value  {- A primitive constant of type B. -}
  _,_⊢_,_↦_ : (fv : Value) → (FV : List Value) → (v : Value) → (V : List Value) → (w : Value) → Value
      {- An entry in a function's graph. -}
  _,_⊢ν : (fv : Value) → (FV : List Value) → Value      {- The empty function -}
  ω : Value      {- An error value, to serve as a default value in Envs and
                    to differentiate from converging -}
  ⦅_∣_,_⦆ : {- Closure Representations -}
      (f : Value ) → (fv : Value) → (FV : List Value) → Value
  ∥_∥ : (ds : List Value) → Value                 {- Tuples -}
  left_,_ : (v : Value) → (V : List Value) → Value                {- Sums -}
  right_,_ : (v : Value) → (V : List Value) → Value               {- Sums -}



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

clos-inj : ∀ {f f' fv fv' FV FV'} → ⦅ f ∣ fv , FV ⦆ ≡ ⦅ f' ∣ fv' , FV' ⦆ → f ≡ f' × fv ≡ fv' × FV ≡ FV'
clos-inj refl = ⟨ refl , ⟨ refl , refl ⟩ ⟩

clos-inj-uncurried : ∀ {f f' fv fv' FV FV'} → ⦅ f ∣ fv , FV ⦆ ≡ ⦅ f' ∣ fv' , FV' ⦆ 
  → ⟨ f , ⟨ fv , FV ⟩ ⟩ ≡ ⟨ f' , ⟨ fv' , FV' ⟩ ⟩
clos-inj-uncurried refl = refl

tup-inj : ∀ {ds ds'} → ∥ ds ∥ ≡ ∥ ds' ∥ → ds ≡ ds'
tup-inj refl = refl

left-inj : ∀ {v v' V V'} → (left v , V) ≡ left v' , V' → v ≡ v' × V ≡ V'
left-inj refl = ⟨ refl , refl ⟩

left-inj-uncurried : ∀ {v v' V V'} → (left v , V) ≡ left v' , V' → ⟨ v , V ⟩ ≡ ⟨ v' , V' ⟩
left-inj-uncurried refl = refl

right-inj : ∀ {v v' V V'} →  (right v , V) ≡ right v' , V' → v ≡ v' × V ≡ V'
right-inj refl = ⟨ refl , refl ⟩

right-inj-uncurried : ∀ {v v' V V'} →  (right v , V) ≡ right v' , V' → ⟨ v , V ⟩ ≡ ⟨ v' , V' ⟩
right-inj-uncurried refl = refl

ν-inj : ∀ {fv fv' FV FV'} → fv , FV ⊢ν ≡ fv' , FV' ⊢ν → fv ≡ fv' × FV ≡ FV'
ν-inj refl = ⟨ refl , refl ⟩

↦-inj : ∀ {fv fv' FV FV' v v' V V' w w'} → fv , FV ⊢ v , V ↦ w ≡ fv' , FV' ⊢ v' , V' ↦ w'
      → fv ≡ fv' × FV ≡ FV' × v ≡ v' × V ≡ V' × w ≡ w'
↦-inj refl = ⟨ refl , ⟨ refl , ⟨ refl , ⟨ refl , refl ⟩ ⟩ ⟩ ⟩

↦-inj-uncurried : ∀ {fv fv' FV FV' v v' V V' w w'} → fv , FV ⊢ v , V ↦ w ≡ fv' , FV' ⊢ v' , V' ↦ w'
      → ⟨ fv , ⟨ FV , ⟨ v , ⟨ V , w ⟩ ⟩ ⟩ ⟩ ≡ ⟨ fv' , ⟨ FV' , ⟨ v' , ⟨ V' , w' ⟩ ⟩ ⟩ ⟩
↦-inj-uncurried refl = refl



_d≟_ : (d₁ : Value) → (d₂ : Value) → Dec (d₁ ≡ d₂)
_ds≟_ : (ds₁ : List Value) → (ds₂ : List Value) → Dec (ds₁ ≡ ds₂)
const {B} k d≟ const {B'} k₁ with base-eq? B B'
... | no neq = no λ z → neq (const-inj-base z)
... | yes refl = map′ (cong (const {B})) const-inj (base-rep-eq? k k₁)
const k d≟ (d₂ , FV₁ ⊢ν) = no (λ ())
const k d≟ (fv , FV ⊢ v , V ↦ w) = no (λ ())
const k d≟ ω = no (λ ())
const k d≟ ⦅ d₂ ∣ fv , FV₁ ⦆ = no (λ ())
const k d≟ ∥ ds ∥ = no (λ ())
const k d≟ (left v , V₁) = no (λ ())
const k d≟ (right v , V₁) = no (λ ())
(d₁ , FV ⊢ v , V ↦ d₃) d≟ const k = no (λ ())
(d₁ , FV ⊢ v , V ↦ d₃) d≟ (d₂ , FV₁ ⊢ v₁ , V₁ ↦ d₄) = 
  map′ (cong (λ z → proj₁ z , proj₁ (proj₂ z) ⊢ proj₁ (proj₂ (proj₂ z)) , proj₁ (proj₂ (proj₂ (proj₂ z))) 
                                              ↦ (proj₂ (proj₂ (proj₂ (proj₂ z))))))
        ↦-inj-uncurried 
        (map′ (uncurry (cong₂ ⟨_,_⟩)) ,-injective ((d₁ d≟ d₂) ×-dec 
        map′ (uncurry (cong₂ ⟨_,_⟩)) ,-injective ((FV ds≟ FV₁) ×-dec 
        map′ (uncurry (cong₂ ⟨_,_⟩)) ,-injective ((v d≟ v₁) ×-dec
        map′ (uncurry (cong₂ ⟨_,_⟩)) ,-injective ((V ds≟ V₁) ×-dec (d₃ d≟ d₄))))))
(d₁ , FV ⊢ v , V ↦ d₃) d≟ (d₂ , FV₁ ⊢ν) = no (λ ())
(d₁ , FV ⊢ v , V ↦ d₃) d≟ ω = no (λ ())
(d₁ , FV ⊢ v , V ↦ d₃) d≟ ⦅ d₂ ∣ fv , FV₁ ⦆ = no (λ ())
(d₁ , FV ⊢ v , V ↦ d₃) d≟ ∥ ds ∥ = no (λ ())
(d₁ , FV ⊢ v , V ↦ d₃) d≟ (left v₁ , V₁) = no (λ ())
(d₁ , FV ⊢ v , V ↦ d₃) d≟ (right v₁ , V₁) = no (λ ())
(d₁ , FV ⊢ν) d≟ const k = no (λ ())
(d₁ , FV ⊢ν) d≟ (d₂ , FV₁ ⊢ v , V ↦ d₃) = no (λ ())
(d₁ , FV ⊢ν) d≟ (d₂ , FV₁ ⊢ν) = 
  map′ (uncurry (cong₂ _,_⊢ν)) ν-inj ((d₁ d≟ d₂) ×-dec (FV ds≟ FV₁))
(d₁ , FV ⊢ν) d≟ ω = no (λ ())
(d₁ , FV ⊢ν) d≟ ⦅ d₂ ∣ fv , FV₁ ⦆ = no (λ ())
(d₁ , FV ⊢ν) d≟ ∥ ds ∥ = no (λ ())
(d₁ , FV ⊢ν) d≟ (left v , V) = no (λ ())
(d₁ , FV ⊢ν) d≟  (right v , V) = no (λ ())
ω d≟ const k = no (λ ())
ω d≟ (d₂ , FV ⊢ v , V ↦ d₃) = no (λ ())
ω d≟ (d₂ , FV ⊢ν) = no (λ ())
ω d≟ ω = yes refl
ω d≟ ⦅ d₂ ∣ fv , FV ⦆ = no (λ ())
ω d≟ ∥ ds ∥ = no (λ ())
ω d≟ (left v , V) = no (λ ())
ω d≟  (right v , V) = no (λ ())
⦅ d₁ ∣ fv , FV ⦆ d≟ const k = no (λ ())
⦅ d₁ ∣ fv , FV ⦆ d≟ (d₂ , FV₁ ⊢ v , V ↦ d₃) = no (λ ())
⦅ d₁ ∣ fv , FV ⦆ d≟ (d₂ , FV₁ ⊢ν) = no (λ ())
⦅ d₁ ∣ fv , FV ⦆ d≟ ω = no (λ ())
⦅ d₁ ∣ fv₁ , FV ⦆ d≟ ⦅ d₂ ∣ fv₂ , FV₁ ⦆ = 
  map′ (cong (λ z → ⦅ proj₁ z ∣ proj₁ (proj₂ z) , proj₂ (proj₂ z)⦆)) 
       clos-inj-uncurried
       (map′ (uncurry (cong₂ ⟨_,_⟩)) ,-injective ((d₁ d≟ d₂) ×-dec 
        map′ (uncurry (cong₂ ⟨_,_⟩)) ,-injective ((fv₁ d≟ fv₂) ×-dec (FV ds≟ FV₁))))
⦅ d₁ ∣ fv , FV ⦆ d≟ ∥ ds ∥ = no (λ ())
⦅ d₁ ∣ fv , FV ⦆ d≟ (left v , V) = no (λ ())
⦅ d₁ ∣ fv , FV ⦆ d≟  (right v , V) = no (λ ())
∥ ds ∥ d≟ const k = no (λ ())
∥ ds ∥ d≟ (d₂ , FV ⊢ v , V ↦ d₃) = no (λ ())
∥ ds ∥ d≟ (d₂ , FV ⊢ν) = no (λ ())
∥ ds ∥ d≟ ω = no (λ ())
∥ ds ∥ d≟ ⦅ d₂ ∣ fv , FV ⦆ = no (λ ())
∥ ds ∥ d≟ ∥ ds₁ ∥ = map′ (cong ∥_∥) tup-inj (ds ds≟ ds₁)
∥ ds ∥ d≟ (left v , V) = no (λ ())
∥ ds ∥ d≟  (right v , V) = no (λ ())
(left v , V) d≟ const k = no (λ ())
(left v , V) d≟ (d₂ , FV ⊢ v₁  , V₁ ↦ d₃) = no (λ ())
(left v , V) d≟ (d₂ , FV ⊢ν) = no (λ ())
(left v , V) d≟ ω = no (λ ())
(left v , V) d≟ ⦅ d₂ ∣ fv , FV ⦆ = no (λ ())
(left v , V) d≟ ∥ ds ∥ = no (λ ())
(left v , V) d≟ (left v₁ , V₁) = map′ (cong (λ z → left proj₁ z , proj₂ z)) left-inj-uncurried 
   (map′ (uncurry (cong₂ ⟨_,_⟩)) ,-injective ((v d≟ v₁) ×-dec (V ds≟ V₁)))
(left v , V) d≟ (right v₁ , V₁) = no (λ ())
(right v , V) d≟ const k = no (λ ())
(right v , V) d≟ (d₂ , FV ⊢ v₁  , V₁ ↦ d₃) = no (λ ())
(right v , V) d≟ (d₂ , FV ⊢ν) = no (λ ())
(right v , V) d≟ ω = no (λ ())
(right v , V) d≟ ⦅ d₂ ∣ fv , FV ⦆ = no (λ ())
(right v , V) d≟ ∥ ds ∥ = no (λ ())
(right v , V) d≟ (left v₁ , V₁) = no (λ ())
(right v , V) d≟ (right v₁ , V₁) = map′ (cong (λ z → right proj₁ z , proj₂ z)) right-inj-uncurried 
  (map′ (uncurry (cong₂ ⟨_,_⟩)) ,-injective ((v d≟ v₁) ×-dec (V ds≟ V₁)))
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
const x ~ (fv , FV ⊢ v₁  , V₁ ↦ v) = False
const x ~ (fv , FV ⊢ν) = False
const x ~ ω = False  
const x ~ ⦅ f ∣ fv , FV ⦆ = False
const x ~ ∥ x₁ ∥ = False
const x ~ (left x₁ , X₁) = False
const x ~ (right x₁ , X₁) = False
(fv , FV ⊢ v' , V' ↦ u) ~ const x₂ = False
(fv , us ⊢ v , V ↦ w) ~ (fv₁ , FV₁ ⊢ v₁ , V₁ ↦ w₁) = (¬ (v ∷ V) ≈ (v₁ ∷ V₁)) ⊎ ( (v ∷ V) ≈ (v₁ ∷ V₁) × w ~ w₁ )
(fv' , FV' ⊢ v' , V' ↦ u) ~ (fv , FV ⊢ν) = True
(fv' , FV ⊢ v' , V' ↦ u) ~ ω = False
(fv , FV ⊢ v' , V' ↦ u) ~ ⦅ f ∣ fv' , FV' ⦆ = False
(fv' , FV ⊢ v' , V' ↦ u) ~ ∥ x₂ ∥ = False
(fv' , FV ⊢ v' , V' ↦ u) ~ (left x , X) = False
(fv' , FV ⊢ v' , V' ↦ u) ~ (right x , X) = False
(fv , FV ⊢ν) ~ const x = False
(fv , FV ⊢ν) ~ (fv' , FV' ⊢ v' , V' ↦ v) = True
(fv , FV ⊢ν) ~ (fv' , FV' ⊢ν) = True
(fv , FV ⊢ν) ~ ω = False
(fv , FV ⊢ν) ~ ⦅ f ∣ fv' , FV' ⦆ = False
(fv , FV ⊢ν) ~ ∥ x ∥ = False
(fv , FV ⊢ν) ~ (left x , X) = False
(fv , FV ⊢ν) ~ (right x , X) = False
ω ~ const x = False
ω ~ (fv' , x ⊢ v' , V' ↦ v) = False
ω ~ (fv , FV ⊢ν) = False
ω ~ ω = True {- starting with ω related with just itself -}
ω ~ ⦅ f ∣ fv' , FV' ⦆ = False
ω ~ ∥ x ∥ = False
ω ~ (left x , X) = False
ω ~ (right x , X) = False
⦅ f ∣ fv' , FV' ⦆ ~ const x = False
⦅ f ∣ fv' , FV' ⦆ ~ (fv , x ⊢ v' , V' ↦ v) = False
⦅ f ∣ fv' , FV' ⦆ ~ (fv , FV ⊢ν) = False
⦅ f ∣ fv' , FV' ⦆ ~ ω = False
⦅ f ∣ fv , FV ⦆ ~ ⦅ f' ∣ fv' , FV' ⦆ = f ~ f' × (fv ∷ FV) ≈ (fv' ∷ FV')
⦅ f ∣ fv' , FV' ⦆ ~ ∥ x ∥ = False
⦅ f ∣ fv' , FV' ⦆ ~ (left x , X) = False
⦅ f ∣ fv' , FV' ⦆ ~ (right x , X) = False
∥ x ∥ ~ const x₁ = False
∥ x ∥ ~ (fv' , FV' ⊢ v₁  , V₁ ↦ v) = False
∥ x ∥ ~ (fv , FV ⊢ν) = False
∥ x ∥ ~ ω = False
∥ x ∥ ~ ⦅ f ∣ fv' , FV' ⦆ = False
∥ [] ∥ ~ ∥ [] ∥ = True
∥ [] ∥ ~ ∥ x ∷ x₁ ∥ = False
∥ x ∷ x₂ ∥ ~ ∥ [] ∥ = False
∥ x ∷ xs ∥ ~ ∥ x₁ ∷ xs₁ ∥ = x ~ x₁ × ∥ xs ∥ ~ ∥ xs₁ ∥
∥ x ∥ ~ (left x₁ , X₁) = False
∥ x ∥ ~ (right x₁ , X₁) = False
(left x , X) ~ const x₁ = False
(left x , X) ~ (fv' , FV' ⊢ v₁  , V₁ ↦ v) = False
(left x , X) ~ (fv , FV ⊢ν) = False
(left x , X) ~ ω = False
(left x , X) ~ ⦅ f ∣ fv' , FV' ⦆ = False
(left x , X) ~ ∥ x₁ ∥ = False
(left x , X) ~ (left x₁ , X₁) = (x ∷ X) ≈ (x₁ ∷ X₁)
(left x , X) ~ (right x₁ , X₁) = False
(right x , X) ~ const x₁ = False
(right x , X) ~ (fv' , FV' ⊢ v₁  , V₁ ↦ v) = False
(right x , X) ~ (fv , FV ⊢ν) = False
(right x , X) ~ ω = False
(right x , X) ~ ⦅ f ∣ fv' , FV' ⦆ = False
(right x , X) ~ ∥ x₁ ∥ = False
(right x , X) ~ (left x₁ , X₁) = False
(right x , X) ~ (right x₁ , X₁) = (x  ∷ X) ≈ (x₁ ∷ X₁)

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
~-sym (fv , fvs ⊢ v , V ↦ w) (fv' , fvs' ⊢ v' , V' ↦ w') (inj₁ ¬V~V') = 
  inj₁ λ z → ¬V~V' (≈-sym (v' ∷ V') (v ∷ V) z)
~-sym (fv , fvs ⊢ v , V ↦ w) (fv' , fvs' ⊢ v' , V' ↦ w') (inj₂ ⟨ V~V' , w~w' ⟩) = 
  inj₂ ⟨ ≈-sym (v ∷ V) (v' ∷ V') V~V' , ~-sym w w' w~w' ⟩
~-sym (fv' , x ⊢ v' , V' ↦ u) (fv , FV ⊢ν) u~v = tt
~-sym (fv , FV ⊢ν) (fv' , x ⊢ v' , V' ↦ v) u~v = tt
~-sym (fv , FV ⊢ν) (fv' , FV' ⊢ν) u~v = tt
~-sym ω ω u~v = tt
~-sym ⦅ f ∣ fv , FV ⦆ ⦅ f' ∣ fv' , FV' ⦆ ⟨ fst , snd ⟩ = 
  ⟨ ~-sym f f' fst , ≈-sym (fv ∷ FV) (fv' ∷ FV') snd ⟩
~-sym ∥ [] ∥ ∥ [] ∥ u~v = tt
~-sym ∥ x ∷ x₂ ∥ ∥ x₁ ∷ x₃ ∥ ⟨ fst , rst ⟩ = 
  ⟨ ~-sym x x₁ fst , ~-sym ∥ x₂ ∥ ∥ x₃ ∥ rst ⟩
~-sym ((left x , X)) ((left x₁ , X₁)) u~v = ≈-sym (x ∷ X) (x₁ ∷ X₁) u~v
~-sym ((right x , X)) ((right x₁ , X₁)) u~v = ≈-sym (x ∷ X) (x₁ ∷ X₁) u~v

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
const x ~? (fv' , FV' ⊢ v₁  , V₁ ↦ v) = no (λ z → z)
const x ~? (fv , FV ⊢ν) = no (λ z → z)
const x ~? ω = no (λ z → z)
const x ~? ⦅ f ∣ fv' , FV' ⦆ = no (λ z → z)
const x ~? ∥ x₁ ∥ = no (λ z → z)
const x ~? (left x₁ , X₁) = no (λ z → z)
const x ~? (right x₁ , X₁) = no (λ z → z)
(fv' , x ⊢ v' , V' ↦ u) ~? const x₂ = no (λ z → z)
(fv , fvs ⊢ v , V ↦ w) ~? (fv' , fvs' ⊢ v' , V' ↦ w') with (v ∷ V) ≈? (v' ∷ V')
... | no ¬V~V' = yes (inj₁ ¬V~V')
... | yes V~V' with w ~? w'
... | no ¬w~w' = no (λ z → [ (λ x → x V~V') 
                           , (λ x → ¬w~w' (proj₂ x)) ] z )
... | yes w~w' = yes (inj₂ ⟨ V~V' , w~w' ⟩)
(fv' , FV' ⊢ v' , V' ↦ u) ~? (fv , FV ⊢ν) = yes tt
(fv' , FV ⊢ v' , V' ↦ u) ~? ω = no (λ z → z)
(fv , FV ⊢ v' , V' ↦ u) ~? ⦅ f ∣ fv' , FV' ⦆ = no (λ z → z)
(fv' , FV ⊢ v' , V' ↦ u) ~? ∥ x₂ ∥ = no (λ z → z)
(fv' , FV ⊢ v' , V' ↦ u) ~? (left x , X) = no (λ z → z)
(fv' , FV ⊢ v' , V' ↦ u) ~? (right x , X) = no (λ z → z)
(fv , FV ⊢ν) ~? const x = no (λ z → z)
(fv , FV ⊢ν) ~? (fv' , x ⊢ v' , V' ↦ v) = yes tt
(fv , FV ⊢ν) ~? (fv' , FV' ⊢ν) = yes tt
(fv , FV ⊢ν) ~? ω = no (λ z → z)
(fv , FV ⊢ν) ~? ⦅ f ∣ fv' , FV' ⦆ = no (λ z → z)
(fv , FV ⊢ν) ~? ∥ x ∥ = no (λ z → z)
(fv , FV ⊢ν) ~? (left x , X) = no (λ z → z)
(fv , FV ⊢ν) ~? (right x , X) = no (λ z → z)
ω ~? const x = no (λ z → z)
ω ~? (fv' , x ⊢ v' , V' ↦ v) = no (λ z → z)
ω ~? (fv , FV ⊢ν) = no (λ z → z)
ω ~? ω = yes tt
ω ~? ⦅ f ∣ fv' , FV' ⦆ = no (λ z → z)
ω ~? ∥ x ∥ = no (λ z → z)
ω ~? (left x , X) = no (λ z → z)
ω ~? (right x , X) = no (λ z → z)
⦅ f ∣ fv' , FV' ⦆ ~? const x = no (λ z → z)
⦅ f ∣ fv' , FV' ⦆ ~? (fv , x ⊢ v' , V' ↦ v) = no (λ z → z)
⦅ f ∣ fv' , FV' ⦆ ~? (fv , FV ⊢ν) = no (λ z → z)
⦅ f ∣ fv' , FV' ⦆ ~? ω = no (λ z → z)
⦅ f ∣ fv , FV ⦆ ~? ⦅ f' ∣ fv' , FV' ⦆ = (f ~? f') ×-dec ((fv ∷ FV) ≈? (fv' ∷ FV'))
⦅ f ∣ fv' , FV' ⦆ ~? ∥ x ∥ = no (λ z → z)
⦅ f ∣ fv' , FV' ⦆ ~? (left x , X) = no (λ z → z)
⦅ f ∣ fv' , FV' ⦆ ~? (right x , X) = no (λ z → z)
∥ x ∥ ~? const x₁ = no (λ z → z)
∥ x ∥ ~? (fv' , FV' ⊢ v₁  , V₁ ↦ v) = no (λ z → z)
∥ x ∥ ~? (fv , FV ⊢ν) = no (λ z → z)
∥ x ∥ ~? ω = no (λ z → z)
∥ x ∥ ~? ⦅ f ∣ fv' , FV' ⦆ = no (λ z → z)
∥ [] ∥ ~? ∥ [] ∥ = yes tt
∥ [] ∥ ~? ∥ x ∷ x₁ ∥ = no (λ z → z)
∥ x ∷ x₂ ∥ ~? ∥ [] ∥ = no (λ z → z)
∥ x ∷ x₂ ∥ ~? ∥ x₁ ∷ x₃ ∥ = (x ~? x₁) ×-dec (∥ x₂ ∥ ~? ∥ x₃ ∥)
∥ x ∥ ~? (left x₁ , X₁) = no (λ z → z)
∥ x ∥ ~? (right x₁ , X₁) = no (λ z → z)
(left x , X) ~? const x₁ = no (λ z → z)
(left x , X) ~? (fv' , FV' ⊢ v₁  , V₁ ↦ v) = no (λ z → z)
(left x , X) ~? (fv , FV ⊢ν) = no (λ z → z)
(left x , X) ~? ω = no (λ z → z)
(left x , X) ~? ⦅ f ∣ fv' , FV' ⦆ = no (λ z → z)
(left x , X) ~? ∥ x₁ ∥ = no (λ z → z)
(left x , X) ~? (left x₁ , X₁) = (x ∷ X) ≈? (x₁ ∷ X₁)
(left x , X) ~? (right x₁ , X₁) = no (λ z → z)
(right x , X) ~? const x₁ = no (λ z → z)
(right x , X) ~? (fv' , FV' ⊢ v₁  , V₁ ↦ v) = no (λ z → z)
(right x , X) ~? (fv , FV ⊢ν) = no (λ z → z)
(right x , X) ~? ω = no (λ z → z)
(right x , X) ~? ⦅ f ∣ fv' , FV' ⦆ = no (λ z → z)
(right x , X) ~? ∥ x₁ ∥ = no (λ z → z)
(right x , X) ~? (left x₁ , X₁) = no (λ z → z)
(right x , X) ~? (right x₁ , X₁) = (x ∷ X) ≈? (x₁ ∷ X₁)

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



module DomainAnnLam where

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


{- Denotational Values --------------------------------------------------------}

data Value : Set where
  const : {B : Base} → (k : base-rep B) → Value  {- A primitive constant of type B. -}
  _∷_⊢_∷_↦_ : (fv : Value) → (FV : List Value) → (v : Value) → (V : List Value) → (w : Value) → Value
      {- An entry in a function's graph. -}
  _∷_⊢ν : (fv : Value) → (FV : List Value) → Value      {- The empty function -}
  ω : Value          {- An error value, to serve as a default value in Envs and
                        to differentiate from converging -}
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

tup-inj : ∀ {ds ds'} → ∥ ds ∥ ≡ ∥ ds' ∥ → ds ≡ ds'
tup-inj refl = refl

left-inj : ∀ {v v'} → (left v) ≡ left v' → v ≡ v'
left-inj refl = refl

right-inj : ∀ {v v'} → (right v) ≡ right v' → v ≡ v'
right-inj refl = refl

ν-inj : ∀ {fv fv' FV FV'} → fv ∷ FV ⊢ν ≡ (fv' ∷ FV' ⊢ν) → fv ≡ fv' × FV ≡ FV'
ν-inj refl = ⟨ refl , refl ⟩

↦-inj : ∀ {fv fv' FV FV' v v' V V' w w'} → fv ∷ FV ⊢  v ∷ V ↦ w ≡ fv' ∷ FV' ⊢ v' ∷ V' ↦ w'
      → fv ≡ fv' × FV ≡ FV' × v ≡ v' × V ≡ V' × w ≡ w'
↦-inj refl = ⟨ refl , ⟨ refl , ⟨ refl , ⟨ refl , refl ⟩ ⟩ ⟩ ⟩

↦-inj-uncurried : ∀ {fv fv' FV FV' v v' V V' w w'} → fv ∷ FV ⊢ v ∷ V ↦ w ≡ fv' ∷ FV' ⊢  v' ∷ V' ↦ w'
      → ⟨ fv , ⟨ FV , ⟨ v , ⟨ V , w ⟩ ⟩ ⟩ ⟩ ≡ ⟨ fv' , ⟨ FV' , ⟨ v' , ⟨ V' , w' ⟩ ⟩ ⟩ ⟩
↦-inj-uncurried refl = refl

_d≟_ : (d₁ : Value) → (d₂ : Value) → Dec (d₁ ≡ d₂)
_ds≟_ : (ds₁ : List Value) → (ds₂ : List Value) → Dec (ds₁ ≡ ds₂)
const {B} k d≟ const {B'} k₁ with base-eq? B B'
... | no neq = no λ z → neq (const-inj-base z)
... | yes refl = map′ (cong (const {B})) const-inj (base-rep-eq? k k₁)
const k d≟ (fv' ∷ FV' ⊢ν) = no (λ ())
const k d≟ (fv ∷ FV ⊢  v ∷ V ↦ w) = no (λ ())
const k d≟ ω = no (λ ())
const k d≟ ∥ ds ∥ = no (λ ())
const k d≟ (left v₁) = no (λ ())
const k d≟ (right v₁) = no (λ ())
(fv ∷ FV ⊢  v ∷ V ↦ w) d≟ const k = no (λ ())
(fv ∷ FV ⊢ v ∷ V ↦ w) d≟ (fv' ∷ FV' ⊢  v' ∷ V' ↦ w') = 
  map′ (cong (λ z → proj₁ z ∷ proj₁ (proj₂ z) ⊢ proj₁ (proj₂ (proj₂ z)) ∷ proj₁ (proj₂ (proj₂ (proj₂ z))) 
                                              ↦ (proj₂ (proj₂ (proj₂ (proj₂ z))))))
        ↦-inj-uncurried 
        (map′ (uncurry (cong₂ ⟨_,_⟩)) ,-injective ((fv d≟ fv') ×-dec 
        map′ (uncurry (cong₂ ⟨_,_⟩)) ,-injective ((FV ds≟ FV') ×-dec 
        map′ (uncurry (cong₂ ⟨_,_⟩)) ,-injective ((v d≟ v') ×-dec
        map′ (uncurry (cong₂ ⟨_,_⟩)) ,-injective ((V ds≟ V') ×-dec (w d≟ w'))))))
(fv ∷ FV ⊢  v ∷ V ↦ w) d≟ (fv' ∷ FV' ⊢ν) = no (λ ())
(fv ∷ FV ⊢  v ∷ V ↦ w) d≟ ω = no (λ ())
(fv ∷ FV ⊢  v ∷ V ↦ w) d≟ ∥ ds ∥ = no (λ ())
(fv ∷ FV ⊢  v ∷ V ↦ w) d≟ (left v₁) = no (λ ())
(fv ∷ FV ⊢  v ∷ V ↦ w) d≟ (right v₁) = no (λ ())
(fv ∷ FV ⊢ν) d≟ const k = no (λ ())
(fv ∷ FV ⊢ν) d≟ (d₂ ∷ FV₁ ⊢ v ∷ V ↦ d₃) = no (λ ())
(fv ∷ FV ⊢ν) d≟ (fv' ∷ FV' ⊢ν) = 
  map′ (uncurry (cong₂ _∷_⊢ν)) ν-inj ((fv d≟ fv') ×-dec (FV ds≟ FV'))
(fv ∷ FV ⊢ν) d≟ ω = no (λ ())
(fv ∷ FV ⊢ν) d≟ ∥ ds ∥ = no (λ ())
(fv ∷ FV ⊢ν) d≟ (left v) = no (λ ())
(fv ∷ FV ⊢ν) d≟  (right v) = no (λ ())
ω d≟ const k = no (λ ())
ω d≟ (d₂ ∷ FV ⊢ v ∷ V ↦ d₃) = no (λ ())
ω d≟ (d₂ ∷ FV ⊢ν) = no (λ ())
ω d≟ ω = yes refl
ω d≟ ∥ ds ∥ = no (λ ())
ω d≟ (left v) = no (λ ())
ω d≟  (right v) = no (λ ())
∥ ds ∥ d≟ const k = no (λ ())
∥ ds ∥ d≟ (d₂ ∷ FV ⊢ v ∷ V ↦ d₃) = no (λ ())
∥ ds ∥ d≟ (d₂ ∷ FV ⊢ν) = no (λ ())
∥ ds ∥ d≟ ω = no (λ ())
∥ ds ∥ d≟ ∥ ds₁ ∥ = map′ (cong ∥_∥) tup-inj (ds ds≟ ds₁)
∥ ds ∥ d≟ (left v) = no (λ ())
∥ ds ∥ d≟  (right v) = no (λ ())
(left v) d≟ const k = no (λ ())
(left v) d≟ (d₂ ∷ FV ⊢ v₁  ∷ V₁ ↦ d₃) = no (λ ())
(left v) d≟ (d₂ ∷ FV ⊢ν) = no (λ ())
(left v) d≟ ω = no (λ ())
(left v) d≟ ∥ ds ∥ = no (λ ())
(left v) d≟ (left v₁) = map′ (cong left) left-inj (v d≟ v₁)
(left v) d≟ (right v₁) = no (λ ())
(right v) d≟ const k = no (λ ())
(right v) d≟ (d₂ ∷ FV ⊢ v₁ ∷ V₁ ↦ d₃) = no (λ ())
(right v) d≟ (d₂ ∷ FV ⊢ν) = no (λ ())
(right v) d≟ ω = no (λ ())
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
const x ~ (fv ∷ FV ⊢ v₁ ∷ V₁ ↦ v) = False
const x ~ (fv ∷ FV ⊢ν) = False
const x ~ ω = False  
const x ~ ∥ x₁ ∥ = False
const x ~ (left x₁) = False
const x ~ (right x₁) = False
(fv' ∷ FV' ⊢  v' ∷ V' ↦ w') ~ const x₂ = False
(fv ∷ FV ⊢  v ∷ V ↦ w) ~ (fv' ∷ FV' ⊢  v' ∷ V' ↦ w') = (¬ (v ∷ V) ≈ (v' ∷ V')) ⊎ ( (v ∷ V) ≈ (v' ∷ V') × w ~ w' )
(fv' ∷ FV' ⊢ v' ∷ V' ↦ u) ~ (fv ∷ FV ⊢ν) = True
(fv' ∷ FV' ⊢  v' ∷ V' ↦ w') ~ ω = False
(fv' ∷ FV' ⊢  v' ∷ V' ↦ w') ~ ∥ x₂ ∥ = False
(fv' ∷ FV' ⊢  v' ∷ V' ↦ w') ~ (left x) = False
(fv' ∷ FV' ⊢  v' ∷ V' ↦ w') ~ (right x) = False
(fv ∷ FV ⊢ν) ~ const x = False
(fv ∷ FV ⊢ν) ~ (fv' ∷ FV' ⊢ v' ∷ V' ↦ v) = True
(fv ∷ FV ⊢ν) ~ (fv' ∷ FV' ⊢ν) = True
(fv ∷ FV ⊢ν) ~ ω = False
(fv ∷ FV ⊢ν) ~ ∥ x ∥ = False
(fv ∷ FV ⊢ν) ~ (left x) = False
(fv ∷ FV ⊢ν) ~ (right x) = False
ω ~ const x = False
ω ~ (fv' ∷ x ⊢ v' ∷ V' ↦ v) = False
ω ~ (fv ∷ FV ⊢ν) = False
ω ~ ω = True {- starting with ω related with just itself -}
ω ~ ∥ x ∥ = False
ω ~ (left x) = False
ω ~ (right x) = False
∥ x ∥ ~ const x₁ = False
∥ x ∥ ~ (fv' ∷ FV' ⊢ v₁ ∷ V₁ ↦ v) = False
∥ x ∥ ~ (fv ∷ FV ⊢ν) = False
∥ x ∥ ~ ω = False
∥ [] ∥ ~ ∥ [] ∥ = True
∥ [] ∥ ~ ∥ x ∷ x₁ ∥ = False
∥ x ∷ x₂ ∥ ~ ∥ [] ∥ = False
∥ x ∷ xs ∥ ~ ∥ x₁ ∷ xs₁ ∥ = x ~ x₁ × ∥ xs ∥ ~ ∥ xs₁ ∥
∥ x ∥ ~ (left x₁) = False
∥ x ∥ ~ (right x₁) = False
(left x) ~ const x₁ = False
(left x) ~ (fv' ∷ FV' ⊢ v₁ ∷ V₁ ↦ v) = False
(left x) ~ (fv ∷ FV ⊢ν) = False
(left x) ~ ω = False
(left x) ~ ∥ x₁ ∥ = False
(left x) ~ (left x₁) = x ~ x₁
(left x) ~ (right x₁) = False
(right x) ~ const x₁ = False
(right x) ~ (fv' ∷ FV' ⊢ v₁ ∷ V₁ ↦ v) = False
(right x) ~ (fv ∷ FV ⊢ν) = False
(right x) ~ ω = False
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
~-sym (fv ∷ FV ⊢  v ∷ V ↦ w) (fv' ∷ FV' ⊢  v' ∷ V' ↦ w') (inj₁ ¬V~V') = 
  inj₁ λ z → ¬V~V' (≈-sym (v' ∷ V') (v ∷ V) z)
~-sym (fv ∷ FV ⊢  v ∷ V ↦ w) (fv' ∷ FV' ⊢  v' ∷ V' ↦ w') (inj₂ ⟨ V~V' , w~w' ⟩) = 
  inj₂ ⟨ ≈-sym (v ∷ V) (v' ∷ V') V~V' , ~-sym w w' w~w' ⟩
~-sym (fv' ∷ x ⊢ v' ∷ V' ↦ u) (fv ∷ FV ⊢ν) u~v = tt
~-sym (fv ∷ FV ⊢ν) (fv' ∷ x ⊢ v' ∷ V' ↦ v) u~v = tt
~-sym (fv ∷ FV ⊢ν) (fv' ∷ FV' ⊢ν) u~v = tt
~-sym ω ω u~v = tt
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
const x ~? (fv' ∷ FV' ⊢ v₁ ∷ V₁ ↦ v) = no (λ z → z)
const x ~? (fv ∷ FV ⊢ν) = no (λ z → z)
const x ~? ω = no (λ z → z)
const x ~? ∥ x₁ ∥ = no (λ z → z)
const x ~? (left x₁) = no (λ z → z)
const x ~? (right x₁) = no (λ z → z)
(fv' ∷ x ⊢ v' ∷ V' ↦ u) ~? const x₂ = no (λ z → z)
(fv ∷ FV ⊢ v ∷ V ↦ w) ~? (fv' ∷ FV' ⊢  v' ∷ V' ↦ w') with (v ∷ V) ≈? (v' ∷ V')
... | no ¬V~V' = yes (inj₁ ¬V~V')
... | yes V~V' with w ~? w'
... | no ¬w~w' = no (λ z → [ (λ x → x V~V') 
                           , (λ x → ¬w~w' (proj₂ x)) ] z )
... | yes w~w' = yes (inj₂ ⟨ V~V' , w~w' ⟩)
(fv' ∷ FV' ⊢ v' ∷ V' ↦ w') ~? (fv ∷ FV ⊢ν) = yes tt
(fv' ∷ FV' ⊢ v' ∷ V' ↦ w') ~? ω = no (λ z → z)
(fv' ∷ FV' ⊢ v' ∷ V' ↦ w') ~? ∥ x₂ ∥ = no (λ z → z)
(fv' ∷ FV' ⊢ v' ∷ V' ↦ w') ~? (left x) = no (λ z → z)
(fv' ∷ FV' ⊢ v' ∷ V' ↦ w') ~? (right x) = no (λ z → z)
(fv ∷ FV ⊢ν) ~? const x = no (λ z → z)
(fv ∷ FV ⊢ν) ~? (fv' ∷ x ⊢ v' ∷ V' ↦ v) = yes tt
(fv ∷ FV ⊢ν) ~? (fv' ∷ FV' ⊢ν) = yes tt
(fv ∷ FV ⊢ν) ~? ω = no (λ z → z)
(fv ∷ FV ⊢ν) ~? ∥ x ∥ = no (λ z → z)
(fv ∷ FV ⊢ν) ~? (left x) = no (λ z → z)
(fv ∷ FV ⊢ν) ~? (right x) = no (λ z → z)
ω ~? const x = no (λ z → z)
ω ~? (fv' ∷ x ⊢ v' ∷ V' ↦ v) = no (λ z → z)
ω ~? (fv ∷ FV ⊢ν) = no (λ z → z)
ω ~? ω = yes tt
ω ~? ∥ x ∥ = no (λ z → z)
ω ~? (left x) = no (λ z → z)
ω ~? (right x) = no (λ z → z)
∥ x ∥ ~? const x₁ = no (λ z → z)
∥ x ∥ ~? (fv' ∷ FV' ⊢ v₁ ∷ V₁ ↦ v) = no (λ z → z)
∥ x ∥ ~? (fv ∷ FV ⊢ν) = no (λ z → z)
∥ x ∥ ~? ω = no (λ z → z)
∥ [] ∥ ~? ∥ [] ∥ = yes tt
∥ [] ∥ ~? ∥ x ∷ x₁ ∥ = no (λ z → z)
∥ x ∷ x₂ ∥ ~? ∥ [] ∥ = no (λ z → z)
∥ x ∷ x₂ ∥ ~? ∥ x₁ ∷ x₃ ∥ = (x ~? x₁) ×-dec (∥ x₂ ∥ ~? ∥ x₃ ∥)
∥ x ∥ ~? (left x₁) = no (λ z → z)
∥ x ∥ ~? (right x₁) = no (λ z → z)
(left x) ~? const x₁ = no (λ z → z)
(left x) ~? (fv' ∷ FV' ⊢ v₁ ∷ V₁ ↦ v) = no (λ z → z)
(left x) ~? (fv ∷ FV ⊢ν) = no (λ z → z)
(left x) ~? ω = no (λ z → z)
(left x) ~? ∥ x₁ ∥ = no (λ z → z)
(left x) ~? (left x₁) = x ~? x₁
(left x) ~? (right x₁) = no (λ z → z)
(right x) ~? const x₁ = no (λ z → z)
(right x) ~? (fv' ∷ FV' ⊢ v₁ ∷ V₁ ↦ v) = no (λ z → z)
(right x) ~? (fv ∷ FV ⊢ν) = no (λ z → z)
(right x) ~? ω = no (λ z → z)
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


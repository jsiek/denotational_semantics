
module Compiler.Model.Graph.Domain.ISWIM.Domain where

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
open import Data.Fin using (Fin; zero; suc)
open import Data.Fin.Properties using () renaming (_≟_ to _fin≟_)
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
  _↦_ : (V : List Value) → (w : Value) → Value
      {- An entry in a function's graph. -}
  ν : Value      {- The empty function -}
  ω : Value          {- An error value, to serve as a default value in Envs and
                        to differentiate from converging -}
  ⦅_∣ : (u : Value) → Value  
  ∣_⦆ : (V : List Value) → Value
         {- closure values are pairs with multi-value snds (to store environments), 
            which we split up into car and cdr behaviors 
            for easier distributivity properties
            Think of a pair ⦅ u , V ⦆ as ⦅ u ∣ ⊔ ∣ V ⦆ -}
  tup[_]_ : ∀ {n} (i : Fin n) → (d : Value) → Value                 {- Tuples -}
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

fst-inj : ∀ {v v'} → ⦅ v ∣ ≡ ⦅ v' ∣ → v ≡ v'
fst-inj refl = refl

snd-inj : ∀ {v v'} → ∣ v ⦆ ≡ ∣ v' ⦆ → v ≡ v'
snd-inj refl = refl

tup-inj-easy : ∀ {n} {i i' : Fin n} {d d'} → (tup[ i ] d) ≡ (tup[ i' ] d') 
   → ⟨ i , d ⟩ ≡ ⟨ i' , d' ⟩
tup-inj-easy refl = refl

tup-inj : ∀ {n n'} {i : Fin n} {i' : Fin n'} {d d'} 
        → (tup[ i ] d) ≡ (tup[ i' ] d') → 
   Σ[ n≡n' ∈ n ≡ n' ] (subst Fin n≡n' i) ≡ i' × d ≡ d'
tup-inj refl = ⟨ refl , ⟨ refl , refl ⟩ ⟩

tup-inj-uncurried : ∀ {n n'} {i : Fin n} {i' : Fin n'} {d d'} 
        → (tup[ i ] d) ≡ (tup[ i' ] d') → 
   Σ[ n≡n' ∈ n ≡ n' ] ⟨ (subst Fin n≡n' i) , d ⟩ ≡ ⟨ i' , d' ⟩
tup-inj-uncurried refl = ⟨ refl , refl ⟩

tup-inj-uncurried' : ∀ {n n'} {i : Fin n} {i' : Fin n'} {d d'} 
        → (tup[ i ] d) ≡ (tup[ i' ] d') → (n≡n' : n ≡ n') →
   ⟨ (subst Fin n≡n' i) , d ⟩ ≡ ⟨ i' , d' ⟩
tup-inj-uncurried' refl refl = refl

left-inj : ∀ {v v'} → (left v) ≡ left v' → v ≡ v'
left-inj refl = refl

right-inj : ∀ {v v'} → (right v) ≡ right v' → v ≡ v'
right-inj refl = refl

↦-inj : ∀ {V V' w w'} →  V ↦ w ≡ V' ↦ w'
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
const k d≟ ⦅ d₁' ∣ = no (λ ())
const k d≟ ∣ d₂' ⦆ = no (λ ())
const k d≟ (tup[ i ] d) = no (λ ())
const k d≟ (left v₁) = no (λ ())
const k d≟ (right v₁) = no (λ ())
(V ↦ w) d≟ const k = no (λ ())
(V ↦ w) d≟ (V' ↦ w') = map′ (uncurry (cong₂ _↦_)) ↦-inj ((V ds≟ V') ×-dec (w d≟ w'))
(V ↦ w) d≟ ν = no (λ ())
(V ↦ w) d≟ ω = no (λ ())
(V ↦ w) d≟ ⦅ d₁' ∣ = no (λ ())
(V ↦ w) d≟ ∣ d₂' ⦆ = no (λ ())
(V ↦ w) d≟ (tup[ i ] d) = no (λ ())
(V ↦ w) d≟ (left v₁) = no (λ ())
(V ↦ w) d≟ (right v₁) = no (λ ())
ν d≟ const k = no (λ ())
ν d≟ (V ↦ d₃) = no (λ ())
ν d≟ ν = yes refl
ν d≟ ω = no (λ ())
ν d≟ ⦅ d₁' ∣ = no (λ ())
ν d≟ ∣ d₂' ⦆ = no (λ ())
ν d≟ (tup[ i ] d) = no (λ ())
ν d≟ (left v) = no (λ ())
ν d≟  (right v) = no (λ ())
ω d≟ const k = no (λ ())
ω d≟ (V ↦ d₃) = no (λ ())
ω d≟ ν = no (λ ())
ω d≟ ω = yes refl
ω d≟ ⦅ d₁ ∣ = no (λ ())
ω d≟ ∣ d₂ ⦆ = no (λ ())
ω d≟ (tup[ i ] d) = no (λ ())
ω d≟ (left v) = no (λ ())
ω d≟ (right v) = no (λ ())
⦅ u ∣ d≟ const k = no (λ ())
⦅ u ∣ d≟ (V ↦ v) = no (λ ())
⦅ u ∣ d≟ ν = no (λ ())
⦅ u ∣ d≟ ω = no (λ ())
⦅ u ∣ d≟ ⦅ v ∣ = map′ (cong ⦅_∣) fst-inj (u d≟ v)
⦅ u ∣ d≟ ∣ V ⦆ = no (λ ())
⦅ u ∣ d≟ (tup[ i ] d) = no (λ ())
⦅ u ∣ d≟ left v = no (λ ())
⦅ u ∣ d≟ right v = no (λ ())
∣ V ⦆ d≟ const k = no (λ ())
∣ V ⦆ d≟ (V₁ ↦ v) = no (λ ())
∣ V ⦆ d≟ ν = no (λ ())
∣ V ⦆ d≟ ω = no (λ ())
∣ V ⦆ d≟ ⦅ v ∣ = no (λ ())
∣ V ⦆ d≟ ∣ V₁ ⦆ = map′ (cong ∣_⦆) snd-inj (V ds≟ V₁)
∣ V ⦆ d≟ (tup[ i ] d) = no (λ ())
∣ V ⦆ d≟ left v = no (λ ())
∣ V ⦆ d≟ right v = no (λ ())
(tup[ i ] d) d≟ const k = no (λ ())
(tup[ i ] d) d≟ (V ↦ d₃) = no (λ ())
(tup[ i ] d) d≟ ν = no (λ ())
(tup[ i ] d) d≟ ω = no (λ ())
(tup[_]_ {n} i d) d≟ (tup[_]_ {n'} i' d') with n ≟ n'
... | no neq = no λ z → neq (proj₁ (tup-inj z))
... | yes refl = map′ (cong (λ z → tup[ proj₁ z ] proj₂ z))
        (λ z → tup-inj-uncurried' z refl)
        (map′ (uncurry (cong₂ ⟨_,_⟩)) ,-injective (i fin≟ i' ×-dec (d d≟ d')))
(tup[ i ] d) d≟ (left v) = no (λ ())
(tup[ i ] d) d≟ (right v) = no (λ ())
(tup[ i ] d) d≟ ⦅ v ∣ = no (λ ())
(tup[ i ] d) d≟ ∣ v ⦆ = no (λ ())
(left v) d≟ const k = no (λ ())
(left v) d≟ (V₁ ↦ d₃) = no (λ ())
(left v) d≟ ν = no (λ ())
(left v) d≟ ω = no (λ ())
(left v) d≟ ⦅ d₁ ∣ = no (λ ())
(left v) d≟ ∣ d₂ ⦆ = no (λ ())
(left v) d≟ (tup[ i ] d) = no (λ ())
(left v) d≟ (left v₁) = map′ (cong left) left-inj (v d≟ v₁)
(left v) d≟ (right v₁) = no (λ ())
(right v) d≟ const k = no (λ ())
(right v) d≟ (V₁ ↦ d₃) = no (λ ())
(right v) d≟ ν = no (λ ())
(right v) d≟ ω = no (λ ())
(right v) d≟ ⦅ d₁ ∣ = no (λ ())
(right v) d≟ ∣ d₂ ⦆ = no (λ ())
(right v) d≟ (tup[ i ] d) = no (λ ())
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
const {B} x ~ const {B₁} x₁ = Σ[ B≡ ∈ B ≡ B₁ ] (subst base-rep B≡ x) ≡ x₁
const x ~ (V₁ ↦ v) = False
const x ~ ν = False
const x ~ ω = False  
const x ~ ⦅ d₁ ∣ = False
const x ~ ∣ d₂ ⦆ = False
const x ~ (tup[ i ] d') = False
const x ~ (left x₁) = False
const x ~ (right x₁) = False
(V' ↦ w') ~ const x₂ = False
(V ↦ w) ~ (V' ↦ w') = (¬ V ≈ V') ⊎ (V ≈ V' × w ~ w' )
(V' ↦ u) ~ ν = True
(V' ↦ w') ~ ω = False
(V' ↦ w') ~ ⦅ d₁' ∣ = False
(V' ↦ w') ~ ∣ d₂' ⦆ = False
(V' ↦ w') ~ (tup[ i ] d') = False
(V' ↦ w') ~ (left x) = False
(V' ↦ w') ~ (right x) = False
ν ~ const x = False
ν ~ (V' ↦ v) = True
ν ~ ν = True
ν ~ ω = False
ν ~ ⦅ d₁' ∣ = False
ν ~ ∣ d₂' ⦆ = False
ν ~ (tup[ i ] d') = False
ν ~ (left x) = False
ν ~ (right x) = False
ω ~ const x = False
ω ~ (V' ↦ v) = False
ω ~ ν = False
ω ~ ω = True {- starting with ω related with just itself -}
ω ~ ⦅ d₁' ∣ = False
ω ~ ∣ d₂' ⦆ = False
ω ~ (tup[ i ] d') = False
ω ~ (left x) = False
ω ~ (right x) = False
⦅ u ∣ ~ const k = False
⦅ u ∣ ~ (V ↦ v) = False
⦅ u ∣ ~ ν = False
⦅ u ∣ ~ ω = False
⦅ u ∣ ~ ⦅ v ∣ = u ~ v
⦅ u ∣ ~ ∣ V ⦆ = True
⦅ u ∣ ~ (tup[ i ] d) = False
⦅ u ∣ ~ left v = False
⦅ u ∣ ~ right v = False
∣ V ⦆ ~ const k = False
∣ V ⦆ ~ (V₁ ↦ v) = False
∣ V ⦆ ~ ν = False
∣ V ⦆ ~ ω = False
∣ V ⦆ ~ ⦅ v ∣ = True
∣ V ⦆ ~ ∣ V₁ ⦆ = V ≈ V₁
∣ V ⦆ ~ (tup[ i ] d) = False
∣ V ⦆ ~ left v = False
∣ V ⦆ ~ right v = False
(tup[ i ] d') ~ const x₁ = False
(tup[ i ] d') ~ (V₁ ↦ v) = False
(tup[ i ] d') ~ ν = False
(tup[ i ] d') ~ ω = False
(tup[ i ] d') ~ ⦅ d₁' ∣ = False
(tup[ i ] d') ~ ∣ d₂' ⦆ = False
(tup[_]_ {n} i d) ~ (tup[_]_ {n'} i' d') 
    = Σ[ n≡ ∈ n ≡ n' ] ((¬ ((subst Fin n≡ i) ≡ i')) ⊎ ((subst Fin n≡ i) ≡ i' × d ~ d'))
(tup[ i ] d') ~ (left x₁) = False
(tup[ i ] d') ~ (right x₁) = False
(left x) ~ const x₁ = False
(left x) ~ (V₁ ↦ v) = False
(left x) ~ ν = False
(left x) ~ ω = False
(left x) ~ ⦅ d₁' ∣ = False
(left x) ~ ∣ d₂' ⦆ = False
(left x) ~ (tup[ i ] d') = False
(left x) ~ (left x₁) = x ~ x₁
(left x) ~ (right x₁) = False
(right x) ~ const x₁ = False
(right x) ~ (V₁ ↦ v) = False
(right x) ~ ν = False
(right x) ~ ω = False
(right x) ~ ⦅ d₁' ∣ = False
(right x) ~ ∣ d₂' ⦆ = False
(right x) ~ (tup[ i ] d') = False
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
~-sym (const {B} x) (const {B₁} x₁) ⟨ refl , u~v ⟩ = ⟨ refl , sym u~v ⟩
~-sym  (V ↦ w)  (V' ↦ w') (inj₁ ¬V~V') = 
  inj₁ λ z → ¬V~V' (≈-sym V' V z)
~-sym  (V ↦ w)  (V' ↦ w') (inj₂ ⟨ V~V' , w~w' ⟩) = 
  inj₂ ⟨ ≈-sym V V' V~V' , ~-sym w w' w~w' ⟩
~-sym (V' ↦ u) ν u~v = tt
~-sym ν (V' ↦ v) u~v = tt
~-sym ν ν u~v = tt
~-sym ω ω u~v = tt
~-sym ⦅ u ∣ ⦅ v ∣ u~v = ~-sym u v u~v
~-sym ⦅ u ∣ ∣ V ⦆ u~v = tt
~-sym ∣ V ⦆ ⦅ v ∣ u~v = tt
~-sym ∣ V ⦆ ∣ V₁ ⦆ u~v = ≈-sym V V₁ u~v
~-sym (tup[_]_ {n} i d) (tup[_]_ {n'} i' d') ⟨ refl , inj₁ neq ⟩ = 
    ⟨ refl , inj₁ (λ z → neq (sym z)) ⟩
~-sym (tup[_]_ {n} i d) (tup[_]_ {n'} i' d') ⟨ refl , inj₂ ⟨ refl , d~ ⟩ ⟩ =
    ⟨ refl , inj₂ ⟨ refl , ~-sym d d' d~ ⟩ ⟩
~-sym (left x) (left x₁) u~v = ~-sym x x₁ u~v
~-sym (right x) (right x₁) u~v = ~-sym x x₁ u~v

~-sym-All u [] [] = []
~-sym-All u (x ∷ xs) (px ∷ V~u) = 
  ~-sym x u px ∷ ~-sym-All u xs V~u

≈-sym U [] U≈V = tt
≈-sym U (x ∷ V) U≈V = 
  ⟨ ~-sym-All x U (≈head U x V U≈V) 
  , ≈-sym U V (≈tail U x V U≈V) ⟩

~-tup-inv : ∀ {n}{i i' : Fin n}{d d'} → tup[ i ] d ~ tup[ i' ] d'
    → (¬ (i ≡ i')) ⊎ (i ≡ i' × d ~ d')
~-tup-inv ⟨ refl , snd ⟩ = snd

~-const-inv : ∀ {B k k'} → const {B} k ~ const k' 
    → k ≡ k'
~-const-inv ⟨ refl , snd ⟩ = snd

_≈?_ : (U V : List Value) → Dec (U ≈ V)
_~>?_ : (u : Value) (V : List Value) → Dec (All (u ~_) V)
_~?_ : (u v : Value) → Dec (u ~ v)
const {B} x ~? const {B'} x₁ with base-eq? B B'
... | no neq = no λ z → neq (proj₁ z)
... | yes refl with base-rep-eq? x x₁
... | no neq = no λ z → neq (~-const-inv z)
... | yes refl = yes ⟨ refl , refl ⟩
const x ~? (V₁ ↦ v) = no (λ z → z)
const x ~? ν = no (λ z → z)
const x ~? ω = no (λ z → z)
const x ~? ⦅ d₁' ∣ = no (λ z → z)
const x ~? ∣ d₂' ⦆ = no (λ z → z)
const x ~? (tup[ i ] d') = no (λ z → z)
const x ~? (left x₁) = no (λ z → z)
const x ~? (right x₁) = no (λ z → z)
(V' ↦ u) ~? const x₂ = no (λ z → z)
(V ↦ w) ~?  (V' ↦ w') with V ≈? V'
... | no ¬V~V' = yes (inj₁ ¬V~V')
... | yes V~V' with w ~? w'
... | no ¬w~w' = no (λ z → [ (λ x → x V~V') 
                           , (λ x → ¬w~w' (proj₂ x)) ] z )
... | yes w~w' = yes (inj₂ ⟨ V~V' , w~w' ⟩)
(V' ↦ w') ~? ν = yes tt
(V' ↦ w') ~? ω = no (λ z → z)
(V' ↦ w') ~? ⦅ d₁' ∣ = no (λ z → z)
(V' ↦ w') ~? ∣ d₂' ⦆ = no (λ z → z)
(V' ↦ w') ~? (tup[ i ] d') = no (λ z → z)
(V' ↦ w') ~? (left x) = no (λ z → z)
(V' ↦ w') ~? (right x) = no (λ z → z)
ν ~? const x = no (λ z → z)
ν ~? (V' ↦ v) = yes tt
ν ~? ν = yes tt
ν ~? ω = no (λ z → z)
ν ~? ⦅ d₁' ∣ = no (λ z → z)
ν ~? ∣ d₂' ⦆ = no (λ z → z)
ν ~? (tup[ i ] d') = no (λ z → z)
ν ~? (left x) = no (λ z → z)
ν ~? (right x) = no (λ z → z)
ω ~? const x = no (λ z → z)
ω ~? (V' ↦ v) = no (λ z → z)
ω ~? ν = no (λ z → z)
ω ~? ω = yes tt
ω ~? ⦅ d₁' ∣ = no (λ z → z)
ω ~? ∣ d₂' ⦆ = no (λ z → z)
ω ~? (tup[ i ] d') = no (λ z → z)
ω ~? (left x) = no (λ z → z)
ω ~? (right x) = no (λ z → z)
⦅ u ∣ ~? const k = no λ z → z
⦅ u ∣ ~? (V ↦ v) = no (λ z → z)
⦅ u ∣ ~? ν = no (λ z → z)
⦅ u ∣ ~? ω = no (λ z → z)
⦅ u ∣ ~? ⦅ v ∣ = u ~? v
⦅ u ∣ ~? ∣ V ⦆ = yes tt
⦅ u ∣ ~? (tup[ i ] d) = no (λ z → z)
⦅ u ∣ ~? left v = no (λ z → z)
⦅ u ∣ ~? right v = no (λ z → z)
∣ V ⦆ ~? const k = no (λ z → z)
∣ V ⦆ ~? (V₁ ↦ v) = no (λ z → z)
∣ V ⦆ ~? ν = no (λ z → z)
∣ V ⦆ ~? ω = no (λ z → z)
∣ V ⦆ ~? ⦅ v ∣ = yes tt
∣ V ⦆ ~? ∣ V₁ ⦆ = V ≈? V₁
∣ V ⦆ ~? (tup[ i ] d) = no (λ z → z)
∣ V ⦆ ~? left v = no (λ z → z)
∣ V ⦆ ~? right v = no (λ z → z)
(tup[ i ] d') ~? const x₁ = no (λ z → z)
(tup[ i ] d') ~? (V₁ ↦ v) = no (λ z → z)
(tup[ i ] d') ~? ν = no (λ z → z)
(tup[ i ] d') ~? ω = no (λ z → z)
(tup[ i ] d') ~? ⦅ d₁' ∣ = no (λ z → z)
(tup[ i ] d') ~? ∣ d₂' ⦆ = no (λ z → z)
(tup[_]_ {n} i d) ~? (tup[_]_ {n'} i' d') with n ≟ n'
... | no neq = no (λ z → neq (proj₁ z))
... | yes refl with i fin≟ i'
... | no neq = yes ⟨ refl , inj₁ neq ⟩
... | yes refl with d ~? d'
... | yes d~ = yes ⟨ refl , inj₂ ⟨ refl , d~ ⟩ ⟩
... | no ¬d~ = no λ z → ¬d~ ([ (λ x → ⊥-elim (x refl)) 
                            , (λ x → proj₂ x) ] (~-tup-inv {n}{i}{i'}{d} z))
(tup[ i ] d') ~? (left x₁) = no (λ z → z)
(tup[ i ] d') ~? (right x₁) = no (λ z → z)
(left x) ~? const x₁ = no (λ z → z)
(left x) ~? (V₁ ↦ v) = no (λ z → z)
(left x) ~? ν = no (λ z → z)
(left x) ~? ω = no (λ z → z)
(left x) ~? ⦅ d₁' ∣ = no (λ z → z)
(left x) ~? ∣ d₂' ⦆ = no (λ z → z)
(left x) ~? (tup[ i ] d') = no (λ z → z)
(left x) ~? (left x₁) = x ~? x₁
(left x) ~? (right x₁) = no (λ z → z)
(right x) ~? const x₁ = no (λ z → z)
(right x) ~? (V₁ ↦ v) = no (λ z → z)
(right x) ~? ν = no (λ z → z)
(right x) ~? ω = no (λ z → z)
(right x) ~? ⦅ d₁' ∣ = no (λ z → z)
(right x) ~? ∣ d₂' ⦆ = no (λ z → z)
(right x) ~? (tup[ i ] d') = no (λ z → z)
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


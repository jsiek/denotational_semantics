module Compiler.Model.Graph.Domain.ISWIM.Domain where

open import Primitives
open import SetsAsPredicates
open import abt.Sig using (Sig; ν; ■) public
open import abt.Var using (Var) public
open import abt.GSubst using (_•_) public
open import NewDenotProperties

open import Data.Empty using (⊥-elim) renaming (⊥ to False)
open import Data.List using (List ; _∷_ ; []; _++_; length; replicate)
open import Data.List.Relation.Unary.Any using (Any; here; there; any?)
open import Data.List.Relation.Unary.All 
  using (All; []; _∷_; head; tail; lookup; tabulate; all?)
  renaming (map to allmap)
open import Data.Nat using (ℕ; zero; suc; _≟_; _<_; z≤n; s≤s; _+_)
open import Data.Fin using (Fin; zero; suc)
open import Data.Fin.Properties using () renaming (_≟_ to _fin≟_)
open import Data.Product using (_×_; Σ; Σ-syntax; proj₁; proj₂; ∃; ∃-syntax; uncurry)
    renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Unit using (tt) renaming (⊤ to True)
open import Relation.Binary.PropositionalEquality
    using (_≡_; _≢_; refl; sym; trans; subst; cong; cong₂)
open import Relation.Nullary using (¬_; Dec; yes; no)


{- Denotational Values --------------------------------------------------------}

data Value : Set where
  const : {B : Base} → (k : base-rep B) → Value  {- A primitive constant of type B. -}
  _↦_ : (V : List Value) → (w : Value) → Value
      {- An entry in a function's graph. -}
  ν : Value      {- The empty function -}
  ω : Value          {- An error value, to serve as a default value in Envs and
                        to differentiate from converging -}
  ⦅_∣ : (u : Value) → Value  
  ∣_⦆ : (v : Value) → Value
         {- closure values are pairs, which we split up into car and cdr
            behaviors for easier distributivity properties.
            Think of a pair ⦅ u , v ⦆ as ⦅ u ∣ ⊔ ∣ v ⦆.  A closure whose
            environment is approximated by several values v₁ … vₙ is
            represented by the elements ∣ v₁ ⦆ … ∣ vₙ ⦆ of its denotation. -}
  tup[_]_ : ∀ {n} (i : Fin n) → (d : Value) → Value                 {- Tuples -}
  left : (d : Value) → Value                      {- Sums -}
  right : (d : Value) → Value                     {- Sums -}
  ⟨⟩ : Value                                      {- the empty tuple -}

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
⦅ u ∣ ~ ∣ v ⦆ = True
⦅ u ∣ ~ (tup[ i ] d) = False
⦅ u ∣ ~ left v = False
⦅ u ∣ ~ right v = False
∣ v ⦆ ~ const k = False
∣ v ⦆ ~ (V₁ ↦ w) = False
∣ v ⦆ ~ ν = False
∣ v ⦆ ~ ω = False
∣ v ⦆ ~ ⦅ w ∣ = True
∣ v ⦆ ~ ∣ v₁ ⦆ = v ~ v₁
∣ v ⦆ ~ (tup[ i ] d) = False
∣ v ⦆ ~ left w = False
∣ v ⦆ ~ right w = False
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
⟨⟩ ~ ⟨⟩ = True
⟨⟩ ~ (const k) = False
⟨⟩ ~ (V ↦ w) = False
⟨⟩ ~ ν = False
⟨⟩ ~ ω = False
⟨⟩ ~ ⦅ u ∣ = False
⟨⟩ ~ ∣ v ⦆ = False
⟨⟩ ~ (tup[ i ] d) = False
⟨⟩ ~ (left v) = False
⟨⟩ ~ (right v) = False
(const k) ~ ⟨⟩ = False
(V ↦ w) ~ ⟨⟩ = False
ν ~ ⟨⟩ = False
ω ~ ⟨⟩ = False
⦅ u ∣ ~ ⟨⟩ = False
∣ v ⦆ ~ ⟨⟩ = False
(tup[ i ] d) ~ ⟨⟩ = False
(left v) ~ ⟨⟩ = False
(right v) ~ ⟨⟩ = False

[] ≈ vs = True 
(u ∷ us) ≈ vs = All (u ~_) vs × us ≈ vs

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
⦅ u ∣ ~? ∣ v ⦆ = yes tt
⦅ u ∣ ~? (tup[ i ] d) = no (λ z → z)
⦅ u ∣ ~? left v = no (λ z → z)
⦅ u ∣ ~? right v = no (λ z → z)
∣ v ⦆ ~? const k = no (λ z → z)
∣ v ⦆ ~? (V₁ ↦ w) = no (λ z → z)
∣ v ⦆ ~? ν = no (λ z → z)
∣ v ⦆ ~? ω = no (λ z → z)
∣ v ⦆ ~? ⦅ w ∣ = yes tt
∣ v ⦆ ~? ∣ v₁ ⦆ = v ~? v₁
∣ v ⦆ ~? (tup[ i ] d) = no (λ z → z)
∣ v ⦆ ~? left w = no (λ z → z)
∣ v ⦆ ~? right w = no (λ z → z)
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
⟨⟩ ~? ⟨⟩ = yes tt
⟨⟩ ~? (const k) = no (λ z → z)
⟨⟩ ~? (V ↦ w) = no (λ z → z)
⟨⟩ ~? ν = no (λ z → z)
⟨⟩ ~? ω = no (λ z → z)
⟨⟩ ~? ⦅ u ∣ = no (λ z → z)
⟨⟩ ~? ∣ v ⦆ = no (λ z → z)
⟨⟩ ~? (tup[ i ] d) = no (λ z → z)
⟨⟩ ~? (left v) = no (λ z → z)
⟨⟩ ~? (right v) = no (λ z → z)
(const k) ~? ⟨⟩ = no (λ z → z)
(V ↦ w) ~? ⟨⟩ = no (λ z → z)
ν ~? ⟨⟩ = no (λ z → z)
ω ~? ⟨⟩ = no (λ z → z)
⦅ u ∣ ~? ⟨⟩ = no (λ z → z)
∣ v ⦆ ~? ⟨⟩ = no (λ z → z)
(tup[ i ] d) ~? ⟨⟩ = no (λ z → z)
(left v) ~? ⟨⟩ = no (λ z → z)
(right v) ~? ⟨⟩ = no (λ z → z)

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


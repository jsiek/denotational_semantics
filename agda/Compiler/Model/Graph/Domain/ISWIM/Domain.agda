module Compiler.Model.Graph.Domain.ISWIM.Domain where

open import Primitives
open import SetsAsPredicates
open import abt.Sig using (Sig; ν; ■) public
open import abt.Var using (Var) public
open import abt.GSubst using (_•_) public
open import NewDenotProperties

open import Data.Empty renaming (⊥ to False)
open import Data.List using (List ; _∷_ ; [])
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using (All; []; _∷_; lookup; tabulate)
open import Data.Fin using (Fin)
open import Data.Product using (_×_; Σ-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₂)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt) renaming (⊤ to True)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Relation.Nullary using (¬_)


{- Denotational Values --------------------------------------------------------}

data Value : Set where
  const : {B : Base} → (k : base-rep B) → Value  {- A primitive constant of type B. -}
  _↦_ : (V : List Value) → (w : Value) → Value
      {- An entry in a function's graph. -}
  ν : Value      {- The empty function -}
  ω : Value          {- An error value, to serve as a default value in Envs and
                        to differentiate from converging -}
  ⦅_,_⦆ : (u : Value) → (v : Value) → Value
         {- A pair. A closure is a pair of its code and its environment;
            a closure whose environment is approximated by several values
            v₁ … vₙ is represented by the elements ⦅ f , v₁ ⦆ … ⦅ f , vₙ ⦆
            of its denotation. -}
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
(V ↦ w) ~ (V' ↦ w') = V ≈ V' → w ~ w'
(V ↦ w) ~ ν = True
ν ~ (V ↦ w) = True
ν ~ ν = True
ω ~ ω = True {- ω is related to just itself -}
⦅ u , v ⦆ ~ ⦅ u' , v' ⦆ = u ~ u' × v ~ v'
(tup[_]_ {n} i d) ~ (tup[_]_ {n'} i' d')
    = Σ[ n≡ ∈ n ≡ n' ] ((¬ ((subst Fin n≡ i) ≡ i')) ⊎ ((subst Fin n≡ i) ≡ i' × d ~ d'))
(left x) ~ (left x₁) = x ~ x₁
(right x) ~ (right x₁) = x ~ x₁
⟨⟩ ~ ⟨⟩ = True
_ ~ _ = False

[] ≈ vs = True 
(u ∷ us) ≈ vs = All (u ~_) vs × us ≈ vs

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


{- every value is consistent with itself -}
~-refl : ∀ v → v ~ v
~-refl (const k) = ⟨ refl , refl ⟩
~-refl (V ↦ w) = λ _ → ~-refl w
~-refl ν = tt
~-refl ω = tt
~-refl ⦅ u , v ⦆ = ⟨ ~-refl u , ~-refl v ⟩
~-refl (tup[ i ] d) = ⟨ refl , inj₂ ⟨ refl , ~-refl d ⟩ ⟩
~-refl (left d) = ~-refl d
~-refl (right d) = ~-refl d
~-refl ⟨⟩ = tt

{- consistent sets, and environments of them: the binders Λ and 𝒞 bind
   only consistent sets -}
Con : 𝒫 Value → Set
Con D = Every _~_ D D

Con-env : (ℕ → 𝒫 Value) → Set
Con-env ρ = ∀ x → Con (ρ x)

Con-• : ∀ {D ρ} → Con D → Con-env ρ → Con-env (D • ρ)
Con-• c cρ zero = c
Con-• c cρ (suc x) = cρ x

Con-⌈⌉ : ∀ v → Con ⌈ v ⌉
Con-⌈⌉ v _ _ refl refl = ~-refl v

≈⇒Con : ∀ {V} → V ≈ V → Con (mem V)
≈⇒Con {V} = ≈⇒Every V V

Con-⊆ : ∀ {D E} → Con D → E ⊆ D → Con E
Con-⊆ c E⊆ = Every-⊆ c E⊆ E⊆

Con⇒≈ : ∀ {D} V → Con D → mem V ⊆ D → V ≈ V
Con⇒≈ V c V⊆ = Every⇒≈ V V (Con-⊆ c V⊆)

≈-single : ∀ {v} → (v ∷ []) ≈ (v ∷ [])
≈-single {v} = ⟨ ~-refl v ∷ [] , tt ⟩

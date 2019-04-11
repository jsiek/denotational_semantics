\begin{code}
module Adequate2 where
\end{code}

## Imports

\begin{code}
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; inspect)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum
open import Agda.Primitive using (lzero)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using (contradiction)
open import Data.Empty using (⊥-elim) renaming (⊥ to Bot)
open import Data.Unit using (⊤; tt)
open import Data.Maybe
open import Data.List using (List; _∷_; _++_; concat; map) renaming ([] to nil)
open import Data.List.NonEmpty using (List⁺; _∷_; _⁺++⁺_; toList) 
open import Data.Nat using (ℕ; suc; zero; _≤_)
open import Relation.Nullary using (Dec; yes; no)

open import Untyped
open import Denot_CBN_BCD
\end{code}

## Inversion of less-than for joins

[JGS: Move this to the section where ⊑ is defined.]

If the join v₁ ⊔ v₂ is less than another value v₃,
then both v₁ and v₂ are less than v₃.

\begin{code}
⊔⊑-invL : ∀{v₁ v₂ v₃ : Value}
        → v₁ ⊔ v₂ ⊑ v₃
          ---------
        → v₁ ⊑ v₃
⊔⊑-invL (ConjL⊑ lt1 lt2) = lt1
⊔⊑-invL (ConjR1⊑ lt) = ConjR1⊑ (⊔⊑-invL lt)
⊔⊑-invL (ConjR2⊑ lt) = ConjR2⊑ (⊔⊑-invL lt)
⊔⊑-invL (Trans⊑ lt1 lt2) = Trans⊑ (⊔⊑-invL lt1) lt2

⊔⊑-invR : ∀{v₁ v₂ v₃ : Value}
       → v₁ ⊔ v₂ ⊑ v₃
         ---------
       → v₂ ⊑ v₃
⊔⊑-invR (ConjL⊑ lt lt₁) = lt₁
⊔⊑-invR (ConjR1⊑ lt) = ConjR1⊑ (⊔⊑-invR lt)
⊔⊑-invR (ConjR2⊑ lt) = ConjR2⊑ (⊔⊑-invR lt)
⊔⊑-invR (Trans⊑ lt lt₁) = Trans⊑ (⊔⊑-invR lt) lt₁
\end{code}


## Inversion of the less-than relation for functions

[JGS: Move this to the section where ⊑ is defined.]

The inversion property for functions is subtle.  What can we deduce
from knowning that a function v₁ ↦ v₁' is less than some value v₂?
That is, what can we deduce about v₂?  This is not easy to answer
because of the Dist⊑ rule , which relates a function on the left to a
pair of functions on the right.  So v₂ may include several functions
that, as a group, relate to v₁ ↦ v₁'. Furthermore, because of the
rules ConjR1⊑ and ConjR2⊑, there may be other things inside v₂, such
as ⊥, that have nothing to do with v₁ ↦ v₁'. So in general, v₂ must
include a collection of functions whose domains are less than v₁ and
whose codomains are greater than v₁'. To precisely state and prove
this inversion property, we will need to define what it means for a
value to _include_ a collection of values.



### Value membership and inclusion

We first define what it means for a value to include another value.
Recall that we think of values as sets of entries with the join
operator v₁ ⊔ v₂ acting like set union. The function value v ↦ v' and
bottom value ⊥ constitute the two kinds of entries.  (In other
contexts one can instead think of ⊥ as the empty set, but here we must
think of it as a kind of element.)  So we write v ∈ v' to mean that v
is an element that is syntactically contained underneath any number of
joins in v'.

\begin{code}
infix 5 _∈_

_∈_ : Value → Value → Set
v ∈ ⊥ = v ≡ ⊥
v ∈ v₁ ↦ v₂ = v ≡ v₁ ↦ v₂
v ∈ (v₁ ⊔ v₂) = v ∈ v₁ ⊎ v ∈ v₂
\end{code}

Because values can represent sets, we can represent collections of
values simply as values. We write v₁ ⊆ v₂ if all the elements of v₁
are also in v₂.

\begin{code}
infix 5 _⊆_

_⊆_ : Value → Value → Set
v₁ ⊆ v₂ = ∀{v₃} → v₃ ∈ v₁ → v₃ ∈ v₂
\end{code}

These notions of membership and inclusion for values are closely
related to the less-than relation. They are narrower relations, they
imply the less-than relation but not the other way around.

\begin{code}
∈→⊑ : ∀{v₁ B : Value}
    → v₁ ∈ B
      -----
    → v₁ ⊑ B
∈→⊑ {.⊥} {⊥} refl = Bot⊑
∈→⊑ {.(B ↦ B₁)} {B ↦ B₁} refl = Refl⊑
∈→⊑ {v₁} {B ⊔ B₁} (inj₁ x) = ConjR1⊑ (∈→⊑ x)
∈→⊑ {v₁} {B ⊔ B₁} (inj₂ y) = ConjR2⊑ (∈→⊑ y)

⊆→⊑ : ∀{v₁ B : Value}
    → v₁ ⊆ B
      -----
    → v₁ ⊑ B
⊆→⊑ {⊥} {B} s with s {⊥} refl
... | x = Bot⊑
⊆→⊑ {v₁ ↦ v₁'} {B} s with s {v₁ ↦ v₁'} refl
... | x = ∈→⊑ x
⊆→⊑ {v₁ ⊔ v₁'} {B} s =
   ConjL⊑ (⊆→⊑ (λ {C} z → s (inj₁ z))) (⊆→⊑ (λ {C} z → s (inj₂ z)))
\end{code}

We shall need some inversion principles for value inclusion.  If the
union of v₁ and v₂ is included in v₃, then of course both v₁ and v₂
are each included in v₃.

\begin{code}
⊔⊆-inv : ∀{v₁ v₂ v₃ : Value}
       → (v₁ ⊔ v₂) ⊆ v₃
         ---------------
       → v₁ ⊆ v₃  ×  v₂ ⊆ v₃
⊔⊆-inv abc = ⟨ (λ {x} x₁ → abc (inj₁ x₁)) , (λ {x} x₁ → abc (inj₂ x₁)) ⟩
\end{code}

In our value representation, the function value v₁ ↦ v₂ is both an
element and also a singleton set. So if v₁ ↦ v₂ is a subset of v₃,
then v₁ ↦ v₂ must be a member of v₃.

\begin{code}
↦⊆→∈ : ∀{v₁ v₂ v₃ : Value}
     → v₁ ↦ v₂ ⊆ v₃
       ---------
     → v₁ ↦ v₂ ∈ v₃
↦⊆→∈{v₁}{v₂}{v₃} incl = incl {v₁ ↦ v₂} refl 
\end{code}


### Function values

To identify collections of functions, we define the following two
predicates. We write Fun v₁ if v₁ is a function value, that is if v₁ ≡
v ↦ v' for some values v and v'. We write Funs v if all the elements
of v are functions.

\begin{code}
data Fun : Value → Set where
  fun : ∀{v₁ v v'} → v₁ ≡ (v ↦ v') → Fun v₁

Funs : Value → Set
Funs v = ∀{v'} → v' ∈ v → Fun v'
\end{code}

Of course, the value ⊥ is not a function.

\begin{code}
¬Fun⊥ : ¬ (Fun ⊥)
¬Fun⊥ (fun ())
\end{code}

In our values-as-sets representation, our sets always include at least
one element. Thus, if all the elements are functions, there is at
least one element that is a function.

\begin{code}
Funs∈ : ∀{v₁}
      → Funs v₁
      → Σ[ B ∈ Value ] Σ[ B' ∈ Value ] B ↦ B' ∈ v₁
Funs∈ {⊥} f with f {⊥} refl
... | fun ()
Funs∈ {v₁ ↦ v₁'} f = ⟨ v₁ , ⟨ v₁' , refl ⟩ ⟩
Funs∈ {v₁ ⊔ v₁'} f
    with Funs∈ {v₁} λ {v'} z → f (inj₁ z)
... | ⟨ B , ⟨ B' , m ⟩ ⟩ = ⟨ B , ⟨ B' , (inj₁ m) ⟩ ⟩
\end{code}

[JGS: UNDER CONSTRUCTION]

\begin{code}
dom : (v : Value) → Value
dom ⊥  = ⊥
dom (v ↦ v') = v
dom (v ⊔ v') = dom v ⊔ dom v'
\end{code}

\begin{code}
cod : (v : Value) → Value
cod ⊥  = ⊥
cod (v ↦ v') = v'
cod (v ⊔ v') = cod v ⊔ cod v'
\end{code}


\begin{code}
fun∈→⊆dom : ∀{Γ D E : Value}
          → Funs Γ  →  (D ↦ E) ∈ Γ
            ----------------------
          → D ⊆ dom Γ
fun∈→⊆dom {⊥} fg ()
fun∈→⊆dom {v₁ ↦ B} fg refl = λ z → z
fun∈→⊆dom {Γ ⊔ Γ₁} fg (inj₁ x) =
  let ih = fun∈→⊆dom {Γ} (λ {v'} z → fg (inj₁ z)) x in
  λ x₁ → inj₁ (ih x₁)
fun∈→⊆dom {Γ ⊔ Γ₁} fg (inj₂ y) =
  let ih = fun∈→⊆dom {Γ₁} (λ {v'} z → fg (inj₂ z)) y in
  λ x₁ → inj₂ (ih x₁)
\end{code}


\begin{code}
Γ⊆A↦B→codΓ⊆B : ∀{Γ A B : Value}
      → Γ ⊆ A ↦ B
        ---------
      → cod Γ ⊆ B
Γ⊆A↦B→codΓ⊆B {⊥} s refl with s {⊥} refl
... | ()
Γ⊆A↦B→codΓ⊆B {C ↦ C'} s m with s {C ↦ C'} refl
... | refl = m
Γ⊆A↦B→codΓ⊆B {Γ ⊔ Γ₁} s (inj₁ x) = Γ⊆A↦B→codΓ⊆B (λ {C} z → s (inj₁ z)) x
Γ⊆A↦B→codΓ⊆B {Γ ⊔ Γ₁} s (inj₂ y) = Γ⊆A↦B→codΓ⊆B (λ {C} z → s (inj₂ z)) y
\end{code}


### Inversion of less-than for functions, the case for Trans⊑

\begin{code}
factor : (A : Value) → (Γ : Value) → (B' : Value) → (C' : Value) → Set
factor A Γ B' C' = Funs Γ × Γ ⊆ A × dom Γ ⊑ B' × C' ⊑ cod Γ
\end{code}


\begin{code}
sub-inv-trans : ∀{Γ' A D : Value}
    → Funs Γ'
    → Γ' ⊆ D
    → (∀{B' C'} → B' ↦ C' ∈ D → Σ[ Γ ∈ Value ] factor A Γ B' C')
      ----------------------------------------------------------
    → Σ[ Γ ∈ Value ] factor A Γ (dom Γ') (cod Γ')
sub-inv-trans {⊥} {A} {D} fg Γ'⊆D IH =
   ⊥-elim (contradiction (fg{v' = ⊥} refl) ¬Fun⊥)
sub-inv-trans {D₃ ↦ D₄} {A} {D} fg Γ'⊆D IH = IH (↦⊆→∈ Γ'⊆D)
sub-inv-trans {Γ₁ ⊔ Γ₂} {A} {D} fg Γ'⊆D IH
    with ⊔⊆-inv Γ'⊆D
... | ⟨ Γ₁⊆D , Γ₂⊆D ⟩
    with sub-inv-trans {Γ₁} {A} {D} (λ {v'} z → fg (inj₁ z)) Γ₁⊆D IH
       | sub-inv-trans {Γ₂} {A} {D} (λ {v'} z → fg (inj₂ z)) Γ₂⊆D IH
... | ⟨ Γ₁' , ⟨ fg1' , ⟨ Γ₁'⊆A , ⟨ domΓ₁'⊑domΓ₁ , codΓ₁⊑codΓ₁' ⟩ ⟩ ⟩ ⟩
    | ⟨ Γ₂' , ⟨ fg2' , ⟨ Γ₂'⊆A , ⟨ domΓ₂'⊑domΓ₂ , codΓ₁⊑codΓ₂' ⟩ ⟩ ⟩ ⟩ =
      ⟨ (Γ₁' ⊔ Γ₂') , ⟨ fg12 , ⟨ Γ₁₂⊆A , ⟨ ⊔⊑⊔ domΓ₁'⊑domΓ₁ domΓ₂'⊑domΓ₂ ,
                                           ⊔⊑⊔ codΓ₁⊑codΓ₁' codΓ₁⊑codΓ₂' ⟩ ⟩ ⟩ ⟩
    where fg12 : {v' : Value} → v' ∈ Γ₁' ⊎ v' ∈ Γ₂' → Fun v'
          fg12 {v'} (inj₁ x) = fg1' x
          fg12 {v'} (inj₂ y) = fg2' y

          Γ₁₂⊆A : {C : Value} → C ∈ Γ₁' ⊎ C ∈ Γ₂' → C ∈ A
          Γ₁₂⊆A {C} (inj₁ x) = Γ₁'⊆A x
          Γ₁₂⊆A {C} (inj₂ y) = Γ₂'⊆A y
\end{code}


### Inversion of less-than for functions

\begin{code}
sub-inv : ∀{A A' : Value}
        → A' ⊑ A
        → ∀{B' C'} → B' ↦ C' ∈ A'
          -------------------------------
        → Σ[ Γ ∈ Value ] factor A Γ B' C'
sub-inv {A} {⊥} Bot⊑ {B'} {C'} ()
sub-inv {A} {A'₁ ⊔ A'₂} (ConjL⊑ lt lt₁) {B'} {C'} (inj₁ x) = sub-inv lt x
sub-inv {A} {A'₁ ⊔ A'₂} (ConjL⊑ lt lt₁) {B'} {C'} (inj₂ y) = sub-inv lt₁ y
sub-inv {A₁ ⊔ A₂} {A'} (ConjR1⊑ lt) {B'} {C'} m
    with sub-inv lt m  
... | ⟨ Γ , ⟨ fg , ⟨ Γ⊆A₁ , ⟨ domΓ⊑B' , C'⊑codΓ ⟩ ⟩ ⟩ ⟩ =
      ⟨ Γ , ⟨ fg , ⟨ (λ {C} z → inj₁ (Γ⊆A₁ z)) , ⟨ domΓ⊑B' , C'⊑codΓ ⟩ ⟩ ⟩ ⟩
sub-inv {A₁ ⊔ A₂} {A'} (ConjR2⊑ lt) {B'} {C'} m
    with sub-inv lt m  
... | ⟨ Γ , ⟨ fg , ⟨ Γ⊆A₂ , ⟨ domΓ⊑B' , C'⊑codΓ ⟩ ⟩ ⟩ ⟩ =
      ⟨ Γ , ⟨ fg , ⟨ (λ {C} z → inj₂ (Γ⊆A₂ z)) , ⟨ domΓ⊑B' , C'⊑codΓ ⟩ ⟩ ⟩ ⟩
sub-inv {A} {A'} (Trans⊑ lt1 lt2) {B'} {C'} m
    with sub-inv lt1 m
... | ⟨ Γ' , ⟨ fg' , ⟨ Γ'⊆D , ⟨ domΓ'⊑B' , C'⊑codΓ' ⟩ ⟩ ⟩ ⟩ 
    with sub-inv-trans {Γ'} fg' Γ'⊆D (sub-inv lt2) 
... | ⟨ Γ , ⟨ fg , ⟨ Γ⊆A , ⟨ domΓ⊑domΓ' , codΓ'⊑codΓ ⟩ ⟩ ⟩ ⟩ =
      ⟨ Γ , ⟨ fg , ⟨ Γ⊆A , ⟨ Trans⊑ domΓ⊑domΓ' domΓ'⊑B' ,
                             Trans⊑ C'⊑codΓ' codΓ'⊑codΓ ⟩ ⟩ ⟩ ⟩
sub-inv {A₁ ↦ A₂} {A'₁ ↦ A'₂} (Fun⊑ lt1 lt2) refl =
  ⟨ A₁ ↦ A₂ , ⟨ (λ {v'} → fun) , ⟨ (λ {C} z → z) , ⟨ lt1 , lt2 ⟩ ⟩ ⟩ ⟩
sub-inv {A₁ ↦ A₂ ⊔ A₁ ↦ A₃} {A₁ ↦ (A₂ ⊔ A₃)} Dist⊑ {.A₁} {.(A₂ ⊔ A₃)} refl =
  ⟨ A₁ ↦ A₂ ⊔ A₁ ↦ A₃ , ⟨ f , ⟨ g , ⟨ (ConjL⊑ Refl⊑ Refl⊑) ,
     ⊔⊑⊔ Refl⊑ Refl⊑ ⟩ ⟩ ⟩ ⟩
  where f : Funs (A₁ ↦ A₂ ⊔ A₁ ↦ A₃)
        f (inj₁ x) = fun x
        f (inj₂ y) = fun y
        g : (A₁ ↦ A₂ ⊔ A₁ ↦ A₃) ⊆ (A₁ ↦ A₂ ⊔ A₁ ↦ A₃)
        g (inj₁ x) = inj₁ x
        g (inj₂ y) = inj₂ y
\end{code}

\begin{code}
sub-inv-fun : ∀{A B C : Value}
    → (A ↦ B) ⊑ C
      --------------------------------------------------------------------------
    → Σ[ Γ ∈ Value ] Funs Γ × Γ ⊆ C × (∀{D E} → (D ↦ E) ∈ Γ → D ⊑ A) × B ⊑ cod Γ
sub-inv-fun{A}{B}{C} abc
    with sub-inv abc {A}{B} refl
... | ⟨ Γ , ⟨ f , ⟨ Γ⊆C , ⟨ db , cc ⟩ ⟩ ⟩ ⟩ =
      ⟨ Γ , ⟨ f , ⟨ Γ⊆C , ⟨ G , cc ⟩ ⟩ ⟩ ⟩
   where G : ∀{D E} → (D ↦ E) ∈ Γ → D ⊑ A
         G{D}{E} m = Trans⊑ (⊆→⊑ (fun∈→⊆dom f m)) db
\end{code}

\begin{code}
↦⊑↦-inv : ∀{v₁ v₂ v₃ v₄}
        → v₁ ↦ v₂ ⊑ v₃ ↦ v₄
          -----------------
        → v₃ ⊑ v₁ × v₂ ⊑ v₄
↦⊑↦-inv{v₁}{v₂}{v₃}{v₄} lt
    with sub-inv-fun lt  
... | ⟨ Γ , ⟨ f , ⟨ Γ⊆v34 , ⟨ lt1 , lt2 ⟩ ⟩ ⟩ ⟩
    with Funs∈ f
... | ⟨ A , ⟨ A' , A↦A'∈Γ ⟩ ⟩
    with Γ⊆v34 A↦A'∈Γ
... | refl =    
  let codΓ⊆v₄ = Γ⊆A↦B→codΓ⊆B Γ⊆v34 in
  ⟨ lt1 A↦A'∈Γ , Trans⊑ lt2 (⊆→⊑ codΓ⊆v₄) ⟩
\end{code}


## Properties of being above a function (more corollaries)


\begin{code}
AboveFun : Value → Set
AboveFun v = Σ[ v₁ ∈ Value ] Σ[ v₂ ∈ Value ] v₁ ↦ v₂ ⊑ v
\end{code}

\begin{code}
AboveFun-⊑ : ∀{v v' : Value}
      → AboveFun v → v ⊑ v'
        -------------------
      → AboveFun v'
AboveFun-⊑ ⟨ v₁ , ⟨ v₂ , lt' ⟩ ⟩ lt = ⟨ v₁ , ⟨ v₂ , Trans⊑ lt' lt ⟩ ⟩
\end{code}

\begin{code}
not-AboveFun-⊔-inv : ∀{v₁ v₂ : Value} → ¬ AboveFun (v₁ ⊔ v₂)
              → ¬ AboveFun v₁ × ¬ AboveFun v₂
not-AboveFun-⊔-inv af = ⟨ f af , g af ⟩
  where
    f : ∀{v₁ v₂ : Value} → ¬ AboveFun (v₁ ⊔ v₂) → ¬ AboveFun v₁
    f{v₁}{v₂} af12 ⟨ v , ⟨ v' , lt ⟩ ⟩ =
        contradiction ⟨ v , ⟨ v' , ConjR1⊑ lt ⟩ ⟩ af12
    g : ∀{v₁ v₂ : Value} → ¬ AboveFun (v₁ ⊔ v₂) → ¬ AboveFun v₂
    g{v₁}{v₂} af12 ⟨ v , ⟨ v' , lt ⟩ ⟩ =
        contradiction ⟨ v , ⟨ v' , ConjR2⊑ lt ⟩ ⟩ af12
\end{code}

\begin{code}
AboveFun⊥ : ¬ AboveFun ⊥
AboveFun⊥ ⟨ v₁ , ⟨ v₂ , lt ⟩ ⟩
    with sub-inv-fun lt
... | ⟨ Γ , ⟨ f , ⟨ Γ⊆⊥ , ⟨ lt1 , lt2 ⟩ ⟩ ⟩ ⟩
    with Funs∈ f
... | ⟨ A , ⟨ B , m ⟩ ⟩
    with Γ⊆⊥ m
... | ()
\end{code}


\begin{code}
AboveFun-⊔ : ∀{v₁ v₂}
           → AboveFun (v₁ ⊔ v₂)
           → AboveFun v₁ ⊎ AboveFun v₂
AboveFun-⊔{v₁}{v₂} ⟨ v , ⟨ v' , v↦v'⊑v₁⊔v₂ ⟩ ⟩ 
    with sub-inv-fun v↦v'⊑v₁⊔v₂
... | ⟨ Γ , ⟨ f , ⟨ Γ⊆v₁⊔v₂ , ⟨ lt1 , lt2 ⟩ ⟩ ⟩ ⟩
    with Funs∈ f
... | ⟨ A , ⟨ B , m ⟩ ⟩
    with Γ⊆v₁⊔v₂ m
... | inj₁ x = inj₁ ⟨ A , ⟨ B , (∈→⊑ x) ⟩ ⟩
... | inj₂ x = inj₂ ⟨ A , ⟨ B , (∈→⊑ x) ⟩ ⟩
\end{code}


\begin{code}
not-AboveFun-⊔ : ∀{v₁ v₂ : Value}
               → ¬ AboveFun v₁ → ¬ AboveFun v₂
               → ¬ AboveFun (v₁ ⊔ v₂)
not-AboveFun-⊔ af1 af2 af12
    with AboveFun-⊔ af12
... | inj₁ x = contradiction x af1
... | inj₂ x = contradiction x af2
\end{code}


\begin{code}
AboveFun? : (v : Value) → Dec (AboveFun v)
AboveFun? ⊥ = no AboveFun⊥
AboveFun? (v ↦ v') = yes ⟨ v , ⟨ v' , Refl⊑ ⟩ ⟩
AboveFun? (v₁ ⊔ v₂)
    with AboveFun? v₁ | AboveFun? v₂
... | yes ⟨ v , ⟨ v' , lt ⟩ ⟩ | _ = yes ⟨ v , ⟨ v' , (ConjR1⊑ lt) ⟩ ⟩
... | no _ | yes ⟨ v , ⟨ v' , lt ⟩ ⟩ = yes ⟨ v , ⟨ v' , (ConjR2⊑ lt) ⟩ ⟩
... | no x | no y = no (not-AboveFun-⊔ x y)
\end{code}


## Big-step semantics for call-by-name lambda calculus

\begin{code}
data Clos : Set

data ClosEnv : Context → Set where
  ∅ : ClosEnv ∅
  _,_ : ∀{Γ} → ClosEnv Γ → Clos → ClosEnv (Γ , ★)
  
data Clos where
  clos : ∀{Γ} → (M : Γ ⊢ ★) → ClosEnv Γ → Clos
\end{code}

\begin{code}
kth : ∀{Γ} → (Γ ∋ ★) → ClosEnv Γ → Clos
kth () ∅
kth Z (ρ , v) = v
kth (S x) (ρ , v) = kth x ρ
\end{code}

\begin{code}
data _⊢_⇓_ : ∀{Γ} → ClosEnv Γ → (Γ ⊢ ★) → Clos → Set where

  ⇓-var : ∀{Γ}{γ : ClosEnv Γ}{x : Γ ∋ ★}{Δ}{δ : ClosEnv Δ}{M : Δ ⊢ ★}{c}
        → kth x γ ≡ clos M δ
        → δ ⊢ M ⇓ c
          -----------
        → γ ⊢ ` x ⇓ c

  ⇓-lam : ∀{Γ}{γ : ClosEnv Γ}{M : Γ , ★ ⊢ ★}
        → γ ⊢ ƛ M ⇓ clos (ƛ M) γ

  ⇓-app : ∀{Γ}{γ : ClosEnv Γ}{L M : Γ ⊢ ★}{Δ}{δ : ClosEnv Δ}{L' : Δ , ★ ⊢ ★}{c}
       → γ ⊢ L ⇓ clos (ƛ L') δ   →   (δ , clos M γ) ⊢ L' ⇓ c
         ---------------------------------------------------
       → γ ⊢ L · M ⇓ c
\end{code}


\begin{code}
⇓-determ : ∀{Γ}{γ : ClosEnv Γ}{M : Γ ⊢ ★}{c c' : Clos}
         → γ ⊢ M ⇓ c → γ ⊢ M ⇓ c'
         → c ≡ c'
⇓-determ (⇓-var eq1 mc) (⇓-var eq2 mc')
      with trans (sym eq1) eq2
... | refl = ⇓-determ mc mc'
⇓-determ ⇓-lam ⇓-lam = refl
⇓-determ (⇓-app mc mc₁) (⇓-app mc' mc'') 
    with ⇓-determ mc mc'
... | refl = ⇓-determ mc₁ mc''
\end{code}



## Adequacy of the denotational semantics

\begin{code}
data WHNF : ∀ {Γ A} → Γ ⊢ A → Set where

  ƛ_ : ∀ {Γ} {N : Γ , ★ ⊢ ★}
     → WHNF (ƛ N)
\end{code}


### Relating values to big-step values (closures)

\begin{code}
𝔼 : Value → Clos → Set
𝕍 : Value → Clos → Set
\end{code}

\begin{code}
𝕍 v (clos (` x₁) γ) = Bot
𝕍 v (clos (M · M₁) γ) = Bot
𝕍 ⊥ (clos (ƛ M) γ) = ⊤
𝕍 (v ↦ v') (clos (ƛ M) γ) =
     (∀{c : Clos} → 𝔼 v c → AboveFun v' → Σ[ c' ∈ Clos ]
           (γ , c) ⊢ M ⇓ c'  ×  𝕍 v' c')
𝕍 (v₁ ⊔ v₂) (clos (ƛ M) γ) = 𝕍 v₁ (clos (ƛ M) γ) × 𝕍 v₂ (clos (ƛ M) γ)
\end{code}

\begin{code}
𝔼 v (clos M γ) = AboveFun v → Σ[ c ∈ Clos ] γ ⊢ M ⇓ c × 𝕍 v c
\end{code}

\begin{code}
𝔾 : ∀{Γ} → Env Γ → ClosEnv Γ → Set
𝔾 ∅ ∅ = ⊤
𝔾 (γ , v) (γ' , c) = 𝔾 γ γ' × 𝔼 v c
\end{code}



\begin{code}
𝕍→WHNF : ∀{Γ}{γ : ClosEnv Γ}{M : Γ ⊢ ★}{v} → 𝕍 v (clos M γ) → WHNF M
𝕍→WHNF {M = ` x} {v} ()
𝕍→WHNF {M = ƛ M} {v} vc = ƛ_
𝕍→WHNF {M = M · M₁} {v} ()
\end{code}

\begin{code}
𝕍→lam : ∀{c v} → 𝕍 v c → Σ[ Γ ∈ Context ] Σ[ γ ∈ ClosEnv Γ ] Σ[ M ∈ Γ , ★ ⊢ ★ ]
                 c ≡ clos (ƛ M) γ
𝕍→lam {clos (` x₁) x} ()
𝕍→lam {clos {Γ} (ƛ M) x} vc = ⟨ Γ , ⟨ x , ⟨ M , refl ⟩ ⟩ ⟩
𝕍→lam {clos (M · M₁) x} ()
\end{code}


\begin{code}
𝕍⊔-intro : ∀{c v₁ v₂} → 𝕍 v₁ c → 𝕍 v₂ c → 𝕍 (v₁ ⊔ v₂) c
𝕍⊔-intro {clos (` x₁) x} () v2c
𝕍⊔-intro {clos (ƛ M) x} v1c v2c = ⟨ v1c , v2c ⟩
𝕍⊔-intro {clos (M · M₁) x} () v2c
\end{code}

\begin{code}
not-AboveFun-𝕍 : ∀{v : Value}{Γ}{γ' : ClosEnv Γ}{M : Γ , ★ ⊢ ★ }
               → ¬ AboveFun v → 𝕍 v (clos (ƛ M) γ')
not-AboveFun-𝕍 {⊥} af = tt
not-AboveFun-𝕍 {v ↦ v'} af = ⊥-elim (contradiction ⟨ v , ⟨ v' , Refl⊑ ⟩ ⟩ af)
not-AboveFun-𝕍 {v₁ ⊔ v₂} af
    with not-AboveFun-⊔-inv af
... | ⟨ af1 , af2 ⟩ =
    ⟨ not-AboveFun-𝕍 af1 , not-AboveFun-𝕍 af2 ⟩
\end{code}


\begin{code}
sub-𝕍 : ∀{c : Clos}{v v'} → 𝕍 v c → v' ⊑ v → 𝕍 v' c
sub-𝔼 : ∀{c : Clos}{v v'} → 𝔼 v c → v' ⊑ v → 𝔼 v' c
\end{code}

\begin{code}
sub-𝕍 {clos (` x₁) x} {v} vc Bot⊑ = vc
sub-𝕍 {clos (ƛ M) x} {v} vc Bot⊑ = tt
sub-𝕍 {clos (M · M₁) x} {v} vc Bot⊑ = vc
sub-𝕍 {clos (` x₁) x} {v} () (ConjL⊑ lt lt₁)
sub-𝕍 {clos (ƛ M) x} {v} vc (ConjL⊑ lt₁ lt₂) = ⟨ (sub-𝕍 vc lt₁) , sub-𝕍 vc lt₂ ⟩
sub-𝕍 {clos (M · M₁) x} {v} () (ConjL⊑ lt lt₁)
sub-𝕍 {clos (` x₁) x} {.(_ ⊔ _)} () (ConjR1⊑ lt)
sub-𝕍 {clos (ƛ M) x} {.(_ ⊔ _)} ⟨ vv1 , vv2 ⟩ (ConjR1⊑ lt) = sub-𝕍 vv1 lt
sub-𝕍 {clos (M · M₁) x} {.(_ ⊔ _)} () (ConjR1⊑ lt)
sub-𝕍 {clos (` x₁) x} {.(_ ⊔ _)} () (ConjR2⊑ lt)
sub-𝕍 {clos (ƛ M) x} {.(_ ⊔ _)} ⟨ vv1 , vv2 ⟩ (ConjR2⊑ lt) = sub-𝕍 vv2 lt
sub-𝕍 {clos (M · M₁) x} {.(_ ⊔ _)} () (ConjR2⊑ lt)
sub-𝕍 {c} {v} vc (Trans⊑{v₂ = v₂} lt lt₁) =
    sub-𝕍 {c} {v₂} (sub-𝕍 {c}{v} vc lt₁) lt
sub-𝕍 {clos (` x₁) x} {.(_ ↦ _)} () (Fun⊑ lt lt₁)
sub-𝕍 {clos (ƛ M) x} {.(_ ↦ _)} vc (Fun⊑ lt lt₁) ev1 sf
    with vc (sub-𝔼 ev1 lt) (AboveFun-⊑ sf lt₁)
... | ⟨ c , ⟨ Mc , v4 ⟩ ⟩ = ⟨ c , ⟨ Mc , sub-𝕍 v4 lt₁ ⟩ ⟩
sub-𝕍 {clos (M · M₁) x} {.(_ ↦ _)} () (Fun⊑ lt lt₁)
sub-𝕍 {clos (` x₁) x} {.(_ ↦ _ ⊔ _ ↦ _)} () Dist⊑
sub-𝕍 {clos (ƛ M) γ} {v₁ ↦ v₂ ⊔ v₁ ↦ v₃} ⟨ vc12 , vc13 ⟩
    Dist⊑ ev1c ⟨ v , ⟨ v' , lt ⟩ ⟩
    with AboveFun? v₂ | AboveFun? v₃
... | yes af2 | no naf3
    with vc12 ev1c af2
... | ⟨ c2 , ⟨ M⇓c2 , 𝕍2c ⟩ ⟩ 
    with 𝕍→lam 𝕍2c
... | ⟨ Γ' , ⟨ δ , ⟨ N , eq ⟩ ⟩ ⟩ rewrite eq =
      let 𝕍3c = not-AboveFun-𝕍{v₃}{Γ'}{δ}{N} naf3 in
      ⟨ clos (ƛ N) δ , ⟨ M⇓c2 , 𝕍⊔-intro 𝕍2c 𝕍3c ⟩ ⟩
sub-𝕍 {c} {v₁ ↦ v₂ ⊔ v₁ ↦ v₃} ⟨ vc12 , vc13 ⟩  Dist⊑ ev1c ⟨ v , ⟨ v' , lt ⟩ ⟩
    | no naf2 | yes af3
    with vc13 ev1c af3
... | ⟨ c3 , ⟨ M⇓c3 , 𝕍3c ⟩ ⟩ 
    with 𝕍→lam 𝕍3c
... | ⟨ Γ' , ⟨ δ , ⟨ N , eq ⟩ ⟩ ⟩ rewrite eq =
      let 𝕍2c = not-AboveFun-𝕍{v₂}{Γ'}{δ}{N} naf2 in
      ⟨ clos (ƛ N) δ , ⟨ M⇓c3 , 𝕍⊔-intro 𝕍2c 𝕍3c ⟩ ⟩
sub-𝕍 {c} {v₁ ↦ v₂ ⊔ v₁ ↦ v₃} ⟨ vc12 , vc13 ⟩  Dist⊑ ev1c ⟨ v , ⟨ v' , lt ⟩ ⟩
    | no naf2 | no naf3
    with AboveFun-⊔ ⟨ v , ⟨ v' , lt ⟩ ⟩
... | inj₁ af2 = ⊥-elim (contradiction af2 naf2)
... | inj₂ af3 = ⊥-elim (contradiction af3 naf3)
sub-𝕍 {c} {v₁ ↦ v₂ ⊔ v₁ ↦ v₃} ⟨ vc12 , vc13 ⟩  Dist⊑ ev1c ⟨ v , ⟨ v' , lt ⟩ ⟩
    | yes af2 | yes af3
    with vc12 ev1c af2 | vc13 ev1c af3
... | ⟨ clos N δ , ⟨ Mc1 , v4 ⟩ ⟩
    | ⟨ c2 , ⟨ Mc2 , v5 ⟩ ⟩ rewrite ⇓-determ Mc2 Mc1 with 𝕍→WHNF v4
... | ƛ_ =
      ⟨ clos N δ , ⟨ Mc1 , ⟨ v4 , v5 ⟩ ⟩ ⟩
sub-𝕍 {clos (M · M₁) x} {.(_ ↦ _ ⊔ _ ↦ _)} () Dist⊑ 
\end{code}

\begin{code}
sub-𝔼 {clos M x} {v} {v'} evc lt fv
    with evc (AboveFun-⊑ fv lt)
... | ⟨ c , ⟨ Mc , vvc ⟩ ⟩ =
      ⟨ c , ⟨ Mc , sub-𝕍 vvc lt ⟩ ⟩
\end{code}


\begin{code}
𝔾-nth : ∀{Γ}{γ : Env Γ}{γ' : ClosEnv Γ}{x : Γ ∋ ★}
         → 𝔾 γ γ' → 𝔼 (nth x γ) (kth x γ')
𝔾-nth {∅} {∅} {∅} {()} tt
𝔾-nth {Γ , ★} {γ , x} {γ' , x₁} {Z} ⟨ fst , snd ⟩ = snd
𝔾-nth {Γ , ★} {γ , x} {γ' , x₁} {S k} ⟨ fst , snd ⟩ = 𝔾-nth fst
\end{code}

\begin{code}
kth-x : ∀{Γ}{γ' : ClosEnv Γ}{x : Γ ∋ ★}
     → Σ[ Δ ∈ Context ] Σ[ δ ∈ ClosEnv Δ ] Σ[ M ∈ Δ ⊢ ★ ]
                 kth x γ' ≡ clos M δ
kth-x{γ' = γ'}{x = x} with kth x γ'
... | clos{Γ = Δ} M δ = ⟨ Δ , ⟨ δ , ⟨ M , refl ⟩ ⟩ ⟩
\end{code}


### Programs with function denotation terminate via call-by-name  

\begin{code}
↓→𝔼 : ∀{Γ}{γ : Env Γ}{γ' : ClosEnv Γ}{M : Γ ⊢ ★ }{v}
            → 𝔾 γ γ' → γ ⊢ M ↓ v → 𝔼 v (clos M γ')
↓→𝔼 {Γ} {γ} {γ'} {`_ x} {v} g var sf 
    with kth-x{Γ}{γ'}{x} | 𝔾-nth{x = x} g
... | ⟨ Δ , ⟨ δ , ⟨ M , eq ⟩ ⟩ ⟩ | g' rewrite eq
    with g' sf
... | ⟨ c , ⟨ L⇓c , Vnc ⟩ ⟩ =
      ⟨ c , ⟨ (⇓-var eq L⇓c) , Vnc ⟩ ⟩
↓→𝔼 {Γ} {γ} {γ'} {L · M} {v} g (↦-elim{v₁ = v₁} d₁ d₂) sf
    with ↓→𝔼 g d₁ ⟨ v₁ , ⟨ v , Refl⊑ ⟩ ⟩
... | ⟨ clos (` x) δ , ⟨ L⇓c , () ⟩ ⟩
... | ⟨ clos (L' · M') δ , ⟨ L⇓c , () ⟩ ⟩ 
... | ⟨ clos (ƛ L') δ , ⟨ L⇓c , Vc ⟩ ⟩
    with Vc {clos M γ'} (↓→𝔼 g d₂) sf
... | ⟨ c' , ⟨ L'⇓c' , Vc' ⟩ ⟩ =
    ⟨ c' , ⟨ ⇓-app L⇓c L'⇓c' , Vc' ⟩ ⟩
↓→𝔼 {Γ} {γ} {γ'} {ƛ M} {v ↦ v'} g (↦-intro d) sf =
  ⟨ (clos (ƛ M) γ') , ⟨ ⇓-lam , G ⟩ ⟩
  where G : {c : Clos} → 𝔼 v c → AboveFun v'
          → Σ-syntax Clos (λ c' → ((γ' , c) ⊢ M ⇓ c') × 𝕍 v' c')
        G {c} evc sfv' =
           ↓→𝔼{Γ , ★}{γ , v}{γ' , c}{M}{v'} ⟨ g , evc ⟩ d sfv'
↓→𝔼 {Γ} {γ} {γ'} {M} {⊥} g ⊥-intro sf = ⊥-elim (AboveFun⊥ sf)
↓→𝔼 {Γ} {γ} {γ'} {M} {v₁ ⊔ v₂} g (⊔-intro d₁ d₂) af12
    with AboveFun? v₁ | AboveFun? v₂
↓→𝔼 g (⊔-intro{v₁ = v₁}{v₂ = v₂} d₁ d₂) af12 | yes af1 | no naf2
    with ↓→𝔼 g d₁ af1 
... | ⟨ c1 , ⟨ M⇓c1 , 𝕍1c ⟩ ⟩
    with 𝕍→lam 𝕍1c
... | ⟨ Γ , ⟨ γ , ⟨ M , eq ⟩ ⟩ ⟩ rewrite eq =     
    let 𝕍2c = not-AboveFun-𝕍{v₂}{Γ}{γ}{M} naf2 in
    ⟨ clos (ƛ M) γ , ⟨ M⇓c1 , 𝕍⊔-intro 𝕍1c 𝕍2c ⟩ ⟩
↓→𝔼 g (⊔-intro{v₁ = v₁}{v₂ = v₂} d₁ d₂) af12 | no naf1  | yes af2
    with ↓→𝔼 g d₂ af2
... | ⟨ c2 , ⟨ M⇓c2 , 𝕍2c ⟩ ⟩
    with 𝕍→lam 𝕍2c
... | ⟨ Γ , ⟨ γ , ⟨ M , eq ⟩ ⟩ ⟩ rewrite eq =     
    let 𝕍1c = not-AboveFun-𝕍{v₁}{Γ}{γ}{M} naf1 in
    ⟨ clos (ƛ M) γ , ⟨ M⇓c2 , 𝕍⊔-intro 𝕍1c 𝕍2c ⟩ ⟩
↓→𝔼 g (⊔-intro d₁ d₂) af12 | no naf1  | no naf2
    with AboveFun-⊔ af12
... | inj₁ af1 = ⊥-elim (contradiction af1 naf1)
... | inj₂ af2 = ⊥-elim (contradiction af2 naf2)
↓→𝔼 g (⊔-intro d₁ d₂) af12 | yes af1 | yes af2
    with ↓→𝔼 g d₁ af1 | ↓→𝔼 g d₂ af2 
... | ⟨ c1 , ⟨ M⇓c1 , 𝕍1c ⟩ ⟩ | ⟨ c2 , ⟨ M⇓c2 , 𝕍2c ⟩ ⟩
    rewrite ⇓-determ M⇓c2 M⇓c1 =
      ⟨ c1 , ⟨ M⇓c1 , 𝕍⊔-intro 𝕍1c 𝕍2c ⟩ ⟩
↓→𝔼 {Γ} {γ} {γ'} {M} {v} g (sub d lt) sf 
    with ↓→𝔼 {Γ} {γ} {γ'} {M} g d (AboveFun-⊑ sf lt)
... | ⟨ c , ⟨ M⇓c , 𝕍c ⟩ ⟩ =
      ⟨ c , ⟨ M⇓c , sub-𝕍 𝕍c lt ⟩ ⟩
\end{code}


### Proof of denotational adequacy (corollary of termination)


\begin{code}
adequacy : ∀{M : ∅ ⊢ ★}{N : ∅ , ★ ⊢ ★}  →  ℰ M ≃ ℰ (ƛ N)
         →  Σ[ c ∈ Clos ] ∅ ⊢ M ⇓ c
adequacy{M}{N} eq 
    with ↓→𝔼 tt ((proj₂ eq) (↦-intro ⊥-intro)) ⟨ ⊥ , ⟨ ⊥ , Refl⊑ ⟩ ⟩
... | ⟨ c , ⟨ M⇓c , Vc ⟩ ⟩ = ⟨ c , M⇓c ⟩
\end{code}

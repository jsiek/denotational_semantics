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

What can we deduce from knowing that a function v₁ ↦ v₁' is less than
some value v₂?  What can we deduce about v₂? The answer to this
question is called the inversion property of less-than for functions.
This question is not easy to answer because of the Dist⊑ rule, which
relates a function on the left to a pair of functions on the right.
So v₂ may include several functions that, as a group, relate to v₁ ↦
v₁'. Furthermore, because of the rules ConjR1⊑ and ConjR2⊑, there may
be other values inside v₂, such as ⊥, that have nothing to do with v₁
↦ v₁'. But in general, we can deduce that v₂ includes a collection of
functions where the join of their domains is less than v₁ and the join
of their codomains is greater than v₁'.

To precisely state and prove this inversion property, we need to
define what it means for a value to _include_ a collection of values.
We also need to define how to compute the join of their domains and
codomains.


### Value membership and inclusion

Recall that we think of a value as a set of entries with the join
operator v₁ ⊔ v₂ acting like set union. The function value v ↦ v' and
bottom value ⊥ constitute the two kinds of elements of the set.  (In
other contexts one can instead think of ⊥ as the empty set, but here
we must think of it as an element.)  We write v ∈ v' to say that v is
an element of v', as defined below.

\begin{code}
infix 5 _∈_

_∈_ : Value → Value → Set
v ∈ ⊥ = v ≡ ⊥
v ∈ v₁ ↦ v₂ = v ≡ v₁ ↦ v₂
v ∈ (v₁ ⊔ v₂) = v ∈ v₁ ⊎ v ∈ v₂
\end{code}

So we can represent a collection of values simply as a value.  We
write v₁ ⊆ v₂ to say that all the elements of v₁ are also in v₂.

\begin{code}
infix 5 _⊆_

_⊆_ : Value → Value → Set
v₁ ⊆ v₂ = ∀{v₃} → v₃ ∈ v₁ → v₃ ∈ v₂
\end{code}

The notions of membership and inclusion for values are closely related
to the less-than relation. They are narrower relations in that they
imply the less-than relation but not the other way around.

\begin{code}
∈→⊑ : ∀{v₁ v₂ : Value}
    → v₁ ∈ v₂
      -----
    → v₁ ⊑ v₂
∈→⊑ {.⊥} {⊥} refl = Bot⊑
∈→⊑ {.(v₂ ↦ v₂₁)} {v₂ ↦ v₂₁} refl = Refl⊑
∈→⊑ {v₁} {v₂ ⊔ v₂₁} (inj₁ x) = ConjR1⊑ (∈→⊑ x)
∈→⊑ {v₁} {v₂ ⊔ v₂₁} (inj₂ y) = ConjR2⊑ (∈→⊑ y)

⊆→⊑ : ∀{v₁ v₂ : Value}
    → v₁ ⊆ v₂
      -----
    → v₁ ⊑ v₂
⊆→⊑ {⊥} {v₂} s with s {⊥} refl
... | x = Bot⊑
⊆→⊑ {v₁ ↦ v₁'} {v₂} s with s {v₁ ↦ v₁'} refl
... | x = ∈→⊑ x
⊆→⊑ {v₁ ⊔ v₁'} {v₂} s =
   ConjL⊑ (⊆→⊑ (λ {C} z → s (inj₁ z))) (⊆→⊑ (λ {C} z → s (inj₂ z)))
\end{code}

We shall also need some inversion principles for value inclusion.  If
the union of v₁ and v₂ is included in v₃, then of course both v₁ and
v₂ are each included in v₃.

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
predicates. We write Fun v₁ if v₁ is a function value, that is, if v₁
≡ v ↦ v' for some values v and v'. We write Funs v if all the elements
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
least one that is a function.

\begin{code}
Funs∈ : ∀{v₁}
      → Funs v₁
      → Σ[ v ∈ Value ] Σ[ v' ∈ Value ] v ↦ v' ∈ v₁
Funs∈ {⊥} f with f {⊥} refl
... | fun ()
Funs∈ {v ↦ v'} f = ⟨ v , ⟨ v' , refl ⟩ ⟩
Funs∈ {v₁ ⊔ v₂} f
    with Funs∈ {v₁} λ {v'} z → f (inj₁ z)
... | ⟨ v , ⟨ v' , m ⟩ ⟩ = ⟨ v , ⟨ v' , (inj₁ m) ⟩ ⟩
\end{code}


### Domains and codomains

Returning to our goal, the inversion principle for less-than a
function, we want to show that v₁ ↦ v₁' ⊑ v₂ implies that v₂ includes
a set of function values such that the join of their domains is less
than v₁ and the join of their codomains is greater than v₁'.

To this end we define the following dom and cod functions.  Given some
value v (that represents a set of entries), dom v returns the join of
their domains and cod v returns the join of their codomains.

\begin{code}
dom : (v : Value) → Value
dom ⊥  = ⊥
dom (v ↦ v') = v
dom (v ⊔ v') = dom v ⊔ dom v'

cod : (v : Value) → Value
cod ⊥  = ⊥
cod (v ↦ v') = v'
cod (v ⊔ v') = cod v ⊔ cod v'
\end{code}

We need just one property each for dom and cod.  Given a collection of
functions represented by value v, and an entry v₁ ↦ v₂ in v, we know
that v₁ is included in the domain of v.

\begin{code}
↦∈→⊆dom : ∀{v v₁ v₂ : Value}
          → Funs v  →  (v₁ ↦ v₂) ∈ v
            ----------------------
          → v₁ ⊆ dom v
↦∈→⊆dom {⊥} fg ()
↦∈→⊆dom {v ↦ v'} fg refl = λ z → z
↦∈→⊆dom {v ⊔ v'} fg (inj₁ x) =
  let ih = ↦∈→⊆dom {v} (λ {v'} z → fg (inj₁ z)) x in
  λ x₁ → inj₁ (ih x₁)
↦∈→⊆dom {v ⊔ v'} fg (inj₂ y) =
  let ih = ↦∈→⊆dom {v'} (λ {v'} z → fg (inj₂ z)) y in
  λ x₁ → inj₂ (ih x₁)
\end{code}

Regarding cod, suppose we have a collection of functions represented
by v, but all of them are just copies of v₁ ↦ v₂.  Then the cod v is
included in v₂.

\begin{code}
⊆↦→cod⊆ : ∀{v v₁ v₂ : Value}
      → v ⊆ v₁ ↦ v₂
        ---------
      → cod v ⊆ v₂
⊆↦→cod⊆ {⊥} s refl with s {⊥} refl
... | ()
⊆↦→cod⊆ {C ↦ C'} s m with s {C ↦ C'} refl
... | refl = m
⊆↦→cod⊆ {v ⊔ v₁} s (inj₁ x) = ⊆↦→cod⊆ (λ {C} z → s (inj₁ z)) x
⊆↦→cod⊆ {v ⊔ v₁} s (inj₂ y) = ⊆↦→cod⊆ (λ {C} z → s (inj₂ z)) y
\end{code}

With the dom and cod functions in hand, we can make precise the
conclusion of the inversion principle for functions, which we package
into the following predicate named factor. We say that v₁ ↦ v₁'
_factors_ v₂ into v₂'.

\begin{code}
factor : (v₂ : Value) → (v₂' : Value) → (v₁ : Value) → (v₁' : Value) → Set
factor v₂ v₂' v₁ v₁' = Funs v₂' × v₂' ⊆ v₂ × dom v₂' ⊑ v₁ × v₁' ⊑ cod v₂'
\end{code}

We prove the inversion principle for functions by induction on the
derivation of the less-than relation. To make the induction hypothesis
stronger, we broaden the premise to v₁ ⊑ v₂ (instead of v₁ ↦ v₁' ⊑
v₂), and strengthen the conclusion to say that for _every_ function
value w₁ ↦ w₁' ∈ v₁, w₁ ↦ w₁' factors v₂ into v₂'.

### Inversion of less-than for functions, the case for Trans⊑

The crux of the proof is the case for Trans⊑.

    v₁ ⊑ u   u ⊑ v₂
    --------------- (Trans⊑)
        v₁ ⊑ v₂

By the induction hypothesis for v₁ ⊑ u, we know
that w₁ ↦ w₁' factors u into u', for some value u',
so we have Funs u' and u' ⊆ u.
By the induction hypothesis for u ⊑ v₂, we know
that for any u₁ ↦ u₂ ∈ u, u₁ ↦ u₂ factors v₂ into v₂'.
With these facts in hand, we proceed by induction on u'
to prove that (dom u') ↦ (cod u') factors v₂ into v₂'.
We discuss each case of the proof in the text below.

\begin{code}
sub-inv-trans : ∀{u' v₂ u : Value}
    → Funs u'  →  u' ⊆ u
    → (∀{u₁ u₂} → u₁ ↦ u₂ ∈ u → Σ[ v₂' ∈ Value ] factor v₂ v₂' u₁ u₂)
      ---------------------------------------------------------------
    → Σ[ v₂' ∈ Value ] factor v₂ v₂' (dom u') (cod u')
sub-inv-trans {⊥} {v₂} {u} fu' u'⊆u IH =
   ⊥-elim (contradiction (fu'{v' = ⊥} refl) ¬Fun⊥)
sub-inv-trans {u₁' ↦ u₂'} {v₂} {u} fg u'⊆u IH = IH (↦⊆→∈ u'⊆u)
sub-inv-trans {u₁' ⊔ u₂'} {v₂} {u} fg u'⊆u IH
    with ⊔⊆-inv u'⊆u
... | ⟨ u₁'⊆u , u₂'⊆u ⟩
    with sub-inv-trans {u₁'} {v₂} {u} (λ {v'} z → fg (inj₁ z)) u₁'⊆u IH
       | sub-inv-trans {u₂'} {v₂} {u} (λ {v'} z → fg (inj₂ z)) u₂'⊆u IH
... | ⟨ v₂₁' , ⟨ fu21' , ⟨ v₂₁'⊆v₂ , ⟨ dv₂₁'⊑du₁' , cu₁'⊑cv₂₁' ⟩ ⟩ ⟩ ⟩
    | ⟨ v₂₂' , ⟨ fu22' , ⟨ v₂₂'⊆v₂ , ⟨ dv₂₂'⊑du₂' , cu₁'⊑cv₂₂' ⟩ ⟩ ⟩ ⟩ =
      let x = ⊔⊑⊔ dv₂₁'⊑du₁' dv₂₂'⊑du₂' in
      let y = ⊔⊑⊔ cu₁'⊑cv₂₁' cu₁'⊑cv₂₂' in
      let z = {!!} in
      ⟨ (v₂₁' ⊔ v₂₂') , ⟨ fv₂' , ⟨ v₂'⊆v₂ ,
      ⟨ ⊔⊑⊔ dv₂₁'⊑du₁' dv₂₂'⊑du₂' ,
        ⊔⊑⊔ cu₁'⊑cv₂₁' cu₁'⊑cv₂₂' ⟩ ⟩ ⟩ ⟩
    where fv₂' : {v' : Value} → v' ∈ v₂₁' ⊎ v' ∈ v₂₂' → Fun v'
          fv₂' {v'} (inj₁ x) = fu21' x
          fv₂' {v'} (inj₂ y) = fu22' y

          v₂'⊆v₂ : {C : Value} → C ∈ v₂₁' ⊎ C ∈ v₂₂' → C ∈ v₂
          v₂'⊆v₂ {C} (inj₁ x) = v₂₁'⊆v₂ x
          v₂'⊆v₂ {C} (inj₂ y) = v₂₂'⊆v₂ y
\end{code}

* Suppose u' ≡ ⊥. Then we have a contradiction because
  it is not the case that Fun ⊥.

* Suppose u' ≡ u₁' ↦ u₂'. Then u₁' ↦ u₂' ∈ u and we can apply the
  premise (the induction hypothesis from u ⊑ v₂) to obtain that
  u₁' ↦ u₂' factors of v₂ into v₂'. This case is complete because
  dom u' ≡ u₁' and cod u' ≡ u₂'.
  
* Suppose u' ≡ u₁' ⊔ u₂'. Then we have u₁' ⊆ u and u₂' ⊆ u. We also  
  have Funs u₁' and Funs u₂', so we can apply the induction hypothesis
  for both u₁' and u₂'. So there exists values v₂₁' and v₂₂' such that
  (dom u₁') ↦ (cod u₁') factors u into v₂₁' and
  (dom u₂') ↦ (cod u₂') factors u into v₂₂'.
  We will show that (dom u) ↦ (cod u) factors u into (v₂₁' ⊔ v₂₂').
  So we need to show that
  
    dom (v₂₁' ⊔ v₂₂') ⊑ dom (u₁' ⊔ u₂')
    cod (u₁' ⊔ u₂') ⊑ cod (v₂₁' ⊔ v₂₂')
  
  But those both follow directly from the factoring of
  u into v₂₁' and v₂₂', using the monotonicity of ⊔ with respect to ⊑.
  

### Inversion of less-than for functions

\begin{code}
sub-inv : ∀{v₂ v₁ : Value}
        → v₁ ⊑ v₂
        → ∀{w₁ w₁'} → w₁ ↦ w₁' ∈ v₁
          -------------------------------
        → Σ[ v₂' ∈ Value ] factor v₂ v₂' w₁ w₁'
sub-inv {v₂} {⊥} Bot⊑ {w₁} {w₁'} ()
sub-inv {v₂} {v₁₁ ⊔ v₁₂} (ConjL⊑ lt1 lt2) {w₁} {w₁'} (inj₁ x) = sub-inv lt1 x
sub-inv {v₂} {v₁₁ ⊔ v₁₂} (ConjL⊑ lt1 lt2) {w₁} {w₁'} (inj₂ y) = sub-inv lt2 y
sub-inv {v₂₁ ⊔ v₂₂} {v₁} (ConjR1⊑ lt) {w₁} {w₁'} m
    with sub-inv lt m  
... | ⟨ v₂₁' , ⟨ fv₂₁' , ⟨ v₂₁'⊆v₂₁ , ⟨ domv₂₁'⊑w₁ , w₁'⊑codv₂₁' ⟩ ⟩ ⟩ ⟩ =
      ⟨ v₂₁' , ⟨ fv₂₁' , ⟨ (λ {w} z → inj₁ (v₂₁'⊆v₂₁ z)) ,
                                   ⟨ domv₂₁'⊑w₁ , w₁'⊑codv₂₁' ⟩ ⟩ ⟩ ⟩
sub-inv {v₂₁ ⊔ v₂₂} {v₁} (ConjR2⊑ lt) {w₁} {w₁'} m
    with sub-inv lt m  
... | ⟨ v₂₂' , ⟨ fv₂₂' , ⟨ v₂₂'⊆v₂₂ , ⟨ domv₂₂'⊑w₁ , w₁'⊑codv₂₂' ⟩ ⟩ ⟩ ⟩ =
      ⟨ v₂₂' , ⟨ fv₂₂' , ⟨ (λ {C} z → inj₂ (v₂₂'⊆v₂₂ z)) ,
                                   ⟨ domv₂₂'⊑w₁ , w₁'⊑codv₂₂' ⟩ ⟩ ⟩ ⟩
sub-inv {v₂} {v₁} (Trans⊑{v₂ = u} v₁⊑u u⊑v₂) {w₁} {w₁'} w₁↦w₁'∈v₁
    with sub-inv v₁⊑u w₁↦w₁'∈v₁
... | ⟨ u' , ⟨ fu' , ⟨ u'⊆u , ⟨ domu'⊑w₁ , w₁'⊑codu' ⟩ ⟩ ⟩ ⟩ 
    with sub-inv-trans {u'} fu' u'⊆u (sub-inv u⊑v₂) 
... | ⟨ v₂' , ⟨ fv₂' , ⟨ v₂'⊆v₂ , ⟨ domv₂'⊑domu' , codu'⊑codv₂' ⟩ ⟩ ⟩ ⟩ =
      ⟨ v₂' , ⟨ fv₂' , ⟨ v₂'⊆v₂ , ⟨ Trans⊑ domv₂'⊑domu' domu'⊑w₁ ,
                                  Trans⊑ w₁'⊑codu' codu'⊑codv₂' ⟩ ⟩ ⟩ ⟩
sub-inv {v₂₁ ↦ v₂₂} {v₁₁ ↦ v₁₂} (Fun⊑ lt1 lt2) refl =
    ⟨ v₂₁ ↦ v₂₂ , ⟨ (λ {v'} → fun) , ⟨ (λ {C} z → z) , ⟨ lt1 , lt2 ⟩ ⟩ ⟩ ⟩
sub-inv {v₂₁ ↦ v₂₂ ⊔ v₂₁ ↦ v₂₃} {v₂₁ ↦ (v₂₂ ⊔ v₂₃)} Dist⊑
    {.v₂₁} {.(v₂₂ ⊔ v₂₃)} refl =
    ⟨ v₂₁ ↦ v₂₂ ⊔ v₂₁ ↦ v₂₃ , ⟨ f , ⟨ g , ⟨ ConjL⊑ Refl⊑ Refl⊑ ,
                                            ⊔⊑⊔ Refl⊑ Refl⊑ ⟩ ⟩ ⟩ ⟩
  where f : Funs (v₂₁ ↦ v₂₂ ⊔ v₂₁ ↦ v₂₃)
        f (inj₁ x) = fun x
        f (inj₂ y) = fun y
        g : (v₂₁ ↦ v₂₂ ⊔ v₂₁ ↦ v₂₃) ⊆ (v₂₁ ↦ v₂₂ ⊔ v₂₁ ↦ v₂₃)
        g (inj₁ x) = inj₁ x
        g (inj₂ y) = inj₂ y
\end{code}

\begin{code}
sub-inv-fun' : ∀{A B C : Value}
    → (A ↦ B) ⊑ C
      -----------------------------
    → Σ[ Γ ∈ Value ] factor C Γ A B
sub-inv-fun'{A}{B}{C} abc = sub-inv abc {A}{B} refl

sub-inv-fun : ∀{A B C : Value}
    → (A ↦ B) ⊑ C
      --------------------------------------------------------------------------
    → Σ[ Γ ∈ Value ] Funs Γ × Γ ⊆ C × (∀{D E} → (D ↦ E) ∈ Γ → D ⊑ A) × B ⊑ cod Γ
sub-inv-fun{A}{B}{C} abc
    with sub-inv abc {A}{B} refl
... | ⟨ Γ , ⟨ f , ⟨ Γ⊆C , ⟨ db , cc ⟩ ⟩ ⟩ ⟩ =
      ⟨ Γ , ⟨ f , ⟨ Γ⊆C , ⟨ G , cc ⟩ ⟩ ⟩ ⟩
   where G : ∀{D E} → (D ↦ E) ∈ Γ → D ⊑ A
         G{D}{E} m = Trans⊑ (⊆→⊑ (↦∈→⊆dom f m)) db
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
  let codΓ⊆v₄ = ⊆↦→cod⊆ Γ⊆v34 in
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

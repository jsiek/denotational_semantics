{-

  Scott domains: the basics, on top of Tom de Jong's domain theory in
  TypeTopology (DomainTheory.*): the dcpos of this development (DCPO₁:
  carrier and order in 𝓤₁, directed families indexed by types in 𝓤₀),
  applying a continuous map, the identity and composition, continuity
  into an exponential (pointwise), the one-point dcpo, and powers Aᴵ of a
  dcpo (pointwise order; used for tuples and environments).

  Everything is parameterised by propositional truncation (pt) and
  function extensionality (fe), which TypeTopology takes as assumptions.

-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.Sets
open import UF.Sets-Properties
open import UF.Subsingletons-Properties

module Framework.Scott.Base
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
       where

open PropositionalTruncation pt public
open import DomainTheory.Basics.Dcpo pt fe 𝓤₀ public
open import DomainTheory.Basics.Miscelanea pt fe 𝓤₀ public
open import DomainTheory.Basics.Pointed pt fe 𝓤₀ public

{- the dcpos of this development -}
DCPO₁ : 𝓤₂ ̇
DCPO₁ = DCPO {𝓤₁} {𝓤₁}

{- applying a continuous map -}
infixl 30 _·_
_·_ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {P : (X → Y) → 𝓦 ̇ } → Σ P → X → Y
f · x = pr₁ f x

idᶜ : (A : DCPO {𝓤} {𝓣}) → DCPO[ A , A ]
idᶜ A = id , id-is-continuous A

{- identity and composition (g ∘ f) at DCPO₁, with their universe levels
   fixed: Agda compares two applications of DCPO-∘ whose levels are
   written differently by unfolding them, which can take very long -}
id₁ : (A : DCPO₁) → DCPO[ A , A ]
id₁ A = idᶜ A

{- every type is a set, as this development uses K -}
K-is-set : {X : 𝓤 ̇ } → is-set X
K-is-set refl refl = refl

∘₁ : (A B C : DCPO₁) → DCPO[ A , B ] → DCPO[ B , C ] → DCPO[ A , C ]
∘₁ A B C f g = DCPO-∘ A B C f g

{- Exponentials and products at DCPO₁, defined here rather than taken
   from TypeTopology (_⟹ᵈᶜᵖᵒ_, _×ᵈᶜᵖᵒ_): their proofs are named functions
   and their universe levels are always 𝓤₁. (Agda compares two
   exponentials that differ only by an unfolding, for example by the
   copies of a definition that module applications make, by unfolding
   them and comparing their parts; inline proofs, and levels written
   differently, make that unfold large terms, and can take very long.) -}

module _ (A B : DCPO₁) where

 infixr 20 _⟹₁_
 infixr 30 _×₁_

 private
  _⊑ᴱ_ : DCPO[ A , B ] → DCPO[ A , B ] → 𝓤₁ ̇
  f ⊑ᴱ g = (x : ⟨ A ⟩) → f · x ⊑⟨ B ⟩ g · x
  E-set : is-set DCPO[ A , B ]
  E-set = K-is-set
  E-pv : (f g : DCPO[ A , B ]) → is-prop (f ⊑ᴱ g)
  E-pv f g = Π-is-prop fe (λ x → prop-valuedness B (f · x) (g · x))
  E-r : (f : DCPO[ A , B ]) → f ⊑ᴱ f
  E-r f x = reflexivity B (f · x)
  E-t : (f g h : DCPO[ A , B ]) → f ⊑ᴱ g → g ⊑ᴱ h → f ⊑ᴱ h
  E-t f g h u v x = transitivity B (f · x) (g · x) (h · x) (u x) (v x)
  E-a : (f g : DCPO[ A , B ]) → f ⊑ᴱ g → g ⊑ᴱ f → f ＝ g
  E-a f g u v = to-continuous-function-＝ A B (λ x → antisymmetry B (f · x) (g · x) (u x) (v x))

 pointwise-directed : {I : 𝓤₀ ̇ } (α : I → DCPO[ A , B ]) → is-directed _⊑ᴱ_ α
   → (x : ⟨ A ⟩) → is-Directed B (λ i → α i · x)
 pointwise-directed α δ x =
  inhabited-if-directed _⊑ᴱ_ α δ ,
  (λ i j → ∥∥-functor (λ (k , u , v) → k , u x , v x) (semidirected-if-directed _⊑ᴱ_ α δ i j))

 private
  sup-fun : {I : 𝓤₀ ̇ } (α : I → DCPO[ A , B ]) → is-directed _⊑ᴱ_ α → ⟨ A ⟩ → ⟨ B ⟩
  sup-fun α δ x = ∐ B (pointwise-directed α δ x)
  sup-c : {I : 𝓤₀ ̇ } (α : I → DCPO[ A , B ]) (δ : is-directed _⊑ᴱ_ α) → is-continuous A B (sup-fun α δ)
  sup-c {I} α δ J β φ = ub , lub
   where
    ub : (j : J) → sup-fun α δ (β j) ⊑⟨ B ⟩ sup-fun α δ (∐ A φ)
    ub j = ∐-is-lowerbound-of-upperbounds B (pointwise-directed α δ (β j)) _
            (λ i → transitivity B _ _ _
                     (monotone-if-continuous A B (α i) (β j) (∐ A φ) (∐-is-upperbound A φ j))
                     (∐-is-upperbound B (pointwise-directed α δ (∐ A φ)) i))
    lub : (b : ⟨ B ⟩) → ((j : J) → sup-fun α δ (β j) ⊑⟨ B ⟩ b) → sup-fun α δ (∐ A φ) ⊑⟨ B ⟩ b
    lub b u = ∐-is-lowerbound-of-upperbounds B (pointwise-directed α δ (∐ A φ)) b
               (λ i → sup-is-lowerbound-of-upperbounds (underlying-order B) (pr₂ (α i) J β φ) b
                        (λ j → transitivity B _ _ b (∐-is-upperbound B (pointwise-directed α δ (β j)) i) (u j)))
  E-dc : (I : 𝓤₀ ̇ ) (α : I → DCPO[ A , B ]) → is-directed _⊑ᴱ_ α → has-sup _⊑ᴱ_ α
  E-dc I α δ = (sup-fun α δ , sup-c α δ) ,
               (λ i x → ∐-is-upperbound B (pointwise-directed α δ x) i) ,
               (λ g u x → ∐-is-lowerbound-of-upperbounds B (pointwise-directed α δ x) (g · x) (λ i → u i x))

 _⟹₁_ : DCPO₁
 _⟹₁_ = DCPO[ A , B ] , _⊑ᴱ_ , (E-set , E-pv , E-r , E-t , E-a) , E-dc

 private
  _⊑ˣ_ : ⟨ A ⟩ × ⟨ B ⟩ → ⟨ A ⟩ × ⟨ B ⟩ → 𝓤₁ ̇
  (a , b) ⊑ˣ (a' , b') = (a ⊑⟨ A ⟩ a') × (b ⊑⟨ B ⟩ b')
  X-set : is-set (⟨ A ⟩ × ⟨ B ⟩)
  X-set = K-is-set
  X-pv : (p q : ⟨ A ⟩ × ⟨ B ⟩) → is-prop (p ⊑ˣ q)
  X-pv (a , b) (a' , b') = ×-is-prop (prop-valuedness A a a') (prop-valuedness B b b')
  X-r : (p : ⟨ A ⟩ × ⟨ B ⟩) → p ⊑ˣ p
  X-r (a , b) = reflexivity A a , reflexivity B b
  X-t : (p q r : ⟨ A ⟩ × ⟨ B ⟩) → p ⊑ˣ q → q ⊑ˣ r → p ⊑ˣ r
  X-t (a , b) (a' , b') (a'' , b'') (u , v) (u' , v') =
   transitivity A a a' a'' u u' , transitivity B b b' b'' v v'
  X-a : (p q : ⟨ A ⟩ × ⟨ B ⟩) → p ⊑ˣ q → q ⊑ˣ p → p ＝ q
  X-a (a , b) (a' , b') (u , v) (u' , v') = ap₂' (antisymmetry A a a' u u') (antisymmetry B b b' v v')
   where
    ap₂' : {a a' : ⟨ A ⟩} {b b' : ⟨ B ⟩} → a ＝ a' → b ＝ b' → (a , b) ＝ (a' , b')
    ap₂' refl refl = refl

 fst-directed : {I : 𝓤₀ ̇ } (α : I → ⟨ A ⟩ × ⟨ B ⟩) → is-directed _⊑ˣ_ α → is-Directed A (λ i → pr₁ (α i))
 fst-directed α δ = inhabited-if-directed _⊑ˣ_ α δ ,
   (λ i j → ∥∥-functor (λ (k , u , v) → k , pr₁ u , pr₁ v) (semidirected-if-directed _⊑ˣ_ α δ i j))

 snd-directed : {I : 𝓤₀ ̇ } (α : I → ⟨ A ⟩ × ⟨ B ⟩) → is-directed _⊑ˣ_ α → is-Directed B (λ i → pr₂ (α i))
 snd-directed α δ = inhabited-if-directed _⊑ˣ_ α δ ,
   (λ i j → ∥∥-functor (λ (k , u , v) → k , pr₂ u , pr₂ v) (semidirected-if-directed _⊑ˣ_ α δ i j))

 private
  X-dc : (I : 𝓤₀ ̇ ) (α : I → ⟨ A ⟩ × ⟨ B ⟩) → is-directed _⊑ˣ_ α → has-sup _⊑ˣ_ α
  X-dc I α δ = (∐ A (fst-directed α δ) , ∐ B (snd-directed α δ)) ,
               (λ i → ∐-is-upperbound A (fst-directed α δ) i , ∐-is-upperbound B (snd-directed α δ) i) ,
               (λ (a , b) u → ∐-is-lowerbound-of-upperbounds A (fst-directed α δ) a (λ i → pr₁ (u i)) ,
                              ∐-is-lowerbound-of-upperbounds B (snd-directed α δ) b (λ i → pr₂ (u i)))

 _×₁_ : DCPO₁
 _×₁_ = (⟨ A ⟩ × ⟨ B ⟩) , _⊑ˣ_ , (X-set , X-pv , X-r , X-t , X-a) , X-dc

module _ (A B : DCPO₁) where
 private
  fst-c : is-continuous (A ×₁ B) A pr₁
  fst-c I α δ = ∐-is-sup A (fst-directed A B α δ)
  snd-c : is-continuous (A ×₁ B) B pr₂
  snd-c I α δ = ∐-is-sup B (snd-directed A B α δ)
  ev-c₁ : (a : ⟨ A ⟩) → is-continuous (A ⟹₁ B) B (λ f → f · a)
  ev-c₁ a I α δ = ∐-is-sup B (pointwise-directed A B α δ a)

 fst₁ : DCPO[ A ×₁ B , A ]
 fst₁ = pr₁ , fst-c

 snd₁ : DCPO[ A ×₁ B , B ]
 snd₁ = pr₂ , snd-c

 at-point₁ : ⟨ A ⟩ → DCPO[ A ⟹₁ B , B ]
 at-point₁ a = (λ f → f · a) , ev-c₁ a

 const₁ : ⟨ B ⟩ → DCPO[ A , B ]
 const₁ b = (λ _ → b) , constant-functions-are-continuous A B {b}

 {- a map of two arguments, continuous in each, is continuous -}
 module _ {C : DCPO₁} (h : ⟨ A ⟩ → ⟨ B ⟩ → ⟨ C ⟩)
          (h₁ : (b : ⟨ B ⟩) → is-continuous A C (λ a → h a b))
          (h₂ : (a : ⟨ A ⟩) → is-continuous B C (h a)) where

  private
   mono : (a a' : ⟨ A ⟩) (b b' : ⟨ B ⟩) → a ⊑⟨ A ⟩ a' → b ⊑⟨ B ⟩ b' → h a b ⊑⟨ C ⟩ h a' b'
   mono a a' b b' u v = transitivity C _ _ _
     (monotone-if-continuous A C ((λ a → h a b) , h₁ b) a a' u)
     (monotone-if-continuous B C (h a' , h₂ a') b b' v)

  uncurried-continuous : is-continuous (A ×₁ B) C (λ p → h (pr₁ p) (pr₂ p))
  uncurried-continuous I α δ = ub , lub
   where
    a∞ = ∐ A (fst-directed A B α δ)
    b∞ = ∐ B (snd-directed A B α δ)
    ub : (i : I) → h (pr₁ (α i)) (pr₂ (α i)) ⊑⟨ C ⟩ h a∞ b∞
    ub i = mono _ _ _ _ (∐-is-upperbound A (fst-directed A B α δ) i) (∐-is-upperbound B (snd-directed A B α δ) i)
    lub : (c : ⟨ C ⟩) → ((i : I) → h (pr₁ (α i)) (pr₂ (α i)) ⊑⟨ C ⟩ c) → h a∞ b∞ ⊑⟨ C ⟩ c
    lub c u = sup-is-lowerbound-of-upperbounds (underlying-order C) (h₁ b∞ I (λ i → pr₁ (α i)) (fst-directed A B α δ)) c
      (λ i → sup-is-lowerbound-of-upperbounds (underlying-order C) (h₂ (pr₁ (α i)) I (λ j → pr₂ (α j)) (snd-directed A B α δ)) c
        (λ j → ∥∥-rec (prop-valuedness C _ c)
                 (λ (k , (u₁ , _) , (_ , v₂)) → transitivity C _ _ c (mono _ _ _ _ u₁ v₂) (u k))
                 (semidirected-if-Directed (A ×₁ B) α δ i j)))

pair₁ : (P X Y : DCPO₁) → DCPO[ P , X ] → DCPO[ P , Y ] → DCPO[ P , X ×₁ Y ]
pair₁ P X Y f g = (λ p → f · p , g · p) , c
 where
  c : is-continuous P (X ×₁ Y) (λ p → f · p , g · p)
  c I α δ = (λ i → sup-is-upperbound (underlying-order X) (pr₂ f I α δ) i ,
                   sup-is-upperbound (underlying-order Y) (pr₂ g I α δ) i) ,
            (λ (x , y) u → sup-is-lowerbound-of-upperbounds (underlying-order X) (pr₂ f I α δ) x (λ i → pr₁ (u i)) ,
                           sup-is-lowerbound-of-upperbounds (underlying-order Y) (pr₂ g I α δ) y (λ i → pr₂ (u i)))

{- a map into an exponential, from its pointwise continuity -}
to-exp₁ : (A B C : DCPO₁) (f : ⟨ A ⟩ → DCPO[ B , C ])
  → ((b : ⟨ B ⟩) → is-continuous A C (λ a → f a · b)) → DCPO[ A , B ⟹₁ C ]
to-exp₁ A B C f c = f , cont
 where
  cont : is-continuous A (B ⟹₁ C) f
  cont I α δ = (λ i b → sup-is-upperbound (underlying-order C) (c b I α δ) i) ,
               (λ g u b → sup-is-lowerbound-of-upperbounds (underlying-order C) (c b I α δ) (g · b) (λ i → u i b))

eval₁ : (A B : DCPO₁) → DCPO[ (A ⟹₁ B) ×₁ A , B ]
eval₁ A B = (λ p → pr₁ p · pr₂ p) ,
  uncurried-continuous (A ⟹₁ B) A {B} (λ f a → f · a) (λ a → pr₂ (at-point₁ A B a)) (λ f → pr₂ f)

curry₁ : (A B C : DCPO₁) → DCPO[ A ×₁ B , C ] → DCPO[ A , B ⟹₁ C ]
curry₁ A B C h = to-exp₁ A B C k c
 where
  k : ⟨ A ⟩ → DCPO[ B , C ]
  k a = (λ b → h · (a , b)) , pr₂ (∘₁ B (A ×₁ B) C (pair₁ B A B (const₁ B A a) (id₁ B)) h)
  c : (b : ⟨ B ⟩) → is-continuous A C (λ a → h · (a , b))
  c b = pr₂ (∘₁ A (A ×₁ B) C (pair₁ A A B (id₁ A) (const₁ A B b)) h)

{- f ↦ g ∘ f, and g ↦ g ∘ f -}
post₁ : (A B C : DCPO₁) → DCPO[ B , C ] → DCPO[ A ⟹₁ B , A ⟹₁ C ]
post₁ A B C g = to-exp₁ (A ⟹₁ B) A C (λ f → ∘₁ A B C f g)
                  (λ x → pr₂ (∘₁ (A ⟹₁ B) B C (at-point₁ A B x) g))

pre₁ : (A B C : DCPO₁) → DCPO[ A , B ] → DCPO[ B ⟹₁ C , A ⟹₁ C ]
pre₁ A B C f = to-exp₁ (B ⟹₁ C) A C (λ g → ∘₁ A B C f g) (λ x → pr₂ (at-point₁ B C (f · x)))

{- (f , g) ↦ g ∘ f -}
comp₁ : (A B C : DCPO₁) → DCPO[ (A ⟹₁ B) ×₁ (B ⟹₁ C) , A ⟹₁ C ]
comp₁ A B C = (λ p → ∘₁ A B C (pr₁ p) (pr₂ p)) , cont
 where
  cont : is-continuous ((A ⟹₁ B) ×₁ (B ⟹₁ C)) (A ⟹₁ C) (λ p → ∘₁ A B C (pr₁ p) (pr₂ p))
  cont = pr₂ (to-exp₁ ((A ⟹₁ B) ×₁ (B ⟹₁ C)) A C (λ p → ∘₁ A B C (pr₁ p) (pr₂ p))
           (λ x → uncurried-continuous (A ⟹₁ B) (B ⟹₁ C) {C} (λ f g → g · (f · x))
                    (λ g → pr₂ (∘₁ (A ⟹₁ B) B C (at-point₁ A B x) g))
                    (λ f → pr₂ (at-point₁ B C (f · x)))))

{- (The proofs inside the dcpos and maps below are named functions, not
   λs: Agda compares two such dcpos whose arguments differ only up to
   unfolding by comparing their parts, and it compares two partial
   applications of a function by their arguments, but two λs by their
   bodies, which can unfold to large terms.) -}

{- the one-point dcpo -}
module _ where
 private
  ⊑𝟙 : 𝟙 {𝓤₁} → 𝟙 {𝓤₁} → 𝓤₁ ̇
  ⊑𝟙 _ _ = 𝟙
  𝟙-set : is-set (𝟙 {𝓤₁})
  𝟙-set = props-are-sets 𝟙-is-prop
  𝟙-pv : (x y : 𝟙) → is-prop (⊑𝟙 x y)
  𝟙-pv _ _ = 𝟙-is-prop
  𝟙-r : (x : 𝟙) → ⊑𝟙 x x
  𝟙-r _ = ⋆
  𝟙-t : (x y z : 𝟙) → ⊑𝟙 x y → ⊑𝟙 y z → ⊑𝟙 x z
  𝟙-t _ _ _ _ _ = ⋆
  𝟙-a : (x y : 𝟙) → ⊑𝟙 x y → ⊑𝟙 y x → x ＝ y
  𝟙-a x y _ _ = 𝟙-is-prop x y
  𝟙-dc : (I : 𝓤₀ ̇ ) (α : I → 𝟙) → is-directed ⊑𝟙 α → has-sup ⊑𝟙 α
  𝟙-dc I α δ = ⋆ , (λ _ → ⋆) , (λ _ _ → ⋆)

 𝟙ᵈ : DCPO₁
 𝟙ᵈ = 𝟙 , ⊑𝟙 , (𝟙-set , 𝟙-pv , 𝟙-r , 𝟙-t , 𝟙-a) , 𝟙-dc

{- Powers (the index type is a set by K) -------------------------------------}

module _ (I : 𝓤₀ ̇ ) (A : DCPO₁) where

 private
  _⊑ᴾ_ : (I → ⟨ A ⟩) → (I → ⟨ A ⟩) → 𝓤₁ ̇
  f ⊑ᴾ g = (i : I) → f i ⊑⟨ A ⟩ g i

 component-is-directed : {J : 𝓤₀ ̇ } (α : J → I → ⟨ A ⟩) → is-directed _⊑ᴾ_ α
   → (i : I) → is-Directed A (λ j → α j i)
 component-is-directed α δ i =
  inhabited-if-directed _⊑ᴾ_ α δ ,
  (λ j k → ∥∥-functor (λ (l , u , v) → l , u i , v i)
                      (semidirected-if-directed _⊑ᴾ_ α δ j k))

 private
  P-set : is-set (I → ⟨ A ⟩)
  P-set = Π-is-set fe (λ _ → sethood A)
  P-pv : (f g : I → ⟨ A ⟩) → is-prop (f ⊑ᴾ g)
  P-pv f g = Π-is-prop fe (λ i → prop-valuedness A (f i) (g i))
  P-r : (f : I → ⟨ A ⟩) → f ⊑ᴾ f
  P-r f i = reflexivity A (f i)
  P-t : (f g h : I → ⟨ A ⟩) → f ⊑ᴾ g → g ⊑ᴾ h → f ⊑ᴾ h
  P-t f g h u v i = transitivity A (f i) (g i) (h i) (u i) (v i)
  P-a : (f g : I → ⟨ A ⟩) → f ⊑ᴾ g → g ⊑ᴾ f → f ＝ g
  P-a f g u v = dfunext fe (λ i → antisymmetry A (f i) (g i) (u i) (v i))
  P-dc : (J : 𝓤₀ ̇ ) (α : J → I → ⟨ A ⟩) → is-directed _⊑ᴾ_ α → has-sup _⊑ᴾ_ α
  P-dc J α δ = (λ i → ∐ A (component-is-directed α δ i))
             , (λ j i → ∐-is-upperbound A (component-is-directed α δ i) j)
             , (λ g u i → ∐-is-lowerbound-of-upperbounds A
                            (component-is-directed α δ i) (g i) (λ j → u j i))

 Pow : DCPO₁
 Pow = (I → ⟨ A ⟩) , _⊑ᴾ_ , (P-set , P-pv , P-r , P-t , P-a) , P-dc

 {- a map into a power is continuous if each component is -}
 to-Pow-continuous : (B : DCPO {𝓤} {𝓣}) (f : ⟨ B ⟩ → I → ⟨ A ⟩)
   → ((i : I) → is-continuous B A (λ b → f b i))
   → is-continuous B Pow f
 to-Pow-continuous B f c J α δ =
  (λ j i → sup-is-upperbound (underlying-order A) (c i J α δ) j) ,
  (λ g u i → sup-is-lowerbound-of-upperbounds (underlying-order A) (c i J α δ)
                (g i) (λ j → u j i))

 private
  at-c : (i : I) → is-continuous Pow A (λ f → f i)
  at-c i J α δ = ∐-is-upperbound A (component-is-directed α δ i) ,
                 (λ a u → ∐-is-lowerbound-of-upperbounds A
                            (component-is-directed α δ i) a u)

 {- a component of a power -}
 at : I → DCPO[ Pow , A ]
 at i = (λ f → f i) , at-c i

{-

  Scott domains: the domain of values 𝔻 as the bilimit of its stages
  (Framework/Scott/Solve.agda), for the proofs that need induction on
  the depth of values (the delay pass):

    𝓓 0 = 𝟙,   𝓓 (n + 1) = 𝓛 (Σ t , Payload t (𝓓 n)),

  with the projections π∞ n : 𝔻 → 𝓓 n and embeddings ε∞ n : 𝓓 n → 𝔻,
  the maps π n : 𝓓 (n + 1) → 𝓓 n and ε n between consecutive stages,
  and their iterates. Every value is the sup of its approximations
  e n d = ε∞ n (π∞ n d), and π∞ (n + 1) d is unroll d with π∞ n applied to
  its payload (and ε∞ n to the arguments of a function).

-}

open import MLTT.Spartan hiding (inl; inr; cases; _+_; J)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons

open import Data.Nat using (_+_)
open import Data.Nat.Properties using (+-identityʳ; +-suc)
import Relation.Binary.PropositionalEquality as Eq
open import Naturals.Order
open import Naturals.Addition using () renaming (_+_ to _+'_)
open import Notation.Order

module proof.Framework.Scott.Stages
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : propext 𝓤₀)
       where

open import Framework.Scott.Base pt fe
open import Framework.Scott.Lift pt fe pe
open import Framework.Scott.Functor pt fe pe
open import proof.Framework.Scott.Domain pt fe pe
open import Lifting.Miscelanea 𝓤₀ using (value-is-constant)
open 𝔻-solution using (𝓓; π; ε; π'; ε') public

π∞ : (n : ℕ) → DCPO[ 𝔻 , 𝓓 n ]
π∞ = 𝔻-solution.π∞₁

ε∞ : (n : ℕ) → DCPO[ 𝓓 n , 𝔻 ]
ε∞ = 𝔻-solution.ε∞₁

{- the approximation of depth n -}
e : ℕ → ⟨ 𝔻 ⟩ → ⟨ 𝔻 ⟩
e n d = ε∞ n · (π∞ n · d)

e-below : (n : ℕ) (d : ⟨ 𝔻 ⟩) → e n d ⊑⟨ 𝔻 ⟩ d
e-below = 𝔻-solution.ε∞π∞-below

e-mono : (d : ⟨ 𝔻 ⟩) (m n : ℕ) → m ≤ n → e m d ⊑⟨ 𝔻 ⟩ e n d
e-mono = 𝔻-solution.ε∞π∞-mono

e-sup : (d : ⟨ 𝔻 ⟩) → is-sup (underlying-order 𝔻) d (λ n → e n d)
e-sup = 𝔻-solution.ε∞π∞-sup

π∞-ε∞ : (n : ℕ) (x : ⟨ 𝓓 n ⟩) → π∞ n · (ε∞ n · x) ＝ x
π∞-ε∞ = 𝔻-solution.π∞-section

π-π∞ : (n : ℕ) (d : ⟨ 𝔻 ⟩) → π n (π∞ (succ n) · d) ＝ π∞ n · d
π-π∞ = 𝔻-solution.π∞-π

ε∞-ε : (n : ℕ) (x : ⟨ 𝓓 n ⟩) → ε∞ (succ n) · (ε n x) ＝ ε∞ n · x
ε∞-ε n x = ap (_· x) (𝔻-solution.ε∞-step n)

{- the approximations of a value are directed, with the value as sup;
   so a continuous map is the sup of its values on them -}
e-directed : (d : ⟨ 𝔻 ⟩) → is-Directed 𝔻 (λ k → e k d)
e-directed d = ∣ 0 ∣ , (λ i j → ∣ i +' j , e-mono d i (i +' j) (≤-+ i j) , e-mono d j (i +' j) (≤-+' i j) ∣)

e-∐ : (d : ⟨ 𝔻 ⟩) → ∐ 𝔻 {ℕ} {λ k → e k d} (e-directed d) ＝ d
e-∐ d = sups-are-unique (underlying-order 𝔻) (pr₁ (axioms-of-dcpo 𝔻)) (λ k → e k d)
          (∐-is-sup 𝔻 {ℕ} {λ k → e k d} (e-directed d)) (e-sup d)

approx-∐ : (A : DCPO₁) (f : DCPO[ 𝔻 , A ]) (d : ⟨ 𝔻 ⟩)
  → f · d ＝ ∐ A {ℕ} {λ k → f · e k d} (image-is-directed' 𝔻 A f {ℕ} {λ k → e k d} (e-directed d))
approx-∐ A f d = ap (f ·_) (e-∐ d ⁻¹) ∙ continuous-∐-＝ 𝔻 A f {ℕ} {λ k → e k d} (e-directed d)

{- π∞ (n + 1), through unroll -}
π∞-unroll : (n : ℕ) (d : ⟨ 𝔻 ⟩)
  → π∞ (succ n) · d ＝ 𝓛map (obj Val 𝔻) (obj Val (𝓓 n)) (act Val (π∞ n) (ε∞ n)) (unroll · d)
π∞-unroll n d = ap (π∞ (succ n) ·_) (roll-unroll d ⁻¹) ∙ 𝔻-solution.π∞-fold (succ n) (unroll · d)

{- definedness, at every stage but 0 -}
π∞-defined : (n : ℕ) (d : ⟨ 𝔻 ⟩) → is-defined (π∞ (succ n) · d) → defined d
π∞-defined n d p = transport is-defined (π∞-unroll n d) p

defined-π∞ : (n : ℕ) (d : ⟨ 𝔻 ⟩) → defined d → is-defined (π∞ (succ n) · d)
defined-π∞ n d q = transport is-defined (π∞-unroll n d ⁻¹) q

{- the approximation of a value made with a tag -}
π∞-inj : (n : ℕ) (t : Tag) (x : ⟨ obj (Payload t) 𝔻 ⟩)
  → π∞ (succ n) · (inj t · x) ＝ η (t , fmap (Payload t) 𝔻 (𝓓 n) (π∞ n) (ε∞ n) x)
π∞-inj n t x = π∞-unroll n (inj t · x)
               ∙ ap (𝓛map (obj Val 𝔻) (obj Val (𝓓 n)) (act Val (π∞ n) (ε∞ n))) (unroll-roll (η (t , x)))

{- π and ε at stage n + 2, on the payload (stated once: Agda checks it
   fast, but can be slow to unfold π (n + 1) inside a bigger goal) -}
π-succ : (n : ℕ) (s : ⟨ 𝓓 (succ (succ n)) ⟩)
  → π (succ n) s ＝ 𝓛map (obj Val (𝓓 (succ n))) (obj Val (𝓓 n)) (act Val (π' n) (ε' n)) s
π-succ n s = refl

ε-succ : (n : ℕ) (s : ⟨ 𝓓 (succ n) ⟩)
  → ε (succ n) s ＝ 𝓛map (obj Val (𝓓 n)) (obj Val (𝓓 (succ n))) (act Val (ε' n) (π' n)) s
ε-succ n s = refl

{- ε 0 is the least element of 𝓓 1 -}
ε-zero-undefined : (s : ⟨ 𝓓 0 ⟩) → ¬ is-defined (ε 0 s)
ε-zero-undefined s p = p

{- Iterates -------------------------------------------------------------------}

{- k steps down from stage k + n, and up from n -}
πs : (k n : ℕ) → ⟨ 𝓓 (k + n) ⟩ → ⟨ 𝓓 n ⟩
πs zero n x = x
πs (succ k) n x = πs k n (π (k + n) x)

εs : (k n : ℕ) → ⟨ 𝓓 n ⟩ → ⟨ 𝓓 (k + n) ⟩
εs zero n x = x
εs (succ k) n x = ε (k + n) (εs k n x)

πs-π∞ : (k n : ℕ) (d : ⟨ 𝔻 ⟩) → πs k n (π∞ (k + n) · d) ＝ π∞ n · d
πs-π∞ zero n d = refl
πs-π∞ (succ k) n d = ap (πs k n) (π-π∞ (k + n) d) ∙ πs-π∞ k n d

ε∞-εs : (k n : ℕ) (x : ⟨ 𝓓 n ⟩) → ε∞ (k + n) · (εs k n x) ＝ ε∞ n · x
ε∞-εs zero n x = refl
ε∞-εs (succ k) n x = ε∞-ε (k + n) (εs k n x) ∙ ε∞-εs k n x

{- two numbers, one k above the other -}
private
 ≡→＝ : {X : 𝓤₀ ̇ } {x y : X} → x Eq.≡ y → x ＝ y
 ≡→＝ Eq.refl = refl

data Split (m n : ℕ) : 𝓤₀ ̇ where
 lower : (k : ℕ) → n ＝ k + m → Split m n
 higher : (k : ℕ) → m ＝ k + n → Split m n

split : (m n : ℕ) → Split m n
split zero n = lower n (≡→＝ (Eq.sym (+-identityʳ n)))
split (succ m) zero = higher (succ m) (≡→＝ (Eq.sym (+-identityʳ (succ m))))
split (succ m) (succ n) = step (split m n)
 where
  step : Split m n → Split (succ m) (succ n)
  step (lower k e) = lower k (ap succ e ∙ ≡→＝ (Eq.sym (+-suc k m)))
  step (higher k e) = higher k (ap succ e ∙ ≡→＝ (Eq.sym (+-suc k n)))

≤+ : (k n : ℕ) → k ≤ (k + n)
≤+ zero n = ⋆
≤+ (succ k) n = ≤+ k n

{- π∞ m (ε∞ n x): down when m ≤ n, up when n ≤ m -}
π∞-ε∞-down : (k m : ℕ) (x : ⟨ 𝓓 (k + m) ⟩) → π∞ m · (ε∞ (k + m) · x) ＝ πs k m x
π∞-ε∞-down k m x = πs-π∞ k m (ε∞ (k + m) · x) ⁻¹ ∙ ap (πs k m) (π∞-ε∞ (k + m) x)

π∞-ε∞-up : (k n : ℕ) (x : ⟨ 𝓓 n ⟩) → π∞ (k + n) · (ε∞ n · x) ＝ εs k n x
π∞-ε∞-up k n x = ap (π∞ (k + n) ·_) (ε∞-εs k n x ⁻¹) ∙ π∞-ε∞ (k + n) (εs k n x)

{- Sups in a stage 𝓓 (n + 1) -------------------------------------------------------

   A property of the values of the elements of a directed family in
   𝓓 (n + 1) holds of the value of its sup if it is closed under directed
   sups in Σ t , Payload t (𝓓 n): the sup is defined only if some
   element is, and its value is the sup of the values of the defined
   elements. (As proof/Framework/Scott/Lift.agda for any lifting, but
   stated for 𝓓 (n + 1): Agda is slow to see that 𝓓 (n + 1) is a lifting.
   is-defined l and value l are written pr₁ l and pr₁ (pr₂ l).) -}

module _ (n : ℕ) {I : 𝓤₀ ̇ } (α : I → ⟨ 𝓓 (succ n) ⟩) (δ : is-Directed (𝓓 (succ n)) α) where
 private
  A = obj Val (𝓓 n)


 private
  s : ⟨ 𝓓 (succ n) ⟩
  s = ∐ (𝓓 (succ n)) {I} {α} δ
  J = Σ i ꞉ I , pr₁ (α i)
  β : J → ⟨ A ⟩
  β (i , p) = pr₁ (pr₂ (α i)) p

 {- the sup is defined only if some element is -}
 stage-sup-defined : pr₁ s → ∥ J ∥
 stage-sup-defined p = p

 {- the value of the sup is the sup of the values -}
 stage-sup-value : (p : pr₁ s) → is-sup (underlying-order A) (pr₁ (pr₂ s) p) β
 stage-sup-value p = ub , lub
  where
   ub : (j : J) → β j ⊑⟨ A ⟩ pr₁ (pr₂ s) p
   ub (i , pᵢ) = transport (λ - → β (i , pᵢ) ⊑⟨ A ⟩ -)
                   (value-is-constant s (pr₁ (∐-is-upperbound (𝓓 (succ n)) {I} {α} δ i) pᵢ) p)
                   (pr₂ (∐-is-upperbound (𝓓 (succ n)) {I} {α} δ i) pᵢ)
   lub : (u : ⟨ A ⟩) → ((j : J) → β j ⊑⟨ A ⟩ u) → pr₁ (pr₂ s) p ⊑⟨ A ⟩ u
   lub u h = pr₂ below p
    where
     u' : ⟨ 𝓓 (succ n) ⟩
     u' = pr₁ s , (λ _ → u) , being-defined-is-prop s
     below : s ⊑⟨ 𝓓 (succ n) ⟩ u'
     below = ∐-is-lowerbound-of-upperbounds (𝓓 (succ n)) {I} {α} δ u'
               (λ i → (λ pᵢ → pr₁ (∐-is-upperbound (𝓓 (succ n)) {I} {α} δ i) pᵢ) , (λ pᵢ → h (i , pᵢ)))

 {- the values of the defined elements are directed, when one is -}
 stage-values-directed : ∥ J ∥ → is-Directed A β
 stage-values-directed q = q , semi
  where
   semi : is-semidirected (underlying-order A) β
   semi (i , pᵢ) (j , pⱼ) = ∥∥-functor step (semidirected-if-Directed (𝓓 (succ n)) α δ i j)
    where
     step : (Σ k ꞉ I , (α i ⊑⟨ 𝓓 (succ n) ⟩ α k) × (α j ⊑⟨ 𝓓 (succ n) ⟩ α k))
          → Σ m ꞉ J , (β (i , pᵢ) ⊑⟨ A ⟩ β m) × (β (j , pⱼ) ⊑⟨ A ⟩ β m)
     step (k , (f , g) , (f' , g')) =
      (k , f pᵢ) , g pᵢ ,
      transport (λ - → β (j , pⱼ) ⊑⟨ A ⟩ pr₁ (pr₂ (α k)) -) (being-defined-is-prop (α k) (f' pⱼ) (f pᵢ)) (g' pⱼ)

 {- so a property closed under directed sups in A holds of the value of
    the sup when it holds of the values of the elements -}
 stage-sup-ind : {𝓦 : Universe} (Q : ⟨ A ⟩ → 𝓦 ̇ )
   → ({K : 𝓤₀ ̇ } (γ : K → ⟨ A ⟩) (ε : is-Directed A γ) → ((k : K) → Q (γ k)) → Q (∐ A ε))
   → ((i : I) (p : pr₁ (α i)) → Q (pr₁ (pr₂ (α i)) p))
   → (p : pr₁ s) → Q (pr₁ (pr₂ s) p)
 stage-sup-ind Q Q-sup h p =
  transport Q (sups-are-unique (underlying-order A) (pr₁ (axioms-of-dcpo A)) β
                 (∐-is-sup A (stage-values-directed p)) (stage-sup-value p))
    (Q-sup β (stage-values-directed p) (λ j → h (pr₁ j) (pr₂ j)))

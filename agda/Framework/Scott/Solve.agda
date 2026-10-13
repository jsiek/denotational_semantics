{-

  Scott domains: the solution of a recursive domain equation D ≅ F D,
  for a functor F (Framework/Scott/Functor.agda) whose values are
  pointed, as the bilimit of the sequence

    𝓓 0 = 𝟙,   𝓓 (n + 1) = F (𝓓 n)

  with the embedding-projection pairs ε 0 = ⊥ , π 0 = ⋆, and
  ε (n + 1) = F(ε n , π n), π (n + 1) = F(π n , ε n). The bilimit 𝓓∞ and
  its maps ε∞ n, π∞ n are TypeTopology's (DomainTheory.Bilimits.Sequential).
  This generalises TypeTopology's D∞ (DomainTheory.Bilimits.Dinfinity),
  which is the case F X = X ⟹ X with 𝓓 0 = 𝓛 𝟙.

  fold : F 𝓓∞ → 𝓓∞ is the map into the limit given by the cone
  F(π∞ n , ε∞ n) : F 𝓓∞ → 𝓓 (n + 1), and unfold : 𝓓∞ → F 𝓓∞ the map
  out of the colimit given by the cocone F(ε∞ n , π∞ n). That they are
  inverse is proved in proof/Framework/Scott/Solve.agda.

-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons
open import UF.Base using (ap₂)

open import Naturals.Order
open import Naturals.Addition renaming (_+_ to _+'_)
open import Notation.Order

module Framework.Scott.Solve
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : propext 𝓤₀)
       where

open import Framework.Scott.Base pt fe
open import Framework.Scott.Functor pt fe pe
open import DomainTheory.Bilimits.Sequential pt fe 𝓤₁ 𝓤₁

module Solution (F : Functor) (F⊥ : (A : DCPO₁) → has-bottom (obj F A))
  (F-strict : (A B : DCPO₁) (f : DCPO[ A , B ]) (g : DCPO[ B , A ])
            → fmap F A B f g (pr₁ (F⊥ A)) ＝ pr₁ (F⊥ B))
  where

 {- The sequence --------------------------------------------------------------}

 𝓓 : ℕ → DCPO₁
 𝓓 zero = 𝟙ᵈ
 𝓓 (succ n) = obj F (𝓓 n)

 diagram : (n : ℕ) → DCPO[ 𝓓 n , 𝓓 (succ n) ] × DCPO[ 𝓓 (succ n) , 𝓓 n ]
 diagram zero = ((λ _ → pr₁ (F⊥ 𝟙ᵈ)) , constant-functions-are-continuous 𝟙ᵈ (𝓓 1))
              , ((λ _ → ⋆) , constant-functions-are-continuous (𝓓 1) 𝟙ᵈ)
 diagram (succ n) = act F (pr₁ (diagram n)) (pr₂ (diagram n))
                  , act F (pr₂ (diagram n)) (pr₁ (diagram n))

 ε' : (n : ℕ) → DCPO[ 𝓓 n , 𝓓 (succ n) ]
 ε' n = pr₁ (diagram n)

 π' : (n : ℕ) → DCPO[ 𝓓 (succ n) , 𝓓 n ]
 π' n = pr₂ (diagram n)

 ε : (n : ℕ) → ⟨ 𝓓 n ⟩ → ⟨ 𝓓 (succ n) ⟩
 ε n = pr₁ (ε' n)

 π : (n : ℕ) → ⟨ 𝓓 (succ n) ⟩ → ⟨ 𝓓 n ⟩
 π n = pr₁ (π' n)

 ε-section-of-π : (n : ℕ) → π n ∘ ε n ∼ id
 ε-section-of-π zero ⋆ = refl
 ε-section-of-π (succ n) x =
  (fmap-∘ F A B A (ε' n) (π' n) (π' n) (ε' n) x) ⁻¹
  ∙ ap (λ - → fmap F A A - - x) q
  ∙ fmap-id F A x
  where
   A = 𝓓 n
   B = 𝓓 (succ n)
   q : ∘₁ A B A (ε' n) (π' n) ＝ id₁ A
   q = to-continuous-function-＝ A A (ε-section-of-π n)

 επ-deflation : (n : ℕ) (y : ⟨ 𝓓 (succ n) ⟩) → ε n (π n y) ⊑⟨ 𝓓 (succ n) ⟩ y
 επ-deflation zero y = pr₂ (F⊥ 𝟙ᵈ) y
 επ-deflation (succ n) y =
  transitivity (obj F B) _ _ _
   (＝-to-⊒ (obj F B) (fmap-∘ F B A B (π' n) (ε' n) (ε' n) (π' n) y))
   (transitivity (obj F B) _ _ _
     (monotone-if-continuous (Maps B B) (obj F B) (act-at F B B y)
        (ep , ep) (id₁ B , id₁ B) (επ-deflation n , επ-deflation n))
     (＝-to-⊑ (obj F B) (fmap-id F B y)))
  where
   A = 𝓓 n
   B = 𝓓 (succ n)
   ep = ∘₁ B A B (π' n) (ε' n)

 open SequentialDiagram 𝓓 ε π επ-deflation ε-section-of-π
        (λ n → pr₂ (ε' n)) (λ n → pr₂ (π' n)) public

 {- The bilimit D∞, and its maps π∞ n and ε∞ n, are opaque: elsewhere
    they are known only through the facts below. (Transparent, Agda can
    take very long to compare a term that mentions them with one that
    mentions a copy of them made by a module application, as it unfolds
    both to their large normal forms.) They are typed at DCPO₁ for the
    same reason: 𝓓∞'s universe levels are written 𝓤₀ ⊔ 𝓤₁ ⊔ 𝓤₀. -}

 opaque
  D∞ : DCPO₁
  D∞ = 𝓓∞

  π∞₁ : (n : ℕ) → DCPO[ D∞ , 𝓓 n ]
  π∞₁ = π∞'

  ε∞₁ : (n : ℕ) → DCPO[ 𝓓 n , D∞ ]
  ε∞₁ = ε∞'

 opaque
  unfolding D∞ π∞₁ ε∞₁

  {- the commuting squares, as equations of continuous maps -}
  π∞-step : (n : ℕ) → ∘₁ D∞ (𝓓 (succ n)) (𝓓 n) (π∞₁ (succ n)) (π' n) ＝ π∞₁ n
  π∞-step n = to-continuous-function-＝ D∞ (𝓓 n)
               (λ σ → π-in-terms-of-π⁺ n (π∞ (succ n) σ) ∙ π∞-commutes-with-πs n (succ n) (≤-succ n) σ)

  ε∞-step : (n : ℕ) → ∘₁ (𝓓 n) (𝓓 (succ n)) D∞ (ε' n) (ε∞₁ (succ n)) ＝ ε∞₁ n
  ε∞-step n = to-continuous-function-＝ (𝓓 n) D∞
               (λ x → ap (ε∞ (succ n)) (ε-in-terms-of-ε⁺ n x) ∙ ε∞-commutes-with-εs n (succ n) (≤-succ n) x)

  π∞-section : (n : ℕ) (x : ⟨ 𝓓 n ⟩) → π∞₁ n · (ε∞₁ n · x) ＝ x
  π∞-section n = ε∞-section-of-π∞ {n}

  ε∞π∞-below : (n : ℕ) (σ : ⟨ D∞ ⟩) → ε∞₁ n · (π∞₁ n · σ) ⊑⟨ D∞ ⟩ σ
  ε∞π∞-below n = ε∞π∞-deflation {n}

  ε∞π∞-mono : (σ : ⟨ D∞ ⟩) (m n : ℕ) → m ≤ n → ε∞₁ m · (π∞₁ m · σ) ⊑⟨ D∞ ⟩ ε∞₁ n · (π∞₁ n · σ)
  ε∞π∞-mono = ε∞-family-is-monotone

  ε∞π∞-sup : (σ : ⟨ D∞ ⟩) → is-sup (underlying-order D∞) σ (λ n → ε∞₁ n · (π∞₁ n · σ))
  ε∞π∞-sup σ = transport (λ - → is-sup (underlying-order 𝓓∞) - (ε∞-family σ)) ((∐-of-ε∞s σ) ⁻¹)
                 (∐-is-sup 𝓓∞ {ℕ} {ε∞-family σ} (ε∞-family-is-directed σ))

  π∞-π : (n : ℕ) (σ : ⟨ D∞ ⟩) → π n (π∞₁ (succ n) · σ) ＝ π∞₁ n · σ
  π∞-π n σ = π-in-terms-of-π⁺ n (π∞ (succ n) σ) ∙ π∞-commutes-with-πs n (succ n) (≤-succ n) σ

  {- the order of D∞ is componentwise -}
  D∞-⊑ : (σ τ : ⟨ D∞ ⟩) → ((n : ℕ) → π∞₁ n · σ ⊑⟨ 𝓓 n ⟩ π∞₁ n · τ) → σ ⊑⟨ D∞ ⟩ τ
  D∞-⊑ σ τ u = u

  {- D∞ is pointed, as each π n is strict -}
  D∞-has-least : has-least (underlying-order D∞)
  D∞-has-least = ((λ n → bot n) , π⁺-is-strict) , (λ τ n → bot-is-least n (⦅ τ ⦆ n))
   where
    bot : (n : ℕ) → ⟨ 𝓓 n ⟩
    bot zero = ⋆
    bot (succ n) = pr₁ (F⊥ (𝓓 n))
    bot-is-least : (n : ℕ) (x : ⟨ 𝓓 n ⟩) → bot n ⊑⟨ 𝓓 n ⟩ x
    bot-is-least zero x = ⋆
    bot-is-least (succ n) x = pr₂ (F⊥ (𝓓 n)) x
    π-is-strict : (n : ℕ) → π n (bot (succ n)) ＝ bot n
    π-is-strict zero = refl
    π-is-strict (succ n) = F-strict (𝓓 (succ n)) (𝓓 n) (π' n) (ε' n)
    π⁺-is-strict-helper : (n m k : ℕ) (p : n +' k ＝ m) → π⁺-helper n m k p (bot m) ＝ bot n
    π⁺-is-strict-helper n n zero refl = refl
    π⁺-is-strict-helper n m (succ k) refl =
     ap (π⁺-helper n (n +' k) k refl) (π-is-strict (n +' k)) ∙ π⁺-is-strict-helper n (n +' k) k refl
    π⁺-is-strict : (n m : ℕ) (l : n ≤ m) → π⁺ {n} {m} l (bot m) ＝ bot n
    π⁺-is-strict n m l = π⁺-is-strict-helper n m (pr₁ (subtraction' n m l)) (pr₂ (subtraction' n m l))

 {- fold : F D∞ → D∞ ------------------------------------------------------}

 π-exp-to-succ : (n : ℕ) → DCPO[ obj F D∞ , 𝓓 (succ n) ]
 π-exp-to-succ n = act F (π∞₁ n) (ε∞₁ n)

 π-exp : (n : ℕ) → ⟨ obj F D∞ ⟩ → ⟨ 𝓓 n ⟩
 π-exp zero = π 0 ∘ pr₁ (π-exp-to-succ 0)
 π-exp (succ n) = pr₁ (π-exp-to-succ n)

 π-exp-is-continuous : (n : ℕ) → is-continuous (obj F D∞) (𝓓 n) (π-exp n)
 π-exp-is-continuous zero = pr₂ (∘₁ (obj F D∞) (𝓓 1) (𝓓 0) (π-exp-to-succ 0) (π' 0))
 π-exp-is-continuous (succ n) = pr₂ (π-exp-to-succ n)

 π-exp-commutes-with-π : (n : ℕ) → π n ∘ π-exp (succ n) ∼ π-exp n
 π-exp-commutes-with-π zero x = refl
 π-exp-commutes-with-π (succ n) x =
  (fmap-∘ F D∞ (𝓓 (succ n)) (𝓓 n) (π∞₁ (succ n)) (ε∞₁ (succ n)) (π' n) (ε' n) x) ⁻¹
  ∙ ap₂ (λ f g → fmap F D∞ (𝓓 n) f g x) (π∞-step n) (ε∞-step n)

 π-exp-commutes-with-π⁺ : (n m : ℕ) (l : n ≤ m) → π⁺ {n} {m} l ∘ π-exp m ∼ π-exp n
 π-exp-commutes-with-π⁺ = commute-with-πs-lemma (obj F D∞) π-exp π-exp-commutes-with-π

 {- unfold : D∞ → F D∞ ----------------------------------------------------}

 ε-exp-from-succ : (n : ℕ) → DCPO[ 𝓓 (succ n) , obj F D∞ ]
 ε-exp-from-succ n = act F (ε∞₁ n) (π∞₁ n)

 ε-exp : (n : ℕ) → ⟨ 𝓓 n ⟩ → ⟨ obj F D∞ ⟩
 ε-exp zero = pr₁ (ε-exp-from-succ 0) ∘ ε 0
 ε-exp (succ n) = pr₁ (ε-exp-from-succ n)

 ε-exp-is-continuous : (n : ℕ) → is-continuous (𝓓 n) (obj F D∞) (ε-exp n)
 ε-exp-is-continuous zero = pr₂ (∘₁ (𝓓 0) (𝓓 1) (obj F D∞) (ε' 0) (ε-exp-from-succ 0))
 ε-exp-is-continuous (succ n) = pr₂ (ε-exp-from-succ n)

 ε-exp-commutes-with-ε : (n : ℕ) → ε-exp (succ n) ∘ ε n ∼ ε-exp n
 ε-exp-commutes-with-ε zero x = refl
 ε-exp-commutes-with-ε (succ n) x =
  (fmap-∘ F (𝓓 n) (𝓓 (succ n)) D∞ (ε' n) (π' n) (ε∞₁ (succ n)) (π∞₁ (succ n)) x) ⁻¹
  ∙ ap₂ (λ f g → fmap F (𝓓 n) D∞ f g x) (ε∞-step n) (π∞-step n)

 ε-exp-commutes-with-ε⁺ : (n m : ℕ) (l : n ≤ m) → ε-exp m ∘ ε⁺ {n} {m} l ∼ ε-exp n
 ε-exp-commutes-with-ε⁺ = commute-with-εs-lemma (obj F D∞) ε-exp ε-exp-commutes-with-ε

 {- the approximations of unfold σ -}
 unfold-family : ⟨ D∞ ⟩ → ℕ → ⟨ obj F D∞ ⟩
 unfold-family σ n = ε-exp n (π∞₁ n · σ)

 opaque
  unfolding D∞ π∞₁ ε∞₁

  fold : DCPO[ obj F D∞ , D∞ ]
  fold = DcpoCone.limit-mediating-arrow (obj F D∞) π-exp π-exp-is-continuous π-exp-commutes-with-π⁺
       , DcpoCone.limit-mediating-arrow-is-continuous (obj F D∞) π-exp π-exp-is-continuous π-exp-commutes-with-π⁺

  π∞-fold : (n : ℕ) (φ : ⟨ obj F D∞ ⟩) → π∞₁ n · (fold · φ) ＝ π-exp n φ
  π∞-fold n φ = refl

  unfold-family-is-monotone : (σ : ⟨ D∞ ⟩) (m n : ℕ) → m ≤ n
    → unfold-family σ m ⊑⟨ obj F D∞ ⟩ unfold-family σ n
  unfold-family-is-monotone = DcpoCocone.colimit-family-is-monotone (obj F D∞) ε-exp ε-exp-is-continuous ε-exp-commutes-with-ε⁺

  unfold-family-is-directed : (σ : ⟨ D∞ ⟩) → is-Directed (obj F D∞) (unfold-family σ)
  unfold-family-is-directed = DcpoCocone.colimit-family-is-directed (obj F D∞) ε-exp ε-exp-is-continuous ε-exp-commutes-with-ε⁺

  unfold : DCPO[ D∞ , obj F D∞ ]
  unfold = (λ σ → ∐ (obj F D∞) (unfold-family-is-directed σ))
         , DcpoCocone.colimit-mediating-arrow-is-continuous (obj F D∞) ε-exp ε-exp-is-continuous ε-exp-commutes-with-ε⁺

  unfold-is-sup : (σ : ⟨ D∞ ⟩) → unfold · σ ＝ ∐ (obj F D∞) (unfold-family-is-directed σ)
  unfold-is-sup σ = refl

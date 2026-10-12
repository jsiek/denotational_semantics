{-

  Scott domains: the functors whose fixed points the solver
  (Framework/Scott/Solve.agda) constructs. A functor F maps dcpos to
  dcpos, and a pair of continuous maps f : A → B, g : B → A to a
  continuous map F(f , g) : F A → F B, continuously in (f , g) (local
  continuity), preserving identities and composition. Taking pairs makes
  mixed variance uniform: for the exponential, F(f , g) h = f ∘ h ∘ g;
  and an embedding-projection pair (e , p) is mapped to the pair
  F(e , p) , F(p , e).

  The combinators: the identity, constants, powers (Fᴵ), exponentials
  (F ⟹ G), sums of a family over a set of tags (Σ t, F t), and lifting.

-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons
open import UF.Sets

module Framework.Scott.Functor
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : propext 𝓤₀)
       where

open import Framework.Scott.Base pt fe
open import Framework.Scott.Sum pt fe
open import Framework.Scott.Lift pt fe pe

{- the argument of the action of a functor on maps: a pair of maps in
   opposite directions -}
Maps : DCPO₁ → DCPO₁ → DCPO₁
Maps A B = (A ⟹ᵈᶜᵖᵒ B) ×ᵈᶜᵖᵒ (B ⟹ᵈᶜᵖᵒ A)

record Functor : 𝓤₂ ̇ where
 field
  obj : DCPO₁ → DCPO₁
  fmap : (A B : DCPO₁) → DCPO[ A , B ] → DCPO[ B , A ] → ⟨ obj A ⟩ → ⟨ obj B ⟩
  fmap-is-continuous : (A B : DCPO₁) (f : DCPO[ A , B ]) (g : DCPO[ B , A ])
    → is-continuous (obj A) (obj B) (fmap A B f g)
  fmap-is-locally-continuous : (A B : DCPO₁) (x : ⟨ obj A ⟩)
    → is-continuous (Maps A B) (obj B) (λ p → fmap A B (pr₁ p) (pr₂ p) x)
  fmap-id : (A : DCPO₁) (x : ⟨ obj A ⟩) → fmap A A (id₁ A) (id₁ A) x ＝ x
  fmap-∘ : (A B C : DCPO₁) (f : DCPO[ A , B ]) (g : DCPO[ B , A ])
           (f' : DCPO[ B , C ]) (g' : DCPO[ C , B ]) (x : ⟨ obj A ⟩)
    → fmap A C (∘₁ A B C f f') (∘₁ C B A g' g) x ＝ fmap B C f' g' (fmap A B f g x)

open Functor public

{- the action on a pair of maps, as a continuous map -}
act : (F : Functor) {A B : DCPO₁} → DCPO[ A , B ] → DCPO[ B , A ] → DCPO[ obj F A , obj F B ]
act F {A} {B} f g = fmap F A B f g , fmap-is-continuous F A B f g

{- the action at a point, as a continuous function of the pair -}
act-at : (F : Functor) (A B : DCPO₁) (x : ⟨ obj F A ⟩) → DCPO[ Maps A B , obj F B ]
act-at F A B x = (λ p → fmap F A B (pr₁ p) (pr₂ p) x) , fmap-is-locally-continuous F A B x

{- the action, jointly continuous in the pair and the point -}
act-joint : (F : Functor) (A B : DCPO₁) → DCPO[ Maps A B ×ᵈᶜᵖᵒ obj F A , obj F B ]
act-joint F A B = j ,
  continuous-in-arguments→continuous (Maps A B) (obj F A) (obj F B) j
    (λ x → fmap-is-locally-continuous F A B x)
    (λ p → fmap-is-continuous F A B (pr₁ p) (pr₂ p))
 where
  j : ⟨ Maps A B ×ᵈᶜᵖᵒ obj F A ⟩ → ⟨ obj F B ⟩
  j (p , x) = fmap F A B (pr₁ p) (pr₂ p) x

{- The identity -------------------------------------------------------------}

Idᶠ : Functor
Idᶠ = record { obj = λ A → A
             ; fmap = λ A B f g x → f · x
             ; fmap-is-continuous = λ A B f g → pr₂ f
             ; fmap-is-locally-continuous = λ A B x →
                 pr₂ (DCPO-∘ (Maps A B) (A ⟹ᵈᶜᵖᵒ B) B (pr₁-is-continuous (A ⟹ᵈᶜᵖᵒ B) (B ⟹ᵈᶜᵖᵒ A))
                        (at-point A B x))
             ; fmap-id = λ A x → refl
             ; fmap-∘ = λ A B C f g f' g' x → refl }

{- Constants -----------------------------------------------------------------}

Constᶠ : DCPO₁ → Functor
Constᶠ K = record { obj = λ _ → K
                  ; fmap = λ A B f g x → x
                  ; fmap-is-continuous = λ A B f g → id-is-continuous K
                  ; fmap-is-locally-continuous = λ A B x → constant-functions-are-continuous (Maps A B) K
                  ; fmap-id = λ A x → refl
                  ; fmap-∘ = λ A B C f g f' g' x → refl }

{- Powers --------------------------------------------------------------------}

Powᶠ : (I : 𝓤₀ ̇ ) → Functor → Functor
Powᶠ I G =
 record { obj = λ A → Pow I (obj G A)
        ; fmap = λ A B f g x i → fmap G A B f g (x i)
        ; fmap-is-continuous = λ A B f g →
            to-Pow-continuous I (obj G B) (Pow I (obj G A)) (λ x i → fmap G A B f g (x i))
              (λ i → pr₂ (DCPO-∘ (Pow I (obj G A)) (obj G A) (obj G B) (at I (obj G A) i) (act G f g)))
        ; fmap-is-locally-continuous = λ A B x →
            to-Pow-continuous I (obj G B) (Maps A B) (λ p i → fmap G A B (pr₁ p) (pr₂ p) (x i)) (λ i → pr₂ (act-at G A B (x i)))
        ; fmap-id = λ A x → dfunext fe (λ i → fmap-id G A (x i))
        ; fmap-∘ = λ A B C f g f' g' x → dfunext fe (λ i → fmap-∘ G A B C f g f' g' (x i)) }

{- Exponentials ----------------------------------------------------------------}

Expᶠ : Functor → Functor → Functor
Expᶠ G H =
 record { obj = λ A → obj G A ⟹ᵈᶜᵖᵒ obj H A
        ; fmap = k
        ; fmap-is-continuous = λ A B f g →
            DCPO-∘₃-is-continuous₂ (obj G B) (obj G A) (obj H A) (obj H B) (act G g f) (act H f g)
        ; fmap-is-locally-continuous = λ A B h →
            to-exp-continuous (Maps A B) (obj G B) (obj H B) (λ p → k A B (pr₁ p) (pr₂ p) h)
              (λ y → pr₂ (c A B h y))
        ; fmap-id = λ A h → to-continuous-function-＝ (obj G A) (obj H A)
                              (λ y → fmap-id H A _ ∙ ap (pr₁ h) (fmap-id G A y))
        ; fmap-∘ = λ A B C f g f' g' h → to-continuous-function-＝ (obj G C) (obj H C)
                     (λ y → fmap-∘ H A B C f g f' g' _
                            ∙ ap (λ - → fmap H B C f' g' (fmap H A B f g (h · -)))
                                 (fmap-∘ G C B A g' f' g f y)) }
 where
  k : (A B : DCPO₁) → DCPO[ A , B ] → DCPO[ B , A ]
    → DCPO[ obj G A , obj H A ] → DCPO[ obj G B , obj H B ]
  k A B f g h = DCPO-∘₃ (obj G B) (obj G A) (obj H A) (obj H B) (act G g f) h (act H f g)
  swap : (A B : DCPO₁) → DCPO[ Maps A B , Maps B A ]
  swap A B = pairᶜ (Maps A B) (B ⟹ᵈᶜᵖᵒ A) (A ⟹ᵈᶜᵖᵒ B)
               (pr₂-is-continuous (A ⟹ᵈᶜᵖᵒ B) (B ⟹ᵈᶜᵖᵒ A))
               (pr₁-is-continuous (A ⟹ᵈᶜᵖᵒ B) (B ⟹ᵈᶜᵖᵒ A))
  {- p ↦ H(p) (h (G(swap p) y)) -}
  c : (A B : DCPO₁) (h : DCPO[ obj G A , obj H A ]) (y : ⟨ obj G B ⟩) → DCPO[ Maps A B , obj H B ]
  c A B h y = DCPO-∘ (Maps A B) (Maps A B ×ᵈᶜᵖᵒ obj H A) (obj H B)
                (pairᶜ (Maps A B) (Maps A B) (obj H A) (idᶜ (Maps A B))
                   (DCPO-∘ (Maps A B) (obj G A) (obj H A)
                      (DCPO-∘ (Maps A B) (Maps B A) (obj G A) (swap A B) (act-at G B A y)) h))
                (act-joint H A B)

{- Sums ------------------------------------------------------------------------}

Σᶠ : (T : 𝓤₀ ̇ ) → is-set T → (T → Functor) → Functor
Σᶠ T T-is-set G =
 record { obj = O
        ; fmap = λ A B f g (t , x) → t , fmap (G t) A B f g x
        ; fmap-is-continuous = λ A B f g →
            pr₂ (copair T T-is-set (λ t → obj (G t) A) (O B)
                  (λ t → DCPO-∘ (obj (G t) A) (obj (G t) B) (O B) (act (G t) f g) (ι' B t)))
        ; fmap-is-locally-continuous = λ A B (t , x) →
            pr₂ (DCPO-∘ (Maps A B) (obj (G t) B) (O B) (act-at (G t) A B x) (ι' B t))
        ; fmap-id = λ A (t , x) → ap (t ,_) (fmap-id (G t) A x)
        ; fmap-∘ = λ A B C f g f' g' (t , x) → ap (t ,_) (fmap-∘ (G t) A B C f g f' g' x) }
 where
  O : DCPO₁ → DCPO₁
  O A = Σᵈ T T-is-set (λ t → obj (G t) A)
  ι' : (A : DCPO₁) (t : T) → DCPO[ obj (G t) A , O A ]
  ι' A = ι T T-is-set (λ t → obj (G t) A)

{- Lifting ---------------------------------------------------------------------}

Liftᶠ : Functor → Functor
Liftᶠ G =
 record { obj = λ A → 𝓛ᵈ (obj G A)
        ; fmap = λ A B f g → 𝓛map (obj G A) (obj G B) (act G f g)
        ; fmap-is-continuous = λ A B f g → 𝓛map-is-continuous (obj G A) (obj G B) (act G f g)
        ; fmap-is-locally-continuous = λ A B l →
            pr₂ (DCPO-∘ (Maps A B) (obj G A ⟹ᵈᶜᵖᵒ obj G B) (𝓛ᵈ (obj G B))
                   ((λ p → act G (pr₁ p) (pr₂ p)) ,
                    to-exp-continuous (Maps A B) (obj G A) (obj G B) (λ p → act G (pr₁ p) (pr₂ p)) (λ x → pr₂ (act-at G A B x)))
                   ((λ m → 𝓛map (obj G A) (obj G B) m l) ,
                    𝓛map-is-continuous-in-map (obj G A) (obj G B) l))
        ; fmap-id = λ A (P , φ , i) → ap (λ - → P , - , i) (dfunext fe (λ p → fmap-id G A (φ p)))
        ; fmap-∘ = λ A B C f g f' g' (P , φ , i) →
                     ap (λ - → P , - , i) (dfunext fe (λ p → fmap-∘ G A B C f g f' g' (φ p))) }

{- a lifted functor is pointed -}
Liftᶠ-⊥ : (G : Functor) (A : DCPO₁) → has-bottom (obj (Liftᶠ G) A)
Liftᶠ-⊥ G A = pr₂ (𝓛ᵈ⊥ (obj G A))

{- and its action is strict -}
Liftᶠ-strict : (G : Functor) (A B : DCPO₁) (f : DCPO[ A , B ]) (g : DCPO[ B , A ])
  → fmap (Liftᶠ G) A B f g (pr₁ (Liftᶠ-⊥ G A)) ＝ pr₁ (Liftᶠ-⊥ G B)
Liftᶠ-strict G A B f g = ap (λ - → 𝟘 , - , 𝟘-is-prop) (dfunext fe (λ ()))

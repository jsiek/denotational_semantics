{-

  Scott domains: fold : F D∞ → D∞ and unfold : D∞ → F D∞ are inverse
  (Framework/Scott/Solve.agda), so D∞ ≅ F D∞.

  fold (unfold σ) = σ: ⊒ because each component of fold (unfold σ) is
  above F(π∞ n , ε∞ n) (F(ε∞ n , π∞ n) (σ (n + 1))) = σ (n + 1); ⊑
  because fold (F(ε∞ n , π∞ n) (σ (n + 1))) is the sup of its ε∞π∞
  approximations, each below one of σ's.

  unfold (fold φ) = φ: ⊑ because each element F(ε∞ n , π∞ n) (F(π∞ n , ε∞ n) φ)
  = F(ε∞ n ∘ π∞ n , ε∞ n ∘ π∞ n) φ of the colimit family is below
  F(id , id) φ = φ; ⊒ because, F being locally continuous,
  φ = F(∐ ε∞π∞ , ∐ ε∞π∞) φ = ∐ F(ε∞ n ∘ π∞ n , ε∞ n ∘ π∞ n) φ.

  (TypeTopology's D∞ proves the same for F X = X ⟹ X by unfolding the
  exponential; here only the functor laws and local continuity are used.)

-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons
open import UF.Base using (ap₂; transport₂)

open import Naturals.Order
open import Naturals.Addition renaming (_+_ to _+'_)
open import Notation.Order

module proof.Framework.Scott.Solve
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : propext 𝓤₀)
       where

open import Framework.Scott.Base pt fe
open import Framework.Scott.Functor pt fe pe
open import Framework.Scott.Solve pt fe pe public

module SolutionIso (F : Functor) (F⊥ : (A : DCPO₁) → has-bottom (obj F A))
  (F-strict : (A B : DCPO₁) (f : DCPO[ A , B ]) (g : DCPO[ B , A ])
            → fmap F A B f g (pr₁ (F⊥ A)) ＝ pr₁ (F⊥ B))
  where

 open Solution F F⊥ F-strict

 private
  E : DCPO₁
  E = obj F D∞

  fmap-mono : (A B : DCPO₁) (x : ⟨ obj F A ⟩) (f f' : DCPO[ A , B ]) (g g' : DCPO[ B , A ])
    → f ⊑⟨ A ⟹₁ B ⟩ f' → g ⊑⟨ B ⟹₁ A ⟩ g'
    → fmap F A B f g x ⊑⟨ obj F B ⟩ fmap F A B f' g' x
  fmap-mono A B x f f' g g' u v =
   monotone-if-continuous (Maps A B) (obj F B) (act-at F A B x) (f , g) (f' , g') (u , v)

  {- ε∞ n ∘ π∞ n -}
  e : ℕ → DCPO[ D∞ , D∞ ]
  e n = ∘₁ D∞ (𝓓 n) D∞ (π∞₁ n) (ε∞₁ n)

  e-mono : (m n : ℕ) → m ≤ n → e m ⊑⟨ D∞ ⟹₁ D∞ ⟩ e n
  e-mono m n l σ = ε∞π∞-mono σ m n l

  πε-id : (n : ℕ) → ∘₁ (𝓓 n) D∞ (𝓓 n) (ε∞₁ n) (π∞₁ n) ＝ id₁ (𝓓 n)
  πε-id n = to-continuous-function-＝ (𝓓 n) (𝓓 n) (π∞-section n)

  πε : (n : ℕ) (x : ⟨ 𝓓 (succ n) ⟩)
     → fmap F D∞ (𝓓 n) (π∞₁ n) (ε∞₁ n) (fmap F (𝓓 n) D∞ (ε∞₁ n) (π∞₁ n) x) ＝ x
  πε n x = (fmap-∘ F (𝓓 n) D∞ (𝓓 n) (ε∞₁ n) (π∞₁ n) (π∞₁ n) (ε∞₁ n) x) ⁻¹
         ∙ ap (λ h → fmap F (𝓓 n) (𝓓 n) h h x) (πε-id n)
         ∙ fmap-id F (𝓓 n) x

  επ : (n : ℕ) (φ : ⟨ E ⟩)
     → fmap F (𝓓 n) D∞ (ε∞₁ n) (π∞₁ n) (fmap F D∞ (𝓓 n) (π∞₁ n) (ε∞₁ n) φ) ＝ fmap F D∞ D∞ (e n) (e n) φ
  επ n φ = (fmap-∘ F D∞ (𝓓 n) D∞ (π∞₁ n) (ε∞₁ n) (ε∞₁ n) (π∞₁ n) φ) ⁻¹

  fold-mono : (φ ψ : ⟨ E ⟩) → φ ⊑⟨ E ⟩ ψ → fold · φ ⊑⟨ D∞ ⟩ fold · ψ
  fold-mono = monotone-if-continuous E D∞ fold

 {- fold (unfold σ) = σ ----------------------------------------------------}

 fold-unfold : (σ : ⟨ D∞ ⟩) → fold · (unfold · σ) ＝ σ
 fold-unfold σ = antisymmetry D∞ (fold · u) σ a b
  where
   u : ⟨ E ⟩
   u = unfold · σ

   uf = unfold-family σ
   δu = unfold-family-is-directed σ

   {- σ is below fold (unfold σ), componentwise -}
   b-succ : (n : ℕ) → π∞₁ (succ n) · σ ⊑⟨ 𝓓 (succ n) ⟩ π-exp (succ n) u
   b-succ n = transport₂ (λ - -' → - ⊑⟨ 𝓓 (succ n) ⟩ -') (πε n (π∞₁ (succ n) · σ))
                (ap (fmap F D∞ (𝓓 n) (π∞₁ n) (ε∞₁ n)) ((unfold-is-sup σ) ⁻¹))
                (monotone-if-continuous E (𝓓 (succ n)) (act F (π∞₁ n) (ε∞₁ n)) _ _
                   (∐-is-upperbound E δu (succ n)))
   b-at : (n : ℕ) → π∞₁ n · σ ⊑⟨ 𝓓 n ⟩ π-exp n u
   b-at zero = transport (λ - → - ⊑⟨ 𝓓 0 ⟩ π-exp 0 u) (π∞-π 0 σ)
                 (monotone-if-continuous (𝓓 1) (𝓓 0) (π' 0) _ _ (b-succ 0))
   b-at (succ n) = b-succ n
   b : σ ⊑⟨ D∞ ⟩ fold · u
   b = D∞-⊑ σ (fold · u) (λ n → transport (λ - → π∞₁ n · σ ⊑⟨ 𝓓 n ⟩ -) ((π∞-fold n u) ⁻¹) (b-at n))

   {- fold (unfold σ) is below σ -}
   fold-uf : (n : ℕ) → fold · uf (succ n) ⊑⟨ D∞ ⟩ σ
   fold-uf n = sup-is-lowerbound-of-upperbounds (underlying-order D∞) (ε∞π∞-sup (fold · φ)) σ γ
    where
     φ = uf (succ n)
     γ : (m : ℕ) → ε∞₁ m · (π∞₁ m · (fold · φ)) ⊑⟨ D∞ ⟩ σ
     γ m = transitivity D∞ _ _ σ (ε∞π∞-mono (fold · φ) m (succ k) l₁)
            (transitivity D∞ _ _ σ
              (transport (λ - → ε∞₁ (succ k) · - ⊑⟨ D∞ ⟩ ε∞₁ (succ k) · (π∞₁ (succ k) · σ))
                 ((π∞-fold (succ k) φ) ⁻¹)
                 (monotone-if-continuous (𝓓 (succ k)) D∞ (ε∞₁ (succ k)) _ _
                   (transport (λ - → π-exp (succ k) φ ⊑⟨ 𝓓 (succ k) ⟩ -) (πε k (π∞₁ (succ k) · σ))
                     (monotone-if-continuous E (𝓓 (succ k)) (act F (π∞₁ k) (ε∞₁ k)) _ _
                        (unfold-family-is-monotone σ (succ n) (succ k) (≤-+ n m))))))
              (ε∞π∞-below (succ k) σ))
      where
       k = n +' m
       l₁ : m ≤ succ k
       l₁ = ≤-trans m k (succ k) (≤-+' n m) (≤-succ k)

   a : fold · u ⊑⟨ D∞ ⟩ σ
   a = transport (λ - → fold · - ⊑⟨ D∞ ⟩ σ) ((unfold-is-sup σ) ⁻¹)
        (transitivity D∞ _ _ σ (continuous-∐-⊑ E D∞ fold δu)
          (∐-is-lowerbound-of-upperbounds D∞ (image-is-directed' E D∞ fold δu) σ
            (λ n → transitivity D∞ _ _ σ
                     (fold-mono _ _ (unfold-family-is-monotone σ n (succ n) (≤-succ n)))
                     (fold-uf n))))

 {- unfold (fold φ) = φ ----------------------------------------------------}

 private
  ∐e-is-id : (δ : is-Directed (D∞ ⟹₁ D∞) e) → ∐ (D∞ ⟹₁ D∞) {ℕ} {e} δ ＝ id₁ D∞
  ∐e-is-id δ = to-continuous-function-＝ D∞ D∞ {∐ (D∞ ⟹₁ D∞) {ℕ} {e} δ} {id₁ D∞}
               (λ σ → antisymmetry D∞ (∐ D∞ (pointwise-directed D∞ D∞ e δ σ)) σ
                        (∐-is-lowerbound-of-upperbounds D∞ (pointwise-directed D∞ D∞ e δ σ) σ
                           (λ n → ε∞π∞-below n σ))
                        (sup-is-lowerbound-of-upperbounds (underlying-order D∞) (ε∞π∞-sup σ)
                           (∐ D∞ (pointwise-directed D∞ D∞ e δ σ))
                           (∐-is-upperbound D∞ (pointwise-directed D∞ D∞ e δ σ))))

  e-directed : is-Directed (D∞ ⟹₁ D∞) e
  e-directed = ∣ 0 ∣ , (λ m n → ∣ m +' n , e-mono m (m +' n) (≤-+ m n) , e-mono n (m +' n) (≤-+' m n) ∣)

  {- f ↦ F(f , f) φ, continuously -}
  diag : (φ : ⟨ E ⟩) → DCPO[ D∞ ⟹₁ D∞ , E ]
  diag φ = ∘₁ (D∞ ⟹₁ D∞) (Maps D∞ D∞) E
             (pair₁ (D∞ ⟹₁ D∞) (D∞ ⟹₁ D∞) (D∞ ⟹₁ D∞)
                (id₁ (D∞ ⟹₁ D∞)) (id₁ (D∞ ⟹₁ D∞)))
             (act-at F D∞ D∞ φ)

 unfold-fold : (φ : ⟨ E ⟩) → unfold · (fold · φ) ＝ φ
 unfold-fold φ = antisymmetry E (unfold · (fold · φ)) φ a b
  where
   cf : ℕ → ⟨ E ⟩
   cf = unfold-family (fold · φ)

   δf = unfold-family-is-directed (fold · φ)

   cf-succ : (n : ℕ) → cf (succ n) ＝ fmap F D∞ D∞ (e n) (e n) φ
   cf-succ n = ap (fmap F (𝓓 n) D∞ (ε∞₁ n) (π∞₁ n)) (π∞-fold (succ n) φ) ∙ επ n φ

   below-φ : (n : ℕ) → cf (succ n) ⊑⟨ E ⟩ φ
   below-φ n = transport (λ - → - ⊑⟨ E ⟩ φ) ((cf-succ n) ⁻¹)
                (transitivity E _ _ φ
                  (fmap-mono D∞ D∞ φ (e n) (id₁ D∞) (e n) (id₁ D∞) (ε∞π∞-below n) (ε∞π∞-below n))
                  (＝-to-⊑ E (fmap-id F D∞ φ)))

   a : unfold · (fold · φ) ⊑⟨ E ⟩ φ
   a = transport (λ - → - ⊑⟨ E ⟩ φ) ((unfold-is-sup (fold · φ)) ⁻¹)
        (∐-is-lowerbound-of-upperbounds E δf φ γ)
    where
     γ : (n : ℕ) → cf n ⊑⟨ E ⟩ φ
     γ zero = transitivity E _ _ φ (unfold-family-is-monotone (fold · φ) 0 1 ⋆) (below-φ 0)
     γ (succ n) = below-φ n

   b : φ ⊑⟨ E ⟩ unfold · (fold · φ)
   b = transport₂ (λ - -' → - ⊑⟨ E ⟩ -') p ((unfold-is-sup (fold · φ)) ⁻¹)
        (transitivity E (diag φ · ∐ (D∞ ⟹₁ D∞) {ℕ} {e} e-directed)
           (∐ E (image-is-directed' (D∞ ⟹₁ D∞) E (diag φ) {ℕ} {e} e-directed)) (∐ E δf)
           (continuous-∐-⊑ (D∞ ⟹₁ D∞) E (diag φ) {ℕ} {e} e-directed)
           (∐-is-lowerbound-of-upperbounds E
             (image-is-directed' (D∞ ⟹₁ D∞) E (diag φ) {ℕ} {e} e-directed) (∐ E δf)
             (λ n → transport (λ - → - ⊑⟨ E ⟩ ∐ E δf) (cf-succ n)
                      (∐-is-upperbound E δf (succ n)))))
    where
     p : diag φ · ∐ (D∞ ⟹₁ D∞) {ℕ} {e} e-directed ＝ φ
     p = ap (λ f → fmap F D∞ D∞ f f φ) (∐e-is-id e-directed) ∙ fmap-id F D∞ φ

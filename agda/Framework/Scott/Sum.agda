{-

  Scott domains: the sum (coproduct) Σᵈ T G of a family of dcpos G t
  indexed by a set T of tags. Its elements are pairs (t , x) with
  x : G t, and (s , x) ⊑ (t , y) when s = t and x ⊑ y; it has no least
  element (lifting it, Framework/Scott/Lift.agda, gives the separated
  sum). A directed family lies in one summand: its tags are all equal,
  because any two of its elements have an upper bound, and the tag can be
  read off a merely inhabited index type because T is a set. The
  injections ι t and the copairing of continuous maps are continuous.

-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.Sets
open import UF.Sets-Properties

module Framework.Scott.Sum
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
       where

open import Framework.Scott.Base pt fe

module _ (T : 𝓤₀ ̇ ) (T-is-set : is-set T) (G : T → DCPO₁) where

 private
  C : T → 𝓤₁ ̇
  C t = ⟨ G t ⟩

  tr : {s t : T} → s ＝ t → C s → C t
  tr = transport C

  {- transports along parallel equations agree, as T is a set -}
  tr-irr : {s t : T} (e e' : s ＝ t) (x : C s) → tr e x ＝ tr e' x
  tr-irr e e' x = ap (λ - → tr - x) (T-is-set e e')

  tr-∙ : {s t u : T} (e : s ＝ t) (e' : t ＝ u) (x : C s) → tr (e ∙ e') x ＝ tr e' (tr e x)
  tr-∙ refl refl x = refl

 _⊑Σ_ : Σ C → Σ C → 𝓤₁ ̇
 (s , x) ⊑Σ (t , y) = Σ e ꞉ s ＝ t , tr e x ⊑⟨ G t ⟩ y

 private
  ⊑Σ-prop : (a b : Σ C) → is-prop (a ⊑Σ b)
  ⊑Σ-prop (s , x) (t , y) = Σ-is-prop T-is-set (λ e → prop-valuedness (G t) (tr e x) y)

  ⊑Σ-refl : (a : Σ C) → a ⊑Σ a
  ⊑Σ-refl (s , x) = refl , reflexivity (G s) x

  ⊑Σ-trans : (a b c : Σ C) → a ⊑Σ b → b ⊑Σ c → a ⊑Σ c
  ⊑Σ-trans (s , x) (.s , y) (.s , z) (refl , u) (refl , v) =
   refl , transitivity (G s) x y z u v

  ⊑Σ-antisym : (a b : Σ C) → a ⊑Σ b → b ⊑Σ a → a ＝ b
  ⊑Σ-antisym (s , x) (.s , y) (refl , u) (e , v) =
   ap (s ,_) (antisymmetry (G s) x y u (transport (λ - → tr - y ⊑⟨ G s ⟩ x) (T-is-set e refl) v))

  {- the order, for a given equation of the tags -}
  ⊑Σ-at : {s t : T} {x : C s} {y : C t} (e : s ＝ t) → (s , x) ⊑Σ (t , y) → tr e x ⊑⟨ G t ⟩ y
  ⊑Σ-at {x = x} {y} e (e' , u) = transport (λ - → - ⊑⟨ G _ ⟩ y) (tr-irr e' e x) u

  {- transporting a sup -}
  tr-∐ : {s u : T} (e : s ＝ u) {I : 𝓤₀ ̇ } {β : I → C s} (δ : is-Directed (G s) β) (z : C u)
       → ((i : I) → tr e (β i) ⊑⟨ G u ⟩ z) → tr e (∐ (G s) δ) ⊑⟨ G u ⟩ z
  tr-∐ refl δ z = ∐-is-lowerbound-of-upperbounds (G _) δ z

 module _ {I : 𝓤₀ ̇ } (α : I → Σ C) (δ : is-directed _⊑Σ_ α) where

  tags-agree : (i j : I) → pr₁ (α i) ＝ pr₁ (α j)
  tags-agree i j = ∥∥-rec T-is-set (λ (k , (e₁ , _) , (e₂ , _)) → e₁ ∙ e₂ ⁻¹)
                    (semidirected-if-directed _⊑Σ_ α δ i j)

  {- the tag of a directed family -}
  common-tag : Σ t ꞉ T , ((i : I) → pr₁ (α i) ＝ t)
  common-tag = ∥∥-rec prop (λ i → pr₁ (α i) , (λ j → tags-agree j i))
                (inhabited-if-directed _⊑Σ_ α δ)
   where
    prop : is-prop (Σ t ꞉ T , ((i : I) → pr₁ (α i) ＝ t))
    prop (t , h) (t' , h') =
     to-subtype-＝ (λ _ → Π-is-prop fe (λ _ → T-is-set))
      (∥∥-rec T-is-set (λ i → h i ⁻¹ ∙ h' i) (inhabited-if-directed _⊑Σ_ α δ))

  tag : T
  tag = pr₁ common-tag

  tag-eq : (i : I) → pr₁ (α i) ＝ tag
  tag-eq = pr₂ common-tag

  {- the family, in the summand of its tag -}
  in-summand : I → C tag
  in-summand i = tr (tag-eq i) (pr₂ (α i))

  in-summand-is-directed : is-Directed (G tag) in-summand
  in-summand-is-directed =
   inhabited-if-directed _⊑Σ_ α δ ,
   (λ i j → ∥∥-functor (λ (k , u , v) → k , lemma i k u , lemma j k v)
                        (semidirected-if-directed _⊑Σ_ α δ i j))
   where
    lemma : (i k : I) → α i ⊑Σ α k → in-summand i ⊑⟨ G tag ⟩ in-summand k
    lemma i k (e , u) = transport (λ - → - ⊑⟨ G tag ⟩ in-summand k) p
                         (monotone-if-continuous (G (pr₁ (α k))) (G tag)
                           (tr (tag-eq k) , cont (tag-eq k)) _ _ u)
     where
      p : tr (tag-eq k) (tr e (pr₂ (α i))) ＝ in-summand i
      p = tr-∙ e (tag-eq k) (pr₂ (α i)) ⁻¹ ∙ tr-irr (e ∙ tag-eq k) (tag-eq i) (pr₂ (α i))
      cont : {s t : T} (e : s ＝ t) → is-continuous (G s) (G t) (tr e)
      cont refl = id-is-continuous (G _)

  ∐Σ : Σ C
  ∐Σ = tag , ∐ (G tag) in-summand-is-directed

  ∐Σ-is-sup : is-sup _⊑Σ_ ∐Σ α
  ∐Σ-is-sup = (λ i → tag-eq i , ∐-is-upperbound (G tag) in-summand-is-directed i) , lub
   where
    lub : (b : Σ C) → ((i : I) → α i ⊑Σ b) → ∐Σ ⊑Σ b
    lub (t , y) ub = ∥∥-rec (⊑Σ-prop ∐Σ (t , y)) γ (inhabited-if-directed _⊑Σ_ α δ)
     where
      γ : I → ∐Σ ⊑Σ (t , y)
      γ i₀ = e , tr-∐ e in-summand-is-directed y
                    (λ i → transport (λ - → - ⊑⟨ G t ⟩ y) (q i) (⊑Σ-at (tag-eq i ∙ e) (ub i)))
       where
        e : tag ＝ t
        e = tag-eq i₀ ⁻¹ ∙ pr₁ (ub i₀)
        q : (i : I) → tr (tag-eq i ∙ e) (pr₂ (α i)) ＝ tr e (in-summand i)
        q i = tr-∙ (tag-eq i) e (pr₂ (α i))

 Σᵈ : DCPO₁
 Σᵈ = Σ C , _⊑Σ_
    , (Σ-is-set T-is-set (λ t → sethood (G t)) , ⊑Σ-prop , ⊑Σ-refl , ⊑Σ-trans , ⊑Σ-antisym)
    , (λ I α δ → ∐Σ α δ , ∐Σ-is-sup α δ)

 {- the injections -}
 ι : (t : T) → DCPO[ G t , Σᵈ ]
 ι t = (t ,_) , c
  where
   c : is-continuous (G t) Σᵈ (t ,_)
   c I α δ = (λ i → refl , ∐-is-upperbound (G t) δ i) , lub
    where
     lub : (b : Σ C) → ((i : I) → (t , α i) ⊑Σ b) → (t , ∐ (G t) δ) ⊑Σ b
     lub (u , y) ub = ∥∥-rec (⊑Σ-prop _ (u , y))
                       (λ i₀ → pr₁ (ub i₀) , tr-∐ (pr₁ (ub i₀)) δ y (λ i → ⊑Σ-at (pr₁ (ub i₀)) (ub i)))
                       (inhabited-if-Directed (G t) α δ)

 {- copairing -}
 module _ {𝓤' 𝓣' : Universe} (E : DCPO {𝓤'} {𝓣'}) (h : (t : T) → DCPO[ G t , E ]) where

  [_]Σ : Σ C → ⟨ E ⟩
  [_]Σ (t , x) = h t · x

  private
   tr-h : {s t : T} (e : s ＝ t) (x : C s) → h t · tr e x ＝ h s · x
   tr-h refl x = refl

  copair : DCPO[ Σᵈ , E ]
  copair = [_]Σ , c
   where
    c : is-continuous Σᵈ E [_]Σ
    c I α δ = transport (is-sup (underlying-order E) (h (tag α δ) · ∐ (G (tag α δ)) (in-summand-is-directed α δ)))
                (dfunext fe (λ i → tr-h (tag-eq α δ i) (pr₂ (α i))))
                (pr₂ (h (tag α δ)) I (in-summand α δ) (in-summand-is-directed α δ))

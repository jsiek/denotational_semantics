{-

  Continuity of the error-propagating operators
  (Framework/GraphModel/ErrorOps.agda), and what a language of the graph
  model with errors needs of each of them (Good, ContinuityBase.agda).

  An error is witnessed by finitely many elements (ω in an operand, a
  value of the wrong kind, values in the operands before), so it is
  already produced by a finite part of the environment, as values are.

-}

open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.DOpSig
open import proof.Framework.GraphModel.Domain
open import proof.Framework.GraphModel.OpsBase
open import proof.Framework.GraphModel.ErrorOps
open import proof.Framework.GraphModel.Env using (Env; nonempty-env; finiteNE-env; _⊆ₑ_)
open import proof.Framework.GraphModel.DenotProperties
open import proof.Framework.GraphModel.ContinuityBase

open import Data.Nat using (ℕ; zero; suc)
open import Framework.abt.Sig using (∁)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_; replicate) renaming (map to lmap)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺; ∈-map⁻)
open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.Unit.Polymorphic using (⊤) renaming (tt to ptt)
open import Level using (lift; lower)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

module proof.Framework.GraphModel.ErrorContinuity where

{- Witnesses in a finite approximation ------------------------------------------}

{- an element with a property P, already in a finite approximation -}
oneP : ∀ (E : VEnv → 𝒫 Value) {ρ} {P : Value → Set} → Cont E ρ
  → (Σ[ d ∈ Value ] d ∈ E ρ × P d) → Σ[ a ∈ Approx ρ ] Σ[ d ∈ Value ] d ∈ E (env a) × P d
oneP E c ⟨ d , ⟨ d∈ , p ⟩ ⟩ with one E c d∈
... | ⟨ a , d∈′ ⟩ = ⟨ a , ⟨ d , ⟨ d∈′ , p ⟩ ⟩ ⟩

{- the same, for finitely many sets at once -}
coverP : ∀ {m} (P : Value → Set) (Es : Fin m → VEnv → 𝒫 Value) {ρ} → nonempty-env ρ
  → (∀ j → Mono (Es j)) → (∀ j → Cont (Es j) ρ) → (∀ j → Σ[ d ∈ Value ] d ∈ Es j ρ × P d)
  → Σ[ a ∈ Approx ρ ] (∀ j → Σ[ d ∈ Value ] d ∈ Es j (env a) × P d)
coverP {zero} P Es NE ms cs ps = ⟨ approx-init NE , (λ ()) ⟩
coverP {suc m} P Es NE ms cs ps
    with oneP (Es zero) (cs zero) (ps zero)
       | coverP P (λ j → Es (suc j)) NE (λ j → ms (suc j)) (λ j → cs (suc j)) (λ j → ps (suc j))
... | ⟨ a , ⟨ d , ⟨ d∈ , p ⟩ ⟩ ⟩ | ⟨ b , f ⟩ = ⟨ approx-join a b , G ⟩
  where
  G : ∀ j → Σ[ d ∈ Value ] d ∈ Es j (env (approx-join a b)) × P d
  G zero = ⟨ d , ⟨ ms zero (join-l a b) d d∈ , p ⟩ ⟩
  G (suc j) = ⟨ proj₁ (f j) , ⟨ ms (suc j) (join-r a b) _ (proj₁ (proj₂ (f j))) , proj₂ (proj₂ (f j)) ⟩ ⟩

{- operands, as functions of the environment, are monotone -}
oks-mono : ∀ n Es {ρ₁} → OK (replicate n ■) Es ρ₁ → ∀ {ρ ρ′} → ρ ⊆ₑ ρ′
  → results-rel-pres _⊆_ (replicate n ■) (⟪ replicate n ■ ⟫₊ Es ρ) (⟪ replicate n ■ ⟫₊ Es ρ′)
oks-mono zero _ _ _ = ptt
oks-mono (suc n) ⟨ E , Es ⟩ ⟨ ⟨ m , _ ⟩ , oks ⟩ ρ⊆ = ⟨ lift (m ρ⊆) , oks-mono n Es oks ρ⊆ ⟩

errs-cont : ∀ n Es {ρ} → nonempty-env ρ → OK (replicate n ■) Es ρ
  → errs n (⟪ replicate n ■ ⟫₊ Es ρ) → Σ[ a ∈ Approx ρ ] errs n (⟪ replicate n ■ ⟫₊ Es (env a))
errs-cont (suc n) ⟨ E , Es ⟩ NE ⟨ ⟨ m , c ⟩ , oks ⟩ (inj₁ ω∈) with one E c ω∈
... | ⟨ a , ω∈′ ⟩ = ⟨ a , inj₁ ω∈′ ⟩
errs-cont (suc n) ⟨ E , Es ⟩ NE ⟨ ⟨ m , c ⟩ , oks ⟩ (inj₂ ⟨ v , e ⟩)
    with oneP E c v | errs-cont n Es NE oks e
... | ⟨ a , ⟨ d , ⟨ d∈ , d≢ ⟩ ⟩ ⟩ | ⟨ b , e′ ⟩ =
  ⟨ approx-join a b , inj₂ ⟨ ⟨ d , ⟨ m (join-l a b) d d∈ , d≢ ⟩ ⟩
                          , errs-mono n _ _ (oks-mono n Es oks (join-r a b)) e′ ⟩ ⟩

vals-cont : ∀ n Es {ρ} → nonempty-env ρ → OK (replicate n ■) Es ρ
  → vals n (⟪ replicate n ■ ⟫₊ Es ρ) → Σ[ a ∈ Approx ρ ] vals n (⟪ replicate n ■ ⟫₊ Es (env a))
vals-cont n Es NE ok vs =
  coverP (_≢ ω) (λ j ρ → nthD (⟪ replicate n ■ ⟫₊ Es ρ) j) NE
    (λ j → proj₁ (nth-ok Es ok j)) (λ j → proj₂ (nth-ok Es ok j)) vs

{- Application -------------------------------------------------------------------}

⋆ᵉ-cont : Continuous (■ ∷ ■ ∷ []) ⋆ᵉ
⋆ᵉ-cont ⟨ E₁ , ⟨ E₂ , _ ⟩ ⟩ NE ⟨ ⟨ m₁ , c₁ ⟩ , ⟨ ⟨ m₂ , c₂ ⟩ , _ ⟩ ⟩ w (inj₁ ⟨ V , ⟨ e∈ , ⟨ V⊆ , r ⟩ ⟩ ⟩)
    with one E₁ c₁ e∈ | many E₂ NE m₂ c₂ V V⊆
... | ⟨ a , e∈′ ⟩ | ⟨ b , V⊆′ ⟩ =
  done (λ ρ → ⋆ᵉ ⟨ E₁ ρ , ⟨ E₂ ρ , ptt ⟩ ⟩) (approx-join a b) w
    (inj₁ ⟨ V , ⟨ m₁ (join-l a b) _ e∈′ , ⟨ (λ d d∈ → m₂ (join-r a b) d (V⊆′ d d∈)) , r ⟩ ⟩ ⟩)
⋆ᵉ-cont ⟨ E₁ , ⟨ E₂ , _ ⟩ ⟩ NE ⟨ ⟨ m₁ , c₁ ⟩ , ⟨ ⟨ m₂ , c₂ ⟩ , _ ⟩ ⟩ w (inj₂ ⟨ refl , inj₁ ω∈ ⟩)
    with one E₁ c₁ ω∈
... | ⟨ a , ω∈′ ⟩ = done (λ ρ → ⋆ᵉ ⟨ E₁ ρ , ⟨ E₂ ρ , ptt ⟩ ⟩) a ω (inj₂ ⟨ refl , inj₁ ω∈′ ⟩)
⋆ᵉ-cont ⟨ E₁ , ⟨ E₂ , _ ⟩ ⟩ NE ⟨ ⟨ m₁ , c₁ ⟩ , ⟨ ⟨ m₂ , c₂ ⟩ , _ ⟩ ⟩ w (inj₂ ⟨ refl , inj₂ (inj₁ wr) ⟩)
    with oneP E₁ c₁ wr
... | ⟨ a , wr′ ⟩ = done (λ ρ → ⋆ᵉ ⟨ E₁ ρ , ⟨ E₂ ρ , ptt ⟩ ⟩) a ω (inj₂ ⟨ refl , inj₂ (inj₁ wr′) ⟩)
⋆ᵉ-cont ⟨ E₁ , ⟨ E₂ , _ ⟩ ⟩ NE ⟨ ⟨ m₁ , c₁ ⟩ , ⟨ ⟨ m₂ , c₂ ⟩ , _ ⟩ ⟩ w (inj₂ ⟨ refl , inj₂ (inj₂ ⟨ f , ω∈ ⟩) ⟩)
    with oneP E₁ c₁ f | one E₂ c₂ ω∈
... | ⟨ a , ⟨ g , ⟨ g∈ , isf ⟩ ⟩ ⟩ | ⟨ b , ω∈′ ⟩ =
  done (λ ρ → ⋆ᵉ ⟨ E₁ ρ , ⟨ E₂ ρ , ptt ⟩ ⟩) (approx-join a b) ω
    (inj₂ ⟨ refl , inj₂ (inj₂ ⟨ ⟨ g , ⟨ m₁ (join-l a b) g g∈ , isf ⟩ ⟩ , m₂ (join-r a b) ω ω∈′ ⟩) ⟩)

{- Functions, whose body B binds one variable -----------------------------------}

Λᵉ-cont′ : ∀ {B : VEnv → 𝒫 Value} {ρ} → nonempty-env ρ → Mono B
  → (∀ V → V ≢ [] → Cont B (mem V • ρ)) → Cont (λ ρ → Λᵉ ⟨ (λ X → B (X • ρ)) , ptt ⟩) ρ
Λᵉ-cont′ {B} NE m c ν tt = done (λ ρ → Λᵉ ⟨ (λ X → B (X • ρ)) , ptt ⟩) (approx-init NE) ν tt
Λᵉ-cont′ {B} NE m c (V ↦ w) ⟨ w∈ , r ⟩ with c V (proj₁ r) w w∈
... | ⟨ ρ₂ , ⟨ f₂ , ⟨ s₂ , w∈₂ ⟩ ⟩ ⟩ =
  done (λ ρ → Λᵉ ⟨ (λ X → B (X • ρ)) , ptt ⟩) t (V ↦ w) ⟨ m env⊆ w w∈₂ , r ⟩
  where
  t = approx-tail (approx ρ₂ f₂ s₂)
  env⊆ : ∀ x → ρ₂ x ⊆ (mem V • env t) x
  env⊆ zero = s₂ zero
  env⊆ (suc x) = λ d d∈ → d∈

Λᵉ-cont : Continuous (ν ■ ∷ []) Λᵉ
Λᵉ-cont ⟨ B , _ ⟩ NE ⟨ ⟨ m , c ⟩ , _ ⟩ = Λᵉ-cont′ {B} NE m c

{- Tuples -------------------------------------------------------------------------}

𝒯ᵉ-cont : ∀ n → Continuous (replicate n ■) (𝒯ᵉ n)
𝒯ᵉ-cont n Es NE ok ω e with errs-cont n Es NE ok e
... | ⟨ a , e′ ⟩ = done (λ ρ → 𝒯ᵉ n (⟪ replicate n ■ ⟫₊ Es ρ)) a ω e′
𝒯ᵉ-cont zero Es NE ok ⟨⟩ tt = done (λ ρ → 𝒯ᵉ zero (⟪ [] ⟫₊ Es ρ)) (approx-init NE) ⟨⟩ tt
𝒯ᵉ-cont (suc n) Es NE ok (tup[ i ] d) ⟨ refl , ⟨ d∈ , vs ⟩ ⟩
    with one (λ ρ → nthD (⟪ replicate (suc n) ■ ⟫₊ Es ρ) i) (proj₂ (nth-ok Es ok i)) d∈
       | vals-cont (suc n) Es NE ok vs
... | ⟨ a , d∈′ ⟩ | ⟨ b , vs′ ⟩ =
  done (λ ρ → 𝒯ᵉ (suc n) (⟪ replicate (suc n) ■ ⟫₊ Es ρ)) (approx-join a b) (tup[ i ] d)
    ⟨ refl , ⟨ proj₁ (nth-ok Es ok i) (join-l a b) d d∈′
             , vals-mono (suc n) _ _ (oks-mono (suc n) Es ok (join-r a b)) vs′ ⟩ ⟩

projᵉ-cont : ∀ {n} (i : Fin n) → Continuous (■ ∷ []) (projᵉ i)
projᵉ-cont i _ NE ⟨ ⟨ _ , c ⟩ , _ ⟩ d (inj₁ t∈) with c _ t∈
... | ⟨ ρ′ , ⟨ f , ⟨ s , t∈′ ⟩ ⟩ ⟩ = ⟨ ρ′ , ⟨ f , ⟨ s , inj₁ t∈′ ⟩ ⟩ ⟩
projᵉ-cont i _ NE ⟨ ⟨ _ , c ⟩ , _ ⟩ d (inj₂ ⟨ refl , inj₁ ω∈ ⟩) with c ω ω∈
... | ⟨ ρ′ , ⟨ f , ⟨ s , ω∈′ ⟩ ⟩ ⟩ = ⟨ ρ′ , ⟨ f , ⟨ s , inj₂ ⟨ refl , inj₁ ω∈′ ⟩ ⟩ ⟩ ⟩
projᵉ-cont i ⟨ E , _ ⟩ NE ⟨ ⟨ _ , c ⟩ , _ ⟩ d (inj₂ ⟨ refl , inj₂ wr ⟩) with oneP E c wr
... | ⟨ a , wr′ ⟩ = done (λ ρ → projᵉ i ⟨ E ρ , ptt ⟩) a ω (inj₂ ⟨ refl , inj₂ wr′ ⟩)

{- Sums ---------------------------------------------------------------------------}

inlᵉ-cont : Continuous (■ ∷ []) inlᵉ
inlᵉ-cont _ NE ⟨ ⟨ _ , c ⟩ , _ ⟩ (left v) ⟨ v∈ , v≢ ⟩ with c v v∈
... | ⟨ ρ′ , ⟨ f , ⟨ s , v∈′ ⟩ ⟩ ⟩ = ⟨ ρ′ , ⟨ f , ⟨ s , ⟨ v∈′ , v≢ ⟩ ⟩ ⟩ ⟩
inlᵉ-cont _ NE ⟨ ⟨ _ , c ⟩ , _ ⟩ ω ω∈ = c ω ω∈

inrᵉ-cont : Continuous (■ ∷ []) inrᵉ
inrᵉ-cont _ NE ⟨ ⟨ _ , c ⟩ , _ ⟩ (right v) ⟨ v∈ , v≢ ⟩ with c v v∈
... | ⟨ ρ′ , ⟨ f , ⟨ s , v∈′ ⟩ ⟩ ⟩ = ⟨ ρ′ , ⟨ f , ⟨ s , ⟨ v∈′ , v≢ ⟩ ⟩ ⟩ ⟩
inrᵉ-cont _ NE ⟨ ⟨ _ , c ⟩ , _ ⟩ ω ω∈ = c ω ω∈

private
  map-left⊆ : ∀ {D : 𝒫 Value} {U} → (∀ d → d ∈ mem U → left d ∈ D) → mem (lmap left U) ⊆ D
  map-left⊆ all d d∈ with ∈-map⁻ left d∈
  ... | ⟨ y , ⟨ y∈ , refl ⟩ ⟩ = all y y∈

  map-right⊆ : ∀ {D : 𝒫 Value} {U} → (∀ d → d ∈ mem U → right d ∈ D) → mem (lmap right U) ⊆ D
  map-right⊆ all d d∈ with ∈-map⁻ right d∈
  ... | ⟨ y , ⟨ y∈ , refl ⟩ ⟩ = all y y∈

{- case analysis, whose branches B₁ and B₂ bind one variable -}
𝒞ᵉ-cont′ : ∀ {L B₁ B₂ : VEnv → 𝒫 Value} {ρ} → nonempty-env ρ
  → Mono L → Cont L ρ
  → Mono B₁ → (∀ V → V ≢ [] → Cont B₁ (mem V • ρ))
  → Mono B₂ → (∀ V → V ≢ [] → Cont B₂ (mem V • ρ))
  → Cont (λ ρ → 𝒞ᵉ ⟨ L ρ , ⟨ (λ X → B₁ (X • ρ)) , ⟨ (λ X → B₂ (X • ρ)) , ptt ⟩ ⟩ ⟩) ρ
𝒞ᵉ-cont′ {L}{B₁}{B₂} NE mL cL m₁ c₁ m₂ c₂ w (inj₁ ⟨ u , ⟨ U , ⟨ allL , ⟨ w∈ , r ⟩ ⟩ ⟩ ⟩)
    with many L NE mL cL (lmap left (u ∷ U)) (map-left⊆ allL) | c₁ (u ∷ U) (λ ()) w w∈
... | ⟨ a , Ls⊆′ ⟩ | ⟨ ρ₂ , ⟨ f₂ , ⟨ s₂ , w∈₂ ⟩ ⟩ ⟩ =
  done (λ ρ → 𝒞ᵉ ⟨ L ρ , ⟨ (λ X → B₁ (X • ρ)) , ⟨ (λ X → B₂ (X • ρ)) , ptt ⟩ ⟩ ⟩) (approx-join a t) w
    (inj₁ ⟨ u , ⟨ U , ⟨ (λ d d∈ → mL (join-l a t) (left d) (Ls⊆′ (left d) (∈-map⁺ left d∈)))
                     , ⟨ m₁ env⊆ w w∈₂ , r ⟩ ⟩ ⟩ ⟩)
  where
  t = approx-tail (approx ρ₂ f₂ s₂)
  env⊆ : ∀ x → ρ₂ x ⊆ (mem (u ∷ U) • env (approx-join a t)) x
  env⊆ zero = s₂ zero
  env⊆ (suc x) = join-r a t x
𝒞ᵉ-cont′ {L}{B₁}{B₂} NE mL cL m₁ c₁ m₂ c₂ w (inj₂ (inj₁ ⟨ u , ⟨ U , ⟨ allR , ⟨ w∈ , r ⟩ ⟩ ⟩ ⟩))
    with many L NE mL cL (lmap right (u ∷ U)) (map-right⊆ allR) | c₂ (u ∷ U) (λ ()) w w∈
... | ⟨ a , Rs⊆′ ⟩ | ⟨ ρ₂ , ⟨ f₂ , ⟨ s₂ , w∈₂ ⟩ ⟩ ⟩ =
  done (λ ρ → 𝒞ᵉ ⟨ L ρ , ⟨ (λ X → B₁ (X • ρ)) , ⟨ (λ X → B₂ (X • ρ)) , ptt ⟩ ⟩ ⟩) (approx-join a t) w
    (inj₂ (inj₁ ⟨ u , ⟨ U , ⟨ (λ d d∈ → mL (join-l a t) (right d) (Rs⊆′ (right d) (∈-map⁺ right d∈)))
                     , ⟨ m₂ env⊆ w w∈₂ , r ⟩ ⟩ ⟩ ⟩))
  where
  t = approx-tail (approx ρ₂ f₂ s₂)
  env⊆ : ∀ x → ρ₂ x ⊆ (mem (u ∷ U) • env (approx-join a t)) x
  env⊆ zero = s₂ zero
  env⊆ (suc x) = join-r a t x
𝒞ᵉ-cont′ {L}{B₁}{B₂} NE mL cL m₁ c₁ m₂ c₂ w (inj₂ (inj₂ ⟨ refl , inj₁ ω∈ ⟩)) with one L cL ω∈
... | ⟨ a , ω∈′ ⟩ =
  done (λ ρ → 𝒞ᵉ ⟨ L ρ , ⟨ (λ X → B₁ (X • ρ)) , ⟨ (λ X → B₂ (X • ρ)) , ptt ⟩ ⟩ ⟩) a ω
    (inj₂ (inj₂ ⟨ refl , inj₁ ω∈′ ⟩))
𝒞ᵉ-cont′ {L}{B₁}{B₂} NE mL cL m₁ c₁ m₂ c₂ w (inj₂ (inj₂ ⟨ refl , inj₂ wr ⟩)) with oneP L cL wr
... | ⟨ a , wr′ ⟩ =
  done (λ ρ → 𝒞ᵉ ⟨ L ρ , ⟨ (λ X → B₁ (X • ρ)) , ⟨ (λ X → B₂ (X • ρ)) , ptt ⟩ ⟩ ⟩) a ω
    (inj₂ (inj₂ ⟨ refl , inj₂ wr′ ⟩))

𝒞ᵉ-cont : Continuous (■ ∷ ν ■ ∷ ν ■ ∷ []) 𝒞ᵉ
𝒞ᵉ-cont ⟨ L , ⟨ B₁ , ⟨ B₂ , _ ⟩ ⟩ ⟩ NE ⟨ ⟨ mL , cL ⟩ , ⟨ ⟨ m₁ , c₁ ⟩ , ⟨ ⟨ m₂ , c₂ ⟩ , _ ⟩ ⟩ ⟩ =
  𝒞ᵉ-cont′ {L} {B₁} {B₂} NE mL cL m₁ c₁ m₂ c₂

{- let -----------------------------------------------------------------------------}

letᵉ-cont : Continuous (■ ∷ ν ■ ∷ []) letᵉ
letᵉ-cont ⟨ M , ⟨ N , _ ⟩ ⟩ NE ⟨ okM , ⟨ okN , _ ⟩ ⟩ =
  ⋆ᵉ-cont ⟨ (λ ρ → Λᵉ ⟨ (λ X → N (X • ρ)) , ptt ⟩) , ⟨ M , ptt ⟩ ⟩ NE
    ⟨ ⟨ mono-env (ν ■ ∷ []) Λᵉ-mono ⟨ N , ptt ⟩ ⟨ okN , ptt ⟩ , Λᵉ-cont ⟨ N , ptt ⟩ NE ⟨ okN , ptt ⟩ ⟩
    , ⟨ okM , ptt ⟩ ⟩

{- What a language needs of each operator ---------------------------------------------}

⋆ᵉ-good : ∀ {P} → Good P (■ ∷ ■ ∷ []) ⋆ᵉ
⋆ᵉ-good = mk-good ⋆ᵉ-mono ⋆ᵉ-consis ⋆ᵉ-cont

Λᵉ-good : ∀ {P} → Good P (ν ■ ∷ []) Λᵉ
Λᵉ-good = mk-good Λᵉ-mono Λᵉ-consis Λᵉ-cont

𝒯ᵉ-good : ∀ {P} n → Good P (replicate n ■) (𝒯ᵉ n)
𝒯ᵉ-good n = mk-good (𝒯ᵉ-mono n) (𝒯ᵉ-consis n) (𝒯ᵉ-cont n)

projᵉ-good : ∀ {P n} (i : Fin n) → Good P (■ ∷ []) (projᵉ i)
projᵉ-good i = mk-good (projᵉ-mono i) (projᵉ-consis i) (projᵉ-cont i)

inlᵉ-good : ∀ {P} → Good P (■ ∷ []) inlᵉ
inlᵉ-good = mk-good inlᵉ-mono inlᵉ-consis inlᵉ-cont

inrᵉ-good : ∀ {P} → Good P (■ ∷ []) inrᵉ
inrᵉ-good = mk-good inrᵉ-mono inrᵉ-consis inrᵉ-cont

𝒞ᵉ-good : ∀ {P} → Good P (■ ∷ ν ■ ∷ ν ■ ∷ []) 𝒞ᵉ
𝒞ᵉ-good = mk-good 𝒞ᵉ-mono 𝒞ᵉ-consis 𝒞ᵉ-cont

letᵉ-good : ∀ {P} → Good P (■ ∷ ν ■ ∷ []) letᵉ
letᵉ-good = mk-good letᵉ-mono letᵉ-consis letᵉ-cont

{- Closures and pairs (Clos3, Clos4) --------------------------------------------------}

{- the code of a closure is closed -}
ΛΛᵉ-cont : Continuous (∁ (ν (ν ■)) ∷ []) ΛΛᵉ
ΛΛᵉ-cont _ NE _ = const-cont NE

closᵉ-cont : ∀ n → Continuous (∁ (ν (ν ■)) ∷ replicate n ■) (closᵉ n)
closᵉ-cont n ⟨ B , Es ⟩ NE ⟨ okB , oks ⟩ =
  ⋆ᵉ-cont ⟨ (λ ρ → ΛΛᵉ (⟪ ∁ (ν (ν ■)) ∷ [] ⟫₊ ⟨ B , ptt ⟩ ρ))
          , ⟨ (λ ρ → 𝒯ᵉ n (⟪ replicate n ■ ⟫₊ Es ρ)) , ptt ⟩ ⟩ NE
    ⟨ ⟨ (λ _ d d∈ → d∈) , ΛΛᵉ-cont ⟨ B , ptt ⟩ NE ⟨ okB , ptt ⟩ ⟩
    , ⟨ ⟨ mono-env (replicate n ■) (𝒯ᵉ-mono n) Es oks , 𝒯ᵉ-cont n Es NE oks ⟩ , ptt ⟩ ⟩

pairᵉ-cont : Continuous (■ ∷ ■ ∷ []) pairᵉ
pairᵉ-cont ⟨ E₁ , ⟨ E₂ , _ ⟩ ⟩ NE ⟨ ⟨ m₁ , c₁ ⟩ , ⟨ ⟨ m₂ , c₂ ⟩ , _ ⟩ ⟩ ⦅ u , v ⦆ ⟨ u∈ , ⟨ v∈ , r ⟩ ⟩
    with one E₁ c₁ u∈ | one E₂ c₂ v∈
... | ⟨ a , u∈′ ⟩ | ⟨ b , v∈′ ⟩ =
  done (λ ρ → pairᵉ ⟨ E₁ ρ , ⟨ E₂ ρ , ptt ⟩ ⟩) (approx-join a b) ⦅ u , v ⦆
    ⟨ m₁ (join-l a b) u u∈′ , ⟨ m₂ (join-r a b) v v∈′ , r ⟩ ⟩
pairᵉ-cont ⟨ E₁ , ⟨ E₂ , _ ⟩ ⟩ NE oks ω e with errs-cont 2 ⟨ E₁ , ⟨ E₂ , ptt ⟩ ⟩ NE oks e
... | ⟨ a , e′ ⟩ = done (λ ρ → pairᵉ ⟨ E₁ ρ , ⟨ E₂ ρ , ptt ⟩ ⟩) a ω e′

carᵉ-cont : Continuous (■ ∷ []) carᵉ
carᵉ-cont _ NE ⟨ ⟨ _ , c ⟩ , _ ⟩ u (inj₁ ⟨ v , uv∈ ⟩) with c _ uv∈
... | ⟨ ρ′ , ⟨ f , ⟨ s , uv∈′ ⟩ ⟩ ⟩ = ⟨ ρ′ , ⟨ f , ⟨ s , inj₁ ⟨ v , uv∈′ ⟩ ⟩ ⟩ ⟩
carᵉ-cont _ NE ⟨ ⟨ _ , c ⟩ , _ ⟩ u (inj₂ ⟨ refl , inj₁ ω∈ ⟩) with c ω ω∈
... | ⟨ ρ′ , ⟨ f , ⟨ s , ω∈′ ⟩ ⟩ ⟩ = ⟨ ρ′ , ⟨ f , ⟨ s , inj₂ ⟨ refl , inj₁ ω∈′ ⟩ ⟩ ⟩ ⟩
carᵉ-cont ⟨ E , _ ⟩ NE ⟨ ⟨ _ , c ⟩ , _ ⟩ u (inj₂ ⟨ refl , inj₂ wr ⟩) with oneP E c wr
... | ⟨ a , wr′ ⟩ = done (λ ρ → carᵉ ⟨ E ρ , ptt ⟩) a ω (inj₂ ⟨ refl , inj₂ wr′ ⟩)

cdrᵉ-cont : Continuous (■ ∷ []) cdrᵉ
cdrᵉ-cont _ NE ⟨ ⟨ _ , c ⟩ , _ ⟩ v (inj₁ ⟨ u , uv∈ ⟩) with c _ uv∈
... | ⟨ ρ′ , ⟨ f , ⟨ s , uv∈′ ⟩ ⟩ ⟩ = ⟨ ρ′ , ⟨ f , ⟨ s , inj₁ ⟨ u , uv∈′ ⟩ ⟩ ⟩ ⟩
cdrᵉ-cont _ NE ⟨ ⟨ _ , c ⟩ , _ ⟩ v (inj₂ ⟨ refl , inj₁ ω∈ ⟩) with c ω ω∈
... | ⟨ ρ′ , ⟨ f , ⟨ s , ω∈′ ⟩ ⟩ ⟩ = ⟨ ρ′ , ⟨ f , ⟨ s , inj₂ ⟨ refl , inj₁ ω∈′ ⟩ ⟩ ⟩ ⟩
cdrᵉ-cont ⟨ E , _ ⟩ NE ⟨ ⟨ _ , c ⟩ , _ ⟩ v (inj₂ ⟨ refl , inj₂ wr ⟩) with oneP E c wr
... | ⟨ a , wr′ ⟩ = done (λ ρ → cdrᵉ ⟨ E ρ , ptt ⟩) a ω (inj₂ ⟨ refl , inj₂ wr′ ⟩)

callᵉ-cont : Continuous (■ ∷ ■ ∷ ■ ∷ []) callᵉ
callᵉ-cont ⟨ E₁ , ⟨ E₂ , ⟨ E₃ , _ ⟩ ⟩ ⟩ NE ⟨ ⟨ m₁ , c₁ ⟩ , ⟨ ⟨ m₂ , c₂ ⟩ , ⟨ ⟨ m₃ , c₃ ⟩ , _ ⟩ ⟩ ⟩ w
    (inj₁ ⟨ V , ⟨ U , ⟨ e∈ , ⟨ V⊆ , ⟨ U⊆ , r ⟩ ⟩ ⟩ ⟩ ⟩)
    with one E₁ c₁ e∈ | many E₂ NE m₂ c₂ V V⊆ | many E₃ NE m₃ c₃ U U⊆
... | ⟨ a , e∈′ ⟩ | ⟨ b , V⊆′ ⟩ | ⟨ c , U⊆′ ⟩ =
  done (λ ρ → callᵉ ⟨ E₁ ρ , ⟨ E₂ ρ , ⟨ E₃ ρ , ptt ⟩ ⟩ ⟩) (approx-join a (approx-join b c)) w
    (inj₁ ⟨ V , ⟨ U , ⟨ m₁ (join-l a bc) _ e∈′
          , ⟨ (λ d d∈ → m₂ (λ x d′ d′∈ → join-r a bc x d′ (join-l b c x d′ d′∈)) d (V⊆′ d d∈))
          , ⟨ (λ d d∈ → m₃ (λ x d′ d′∈ → join-r a bc x d′ (join-r b c x d′ d′∈)) d (U⊆′ d d∈)) , r ⟩ ⟩ ⟩ ⟩ ⟩)
  where bc = approx-join b c
callᵉ-cont ⟨ E₁ , ⟨ E₂ , ⟨ E₃ , _ ⟩ ⟩ ⟩ NE oks w (inj₂ ⟨ refl , inj₁ e ⟩)
    with errs-cont 3 ⟨ E₁ , ⟨ E₂ , ⟨ E₃ , ptt ⟩ ⟩ ⟩ NE oks e
... | ⟨ a , e′ ⟩ = done (λ ρ → callᵉ ⟨ E₁ ρ , ⟨ E₂ ρ , ⟨ E₃ ρ , ptt ⟩ ⟩ ⟩) a ω (inj₂ ⟨ refl , inj₁ e′ ⟩)
callᵉ-cont ⟨ E₁ , ⟨ E₂ , ⟨ E₃ , _ ⟩ ⟩ ⟩ NE ⟨ ⟨ m₁ , c₁ ⟩ , ⟨ ⟨ m₂ , c₂ ⟩ , ⟨ ⟨ m₃ , c₃ ⟩ , _ ⟩ ⟩ ⟩ w
    (inj₂ ⟨ refl , inj₂ ⟨ wr , ⟨ vm , vn ⟩ ⟩ ⟩)
    with oneP E₁ c₁ wr | oneP E₂ c₂ vm | oneP E₃ c₃ vn
... | ⟨ a , ⟨ d , ⟨ d∈ , r ⟩ ⟩ ⟩ | ⟨ b , ⟨ e , ⟨ e∈ , r' ⟩ ⟩ ⟩ | ⟨ c , ⟨ f , ⟨ f∈ , r'' ⟩ ⟩ ⟩ =
  done (λ ρ → callᵉ ⟨ E₁ ρ , ⟨ E₂ ρ , ⟨ E₃ ρ , ptt ⟩ ⟩ ⟩) (approx-join a bc) ω
    (inj₂ ⟨ refl , inj₂ ⟨ ⟨ d , ⟨ m₁ (join-l a bc) d d∈ , r ⟩ ⟩
                       , ⟨ ⟨ e , ⟨ m₂ (λ x d′ d′∈ → join-r a bc x d′ (join-l b c x d′ d′∈)) e e∈ , r' ⟩ ⟩
                         , ⟨ f , ⟨ m₃ (λ x d′ d′∈ → join-r a bc x d′ (join-r b c x d′ d′∈)) f f∈ , r'' ⟩ ⟩ ⟩ ⟩ ⟩)
  where bc = approx-join b c

ΛΛᵉ-good : ∀ {P} → Good P (∁ (ν (ν ■)) ∷ []) ΛΛᵉ
ΛΛᵉ-good = mk-good ΛΛᵉ-mono ΛΛᵉ-consis ΛΛᵉ-cont

closᵉ-good : ∀ {P} n → Good P (∁ (ν (ν ■)) ∷ replicate n ■) (closᵉ n)
closᵉ-good n = mk-good (closᵉ-mono n) (closᵉ-consis n) (closᵉ-cont n)

pairᵉ-good : ∀ {P} → Good P (■ ∷ ■ ∷ []) pairᵉ
pairᵉ-good = mk-good pairᵉ-mono pairᵉ-consis pairᵉ-cont

carᵉ-good : ∀ {P} → Good P (■ ∷ []) carᵉ
carᵉ-good = mk-good carᵉ-mono carᵉ-consis carᵉ-cont

cdrᵉ-good : ∀ {P} → Good P (■ ∷ []) cdrᵉ
cdrᵉ-good = mk-good cdrᵉ-mono cdrᵉ-consis cdrᵉ-cont

callᵉ-good : ∀ {P} → Good P (■ ∷ ■ ∷ ■ ∷ []) callᵉ
callᵉ-good = mk-good callᵉ-mono callᵉ-consis callᵉ-cont

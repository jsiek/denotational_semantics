{-

  Continuity of the graph-model operators.

  (The definitions, Continuous and Good, are in ContinuityBase.agda.)

  Each lemma says that an operator preserves continuity (Continuous): if
  the bodies of its operands are monotone and continuous wherever the
  operands put them (every element is already produced by a finite,
  nonempty sub-environment), then so is the result. With monotonicity and
  consistency, this is what a language needs of each of its operators
  (Good); the properties of whole terms follow once, in SemanticsUtil.

-}

open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.DOpSig
open import proof.Framework.GraphModel.Domain
open import proof.Framework.GraphModel.Ops
open import proof.Framework.GraphModel.Env using (Env; nonempty-env; finiteNE-env; _⊆ₑ_; _⊔ₑ_; join-finiteNE-env; •-~)
open import proof.Framework.GraphModel.DenotProperties
open import Framework.abt.ScopedTuple using (Tuple)
open import Framework.abt.Sig using (Sig; Result; ∁)

open import Data.Nat using (zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_; replicate) renaming (map to lmap)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺; ∈-map⁻)
open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax)
  renaming (_,_ to ⟨_,_⟩ )
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit.Polymorphic using (⊤) renaming (tt to ptt)
open import Level using (lift; lower)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≢_; refl)

module proof.Framework.GraphModel.Continuity where

open import proof.Framework.GraphModel.ContinuityBase public

ΛΛ-cont : Continuous (∁ (ν (ν ■)) ∷ []) ΛΛ
ΛΛ-cont _ NE _ = const-cont NE

{- Functions, whose body B binds one variable -----------------------------------}

Λ-cont′ : ∀ {B : VEnv → 𝒫 Value} {ρ} → nonempty-env ρ → Mono B
  → (∀ V → V ≢ [] → Cont B (mem V • ρ)) → Cont (λ ρ → Λ ⟨ (λ X → B (X • ρ)) , ptt ⟩) ρ
Λ-cont′ {B} NE m c ν tt = done (λ ρ → Λ ⟨ (λ X → B (X • ρ)) , ptt ⟩) (approx-init NE) ν tt
Λ-cont′ {B} NE m c (V ↦ w) ⟨ w∈ , neV ⟩ with c V (proj₁ neV) w w∈
... | ⟨ ρ₂ , ⟨ f₂ , ⟨ s₂ , w∈₂ ⟩ ⟩ ⟩ =
  done (λ ρ → Λ ⟨ (λ X → B (X • ρ)) , ptt ⟩) t (V ↦ w) ⟨ m env⊆ w w∈₂ , neV ⟩
  where
  t = approx-tail (approx ρ₂ f₂ s₂)
  env⊆ : ∀ x → ρ₂ x ⊆ (mem V • env t) x
  env⊆ zero = s₂ zero
  env⊆ (suc x) = λ d d∈ → d∈

Λ-cont : Continuous (ν ■ ∷ []) Λ
Λ-cont ⟨ B , _ ⟩ NE ⟨ ⟨ m , c ⟩ , _ ⟩ = Λ-cont′ {B} NE m c

{- Application ----------------------------------------------------------------}

⋆-cont : Continuous (■ ∷ ■ ∷ []) ⋆
⋆-cont ⟨ E₁ , ⟨ E₂ , _ ⟩ ⟩ NE ⟨ ⟨ m₁ , c₁ ⟩ , ⟨ ⟨ m₂ , c₂ ⟩ , _ ⟩ ⟩ w ⟨ V , ⟨ e∈ , ⟨ V⊆ , ne ⟩ ⟩ ⟩
    with one E₁ c₁ e∈ | many E₂ NE m₂ c₂ V V⊆
... | ⟨ a , e∈′ ⟩ | ⟨ b , V⊆′ ⟩ =
  done (λ ρ → ⋆ ⟨ E₁ ρ , ⟨ E₂ ρ , ptt ⟩ ⟩) (approx-join a b) w
    ⟨ V , ⟨ m₁ (join-l a b) _ e∈′ , ⟨ (λ d d∈ → m₂ (join-r a b) d (V⊆′ d d∈)) , ne ⟩ ⟩ ⟩

{- Pairs ----------------------------------------------------------------------}

pair-cont : Continuous (■ ∷ ■ ∷ []) pair
pair-cont ⟨ E₁ , ⟨ E₂ , _ ⟩ ⟩ NE ⟨ ⟨ m₁ , c₁ ⟩ , ⟨ ⟨ m₂ , c₂ ⟩ , _ ⟩ ⟩ ⦅ u , v ⦆ ⟨ u∈ , v∈ ⟩
    with one E₁ c₁ u∈ | one E₂ c₂ v∈
... | ⟨ a , u∈′ ⟩ | ⟨ b , v∈′ ⟩ =
  done (λ ρ → pair ⟨ E₁ ρ , ⟨ E₂ ρ , ptt ⟩ ⟩) (approx-join a b) ⦅ u , v ⦆
    ⟨ m₁ (join-l a b) u u∈′ , m₂ (join-r a b) v v∈′ ⟩

car-cont′ : ∀ {E ρ} → Cont E ρ → Cont (λ ρ → car ⟨ E ρ , ptt ⟩) ρ
car-cont′ {E} c u ⟨ v , uv∈ ⟩ with c ⦅ u , v ⦆ uv∈
... | ⟨ ρ′ , ⟨ f , ⟨ s , uv∈′ ⟩ ⟩ ⟩ = ⟨ ρ′ , ⟨ f , ⟨ s , ⟨ v , uv∈′ ⟩ ⟩ ⟩ ⟩

cdr-cont′ : ∀ {E ρ} → Cont E ρ → Cont (λ ρ → cdr ⟨ E ρ , ptt ⟩) ρ
cdr-cont′ {E} c v ⟨ u , uv∈ ⟩ with c ⦅ u , v ⦆ uv∈
... | ⟨ ρ′ , ⟨ f , ⟨ s , uv∈′ ⟩ ⟩ ⟩ = ⟨ ρ′ , ⟨ f , ⟨ s , ⟨ u , uv∈′ ⟩ ⟩ ⟩ ⟩

car-cont : Continuous (■ ∷ []) car
car-cont ⟨ E , _ ⟩ NE ⟨ ⟨ _ , c ⟩ , _ ⟩ = car-cont′ {E} c

cdr-cont : Continuous (■ ∷ []) cdr
cdr-cont ⟨ E , _ ⟩ NE ⟨ ⟨ _ , c ⟩ , _ ⟩ = cdr-cont′ {E} c

𝒯-cont : ∀ n → Continuous (replicate n ■) (𝒯 n)
𝒯-cont zero Es NE _ ⟨⟩ tt = done (λ ρ → 𝒯 zero (⟪ [] ⟫₊ Es ρ)) (approx-init NE) ⟨⟩ tt
𝒯-cont (suc n) Es NE ok (tup[ i ] d) ⟨ refl , ⟨ d∈ , ne ⟩ ⟩
    with one (λ ρ → nthD (⟪ replicate (suc n) ■ ⟫₊ Es ρ) i) (proj₂ (nth-ok Es ok i)) d∈
       | cover (λ j ρ → nthD (⟪ replicate (suc n) ■ ⟫₊ Es ρ) j) NE
           (λ j → proj₁ (nth-ok Es ok j)) (λ j → proj₂ (nth-ok Es ok j)) ne
... | ⟨ a , d∈′ ⟩ | ⟨ b , ne′ ⟩ =
  done (λ ρ → 𝒯 (suc n) (⟪ replicate (suc n) ■ ⟫₊ Es ρ)) (approx-join a b) (tup[ i ] d)
    ⟨ refl , ⟨ proj₁ (nth-ok Es ok i) (join-l a b) d d∈′
             , (λ j → ⟨ proj₁ (ne′ j) , proj₁ (nth-ok Es ok j) (join-r a b) _ (proj₂ (ne′ j)) ⟩) ⟩ ⟩

proj-cont : ∀ {n} (i : Fin n) → Continuous (■ ∷ []) (proj i)
proj-cont i _ NE ⟨ ⟨ _ , c ⟩ , _ ⟩ d d∈ = c (tup[ i ] d) d∈

{- Sums -----------------------------------------------------------------------}

inl-cont : Continuous (■ ∷ []) inl
inl-cont _ NE ⟨ ⟨ _ , c ⟩ , _ ⟩ (left d) d∈ = c d d∈

inr-cont : Continuous (■ ∷ []) inr
inr-cont _ NE ⟨ ⟨ _ , c ⟩ , _ ⟩ (right d) d∈ = c d d∈

{- Case analysis, whose branches B₁ and B₂ bind one variable -}
map-left⊆ : ∀ {D : 𝒫 Value} {U} → (∀ d → d ∈ mem U → left d ∈ D) → mem (lmap left U) ⊆ D
map-left⊆ all d d∈ with ∈-map⁻ left d∈
... | ⟨ y , ⟨ y∈ , refl ⟩ ⟩ = all y y∈

map-right⊆ : ∀ {D : 𝒫 Value} {U} → (∀ d → d ∈ mem U → right d ∈ D) → mem (lmap right U) ⊆ D
map-right⊆ all d d∈ with ∈-map⁻ right d∈
... | ⟨ y , ⟨ y∈ , refl ⟩ ⟩ = all y y∈

𝒞-cont′ : ∀ {L B₁ B₂ : VEnv → 𝒫 Value} {ρ} → nonempty-env ρ
  → Mono L → Cont L ρ
  → Mono B₁ → (∀ V → V ≢ [] → Cont B₁ (mem V • ρ))
  → Mono B₂ → (∀ V → V ≢ [] → Cont B₂ (mem V • ρ))
  → Cont (λ ρ → 𝒞 ⟨ L ρ , ⟨ (λ X → B₁ (X • ρ)) , ⟨ (λ X → B₂ (X • ρ)) , ptt ⟩ ⟩ ⟩) ρ
𝒞-cont′ {L}{B₁}{B₂} NE mL cL m₁ c₁ m₂ c₂ w (inj₁ ⟨ u , ⟨ U , ⟨ allL , ⟨ w∈ , c ⟩ ⟩ ⟩ ⟩)
    with many L NE mL cL (lmap left (u ∷ U)) (map-left⊆ allL) | c₁ (u ∷ U) (λ ()) w w∈
... | ⟨ a , Ls⊆′ ⟩ | ⟨ ρ₂ , ⟨ f₂ , ⟨ s₂ , w∈₂ ⟩ ⟩ ⟩ =
  done (λ ρ → 𝒞 ⟨ L ρ , ⟨ (λ X → B₁ (X • ρ)) , ⟨ (λ X → B₂ (X • ρ)) , ptt ⟩ ⟩ ⟩) (approx-join a t) w
    (inj₁ ⟨ u , ⟨ U , ⟨ (λ d d∈ → mL (join-l a t) (left d) (Ls⊆′ (left d) (∈-map⁺ left d∈)))
                     , ⟨ m₁ env⊆ w w∈₂ , c ⟩ ⟩ ⟩ ⟩)
  where
  t = approx-tail (approx ρ₂ f₂ s₂)
  env⊆ : ∀ x → ρ₂ x ⊆ (mem (u ∷ U) • env (approx-join a t)) x
  env⊆ zero = s₂ zero
  env⊆ (suc x) = join-r a t x
𝒞-cont′ {L}{B₁}{B₂} NE mL cL m₁ c₁ m₂ c₂ w (inj₂ ⟨ u , ⟨ U , ⟨ allR , ⟨ w∈ , c ⟩ ⟩ ⟩ ⟩)
    with many L NE mL cL (lmap right (u ∷ U)) (map-right⊆ allR) | c₂ (u ∷ U) (λ ()) w w∈
... | ⟨ a , Rs⊆′ ⟩ | ⟨ ρ₂ , ⟨ f₂ , ⟨ s₂ , w∈₂ ⟩ ⟩ ⟩ =
  done (λ ρ → 𝒞 ⟨ L ρ , ⟨ (λ X → B₁ (X • ρ)) , ⟨ (λ X → B₂ (X • ρ)) , ptt ⟩ ⟩ ⟩) (approx-join a t) w
    (inj₂ ⟨ u , ⟨ U , ⟨ (λ d d∈ → mL (join-l a t) (right d) (Rs⊆′ (right d) (∈-map⁺ right d∈)))
                     , ⟨ m₂ env⊆ w w∈₂ , c ⟩ ⟩ ⟩ ⟩)
  where
  t = approx-tail (approx ρ₂ f₂ s₂)
  env⊆ : ∀ x → ρ₂ x ⊆ (mem (u ∷ U) • env (approx-join a t)) x
  env⊆ zero = s₂ zero
  env⊆ (suc x) = join-r a t x

𝒞-cont : Continuous (■ ∷ ν ■ ∷ ν ■ ∷ []) 𝒞
𝒞-cont ⟨ L , ⟨ B₁ , ⟨ B₂ , _ ⟩ ⟩ ⟩ NE ⟨ ⟨ mL , cL ⟩ , ⟨ ⟨ m₁ , c₁ ⟩ , ⟨ ⟨ m₂ , c₂ ⟩ , _ ⟩ ⟩ ⟩ =
  𝒞-cont′ {L} {B₁} {B₂} NE mL cL m₁ c₁ m₂ c₂

{- Composites -------------------------------------------------------------------}

letD-cont : Continuous (■ ∷ ν ■ ∷ []) letD
letD-cont ⟨ M , ⟨ N , _ ⟩ ⟩ NE ⟨ okM , ⟨ okN , _ ⟩ ⟩ =
  ⋆-cont ⟨ (λ ρ → Λ ⟨ (λ X → N (X • ρ)) , ptt ⟩) , ⟨ M , ptt ⟩ ⟩ NE
    ⟨ ⟨ mono-env (ν ■ ∷ []) Λ-mono ⟨ N , ptt ⟩ ⟨ okN , ptt ⟩ , Λ-cont ⟨ N , ptt ⟩ NE ⟨ okN , ptt ⟩ ⟩
    , ⟨ okM , ptt ⟩ ⟩

⋆₂-cont : Continuous (■ ∷ ■ ∷ ■ ∷ []) ⋆₂
⋆₂-cont ⟨ L , ⟨ M , ⟨ N , _ ⟩ ⟩ ⟩ NE ⟨ okL , ⟨ okM , ⟨ okN , _ ⟩ ⟩ ⟩ =
  ⋆-cont ⟨ (λ ρ → ⋆ ⟨ L ρ , ⟨ M ρ , ptt ⟩ ⟩) , ⟨ N , ptt ⟩ ⟩ NE
    ⟨ ⟨ mono-env (■ ∷ ■ ∷ []) ⋆-mono ⟨ L , ⟨ M , ptt ⟩ ⟩ okLM , ⋆-cont ⟨ L , ⟨ M , ptt ⟩ ⟩ NE okLM ⟩
    , ⟨ okN , ptt ⟩ ⟩
  where okLM = ⟨ okL , ⟨ okM , ptt ⟩ ⟩

closD-cont : ∀ n → Continuous (∁ (ν (ν ■)) ∷ replicate n ■) (closD n)
closD-cont n ⟨ B , Es ⟩ NE ⟨ okB , oks ⟩ =
  ⋆-cont ⟨ (λ ρ → ΛΛ (⟪ ∁ (ν (ν ■)) ∷ [] ⟫₊ ⟨ B , ptt ⟩ ρ))
         , ⟨ (λ ρ → 𝒯 n (⟪ replicate n ■ ⟫₊ Es ρ)) , ptt ⟩ ⟩ NE
    ⟨ ⟨ (λ _ d d∈ → d∈) , ΛΛ-cont ⟨ B , ptt ⟩ NE ⟨ okB , ptt ⟩ ⟩
    , ⟨ ⟨ mono-env (replicate n ■) (𝒯-mono n) Es oks , 𝒯-cont n Es NE oks ⟩ , ptt ⟩ ⟩

Λ-good : ∀ {P} → Good P (ν ■ ∷ []) Λ
Λ-good = mk-good Λ-mono Λ-consis Λ-cont

⋆-good : ∀ {P} → Good P (■ ∷ ■ ∷ []) ⋆
⋆-good = mk-good ⋆-mono ⋆-consis ⋆-cont

pair-good : ∀ {P} → Good P (■ ∷ ■ ∷ []) pair
pair-good = mk-good pair-mono pair-consis pair-cont

car-good : ∀ {P} → Good P (■ ∷ []) car
car-good = mk-good car-mono car-consis car-cont

cdr-good : ∀ {P} → Good P (■ ∷ []) cdr
cdr-good = mk-good cdr-mono cdr-consis cdr-cont

𝒯-good : ∀ {P} n → Good P (replicate n ■) (𝒯 n)
𝒯-good n = mk-good (𝒯-mono n) (𝒯-consis n) (𝒯-cont n)

proj-good : ∀ {P n} (i : Fin n) → Good P (■ ∷ []) (proj i)
proj-good i = mk-good (proj-mono i) (proj-consis i) (proj-cont i)

inl-good : ∀ {P} → Good P (■ ∷ []) inl
inl-good = mk-good inl-mono inl-consis inl-cont

inr-good : ∀ {P} → Good P (■ ∷ []) inr
inr-good = mk-good inr-mono inr-consis inr-cont

𝒞-good : ∀ {P} → Good P (■ ∷ ν ■ ∷ ν ■ ∷ []) 𝒞
𝒞-good = mk-good 𝒞-mono 𝒞-consis 𝒞-cont

letD-good : ∀ {P} → Good P (■ ∷ ν ■ ∷ []) letD
letD-good = mk-good letD-mono letD-consis letD-cont

⋆₂-good : ∀ {P} → Good P (■ ∷ ■ ∷ ■ ∷ []) ⋆₂
⋆₂-good = mk-good ⋆₂-mono ⋆₂-consis ⋆₂-cont

ΛΛ-good : ∀ {P} → Good P (∁ (ν (ν ■)) ∷ []) ΛΛ
ΛΛ-good = mk-good ΛΛ-mono ΛΛ-consis ΛΛ-cont

closD-good : ∀ {P} n → Good P (∁ (ν (ν ■)) ∷ replicate n ■) (closD n)
closD-good n = mk-good (closD-mono n) (closD-consis n) (closD-cont n)

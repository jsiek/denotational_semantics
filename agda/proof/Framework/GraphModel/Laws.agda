{-

  Laws of the graph model's operators: how a let or a case commutes with
  a continuation (let-law, case-law), used by lift locals; and writes
  strict in their value (strict-≃), used by select. The counterpart, with
  errors, is in ErrorMonad.

-}

open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.Domain
open import proof.Framework.GraphModel.Ops
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Product using (_×_; Σ-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

module proof.Framework.GraphModel.Laws where

{- Commuting with let and case --------------------------------------------------------}

MonoF : (𝒫 Value → 𝒫 Value) → Set₁
MonoF F = ∀ {X X'} → X ⊆ X' → F X ⊆ F X'

{- u is in F on a finite, nonempty part of P -}
Run : 𝒫 Value → (𝒫 Value → 𝒫 Value) → 𝒫 Value
Run P F u = Σ[ Y ∈ List Value ] Y ≢ [] × (mem Y ⊆ P × u ∈ F (mem Y))

{- finitely many such elements are all in F on one finite part of P -}
gather : ∀ {P F} → MonoF F → ∀ V → mem V ⊆ Run P F → V ≢ [] → Σ[ Y ∈ List Value ] Y ≢ [] × (mem Y ⊆ P × mem V ⊆ F (mem Y))
gather mF [] h ne = ⊥-elim (ne refl)
gather mF (v ∷ []) h _ with h v (here refl)
... | ⟨ Y , ⟨ neY , ⟨ Y⊆ , v∈ ⟩ ⟩ ⟩ = ⟨ Y , ⟨ neY , ⟨ Y⊆ , (λ { _ (here refl) → v∈ }) ⟩ ⟩ ⟩
gather {P} mF (v ∷ v' ∷ V) h _ with h v (here refl) | gather mF (v' ∷ V) (λ u u∈ → h u (there u∈)) (λ ())
... | ⟨ [] , ⟨ neY , _ ⟩ ⟩ | _ = ⊥-elim (neY refl)
... | ⟨ y ∷ Y , ⟨ _ , ⟨ Y⊆ , v∈ ⟩ ⟩ ⟩ | ⟨ Y' , ⟨ _ , ⟨ Y'⊆ , V⊆ ⟩ ⟩ ⟩ =
  ⟨ y ∷ Y ++ Y' , ⟨ (λ ()) , ⟨ P⊆ , (λ { _ (here refl) → mF (λ _ → ∈-++⁺ˡ) _ v∈
                                       ; u (there u∈) → mF (λ _ → ∈-++⁺ʳ (y ∷ Y)) u (V⊆ u u∈) }) ⟩ ⟩ ⟩
  where
  P⊆ : mem (y ∷ Y ++ Y') ⊆ P
  P⊆ u u∈ with ∈-++⁻ (y ∷ Y) u∈
  ... | inj₁ i = Y⊆ u i
  ... | inj₂ i = Y'⊆ u i

{- ⋆ ⟨ Λ G , - ⟩ of such elements, for a consistent P: they come from F
   on one consistent finite part of P -}
join : ∀ {P F G w} → Con P → MonoF F → w ∈ ⋆ ⟨ Λ ⟨ G , ptt ⟩ , ⟨ Run P F , ptt ⟩ ⟩
  → Σ[ y ∈ Value ] Σ[ Y ∈ List Value ]
      mem (y ∷ Y) ⊆ P × (w ∈ ⋆ ⟨ Λ ⟨ G , ptt ⟩ , ⟨ F (mem (y ∷ Y)) , ptt ⟩ ⟩ × (y ∷ Y) ≈ (y ∷ Y))
join {P} cP mF ⟨ V , ⟨ w∈ , ⟨ V⊆ , neV ⟩ ⟩ ⟩ with gather mF V V⊆ neV
... | ⟨ [] , ⟨ neY , _ ⟩ ⟩ = ⊥-elim (neY refl)
... | ⟨ y ∷ Y , ⟨ _ , ⟨ Y⊆ , V⊆' ⟩ ⟩ ⟩ =
  ⟨ y , ⟨ Y , ⟨ Y⊆ , ⟨ ⟨ V , ⟨ w∈ , ⟨ V⊆' , neV ⟩ ⟩ ⟩ , Con⇒≈ (y ∷ Y) cP Y⊆ ⟩ ⟩ ⟩ ⟩

{- the meaning of the enclosing lets, given the value -}
K⟨_⟩ : Maybe (𝒫 Value → 𝒫 Value) → 𝒫 Value → 𝒫 Value
K⟨ nothing ⟩ D = D
K⟨ just G ⟩ D = ⋆ ⟨ Λ ⟨ G , ptt ⟩ , ⟨ D , ptt ⟩ ⟩

K-≃ : ∀ k {D D'} → D ≃ D' → K⟨ k ⟩ D ≃ K⟨ k ⟩ D'
K-≃ nothing eq = eq
K-≃ (just G) eq = ⋆-≃ {Λ ⟨ G , ptt ⟩} {Λ ⟨ G , ptt ⟩} ≃-refl eq

let-law : ∀ k {D F} → Con D → MonoF F
  → K⟨ k ⟩ (⋆ ⟨ Λ ⟨ F , ptt ⟩ , ⟨ D , ptt ⟩ ⟩) ≃ ⋆ ⟨ Λ ⟨ (λ X → K⟨ k ⟩ (F X)) , ptt ⟩ , ⟨ D , ptt ⟩ ⟩
let-law nothing cD mF = ≃-refl
let-law (just G) {D} {F} cD mF = ⟨ L , R ⟩
  where
  L : K⟨ just G ⟩ (⋆ ⟨ Λ ⟨ F , ptt ⟩ , ⟨ D , ptt ⟩ ⟩) ⊆ ⋆ ⟨ Λ ⟨ (λ X → K⟨ just G ⟩ (F X)) , ptt ⟩ , ⟨ D , ptt ⟩ ⟩
  L w ⟨ V , ⟨ w∈ , ⟨ V⊆ , neV ⟩ ⟩ ⟩ with join {D} {F} {G} cD mF ⟨ V , ⟨ w∈ , ⟨ (λ u u∈ → run (V⊆ u u∈)) , neV ⟩ ⟩ ⟩
    where
    run : ∀ {u} → u ∈ ⋆ ⟨ Λ ⟨ F , ptt ⟩ , ⟨ D , ptt ⟩ ⟩ → u ∈ Run D F
    run ⟨ Y , ⟨ ⟨ u∈ , ⟨ neY , _ ⟩ ⟩ , ⟨ Y⊆ , _ ⟩ ⟩ ⟩ = ⟨ Y , ⟨ neY , ⟨ Y⊆ , u∈ ⟩ ⟩ ⟩
  ... | ⟨ y , ⟨ Y , ⟨ Y⊆ , ⟨ w∈' , cY ⟩ ⟩ ⟩ ⟩ = ⟨ y ∷ Y , ⟨ ⟨ w∈' , ⟨ (λ ()) , cY ⟩ ⟩ , ⟨ Y⊆ , (λ ()) ⟩ ⟩ ⟩
  R : ⋆ ⟨ Λ ⟨ (λ X → K⟨ just G ⟩ (F X)) , ptt ⟩ , ⟨ D , ptt ⟩ ⟩ ⊆ K⟨ just G ⟩ (⋆ ⟨ Λ ⟨ F , ptt ⟩ , ⟨ D , ptt ⟩ ⟩)
  R w ⟨ Y , ⟨ ⟨ ⟨ V , ⟨ w∈ , ⟨ V⊆ , neV ⟩ ⟩ ⟩ , ⟨ neY , cY ⟩ ⟩ , ⟨ Y⊆ , _ ⟩ ⟩ ⟩ =
    ⟨ V , ⟨ w∈ , ⟨ (λ u u∈ → ⟨ Y , ⟨ ⟨ V⊆ u u∈ , ⟨ neY , cY ⟩ ⟩ , ⟨ Y⊆ , neY ⟩ ⟩ ⟩) , neV ⟩ ⟩ ⟩

case-law : ∀ k {A F₁ F₂} → Con A → MonoF F₁ → MonoF F₂
  → K⟨ k ⟩ (𝒞 ⟨ A , ⟨ F₁ , ⟨ F₂ , ptt ⟩ ⟩ ⟩) ≃ 𝒞 ⟨ A , ⟨ (λ X → K⟨ k ⟩ (F₁ X)) , ⟨ (λ X → K⟨ k ⟩ (F₂ X)) , ptt ⟩ ⟩ ⟩
case-law nothing cA m₁ m₂ = ≃-refl
case-law (just G) {A} {F₁} {F₂} cA m₁ m₂ = ⟨ L , R ⟩
  where
  L : K⟨ just G ⟩ (𝒞 ⟨ A , ⟨ F₁ , ⟨ F₂ , ptt ⟩ ⟩ ⟩) ⊆ 𝒞 ⟨ A , ⟨ (λ X → K⟨ just G ⟩ (F₁ X)) , ⟨ (λ X → K⟨ just G ⟩ (F₂ X)) , ptt ⟩ ⟩ ⟩
  L w ⟨ [] , ⟨ _ , ⟨ _ , neV ⟩ ⟩ ⟩ = ⊥-elim (neV refl)
  L w ⟨ u₀ ∷ V , ⟨ w∈ , ⟨ V⊆ , neV ⟩ ⟩ ⟩ with V⊆ u₀ (here refl)
  ... | inj₁ ⟨ v₀ , ⟨ _ , ⟨ all₀ , _ ⟩ ⟩ ⟩ =
    inj₁ (join {F = F₁} {G} (λ a b → cA _ _) m₁ ⟨ u₀ ∷ V , ⟨ w∈ , ⟨ lefts , neV ⟩ ⟩ ⟩)
    where
    lefts : mem (u₀ ∷ V) ⊆ Run (λ d → left d ∈ A) F₁
    lefts u u∈ with V⊆ u u∈
    ... | inj₁ ⟨ v , ⟨ V' , ⟨ all , ⟨ u∈' , _ ⟩ ⟩ ⟩ ⟩ = ⟨ v ∷ V' , ⟨ (λ ()) , ⟨ all , u∈' ⟩ ⟩ ⟩
    ... | inj₂ ⟨ v , ⟨ V' , ⟨ all , _ ⟩ ⟩ ⟩ = ⊥-elim (cA _ _ (all₀ v₀ (here refl)) (all v (here refl)))
  ... | inj₂ ⟨ v₀ , ⟨ _ , ⟨ all₀ , _ ⟩ ⟩ ⟩ =
    inj₂ (join {F = F₂} {G} (λ a b → cA _ _) m₂ ⟨ u₀ ∷ V , ⟨ w∈ , ⟨ rights , neV ⟩ ⟩ ⟩)
    where
    rights : mem (u₀ ∷ V) ⊆ Run (λ d → right d ∈ A) F₂
    rights u u∈ with V⊆ u u∈
    ... | inj₂ ⟨ v , ⟨ V' , ⟨ all , ⟨ u∈' , _ ⟩ ⟩ ⟩ ⟩ = ⟨ v ∷ V' , ⟨ (λ ()) , ⟨ all , u∈' ⟩ ⟩ ⟩
    ... | inj₁ ⟨ v , ⟨ V' , ⟨ all , _ ⟩ ⟩ ⟩ = ⊥-elim (cA _ _ (all₀ v₀ (here refl)) (all v (here refl)))
  R : 𝒞 ⟨ A , ⟨ (λ X → K⟨ just G ⟩ (F₁ X)) , ⟨ (λ X → K⟨ just G ⟩ (F₂ X)) , ptt ⟩ ⟩ ⟩ ⊆ K⟨ just G ⟩ (𝒞 ⟨ A , ⟨ F₁ , ⟨ F₂ , ptt ⟩ ⟩ ⟩)
  R w (inj₁ ⟨ v , ⟨ V' , ⟨ all , ⟨ ⟨ V , ⟨ w∈ , ⟨ V⊆ , neV ⟩ ⟩ ⟩ , c ⟩ ⟩ ⟩ ⟩) =
    ⟨ V , ⟨ w∈ , ⟨ (λ u u∈ → inj₁ ⟨ v , ⟨ V' , ⟨ all , ⟨ V⊆ u u∈ , c ⟩ ⟩ ⟩ ⟩) , neV ⟩ ⟩ ⟩
  R w (inj₂ ⟨ v , ⟨ V' , ⟨ all , ⟨ ⟨ V , ⟨ w∈ , ⟨ V⊆ , neV ⟩ ⟩ ⟩ , c ⟩ ⟩ ⟩ ⟩) =
    ⟨ V , ⟨ w∈ , ⟨ (λ u u∈ → inj₂ ⟨ v , ⟨ V' , ⟨ all , ⟨ V⊆ u u∈ , c ⟩ ⟩ ⟩ ⟩) , neV ⟩ ⟩ ⟩

{- Strictness ---------------------------------------------------------------------------}

{- strict D X is X when each element of X needs D to be nonempty -}
strict-≃ : ∀ {D X X'} → X ≃ X' → (∀ w → w ∈ X → nonempty D) → strict D X ≃ X'
strict-≃ ⟨ X⊆ , X⊇ ⟩ ne = ⟨ (λ w p → X⊆ w (proj₂ p)) , (λ w p → ⟨ ne w (X⊇ w p) , X⊇ w p ⟩) ⟩

strict-≃₂ : ∀ {D₁ D₂ X X'} → X ≃ X' → (∀ w → w ∈ X → nonempty D₂) → (nonempty D₂ → nonempty D₁)
  → strict D₁ (strict D₂ X) ≃ X'
strict-≃₂ X≃ ne f = strict-≃ (strict-≃ X≃ ne) (λ w w∈ → f (proj₁ w∈))

strict-≃₃ : ∀ {D₁ D₂ D₃ X X'} → X ≃ X' → (∀ w → w ∈ X → nonempty D₃) → (nonempty D₃ → nonempty D₂)
  → (nonempty D₃ → nonempty D₁) → strict D₁ (strict D₂ (strict D₃ X)) ≃ X'
strict-≃₃ X≃ ne f₂ f₁ = strict-≃ (strict-≃₂ X≃ ne f₂) (λ w w∈ → f₁ (proj₁ (proj₂ w∈)))

⋆-ne : ∀ {D E} → nonempty (⋆ ⟨ D , ⟨ E , ptt ⟩ ⟩) → nonempty D × nonempty E
⋆-ne ⟨ w , ⟨ V , ⟨ e∈ , ⟨ V⊆ , ne ⟩ ⟩ ⟩ ⟩ = ⟨ ⟨ _ , e∈ ⟩ , ne-mem ne V⊆ ⟩

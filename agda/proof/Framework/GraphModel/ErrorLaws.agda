{-

  Laws of the binders of the error-propagating operators: congruences
  from equal operands (𝒞ᵉ-RR, letᵉ-RR, ΛΛᵉ-≃), and how a let or a case
  commutes with a continuation (let-law, case-law), used by lift locals.

-}

open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.DOpSig using (Results; RRs; RRs-refl)
open import proof.Framework.GraphModel.Domain
open import proof.Framework.GraphModel.OpsBase using (nthD-≃)
open import proof.Framework.GraphModel.ErrorOps
open import proof.Framework.GraphModel.Env using (Env)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _⊔_; _<_; _≤_; _≟_; _<?_; s≤s)
open import Data.Nat.Properties
open import Data.List using (List; []; _∷_; _++_; length; replicate)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Product using (_×_; Σ-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Data.Unit using (tt)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Level using (lower) renaming (lift to up)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; subst)
open import Relation.Nullary using (yes; no)
open import Framework.abt.Sig using (Sig; ■; ν; ∁)

module proof.Framework.GraphModel.ErrorLaws where

{- congruences of the binders, from equal operands -}

𝒞ᵉ-RR : ∀ {D F G D' F' G'} → RRs (■ ∷ ν ■ ∷ ν ■ ∷ []) ⟨ D , ⟨ F , ⟨ G , ptt ⟩ ⟩ ⟩ ⟨ D' , ⟨ F' , ⟨ G' , ptt ⟩ ⟩ ⟩
  → 𝒞ᵉ ⟨ D , ⟨ F , ⟨ G , ptt ⟩ ⟩ ⟩ ≃ 𝒞ᵉ ⟨ D' , ⟨ F' , ⟨ G' , ptt ⟩ ⟩ ⟩
𝒞ᵉ-RR {F = F} {G} {F' = F'} {G'} ⟨ D≃ , ⟨ F≃ , ⟨ G≃ , _ ⟩ ⟩ ⟩ =
  𝒞ᵉ-≃ {F = F} {F'} {G} {G'} (lower D≃) (λ _ _ _ _ → lower (F≃ _ _ ≃-refl)) (λ _ _ _ _ → lower (G≃ _ _ ≃-refl))

letᵉ-RR : ∀ {D F D' F'} → RRs (■ ∷ ν ■ ∷ []) ⟨ D , ⟨ F , ptt ⟩ ⟩ ⟨ D' , ⟨ F' , ptt ⟩ ⟩
  → letᵉ ⟨ D , ⟨ F , ptt ⟩ ⟩ ≃ letᵉ ⟨ D' , ⟨ F' , ptt ⟩ ⟩
letᵉ-RR {F = F} {F' = F'} ⟨ D≃ , ⟨ F≃ , _ ⟩ ⟩ = letᵉ-≃ {F = F} {F'} (lower D≃) (λ _ _ _ _ → lower (F≃ _ _ ≃-refl))

ΛΛᵉ-≃ : ∀ {F F' : 𝒫 Value → 𝒫 Value → 𝒫 Value} → (∀ X Y → F X Y ≃ F' X Y)
  → ΛΛᵉ ⟨ F , ptt ⟩ ≃ ΛΛᵉ ⟨ F' , ptt ⟩
ΛΛᵉ-≃ eq = Λᵉ-≃ (λ V _ _ _ → Λᵉ-≃ (λ U _ _ _ → eq (mem V) (mem U)))

{- commuting with let and case -}

MonoF : (𝒫 Value → 𝒫 Value) → Set₁
MonoF F = ∀ {X X'} → X ⊆ X' → F X ⊆ F X'

{- u is in F on a finite, nonempty part of P without ω -}
Run : 𝒫 Value → (𝒫 Value → 𝒫 Value) → 𝒫 Value
Run P F u = Σ[ Y ∈ List Value ] Y ≢ [] × NoErr Y × (mem Y ⊆ P × u ∈ F (mem Y))

NoErr-++ : ∀ Y Y' → NoErr Y → NoErr Y' → NoErr (Y ++ Y')
NoErr-++ Y Y' n n' ω∈ with ∈-++⁻ Y ω∈
... | inj₁ i = n i
... | inj₂ i = n' i

{- finitely many such elements are all in F on one finite part of P -}
gather : ∀ {P F} → MonoF F → ∀ V → mem V ⊆ Run P F → V ≢ []
  → Σ[ Y ∈ List Value ] Y ≢ [] × NoErr Y × (mem Y ⊆ P × mem V ⊆ F (mem Y))
gather mF [] h ne = ⊥-elim (ne refl)
gather mF (v ∷ []) h _ with h v (here refl)
... | ⟨ Y , ⟨ neY , ⟨ nY , ⟨ Y⊆ , v∈ ⟩ ⟩ ⟩ ⟩ = ⟨ Y , ⟨ neY , ⟨ nY , ⟨ Y⊆ , (λ { _ (here refl) → v∈ }) ⟩ ⟩ ⟩ ⟩
gather {P} mF (v ∷ v' ∷ V) h _ with h v (here refl) | gather mF (v' ∷ V) (λ u u∈ → h u (there u∈)) (λ ())
... | ⟨ [] , ⟨ neY , _ ⟩ ⟩ | _ = ⊥-elim (neY refl)
... | ⟨ y ∷ Y , ⟨ _ , ⟨ nY , ⟨ Y⊆ , v∈ ⟩ ⟩ ⟩ ⟩ | ⟨ Y' , ⟨ _ , ⟨ nY' , ⟨ Y'⊆ , V⊆ ⟩ ⟩ ⟩ ⟩ =
  ⟨ y ∷ Y ++ Y' , ⟨ (λ ()) , ⟨ NoErr-++ (y ∷ Y) Y' nY nY'
  , ⟨ P⊆ , (λ { _ (here refl) → mF (λ _ → ∈-++⁺ˡ) _ v∈
              ; u (there u∈) → mF (λ _ → ∈-++⁺ʳ (y ∷ Y)) u (V⊆ u u∈) }) ⟩ ⟩ ⟩ ⟩
  where
  P⊆ : mem (y ∷ Y ++ Y') ⊆ P
  P⊆ u u∈ with ∈-++⁻ (y ∷ Y) u∈
  ... | inj₁ i = Y⊆ u i
  ... | inj₂ i = Y'⊆ u i

{- letᵉ ⟨ -, G ⟩ of such elements, for a consistent P: they come from F
   on one consistent finite part of P without ω -}
join : ∀ {P F G w} → Con P → MonoF F
  → (Σ[ V ∈ List Value ] (V ↦ w ∈ Λᵉ ⟨ G , ptt ⟩) × mem V ⊆ Run P F × V ≢ [] × NoErr V)
  → Σ[ y ∈ Value ] Σ[ Y ∈ List Value ]
      mem (y ∷ Y) ⊆ P × (w ∈ letᵉ ⟨ F (mem (y ∷ Y)) , ⟨ G , ptt ⟩ ⟩ × (y ∷ Y) ≈ (y ∷ Y) × NoErr (y ∷ Y))
join {P} cP mF ⟨ V , ⟨ w∈ , ⟨ V⊆ , ⟨ neV , nV ⟩ ⟩ ⟩ ⟩ with gather mF V V⊆ neV
... | ⟨ [] , ⟨ neY , _ ⟩ ⟩ = ⊥-elim (neY refl)
... | ⟨ y ∷ Y , ⟨ _ , ⟨ nY , ⟨ Y⊆ , V⊆' ⟩ ⟩ ⟩ ⟩ =
  ⟨ y , ⟨ Y , ⟨ Y⊆ , ⟨ inj₁ ⟨ V , ⟨ w∈ , ⟨ V⊆' , ⟨ neV , nV ⟩ ⟩ ⟩ ⟩ , ⟨ Con⇒≈ (y ∷ Y) cP Y⊆ , nY ⟩ ⟩ ⟩ ⟩ ⟩

{- the meaning of the enclosing lets, given the value -}
K⟨_⟩ : Maybe (𝒫 Value → 𝒫 Value) → 𝒫 Value → 𝒫 Value
K⟨ nothing ⟩ D = D
K⟨ just G ⟩ D = letᵉ ⟨ D , ⟨ G , ptt ⟩ ⟩

K-≃ : ∀ k {D D'} → D ≃ D' → K⟨ k ⟩ D ≃ K⟨ k ⟩ D'
K-≃ nothing eq = eq
K-≃ (just G) eq = ⋆ᵉ-≃ {Λᵉ ⟨ G , ptt ⟩} {Λᵉ ⟨ G , ptt ⟩} ≃-refl eq

{- an error of the operand of a let -}
let-err : ∀ {D G} → ω ∈ D → ω ∈ letᵉ ⟨ D , ⟨ G , ptt ⟩ ⟩
let-err ω∈ = inj₂ ⟨ refl , inj₂ (inj₂ ⟨ ⟨ ν , ⟨ tt , tt ⟩ ⟩ , ω∈ ⟩) ⟩

let-law : ∀ k {D F} → Con D → MonoF F
  → K⟨ k ⟩ (letᵉ ⟨ D , ⟨ F , ptt ⟩ ⟩) ≃ letᵉ ⟨ D , ⟨ (λ X → K⟨ k ⟩ (F X)) , ptt ⟩ ⟩
let-law nothing cD mF = ≃-refl
let-law (just G) {D} {F} cD mF = ⟨ L , R ⟩
  where
  run : ∀ {u} → u ∈ letᵉ ⟨ D , ⟨ F , ptt ⟩ ⟩ → u ≢ ω → u ∈ Run D F
  run (inj₁ ⟨ Y , ⟨ ⟨ u∈ , ⟨ neY , ⟨ _ , nY ⟩ ⟩ ⟩ , ⟨ Y⊆ , _ ⟩ ⟩ ⟩) _ = ⟨ Y , ⟨ neY , ⟨ nY , ⟨ Y⊆ , u∈ ⟩ ⟩ ⟩ ⟩
  run (inj₂ ⟨ refl , _ ⟩) u≢ = ⊥-elim (u≢ refl)
  L : K⟨ just G ⟩ (letᵉ ⟨ D , ⟨ F , ptt ⟩ ⟩) ⊆ letᵉ ⟨ D , ⟨ (λ X → K⟨ just G ⟩ (F X)) , ptt ⟩ ⟩
  L w (inj₁ ⟨ V , ⟨ w∈ , ⟨ V⊆ , ⟨ neV , nV ⟩ ⟩ ⟩ ⟩)
      with join {D} {F} {G} cD mF ⟨ V , ⟨ w∈ , ⟨ (λ u u∈ → run (V⊆ u u∈) (λ { refl → nV u∈ })) , ⟨ neV , nV ⟩ ⟩ ⟩ ⟩
  ... | ⟨ y , ⟨ Y , ⟨ Y⊆ , ⟨ w∈' , ⟨ cY , nY ⟩ ⟩ ⟩ ⟩ ⟩ =
    inj₁ ⟨ y ∷ Y , ⟨ ⟨ w∈' , ⟨ (λ ()) , ⟨ cY , nY ⟩ ⟩ ⟩ , ⟨ Y⊆ , ⟨ (λ ()) , nY ⟩ ⟩ ⟩ ⟩
  L w (inj₂ ⟨ refl , inj₁ () ⟩)
  L w (inj₂ ⟨ refl , inj₂ (inj₁ ⟨ d , ⟨ d∈ , ⟨ _ , nf ⟩ ⟩ ⟩) ⟩) = ⊥-elim (nf (Λᵉ-fun d d∈))
  L w (inj₂ ⟨ refl , inj₂ (inj₂ ⟨ _ , inj₂ ⟨ refl , inj₂ (inj₂ ⟨ _ , ω∈D ⟩) ⟩ ⟩) ⟩) = let-err ω∈D
  L w (inj₂ ⟨ refl , inj₂ (inj₂ ⟨ _ , inj₂ ⟨ refl , inj₁ () ⟩ ⟩) ⟩)
  L w (inj₂ ⟨ refl , inj₂ (inj₂ ⟨ _ , inj₂ ⟨ refl , inj₂ (inj₁ ⟨ d , ⟨ d∈ , ⟨ _ , nf ⟩ ⟩ ⟩) ⟩ ⟩) ⟩) =
    ⊥-elim (nf (Λᵉ-fun d d∈))
  L w (inj₂ ⟨ refl , inj₂ (inj₂ ⟨ _ , inj₁ ⟨ Y , ⟨ ⟨ ω∈F , ⟨ neY , ⟨ cY , nY ⟩ ⟩ ⟩ , ⟨ Y⊆ , _ ⟩ ⟩ ⟩ ⟩) ⟩) =
    inj₁ ⟨ Y , ⟨ ⟨ let-err ω∈F , ⟨ neY , ⟨ cY , nY ⟩ ⟩ ⟩ , ⟨ Y⊆ , ⟨ neY , nY ⟩ ⟩ ⟩ ⟩
  R : letᵉ ⟨ D , ⟨ (λ X → K⟨ just G ⟩ (F X)) , ptt ⟩ ⟩ ⊆ K⟨ just G ⟩ (letᵉ ⟨ D , ⟨ F , ptt ⟩ ⟩)
  R w (inj₁ ⟨ Y , ⟨ ⟨ inj₁ ⟨ V , ⟨ w∈ , ⟨ V⊆ , neVn ⟩ ⟩ ⟩ , ⟨ neY , ⟨ cY , nY ⟩ ⟩ ⟩ , ⟨ Y⊆ , _ ⟩ ⟩ ⟩) =
    inj₁ ⟨ V , ⟨ w∈ , ⟨ (λ u u∈ → inj₁ ⟨ Y , ⟨ ⟨ V⊆ u u∈ , ⟨ neY , ⟨ cY , nY ⟩ ⟩ ⟩ , ⟨ Y⊆ , ⟨ neY , nY ⟩ ⟩ ⟩ ⟩) , neVn ⟩ ⟩ ⟩
  R w (inj₁ ⟨ Y , ⟨ ⟨ inj₂ ⟨ refl , inj₁ () ⟩ , _ ⟩ , _ ⟩ ⟩)
  R w (inj₁ ⟨ Y , ⟨ ⟨ inj₂ ⟨ refl , inj₂ (inj₁ ⟨ d , ⟨ d∈ , ⟨ _ , nf ⟩ ⟩ ⟩) ⟩ , _ ⟩ , _ ⟩ ⟩) = ⊥-elim (nf (Λᵉ-fun d d∈))
  R w (inj₁ ⟨ Y , ⟨ ⟨ inj₂ ⟨ refl , inj₂ (inj₂ ⟨ _ , ω∈F ⟩) ⟩ , ⟨ neY , ⟨ cY , nY ⟩ ⟩ ⟩ , ⟨ Y⊆ , _ ⟩ ⟩ ⟩) =
    let-err (inj₁ ⟨ Y , ⟨ ⟨ ω∈F , ⟨ neY , ⟨ cY , nY ⟩ ⟩ ⟩ , ⟨ Y⊆ , ⟨ neY , nY ⟩ ⟩ ⟩ ⟩)
  R w (inj₂ ⟨ refl , inj₁ () ⟩)
  R w (inj₂ ⟨ refl , inj₂ (inj₁ ⟨ d , ⟨ d∈ , ⟨ _ , nf ⟩ ⟩ ⟩) ⟩) = ⊥-elim (nf (Λᵉ-fun d d∈))
  R w (inj₂ ⟨ refl , inj₂ (inj₂ ⟨ _ , ω∈D ⟩) ⟩) = let-err (let-err ω∈D)

case-law : ∀ k {A F₁ F₂} → Con A → MonoF F₁ → MonoF F₂
  → K⟨ k ⟩ (𝒞ᵉ ⟨ A , ⟨ F₁ , ⟨ F₂ , ptt ⟩ ⟩ ⟩) ≃ 𝒞ᵉ ⟨ A , ⟨ (λ X → K⟨ k ⟩ (F₁ X)) , ⟨ (λ X → K⟨ k ⟩ (F₂ X)) , ptt ⟩ ⟩ ⟩
case-law nothing cA m₁ m₂ = ≃-refl
case-law (just G) {A} {F₁} {F₂} cA m₁ m₂ = ⟨ L , R ⟩
  where
  C = 𝒞ᵉ ⟨ A , ⟨ F₁ , ⟨ F₂ , ptt ⟩ ⟩ ⟩
  C' = 𝒞ᵉ ⟨ A , ⟨ (λ X → K⟨ just G ⟩ (F₁ X)) , ⟨ (λ X → K⟨ just G ⟩ (F₂ X)) , ptt ⟩ ⟩ ⟩
  L : K⟨ just G ⟩ C ⊆ C'
  L w (inj₁ ⟨ [] , ⟨ _ , ⟨ _ , ⟨ neV , _ ⟩ ⟩ ⟩ ⟩) = ⊥-elim (neV refl)
  L w (inj₁ ⟨ u₀ ∷ V , ⟨ w∈ , ⟨ V⊆ , ⟨ neV , nV ⟩ ⟩ ⟩ ⟩) with V⊆ u₀ (here refl)
  ... | inj₂ (inj₂ ⟨ refl , _ ⟩) = ⊥-elim (nV (here refl))
  ... | inj₁ ⟨ v₀ , ⟨ _ , ⟨ all₀ , _ ⟩ ⟩ ⟩ with join {F = F₁} {G} (λ a b → cA _ _) m₁ ⟨ u₀ ∷ V , ⟨ w∈ , ⟨ lefts , ⟨ neV , nV ⟩ ⟩ ⟩ ⟩
    where
    lefts : mem (u₀ ∷ V) ⊆ Run (λ d → left d ∈ A) F₁
    lefts u u∈ with V⊆ u u∈
    ... | inj₁ ⟨ v , ⟨ V' , ⟨ all , ⟨ u∈' , ⟨ _ , n ⟩ ⟩ ⟩ ⟩ ⟩ = ⟨ v ∷ V' , ⟨ (λ ()) , ⟨ n , ⟨ all , u∈' ⟩ ⟩ ⟩ ⟩
    ... | inj₂ (inj₁ ⟨ v , ⟨ V' , ⟨ all , _ ⟩ ⟩ ⟩) = ⊥-elim (cA _ _ (all₀ v₀ (here refl)) (all v (here refl)))
    ... | inj₂ (inj₂ ⟨ refl , _ ⟩) = ⊥-elim (nV u∈)
  ... | ⟨ y , ⟨ Y , ⟨ Y⊆ , ⟨ w∈' , ⟨ cY , nY ⟩ ⟩ ⟩ ⟩ ⟩ = inj₁ ⟨ y , ⟨ Y , ⟨ Y⊆ , ⟨ w∈' , ⟨ cY , nY ⟩ ⟩ ⟩ ⟩ ⟩
  L w (inj₁ ⟨ u₀ ∷ V , ⟨ w∈ , ⟨ V⊆ , ⟨ neV , nV ⟩ ⟩ ⟩ ⟩) | inj₂ (inj₁ ⟨ v₀ , ⟨ _ , ⟨ all₀ , _ ⟩ ⟩ ⟩)
      with join {F = F₂} {G} (λ a b → cA _ _) m₂ ⟨ u₀ ∷ V , ⟨ w∈ , ⟨ rights , ⟨ neV , nV ⟩ ⟩ ⟩ ⟩
    where
    rights : mem (u₀ ∷ V) ⊆ Run (λ d → right d ∈ A) F₂
    rights u u∈ with V⊆ u u∈
    ... | inj₂ (inj₁ ⟨ v , ⟨ V' , ⟨ all , ⟨ u∈' , ⟨ _ , n ⟩ ⟩ ⟩ ⟩ ⟩) = ⟨ v ∷ V' , ⟨ (λ ()) , ⟨ n , ⟨ all , u∈' ⟩ ⟩ ⟩ ⟩
    ... | inj₁ ⟨ v , ⟨ V' , ⟨ all , _ ⟩ ⟩ ⟩ = ⊥-elim (cA _ _ (all₀ v₀ (here refl)) (all v (here refl)))
    ... | inj₂ (inj₂ ⟨ refl , _ ⟩) = ⊥-elim (nV u∈)
  ... | ⟨ y , ⟨ Y , ⟨ Y⊆ , ⟨ w∈' , ⟨ cY , nY ⟩ ⟩ ⟩ ⟩ ⟩ = inj₂ (inj₁ ⟨ y , ⟨ Y , ⟨ Y⊆ , ⟨ w∈' , ⟨ cY , nY ⟩ ⟩ ⟩ ⟩ ⟩)
  L w (inj₂ ⟨ refl , inj₁ () ⟩)
  L w (inj₂ ⟨ refl , inj₂ (inj₁ ⟨ d , ⟨ d∈ , ⟨ _ , nf ⟩ ⟩ ⟩) ⟩) = ⊥-elim (nf (Λᵉ-fun d d∈))
  L w (inj₂ ⟨ refl , inj₂ (inj₂ ⟨ _ , inj₁ ⟨ v , ⟨ V , ⟨ all , ⟨ ω∈ , cn ⟩ ⟩ ⟩ ⟩ ⟩) ⟩) =
    inj₁ ⟨ v , ⟨ V , ⟨ all , ⟨ let-err ω∈ , cn ⟩ ⟩ ⟩ ⟩
  L w (inj₂ ⟨ refl , inj₂ (inj₂ ⟨ _ , inj₂ (inj₁ ⟨ v , ⟨ V , ⟨ all , ⟨ ω∈ , cn ⟩ ⟩ ⟩ ⟩) ⟩) ⟩) =
    inj₂ (inj₁ ⟨ v , ⟨ V , ⟨ all , ⟨ let-err ω∈ , cn ⟩ ⟩ ⟩ ⟩)
  L w (inj₂ ⟨ refl , inj₂ (inj₂ ⟨ _ , inj₂ (inj₂ ⟨ refl , e ⟩) ⟩) ⟩) = inj₂ (inj₂ ⟨ refl , e ⟩)
  R : C' ⊆ K⟨ just G ⟩ C
  R w (inj₁ ⟨ v , ⟨ V' , ⟨ all , ⟨ inj₁ ⟨ V , ⟨ w∈ , ⟨ V⊆ , neVn ⟩ ⟩ ⟩ , c ⟩ ⟩ ⟩ ⟩) =
    inj₁ ⟨ V , ⟨ w∈ , ⟨ (λ u u∈ → inj₁ ⟨ v , ⟨ V' , ⟨ all , ⟨ V⊆ u u∈ , c ⟩ ⟩ ⟩ ⟩) , neVn ⟩ ⟩ ⟩
  R w (inj₁ ⟨ v , ⟨ V' , ⟨ all , ⟨ inj₂ ⟨ refl , inj₁ () ⟩ , c ⟩ ⟩ ⟩ ⟩)
  R w (inj₁ ⟨ v , ⟨ V' , ⟨ all , ⟨ inj₂ ⟨ refl , inj₂ (inj₁ ⟨ d , ⟨ d∈ , ⟨ _ , nf ⟩ ⟩ ⟩) ⟩ , c ⟩ ⟩ ⟩ ⟩) =
    ⊥-elim (nf (Λᵉ-fun d d∈))
  R w (inj₁ ⟨ v , ⟨ V' , ⟨ all , ⟨ inj₂ ⟨ refl , inj₂ (inj₂ ⟨ _ , ω∈ ⟩) ⟩ , c ⟩ ⟩ ⟩ ⟩) =
    let-err (inj₁ ⟨ v , ⟨ V' , ⟨ all , ⟨ ω∈ , c ⟩ ⟩ ⟩ ⟩)
  R w (inj₂ (inj₁ ⟨ v , ⟨ V' , ⟨ all , ⟨ inj₁ ⟨ V , ⟨ w∈ , ⟨ V⊆ , neVn ⟩ ⟩ ⟩ , c ⟩ ⟩ ⟩ ⟩)) =
    inj₁ ⟨ V , ⟨ w∈ , ⟨ (λ u u∈ → inj₂ (inj₁ ⟨ v , ⟨ V' , ⟨ all , ⟨ V⊆ u u∈ , c ⟩ ⟩ ⟩ ⟩)) , neVn ⟩ ⟩ ⟩
  R w (inj₂ (inj₁ ⟨ v , ⟨ V' , ⟨ all , ⟨ inj₂ ⟨ refl , inj₁ () ⟩ , c ⟩ ⟩ ⟩ ⟩))
  R w (inj₂ (inj₁ ⟨ v , ⟨ V' , ⟨ all , ⟨ inj₂ ⟨ refl , inj₂ (inj₁ ⟨ d , ⟨ d∈ , ⟨ _ , nf ⟩ ⟩ ⟩) ⟩ , c ⟩ ⟩ ⟩ ⟩)) =
    ⊥-elim (nf (Λᵉ-fun d d∈))
  R w (inj₂ (inj₁ ⟨ v , ⟨ V' , ⟨ all , ⟨ inj₂ ⟨ refl , inj₂ (inj₂ ⟨ _ , ω∈ ⟩) ⟩ , c ⟩ ⟩ ⟩ ⟩)) =
    let-err (inj₂ (inj₁ ⟨ v , ⟨ V' , ⟨ all , ⟨ ω∈ , c ⟩ ⟩ ⟩ ⟩))
  R w (inj₂ (inj₂ ⟨ refl , e ⟩)) = let-err (inj₂ (inj₂ ⟨ refl , e ⟩))

{- The pass preserves meanings ----------------------------------------------------}


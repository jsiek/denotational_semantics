{-# OPTIONS --allow-unsolved-metas #-}

module Model.Filter.OperationISWIM where

{-

  This is an adaptation of the call-by-name models P(ω) of Scott
  (1976) and Dₐ of Engeler (1981) to call-by-value.

-}

open import Primitives
open import Utilities using (extensionality)
open import SetsAsPredicates
open import Var
open import ScopedTuple hiding (𝒫)
open import Syntax using (Sig; ext; ν; ■; Var; _•_; ↑; id; _⨟_) public
open import NewSigUtil
open import NewDOpSig
open import NewDenotProperties
open import Model.Filter.DomainISWIM renaming (consistent to consistency)

open import Data.Empty using (⊥-elim) renaming (⊥ to False)
open import Data.List using (List ; _∷_ ; []; _++_; length; replicate)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Relation.Unary.All 
  using (All; []; _∷_; head; tail; lookup; tabulate; all?)
  renaming (map to allmap)
open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_)
open import Data.List.Properties using (++-conicalˡ)
open import Data.List.Membership.Propositional renaming (_∈_ to _⋵_)
open import Data.List.Membership.Propositional.Properties
  using (∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.Nat using (ℕ; zero; suc; _≟_; _<_; z≤n; s≤s; _+_)
open import Data.Nat.Properties using (≤-pred)
open import Data.Product using (_×_; Σ; Σ-syntax; proj₁; proj₂; ∃; ∃-syntax)
    renaming (_,_ to ⟨_,_⟩)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Unit using (tt) renaming (⊤ to True)
open import Data.Unit.Polymorphic using (⊤) renaming (tt to ptt)
open import Relation.Binary.PropositionalEquality
    using (_≡_; _≢_; refl; sym; trans; subst)
open import Level using (Level; Lift; lift; lower)
    renaming (zero to lzero; suc to lsuc)
open import Relation.Nullary using (¬_; Dec; yes; no)


{- Denotational Operators -----------------------------------------------------}

{-
_⋆_  Λ  cons  car  cdr  ℒ  ℛ  𝒞  (proj i)  (𝒯' n)  (𝒯 n)  Λ'  Λ′
-}


{- \st -}
⋆ : DOp (𝒫 Value) (■ ∷ ■ ∷ [])
⋆ ⟨ D₁ , ⟨ D₂ , _ ⟩ ⟩ w = 
    Σ[ V ∈ Value ] (V ↦ w) ∈ D₁ × V ∈ D₂ 

ℬ : (B : Base) → base-rep B → DOp (𝒫 Value) []
ℬ B k _ (const {B′} k′)
    with base-eq? B B′
... | yes refl = k ≡ k′
... | no neq = False
ℬ B k _ (u ⊔ v) = ℬ B k ptt u × ℬ B k ptt v
ℬ B k _ d = False

𝓅 : (P : Prim) → rep P → DOp (𝒫 Value) []
𝓅 (base B) k v = ℬ B k v
𝓅 (B ⇒ P) f _ ν = True
𝓅 (B ⇒ P) f _ (const {B'} k ↦ w) with base-eq? B B'
... | yes refl = w ∈ 𝓅 P (f k) ptt
... | no neq = False
𝓅 (B ⇒ P) f _ (u ⊔ v) = 𝓅 (B ⇒ P) f ptt u × 𝓅 (B ⇒ P) f ptt v
𝓅 (B ⇒ P) f _ d = False

pair : DOp (𝒫 Value) (■ ∷ ■ ∷ [])
pair ⟨ D₁ , ⟨ D₂ , _ ⟩ ⟩ ⦅ f , FV ⦆ = f ∈ D₁ × FV ∈ D₂
pair ⟨ D₁ , ⟨ D₂ , _ ⟩ ⟩ (u ⊔ v) = pair ⟨ D₁ , ⟨ D₂ , ptt ⟩ ⟩ u × pair ⟨ D₁ , ⟨ D₂ , ptt ⟩ ⟩ v
pair ⟨ D₁ , ⟨ D₂ , _ ⟩ ⟩ _ = False

car : DOp (𝒫 Value) (■ ∷ [])
car ⟨ D , _ ⟩ f = Σ[ FV ∈ Value ] ⦅ f , FV ⦆ ∈ D

cdr : DOp (𝒫 Value) (■ ∷ [])
cdr ⟨ D , _ ⟩ FV = Σ[ f ∈ Value ] ⦅ f , FV ⦆ ∈ D

𝒯-cons : DOp (𝒫 Value) (■ ∷ ■ ∷ [])
𝒯-cons ⟨ D , ⟨ 𝒯Ds , _ ⟩ ⟩ ∥ d ∷ ds ∥ = d ∈ D × ∥ ds ∥ ∈ 𝒯Ds
𝒯-cons ⟨ D , ⟨ 𝒯Ds , _ ⟩ ⟩ (u ⊔ v) = 
  𝒯-cons ⟨ D , ⟨ 𝒯Ds , _ ⟩ ⟩ u × 𝒯-cons ⟨ D , ⟨ 𝒯Ds , _ ⟩ ⟩ v
𝒯-cons ⟨ D , ⟨ 𝒯Ds , _ ⟩ ⟩ d = False

𝒯 : ∀ n → DOp (𝒫 Value) (replicate n ■)
𝒯 n = Dfold ■ ■ n 𝒯-cons ⌈ ∥ [] ∥ ⌉

nth : ∀ {n} → Vec Value n → ℕ → Value
nth [] i = ω
nth (v ∷ vs) 0 = v
nth (v ∷ vs) (suc i) = nth vs i

proj : ℕ → DOp (𝒫 Value) (■ ∷ [])
proj i ⟨ D , _ ⟩ u = Σ[ n ∈ ℕ ] Σ[ vs ∈ Vec Value n ]
     ∥ vs ∥ ∈ D × u ≡ nth vs i

ℒ : DOp (𝒫 Value) (■ ∷ [])
ℒ ⟨ D , _ ⟩ (left d) = d ∈ D
ℒ ⟨ D , _ ⟩ (u ⊔ v) = ℒ ⟨ D , _ ⟩ u × ℒ ⟨ D , _ ⟩ v
ℒ ⟨ D , _ ⟩ d = False

ℛ : DOp (𝒫 Value) (■ ∷ [])
ℛ ⟨ D , _ ⟩ (right d) = d ∈ D
ℛ ⟨ D , _ ⟩ (u ⊔ v) = ℛ ⟨ D , _ ⟩ u × ℛ ⟨ D , _ ⟩ v
ℛ ⟨ D , _ ⟩ d = False

𝒞 : DOp (𝒫 Value) (■ ∷ ν ■ ∷ ν ■ ∷ [])
𝒞 ⟨ D , ⟨ E , ⟨ F , _ ⟩ ⟩ ⟩ w = 
  Σ[ V ∈ Value ] left V ∈ D × w ∈ E (⌈ V ⌉) 
          ⊎ (Σ[ V ∈ Value ] right V ∈ D × w ∈ F (⌈ V ⌉))

Λ : DOp (𝒫 Value) (ν ■ ∷ [])
Λ ⟨ f , _ ⟩ ν = True
Λ ⟨ f , _ ⟩ (V ↦ w) = w ∈ f (⌈ V ⌉)
Λ ⟨ f , _ ⟩ (u ⊔ v) = Λ ⟨ f , _ ⟩ u × Λ ⟨ f , _ ⟩ v
Λ ⟨ f , _ ⟩ d = False


{- Monotonicity and congruence of operators --------------------------------------------------}

⋆-mono : monotone (■ ∷ ■ ∷ []) ■ ⋆
⋆-mono ⟨ D , ⟨ E , _ ⟩ ⟩ ⟨ D' , ⟨ E' , _ ⟩ ⟩ ⟨ lift D⊆ , ⟨ lift E⊆ , _ ⟩ ⟩ = lift G
  where
  G : ⋆ ⟨ D , ⟨ E , ptt ⟩ ⟩ ⊆ ⋆ ⟨ D' , ⟨ E' , ptt ⟩ ⟩
  G d ⟨ V , ⟨ wv∈D , V∈E ⟩ ⟩ = ⟨ V , ⟨ D⊆ (V ↦ d) wv∈D , E⊆ V V∈E ⟩ ⟩

⋆-cong : congruent (■ ∷ ■ ∷ []) ■ ⋆
⋆-cong ⟨ D , ⟨ E , _ ⟩ ⟩ ⟨ D' , ⟨ E' , _ ⟩ ⟩ 
       ⟨ lift ⟨ D<D' , D'<D ⟩ , ⟨ lift ⟨ E<E' , E'<E ⟩ , _ ⟩ ⟩ = lift G
  where
  G : ⋆ ⟨ D , ⟨ E , ptt ⟩ ⟩ ≃ ⋆ ⟨ D' , ⟨ E' , ptt ⟩ ⟩
  G = ⟨ lower (⋆-mono ⟨ D , ⟨ E , ptt ⟩ ⟩ ⟨ D' , ⟨ E' , ptt ⟩ ⟩ ⟨ lift D<D' , ⟨ lift E<E' , ptt ⟩ ⟩) 
      , lower (⋆-mono ⟨ D' , ⟨ E' , ptt ⟩ ⟩ ⟨ D , ⟨ E , ptt ⟩ ⟩ ⟨ lift D'<D , ⟨ lift E'<E , ptt ⟩ ⟩) ⟩

Λ-mono : monotone (ν ■ ∷ []) ■ Λ
Λ-mono ⟨ F , _ ⟩ ⟨ F' , _ ⟩ ⟨ F⊆ , _ ⟩ = lift G
  where 
  G : Λ ⟨ F , ptt ⟩  ⊆ Λ ⟨ F' , ptt ⟩
  G (V ↦ w) w∈F₁X = lower (F⊆ (⌈ V ⌉) (⌈ V ⌉) (λ d z → z)) w w∈F₁X
  G ν v∈ = tt
  G (d₁ ⊔ d₂) ⟨ d₁∈ , d₂∈ ⟩ = ⟨ G d₁ d₁∈ , G d₂ d₂∈ ⟩

Λ-ext-⊆ : ∀{F₁ F₂ : (𝒫 Value) → (𝒫 Value)}
  → (∀ {X} → F₁ X ⊆ F₂ X)
  → Λ ⟨ F₁ , ptt ⟩ ⊆ Λ ⟨ F₂ , ptt ⟩
Λ-ext-⊆ {F₁} {F₂} F₁⊆F₂ (V ↦ w) w∈F₁X =
    F₁⊆F₂ w w∈F₁X
Λ-ext-⊆ {F₁} {F₂} F₁⊆F₂ ν v∈ = tt
Λ-ext-⊆ {F₁} {F₂} F₁⊆F₂ (u ⊔ v) ⟨ u∈ , v∈ ⟩ = ⟨ Λ-ext-⊆ F₁⊆F₂ u u∈ , Λ-ext-⊆ F₁⊆F₂ v v∈ ⟩

Λ-ext : ∀{F₁ F₂ : (𝒫 Value) → (𝒫 Value)}
  → (∀ {X} → F₁ X ≃ F₂ X)
  → Λ ⟨ F₁ , ptt ⟩ ≃ Λ ⟨ F₂ , ptt ⟩
Λ-ext {F₁}{F₂} F₁≃F₂ = ⟨ Λ-ext-⊆ (proj₁ F₁≃F₂) , Λ-ext-⊆ (proj₂ F₁≃F₂) ⟩

Λ-cong : congruent (ν ■ ∷ []) ■ Λ
Λ-cong ⟨ F , _ ⟩ ⟨ F' , _ ⟩ ⟨ F≃ , _ ⟩ = lift ⟨ G1 , G2 ⟩
  where
  G1 : Λ ⟨ F , _ ⟩ ⊆ Λ ⟨ F' , _ ⟩
  G1 (V ↦ w) w∈FV = proj₁ (lower
     (F≃ (⌈ V ⌉) (⌈ V ⌉)
          ⟨ (λ x x₁ → x₁) , (λ x x₁ → x₁) ⟩))
             w w∈FV
  G1 ν tt = tt
  G1 (u ⊔ v) ⟨ u∈ , v∈ ⟩ = ⟨ G1 u u∈ , G1 v v∈ ⟩
  G2 : Λ ⟨ F' , ptt ⟩ ⊆ Λ ⟨ F , ptt ⟩
  G2 (V ↦ w) w∈F'V = proj₂ (lower 
     (F≃ (⌈ V ⌉) (⌈ V ⌉) 
         ⟨ (λ x x₁ → x₁) , (λ x x₁ → x₁) ⟩)) 
         w w∈F'V
  G2 ν tt = tt
  G2 (u ⊔ v) ⟨ u∈ , v∈ ⟩ = ⟨ G2 u u∈ , G2 v v∈ ⟩

{- 
Λn-mono : ∀ n → monotone (fv ∷ FV ⊢ν-n n (ν ■) ∷ replicate n ■) ■ (Λn n)
Λn-mono zero = Λ-mono
Λn-mono (suc n) ⟨ F , ⟨ D , Ds ⟩ ⟩ ⟨ F' , ⟨ D' , Ds' ⟩ ⟩ ⟨ F⊆ , ⟨ D⊆ , Ds⊆ ⟩ ⟩ = lift G
  where 
  G : Λn (suc n) ⟨ F , ⟨ D , Ds ⟩ ⟩ ⊆ Λn (suc n) ⟨ F' , ⟨ D' , Ds' ⟩ ⟩
  G ν tt = tt
  G (v , V ↦ d) ⟨ FV⊆D , ⟨ neFV , d∈ ⟩ ⟩ = 
     ⟨ (λ z z∈ → lower D⊆ z (FV⊆D z z∈)) , ⟨ neFV , 
     lower (Λn-mono n ⟨ F (mem FV) , Ds ⟩ 
                   ⟨ F' (mem FV) , Ds' ⟩ ⟨ F⊆ (mem FV) (mem FV) (λ d z → z) , Ds⊆ ⟩)  
                   (FVs ⊢ v , V ↦ d) d∈ ⟩ ⟩
-}



pair-mono : monotone (■ ∷ ■ ∷ []) ■ pair
pair-mono ⟨ D , ⟨ E , _ ⟩ ⟩ ⟨ D' , ⟨ E' , _ ⟩ ⟩ ⟨ lift D⊆ , ⟨ lift E⊆ , _ ⟩ ⟩ = lift G
  where
  G : pair ⟨ D , ⟨ E , ptt ⟩ ⟩ ⊆ pair ⟨ D' , ⟨ E' , ptt ⟩ ⟩
  G ⦅ f , FV ⦆ ⟨ f∈D , FV∈E ⟩ = ⟨ D⊆ f f∈D , E⊆ FV FV∈E ⟩
  G (u ⊔ v) ⟨ u∈ , v∈ ⟩ = ⟨ G u u∈ , G v v∈ ⟩

pair-cong : congruent (■ ∷ ■ ∷ []) ■ pair
pair-cong ⟨ D , ⟨ E , _ ⟩ ⟩ ⟨ D' , ⟨ E' , _ ⟩ ⟩ 
       ⟨ lift ⟨ D<D' , D'<D ⟩ , ⟨ lift ⟨ E<E' , E'<E ⟩ , _ ⟩ ⟩ = lift G
  where
  G : pair ⟨ D , ⟨ E , ptt ⟩ ⟩ ≃ pair ⟨ D' , ⟨ E' , ptt ⟩ ⟩
  G = ⟨ lower (pair-mono ⟨ D , ⟨ E , ptt ⟩ ⟩ ⟨ D' , ⟨ E' , ptt ⟩ ⟩ ⟨ lift D<D' , ⟨ lift E<E' , ptt ⟩ ⟩) 
      , lower (pair-mono ⟨ D' , ⟨ E' , ptt ⟩ ⟩ ⟨ D , ⟨ E , ptt ⟩ ⟩ ⟨ lift D'<D , ⟨ lift E'<E , ptt ⟩ ⟩) ⟩

car-mono : monotone (■ ∷ []) ■ car
car-mono ⟨ D , _ ⟩ ⟨ D' , _ ⟩ ⟨ (lift D⊆) , _ ⟩ = lift G
  where
  G : car ⟨ D , ptt ⟩ ⊆ car ⟨ D' , ptt ⟩
  G u ⟨ v , p∈ ⟩ = ⟨ v , D⊆ ⦅ u , v ⦆ p∈ ⟩ 

car-cong : congruent (■ ∷ []) ■ car
car-cong ⟨ D , _ ⟩ ⟨ D' , _ ⟩ ⟨ (lift ⟨ D<D' , D'<D ⟩) , _ ⟩ = lift G
  where
  G : car ⟨ D , ptt ⟩ ≃ car ⟨ D' , ptt ⟩
  G = ⟨ lower (car-mono ⟨ D , ptt ⟩ ⟨ D' , ptt ⟩ ⟨ lift D<D' , ptt ⟩) 
      , lower (car-mono ⟨ D' , ptt ⟩ ⟨ D , ptt ⟩ ⟨ lift D'<D , ptt ⟩) ⟩

cdr-mono : monotone (■ ∷ []) ■ cdr
cdr-mono ⟨ D , _ ⟩ ⟨ D' , _ ⟩ ⟨ (lift D⊆) , _ ⟩ = lift G
  where
  G : cdr ⟨ D , _ ⟩ ⊆ cdr ⟨ D' , _ ⟩
  G v ⟨ u , p∈ ⟩ = ⟨ u , D⊆ ⦅ u , v ⦆ p∈ ⟩

cdr-cong : congruent (■ ∷ []) ■ cdr
cdr-cong ⟨ D , _ ⟩ ⟨ D' , _ ⟩ ⟨ (lift ⟨ D<D' , D'<D ⟩) , _ ⟩ = lift G
  where
  G : cdr ⟨ D , _ ⟩ ≃ cdr ⟨ D' , _ ⟩
  G = ⟨ lower (cdr-mono ⟨ D , ptt ⟩ ⟨ D' , ptt ⟩ ⟨ lift D<D' , ptt ⟩) 
      , lower (cdr-mono ⟨ D' , ptt ⟩ ⟨ D , ptt ⟩ ⟨ lift D'<D , ptt ⟩) ⟩


ℒ-mono : monotone (■ ∷ []) ■ ℒ
ℒ-mono ⟨ D , _ ⟩ ⟨ D' , _ ⟩ ⟨ (lift D⊆) , _ ⟩ = lift G
  where
  G : ℒ ⟨ D , ptt ⟩ ⊆ ℒ ⟨ D' , ptt ⟩
  G (left v) v∈ = D⊆ v v∈
  G (u ⊔ v) ⟨ u∈ , v∈ ⟩ = ⟨ G u u∈ , G v v∈ ⟩

ℒ-cong : congruent (■ ∷ []) ■ ℒ
ℒ-cong ⟨ D , _ ⟩ ⟨ D' , _ ⟩ ⟨ (lift ⟨ D<D' , D'<D ⟩) , _ ⟩ = lift G
  where
  G : ℒ ⟨ D , ptt ⟩ ≃ ℒ ⟨ D' , ptt ⟩
  G = ⟨ lower (ℒ-mono ⟨ D , ptt ⟩ ⟨ D' , ptt ⟩ ⟨ lift D<D' , ptt ⟩) 
      , lower (ℒ-mono ⟨ D' , ptt ⟩ ⟨ D , ptt ⟩ ⟨ lift D'<D , ptt ⟩) ⟩

ℛ-mono : monotone (■ ∷ []) ■ ℛ
ℛ-mono ⟨ D , _ ⟩ ⟨ D' , _ ⟩ ⟨ (lift D⊆) , _ ⟩ = lift G
  where
  G : ℛ ⟨ D , ptt ⟩ ⊆ ℛ ⟨ D' , ptt ⟩
  G (right v) v∈ = D⊆ v v∈
  G (u ⊔ v) ⟨ u∈ , v∈ ⟩ = ⟨ G u u∈ , G v v∈ ⟩

ℛ-cong : congruent (■ ∷ []) ■ ℛ
ℛ-cong ⟨ D , _ ⟩ ⟨ D' , _ ⟩ ⟨ (lift ⟨ D<D' , D'<D ⟩) , _ ⟩ = lift G
  where
  G : ℛ ⟨ D , ptt ⟩ ≃ ℛ ⟨ D' , ptt ⟩
  G = ⟨ lower (ℛ-mono ⟨ D , ptt ⟩ ⟨ D' , ptt ⟩ ⟨ lift D<D' , ptt ⟩) 
      , lower (ℛ-mono ⟨ D' , ptt ⟩ ⟨ D , ptt ⟩ ⟨ lift D'<D , ptt ⟩) ⟩


𝒞-mono : monotone (■ ∷ ν ■ ∷ ν ■ ∷ []) ■ 𝒞
𝒞-mono ⟨ D , ⟨ FL , ⟨ FR , _ ⟩ ⟩ ⟩ ⟨ D' , ⟨ FL' , ⟨ FR' , _ ⟩ ⟩ ⟩ 
       ⟨ lift D⊆ , ⟨ FL⊆ , ⟨ FR⊆ , _ ⟩ ⟩ ⟩ = lift G
  where 
  G : 𝒞 ⟨ D , ⟨ FL , ⟨ FR , _ ⟩ ⟩ ⟩ ⊆ 𝒞 ⟨ D' , ⟨ FL' , ⟨ FR' , _ ⟩ ⟩ ⟩
  G d (inj₁ ⟨ V , ⟨ V∈ , d∈ ⟩ ⟩) = 
    inj₁ ⟨ V , ⟨ D⊆ (left V) V∈ , lower (FL⊆ ⌈ V ⌉ ⌈ V ⌉ (λ d z → z)) d d∈ ⟩ ⟩
  G d (inj₂ ⟨ V , ⟨ V∈ , d∈ ⟩ ⟩) = 
    inj₂ ⟨ V , ⟨ D⊆ (right V) V∈
         , lower (FR⊆ ⌈ V ⌉ ⌈ V ⌉ (λ d z → z)) d d∈ ⟩ ⟩
{-
𝒞-cong : congruent (■ ∷ ■ ∷ ■ ∷ []) ■ 𝒞
𝒞-cong ⟨ D , ⟨ FL , ⟨ FR , _ ⟩ ⟩ ⟩ ⟨ D' , ⟨ FL' , ⟨ FR' , _ ⟩ ⟩ ⟩ 
       ⟨ lift ⟨ D<D' , D'<D ⟩ , ⟨ lift ⟨ FL<FL' , FL'<FL ⟩ , ⟨ lift ⟨ FR<FR' , FR'<FR ⟩ , _ ⟩ ⟩ ⟩ = lift G
  where
  G : 𝒞 ⟨ D , ⟨ FL , ⟨ FR , ptt ⟩ ⟩ ⟩ ≃ 𝒞 ⟨ D' , ⟨ FL' , ⟨ FR' , ptt ⟩ ⟩ ⟩
  G = ⟨ lower (𝒞-mono ⟨ D , ⟨ FL , ⟨ FR , ptt ⟩ ⟩ ⟩ ⟨ D' , ⟨ FL' , ⟨ FR' , ptt ⟩ ⟩ ⟩ ⟨ lift D<D' , ⟨ lift FL<FL' , ⟨ lift FR<FR' , ptt ⟩ ⟩ ⟩) 
      , lower (𝒞-mono ⟨ D' , ⟨ FL' , ⟨ FR' , ptt ⟩ ⟩ ⟩ ⟨ D , ⟨ FL , ⟨ FR , ptt ⟩ ⟩ ⟩ ⟨ lift D'<D , ⟨ lift FL'<FL , ⟨ lift FR'<FR , ptt ⟩ ⟩ ⟩) ⟩
-}

proj-mono : ∀ i → monotone (■ ∷ []) ■ (proj i)
proj-mono i ⟨ D , _ ⟩ ⟨ D' , _ ⟩ ⟨ (lift D⊆) , _ ⟩ = lift G
  where
  G : proj i ⟨ D , ptt ⟩ ⊆ proj i ⟨ D' , ptt ⟩
  G d ⟨ n , ⟨ vs , ⟨ vs∈ , refl ⟩ ⟩ ⟩ = ⟨ n , ⟨ vs , ⟨ D⊆ ∥ vs ∥ vs∈ , refl ⟩ ⟩ ⟩

proj-cong : ∀ i → congruent (■ ∷ []) ■ (proj i)
proj-cong i ⟨ D , _ ⟩ ⟨ D' , _ ⟩ ⟨ (lift ⟨ D<D' , D'<D ⟩) , _ ⟩ = lift G
  where
  G : proj i ⟨ D , _ ⟩ ≃ proj i ⟨ D' , _ ⟩
  G = ⟨ lower (proj-mono i ⟨ D , ptt ⟩ ⟨ D' , ptt ⟩ ⟨ lift D<D' , ptt ⟩) 
      , lower (proj-mono i ⟨ D' , ptt ⟩ ⟨ D , ptt ⟩ ⟨ lift D'<D , ptt ⟩) ⟩

𝒯-cons-mono : monotone (■ ∷ ■ ∷ []) ■ 𝒯-cons
𝒯-cons-mono ⟨ D , ⟨ E , _ ⟩ ⟩ ⟨ D' , ⟨ E' , _ ⟩ ⟩ ⟨ lift D⊆ , ⟨ lift E⊆ , _ ⟩ ⟩ = lift G
  where
  G : 𝒯-cons ⟨ D , ⟨ E , _ ⟩ ⟩ ⊆ 𝒯-cons ⟨ D' , ⟨ E' , _ ⟩ ⟩
  G ∥ d ∷ ds ∥ ⟨ d∈ , ds∈ ⟩ = ⟨ D⊆ d d∈ , E⊆ ∥ ds ∥ ds∈ ⟩
  G (u ⊔ v) ⟨ u∈ , v∈ ⟩ = ⟨ G u u∈ , G v v∈ ⟩

𝒯-mono : ∀ n → monotone (replicate n ■) ■ (𝒯 n)
𝒯-mono n = Dfold-pres _⊆_ ■ ■ n 𝒯-cons 𝒯-cons ⌈ ∥ [] ∥ ⌉ ⌈ ∥ [] ∥ ⌉  
           𝒯-cons-mono (lift (λ d z → z))


{-

{- Consistency ----------------------------------------------------------------}

⋆-consis : consistent _~_ (■ ∷ ■ ∷ []) ■ ⋆
⋆-consis ⟨ D , ⟨ E , _ ⟩ ⟩ ⟨ D' , ⟨ E' , _ ⟩ ⟩ ⟨ lift D~ , ⟨ lift E~ , _ ⟩ ⟩ = lift G
  where
  G : Every _~_ (⋆ ⟨ D , ⟨ E , ptt ⟩ ⟩) (⋆ ⟨ D' , ⟨ E' , ptt ⟩ ⟩)
  G u w ⟨ V , ⟨ u∈D , ⟨ V<E , neV ⟩ ⟩ ⟩
        ⟨ V' , ⟨ w∈D' , ⟨ V<E' , neV' ⟩ ⟩ ⟩
        with D~ (V ↦ u) (V' ↦ w) u∈D w∈D'
  ... | inj₁ x = ⊥-elim (x (Every⇒≈ V V' (Every-⊆ E~ V<E V<E')))
  ... | inj₂ y = proj₂ y

Λ-consis : consistent _~_ (ν ■ ∷ []) ■ Λ
Λ-consis ⟨ F , _ ⟩ ⟨ F' , _ ⟩ ⟨ F~ , _ ⟩ = lift G
  where
  G : Every _~_ (Λ ⟨ F , ptt ⟩) (Λ ⟨ F' , ptt ⟩)
  G ν (V ↦ w) tt _ = tt
  G ν ν tt _ = tt
  G (V ↦ w) ν w∈F₁X tt = tt
  G (V ↦ w) (V' ↦ w') 
    ⟨ w∈F₁X , neV ⟩ ⟨ w∈F₁X' , neV' ⟩ with V ≈? V'
  ... | yes V≈V' = 
    inj₂ ⟨ V≈V' , lower (F~ (mem V) (mem V') (≈⇒Every V V' V≈V')) w w' w∈F₁X w∈F₁X' ⟩
  ... | no ¬V≈V' = inj₁ ¬V≈V'

pair-consis : consistent _~_ (■ ∷ ■ ∷ []) ■ pair
pair-consis ⟨ D , ⟨ E , _ ⟩ ⟩ ⟨ D' , ⟨ E' , _ ⟩ ⟩ ⟨ lift D~ , ⟨ lift E~ , _ ⟩ ⟩ = lift G
  where
  G : Every _~_ (pair ⟨ D , ⟨ E , ptt ⟩ ⟩) (pair ⟨ D' , ⟨ E' , ptt ⟩ ⟩)
  G ⦅ u , V ⦆ ⦅ u' , V' ⦆ ⟨ u∈ , V⊆ ⟩ ⟨ u'∈ , V'⊆ ⟩ = 
    ⟨ D~ u u' u∈ u'∈ 
      , Every⇒≈ V V' (λ a b z z₁ → E~ a b (proj₁ V⊆ a z) (proj₁ V'⊆ b z₁)) ⟩

car-consis : consistent _~_ (■ ∷ []) ■ car
car-consis ⟨ D , _ ⟩ ⟨ D' , _ ⟩ ⟨ (lift D~) , _ ⟩ = lift G
  where
  G : Every _~_ (car ⟨ D , ptt ⟩) (car ⟨ D' , ptt ⟩)
  G u u' ⟨ V , ⟨ p∈ , neV ⟩ ⟩ ⟨ V' , ⟨ p'∈ , neV' ⟩ ⟩ 
   with D~ ⦅ u , V ⦆ ⦅ u' , V' ⦆ p∈ p'∈
  ... | ⟨ u~ , v~ ⟩ = u~

cdr-consis : consistent _~_ (■ ∷ []) ■ cdr
cdr-consis ⟨ D , _ ⟩ ⟨ D' , _ ⟩ ⟨ (lift D~) , _ ⟩ = lift G
  where
  G : Every _~_ (cdr ⟨ D , ptt ⟩) (cdr ⟨ D' , ptt ⟩)
  G v v' ⟨ u , ⟨ V , ⟨ p∈ , v∈V ⟩ ⟩ ⟩ ⟨ u' , ⟨ V' , ⟨ p'∈ , v'∈V' ⟩ ⟩ ⟩
    with D~ ⦅ u , V ⦆ ⦅ u' , V' ⦆ p∈ p'∈
  ... | ⟨ u~ , v~ ⟩ = ≈⇒Every V V' v~ v v' v∈V v'∈V'

ℒ-consis : consistent _~_ (■ ∷ []) ■ ℒ
ℒ-consis ⟨ D , _ ⟩ ⟨ D' , _ ⟩ ⟨ (lift D~) , _ ⟩ = lift G
  where
  G : Every _~_ (ℒ ⟨ D , ptt ⟩) (ℒ ⟨ D' , ptt ⟩)
  G (left u) (left v) U∈ V∈ 
    = D~ u v U∈ V∈

ℛ-consis : consistent _~_ (■ ∷ []) ■ ℛ
ℛ-consis ⟨ D , _ ⟩ ⟨ D' , _ ⟩ ⟨ (lift D~) , _ ⟩ = lift G
  where
  G : Every _~_ (ℛ ⟨ D , ptt ⟩) (ℛ ⟨ D' , ptt ⟩)
  G (right u) (right v) U∈ V∈ 
    = D~ u v U∈ V∈



𝒞-consis : consistent _~_ (■ ∷ ν ■ ∷ ν ■ ∷ []) ■ 𝒞
𝒞-consis ⟨ D , ⟨ FL , ⟨ FR , _ ⟩ ⟩ ⟩ ⟨ D' , ⟨ FL' , ⟨ FR' , _ ⟩ ⟩ ⟩ 
       ⟨ lift D~ , ⟨ FL~ , ⟨ FR~ , _ ⟩ ⟩ ⟩ = lift G
  where 
  G : Every _~_ (𝒞 ⟨ D , ⟨ FL , ⟨ FR , ptt ⟩ ⟩ ⟩) (𝒞 ⟨ D' , ⟨ FL' , ⟨ FR' , ptt ⟩ ⟩ ⟩)
  G u w (inj₁ ⟨ v , ⟨ V , ⟨ V⊆ , u∈ ⟩ ⟩ ⟩ ) (inj₁ ⟨ v' , ⟨ V' , ⟨ V⊆' , w∈ ⟩ ⟩ ⟩)
    = lower (FL~ (mem (v ∷ V)) (mem (v' ∷ V')) V≈V') u w u∈ w∈
    where
    V≈V' : ∀ d d' → d ∈ mem (v ∷ V) → d' ∈ mem (v' ∷ V') → d ~ d'
    V≈V' d d' d∈ d'∈ = D~ (left d) (left d') (V⊆ d d∈) (V⊆' d' d'∈)
  G u w (inj₁ ⟨ v , ⟨ V , ⟨ V⊆ , u∈ ⟩ ⟩ ⟩) (inj₂ ⟨ v' , ⟨ V' , ⟨ V⊆' , w∈ ⟩ ⟩ ⟩) = 
    ⊥-elim (D~ (left v) (right v') (V⊆ v (here refl)) (V⊆' v' (here refl)))
  G u w (inj₂ ⟨ v , ⟨ V , ⟨ V⊆ , u∈ ⟩ ⟩ ⟩) (inj₁ ⟨ v' , ⟨ V' , ⟨ V⊆' , w∈ ⟩ ⟩ ⟩) = 
    ⊥-elim (D~ (right v) (left v') (V⊆ v (here refl)) (V⊆' v' (here refl)))
  G u w (inj₂ ⟨ v , ⟨ V , ⟨ V⊆ , u∈ ⟩ ⟩ ⟩) (inj₂ ⟨ v' , ⟨ V' , ⟨ V⊆' , w∈ ⟩ ⟩ ⟩)
    = lower (FR~ (mem (v ∷ V)) (mem (v' ∷ V')) V≈V') u w u∈ w∈
    where
    V≈V' : ∀ d d' → d ∈ mem (v ∷ V) → d' ∈ mem (v' ∷ V') → d ~ d'
    V≈V' d d' d∈ d'∈ = D~ (right d) (right d') (V⊆ d d∈) (V⊆' d' d'∈)

nth-~ : ∀ i us vs → ∥ us ∥ ~ ∥ vs ∥ → 
    i < length us → i < length vs → 
    nth us i ~ nth vs i
nth-~ zero (x ∷ us) (x₁ ∷ vs) us~vs i<us i<vs = proj₁ us~vs
nth-~ (suc i) (x ∷ us) (x₁ ∷ vs) ⟨ fst , snd ⟩ i<us i<vs = 
  nth-~ i us vs snd (≤-pred i<us) (≤-pred i<vs)

proj-consis : ∀ i → consistent _~_ (■ ∷ []) ■ (proj i)
proj-consis i ⟨ D , _ ⟩ ⟨ D' , _ ⟩ ⟨ (lift D~) , _ ⟩ = lift G
  where
  G : Every _~_ (proj i ⟨ D , ptt ⟩) (proj i ⟨ D' , ptt ⟩)
  G u v ⟨ us , ⟨ i< , ⟨ us∈ , refl ⟩ ⟩ ⟩ 
       ⟨ vs , ⟨ i<' , ⟨ vs∈ , refl ⟩ ⟩ ⟩ 
    with D~ ∥ us ∥ ∥ vs ∥ us∈ vs∈ 
  ... | q = nth-~ i us vs q i< i<'

ℬ-consis : ∀ B k → consistent _~_ [] ■ (ℬ B k)
ℬ-consis B k _ _ _ = lift G
  where 
  G : Every _~_ (ℬ B k ptt) (ℬ B k ptt)
  G (const {B'} k) (const {B''} k') d∈ d'∈ with base-eq? B B' | base-eq? B B''
  ... | yes refl | yes refl with base-eq? B B
  ... | yes refl = trans (sym d∈) d'∈
  ... | no neq = ⊥-elim (neq refl)

𝓅-consis : ∀ P f → consistent _~_ [] ■ (𝓅 P f)
𝓅-consis P f _ _ _ = lift (G P f)
  where
  G : ∀ P f → Every _~_ (𝓅 P f ptt) (𝓅 P f ptt)
  G (base x) f (const {B} k) (const {B'} k') u∈ v∈ with base-eq? x B | base-eq? x B'
  ... | yes refl | yes refl with base-eq? x x
  ... | yes refl = trans (sym u∈) v∈
  ... | no neq = ⊥-elim (neq refl)
  G (x ⇒ P) f (.(const k ∷ []) ↦ u) (.(const k' ∷ []) ↦ v) 
    ⟨ k , ⟨ refl , u∈ ⟩ ⟩ ⟨ k' , ⟨ refl , v∈ ⟩ ⟩ with base-eq? x x | base-rep-eq? k k' 
  ... | no neq | q = ⊥-elim (neq refl )
  ... | yes refl | no neq = inj₁ (λ z → H (head (proj₁ z)))
    where
    H : const k ~ const k' → False
    H z with base-eq? x x | z
    ... | no neq | q = ⊥-elim (neq refl)
    ... | yes refl | q = neq q
  ... | yes refl | yes refl = inj₂ ⟨ ⟨ H ∷ [] , tt ⟩ , G P (f k) u v u∈ v∈ ⟩
    where
    H : const k ~ const k
    H with base-eq? x x
    ... | no neq = ⊥-elim (neq refl)
    ... | yes refl = refl
  G (x ⇒ P) f (V ↦ u) ν u∈ v∈ = tt
  G (x ⇒ P) f ν (V ↦ w) u∈ v∈ = tt
  G (x ⇒ P) f ν ν u∈ v∈ = tt


𝒯-cons-consis : consistent _~_ (■ ∷ ■ ∷ []) ■ 𝒯-cons
𝒯-cons-consis ⟨ D , ⟨ E , _ ⟩ ⟩ ⟨ D' , ⟨ E' , _ ⟩ ⟩ ⟨ lift D~ , ⟨ lift E~ , _ ⟩ ⟩ = lift G
  where
  G : Every _~_ (𝒯-cons ⟨ D , ⟨ E , _ ⟩ ⟩) (𝒯-cons ⟨ D' , ⟨ E' , _ ⟩ ⟩)
  G ∥ u ∷ us ∥ ∥ v ∷ vs ∥ ⟨ u∈ , us∈ ⟩ ⟨ v∈ , vs∈ ⟩ = ⟨ D~ u v u∈ v∈ , E~ ∥ us ∥ ∥ vs ∥ us∈ vs∈ ⟩


𝒯-consis : ∀ n → consistent _~_ (replicate n ■) ■ (𝒯 n)
𝒯-consis n = Dfold-pres (Every _~_) ■ ■ n 𝒯-cons 𝒯-cons ⌈ ∥ [] ∥ ⌉ ⌈ ∥ [] ∥ ⌉  
           𝒯-cons-consis (lift G)
  where
  G : (x x₁ : Value) (x₂ : x ≡ ∥ [] ∥) (x₃ : x₁ ≡ ∥ [] ∥) → x ~ x₁ 
  G .(∥ [] ∥) .(∥ [] ∥) refl refl = tt

{-
𝒜-cons-consis : consistent _~_ (■ ∷ ■ ∷ []) ■ 𝒜-cons
𝒜-cons-consis ⟨ D , ⟨ E , _ ⟩ ⟩ ⟨ D' , ⟨ E' , _ ⟩ ⟩ ⟨ lift D~ , ⟨ lift E~ , _ ⟩ ⟩ = lift G
  where
  G : Every _~_ (𝒜-cons ⟨ D , ⟨ E , _ ⟩ ⟩) (𝒜-cons ⟨ D' , ⟨ E' , _ ⟩ ⟩)
  G (v , V ↦ w) (v , V' ↦ w') ⟨ fvs⊆ , u∈ ⟩ ⟨ fvs'⊆ , v∈ ⟩
     = E~ (V ↦ w) (v ∷ V' ↦ w') u∈ v∈

𝒜-consis : ∀ n → consistent _~_ (■ ∷ replicate n ■) ■ (𝒜 n)
𝒜-consis n ⟨ F , Ds ⟩ ⟨ F' , Ds' ⟩ ⟨ F~ , Ds~ ⟩ = 
  Dfold-pres (Every _~_) ■ ■ n 𝒜-cons 𝒜-cons F F' 𝒜-cons-consis F~ Ds Ds' Ds~
-}


{- Continuity -----------------------------------------------------------------}

{- Bear in mind that Continuity is a property related to environments.
   That is, it involves some  evaluation function  
   
   continuity is the property that whenever a value is in a Dation,
   then there exists a finite environment for which that value is still in the denotation.
   -}






{-

-}

{- More Equations ----------------------------------------------------------}

{-

-}


{- 



{- Basic Properties of Dational Operators ---------------------------------}

k∈℘k : ∀{B}{k} → const {B} k ∈ ℘ (base B) k
k∈℘k {B}{k}
    with base-eq? B B
... | yes refl = refl
... | no neq = neq refl

k′∈℘k⇒P≡B : ∀{P B}{k}{k′} → const {B} k′ ∈ ℘ P k → P ≡ base B
k′∈℘k⇒P≡B {base B′} {B} {k} {k′} k′∈℘k
    with base-eq? B′ B
... | yes refl = refl
... | no neq = ⊥-elim k′∈℘k

k′∈℘k⇒k′≡k : ∀{B}{k}{k′} → const {B} k′ ∈ ℘ (base B) k → k′ ≡ k
k′∈℘k⇒k′≡k {B}{k}{k′} m
    with base-eq? B B
... | yes refl = sym m
... | no neq = ⊥-elim m

v∈ℬk⇒v≡k : ∀{v}{B}{k} → v ∈ ℬ B k → v ≡ const {B} k
v∈ℬk⇒v≡k {const {B′} k′} {B} {k} v∈
    with base-eq? B B′
... | yes refl rewrite v∈ = refl
... | no neq = ⊥-elim v∈

v∈℘k⇒v≡k : ∀{v}{B}{k} → v ∈ ℘ (base B) k → v ≡ const {B} k
v∈℘k⇒v≡k {const {B′} k′} {B} {k} v∈ = v∈ℬk⇒v≡k v∈ 

v∈𝒯⇒v≡∥vs∥ : ∀{n}{Ds}{v}
  → v ∈ 𝒯 n Ds
  → Σ[ vs ∈ List Value ] v ≡ ∥ vs ∥
v∈𝒯⇒v≡∥vs∥ {zero} {Ds} {∥ x ∥} v∈ = ⟨ x , refl ⟩
v∈𝒯⇒v≡∥vs∥ {suc n} {Ds} {∥ x ∥} v∈ = ⟨ x , refl ⟩

NE-Π⇒𝒯 : ∀{n}{Ds : Π n (𝒫 Value)}
   → NE-Π Ds
   → Σ[ vs ∈ List Value ] 𝒯 n Ds ∥ vs ∥
NE-Π⇒𝒯 {zero} {ptt} NE-Ds = ⟨ [] , tt ⟩
NE-Π⇒𝒯 {suc n} {⟨ D , Ds ⟩} ⟨ ⟨ v , v∈D ⟩ , NE-Ds ⟩
    with NE-Π⇒𝒯 {n} {Ds} NE-Ds
... | ⟨ vs , vs⊆ ⟩ = ⟨ v ∷ vs , ⟨ v∈D , vs⊆ ⟩ ⟩

NE-Π⇒NE-𝒯 : ∀{n}{Ds : Π n (𝒫 Value)}
   → NE-Π Ds
   → nonempty (𝒯 n Ds)
NE-Π⇒NE-𝒯{n}{Ds} NE-Ds
    with NE-Π⇒𝒯 NE-Ds
... | ⟨ vs , vs∈𝒯Ds ⟩ = ⟨ ∥ vs ∥ , vs∈𝒯Ds ⟩



{- Abstraction followed by Application is the identity ------------------------}

continuous : (F : 𝒫 Value → 𝒫 Value) → Set₁
continuous F = ∀ X E → mem E ⊆ F X → nonempty X
    → Σ[ D ∈ List Value ] mem D ⊆ X  ×  mem E ⊆ F (mem D)  ×  D ≢ []

monotone : (F : 𝒫 Value → 𝒫 Value) → Set₁
monotone F = ∀ D₁ D₂ → D₁ ⊆ D₂ → F D₁ ⊆ F D₂

Λ-▪-id : ∀ {F : 𝒫 Value → 𝒫 Value}{X : 𝒫 Value}
  → continuous F → monotone F → nonempty X
  → (Λ F) ▪ X ≃ F X
Λ-▪-id {F}{X} Fcont Fmono NE-X = ⟨ (Λ-▪-⊆ Fmono) , (⊆-Λ-▪ Fcont NE-X) ⟩
  where
  Λ-▪-⊆ : ∀ {F : 𝒫 Value → 𝒫 Value}{X : 𝒫 Value}
    → monotone F  →  (Λ F) ▪ X ⊆ F X
  Λ-▪-⊆ {F} {X} Fmono w ⟨ V , ⟨ fvs , ⟨ ⟨ w∈FV , _ ⟩ , ⟨ V<X , V≢[] ⟩ ⟩ ⟩ ⟩ =
      Fmono (mem (v ∷ V)) X V<X w w∈FV

  ⊆-Λ-▪ : ∀ {F : 𝒫 Value → 𝒫 Value}{X : 𝒫 Value}
    → continuous F  → nonempty X →  F X ⊆ (Λ F) ▪ X
  ⊆-Λ-▪ {F}{X} Fcont NE-X w w∈FX 
      with Fcont X (w ∷ []) (λ { d (here refl) → w∈FX }) NE-X
  ... | ⟨ D , ⟨ D<X , ⟨ w∈FD , NE-D ⟩ ⟩ ⟩ = {!!}
  {-
        ⟨ D , ⟨ [] , ⟨ ⟨ w∈FD w (here refl) , NE-D ⟩ , ⟨ D<X , NE-D ⟩ ⟩ ⟩ ⟩
  -}
  
{- Primitive Abstraction followed by Application is the identity --------------}

℘-▪-≃ : ∀{B}{P}{f}{k}  →  (℘ (B ⇒ P) f) ▪ (℘ (base B) k) ≃ ℘ P (f k)
℘-▪-≃ {B}{P}{f}{k} = ⟨ fwd , back ⟩
  where
  fwd : ℘ (B ⇒ P) f ▪ ℘ (base B) k ⊆ ℘ P (f k)
  fwd w ⟨ V , ⟨ fvs , ⟨ ⟨ k′ , ⟨ refl , w∈fk′ ⟩ ⟩ , ⟨ k′∈pk , _ ⟩ ⟩ ⟩ ⟩
      with k′∈pk (const k′) (here refl)
  ... | pkk′ rewrite k′∈℘k⇒k′≡k pkk′ = w∈fk′
  back : ℘ P (f k) ⊆ ℘ (B ⇒ P) f ▪ ℘ (base B) k
  back w w∈fk = ⟨ (const k ∷ []) , ⟨ [] , ⟨ ⟨ k , ⟨ refl , w∈fk ⟩ ⟩ ,
                ⟨ (λ {d (here refl) → k∈℘k}) , (λ ()) ⟩ ⟩ ⟩ ⟩

{- Cons is a Congruence  ------------------------------------------------------}



Π-append-⊆ : ∀{n}{m}{Ds Ds′ : Π n (𝒫 Value)}{Es Es′ : Π m (𝒫 Value)}
   → Ds ⫃ Ds′ → Es ⫃ Es′
   → Π-append Ds Es ⫃ Π-append Ds′ Es′
Π-append-⊆ {zero} {m} {Ds} {Ds′} {Es} {Es′} Ds⊆Ds′ Es⊆Es′ = Es⊆Es′
Π-append-⊆ {suc n} {m} {⟨ D , Ds ⟩} {⟨ D′ , Ds′ ⟩} {Es} {Es′} ⟨ D⊆D′ , Ds⊆Ds′ ⟩
    Es⊆Es′ = ⟨ D⊆D′ , Π-append-⊆ Ds⊆Ds′ Es⊆Es′ ⟩

Π-append-⩭ : ∀{n}{m}{Ds Ds′ : Π n (𝒫 Value)}{Es Es′ : Π m (𝒫 Value)}
   → Ds ⩭ Ds′ → Es ⩭ Es′
   → Π-append Ds Es ⩭ Π-append Ds′ Es′
Π-append-⩭ {zero} {m} {Ds} {Ds′} Ds=Ds′ Es=Es′ = Es=Es′
Π-append-⩭ {suc n} {m} {⟨ D , Ds ⟩} {⟨ D′ , Ds′ ⟩} ⟨ D=D′ , Ds=Ds′ ⟩ Es=Es′ =
    ⟨ D=D′ , Π-append-⩭ Ds=Ds′ Es=Es′ ⟩

{- Cons and Car  --------------------------------------------------------------}

car-of-cons-⊆ : ∀{D₁ D₂ : 𝒫 Value}
  → car (〘 D₁ , D₂ 〙) ⊆ D₁
car-of-cons-⊆ {D₁} {D₂} u ⟨ v , ⟨ u∈D₁ , v∈D₂ ⟩ ⟩ = u∈D₁

car-of-cons : ∀{D₁ D₂ : 𝒫 Value}
  → nonempty D₂
  → car (〘 D₁ , D₂ 〙) ≃ D₁
car-of-cons {D₁}{D₂} ⟨ v , v∈D₂ ⟩ =
    ⟨ car-of-cons-⊆ , (λ u u∈D₁ → ⟨ v , ⟨ u∈D₁ , v∈D₂ ⟩ ⟩) ⟩

cdr-of-cons-⊆ : ∀{D₁ D₂ : 𝒫 Value}
  → cdr 〘 D₁ , D₂ 〙 ⊆ D₂
cdr-of-cons-⊆ {D₁} {D₂} v ⟨ u , ⟨ u∈D₁ , v∈D₂ ⟩ ⟩ = v∈D₂

cdr-of-cons : ∀{D₁ D₂ : 𝒫 Value}
  → nonempty D₁
  → cdr 〘 D₁ , D₂ 〙 ≃ D₂
cdr-of-cons {D₁}{D₂} ⟨ u , u∈D₁ ⟩ =
    ⟨ cdr-of-cons-⊆ , (λ v v∈D₂ → ⟨ u , ⟨ u∈D₁ , v∈D₂ ⟩ ⟩) ⟩

{- Project from a Tuple -------------------------------------------------------}

𝒯-nth-0 : ∀{n}{D}{Ds}
   → NE-Π Ds
   → proj (𝒯 (suc n) ⟨ D , Ds ⟩) 0 ≃ D
𝒯-nth-0 {n}{D}{Ds} NE-Ds = ⟨ G , H ⟩
  where
  G : proj (𝒯 (suc n) ⟨ D , Ds ⟩) 0 ⊆ D
  G .v ⟨ v ∷ vs , ⟨ lt , ⟨ ⟨ v∈D , ∥vs∥∈𝒯Ds ⟩ , refl ⟩ ⟩ ⟩ = v∈D

  H : D ⊆ proj (𝒯 (suc n) ⟨ D , Ds ⟩) 0
  H v v∈D
      with NE-Π⇒𝒯 NE-Ds
  ... | ⟨ vs , vs⊆ ⟩ = ⟨ (v ∷ vs) , ⟨ s≤s z≤n , ⟨ ⟨ v∈D , vs⊆ ⟩ , refl ⟩ ⟩ ⟩

𝒯-nth-suc : ∀{i}{n}{D}{Ds}
   → nonempty D → NE-Π Ds
   → proj (𝒯 (suc n) ⟨ D , Ds ⟩) (suc i)
   ≃ proj (𝒯 n Ds) i
𝒯-nth-suc {i}{n}{D}{Ds} ⟨ u , u∈D ⟩ NE-Ds = ⟨ G , H ⟩
  where
  G : proj (𝒯 (suc n) ⟨ D , Ds ⟩) (suc i) ⊆ proj (𝒯 n Ds) i
  G u ⟨ v ∷ vs , ⟨ s≤s lt , ⟨ ⟨ v∈D , ∥vs∥∈𝒯Ds ⟩ , refl ⟩ ⟩ ⟩ =
      ⟨ vs , ⟨ lt , ⟨ ∥vs∥∈𝒯Ds , refl ⟩ ⟩ ⟩
  H : proj (𝒯 n Ds) i ⊆ proj (𝒯 (suc n) ⟨ D , Ds ⟩) (suc i)
  H v ⟨ vs , ⟨ lt , ⟨ vs⊆Ds , eq ⟩ ⟩ ⟩ =
    ⟨ (u ∷ vs) , ⟨ s≤s lt , ⟨ ⟨ u∈D , vs⊆Ds ⟩ , eq ⟩ ⟩ ⟩

{- Case, Left, and Right ------------------------------------------------------}



ℒ-𝒞 : ∀{D : 𝒫 Value}{F G : 𝒫 Value → 𝒫 Value}
   → continuous F → monotone F → nonempty D
   → 𝒞 (ℒ D) (Λ F) (Λ G) ≃ F D
ℒ-𝒞 {D}{F}{G} Fcont Fmono NE-D = ⟨ fwd , back ⟩
  where
  fwd : 𝒞 (ℒ D) (Λ F) (Λ G) ⊆ F D
  fwd v (inj₁ ⟨ V , ⟨ fvs , ⟨ ⟨ _ , V⊆D ⟩ , ⟨ v∈F[V] , V≢[] ⟩ ⟩ ⟩ ⟩) =
      Fmono (mem (v ∷ V)) D V⊆D v v∈F[V]

  back : F D ⊆ 𝒞 (ℒ D) (Λ F) (Λ G)
  back v v∈F[D]
      with Fcont D (v ∷ []) (λ{d (here refl) → v∈F[D]}) NE-D
  ... | ⟨ E , ⟨ E⊆D , ⟨ v∈FE , NE-E ⟩ ⟩ ⟩ = {!!}
  {-
      inj₁ ⟨ E , ⟨ [] , ⟨ ⟨ NE-E , E⊆D ⟩ , ⟨ v∈FE v (here refl) , NE-E ⟩ ⟩ ⟩ ⟩
-}

ℛ-𝒞 : ∀{D : 𝒫 Value}{F G : 𝒫 Value → 𝒫 Value}
   → continuous G → monotone G → nonempty D
   → 𝒞 (ℛ D) (Λ F) (Λ G) ≃ G D
ℛ-𝒞 {D}{F}{G} Gcont Gmono NE-D = ⟨ fwd , back ⟩
  where
  fwd : 𝒞 (ℛ D) (Λ F) (Λ G) ⊆ G D
  fwd v (inj₂ ⟨ V , ⟨ fvs , ⟨ ⟨ _ , V⊆D ⟩ , ⟨ v∈G[V] , V≢[] ⟩ ⟩ ⟩ ⟩) =
      Gmono (mem (v ∷ V)) D V⊆D v v∈G[V]

  back : G D ⊆ 𝒞 (ℛ D) (Λ F) (Λ G)
  back v v∈G[D]
      with Gcont D (v ∷ []) (λ{d (here refl) → v∈G[D]}) NE-D
  ... | ⟨ E , ⟨ E⊆D , ⟨ v∈GE , NE-E ⟩ ⟩ ⟩ = {!!}
  {-
      inj₂ ⟨ E , ⟨ [] , ⟨ ⟨ NE-E , E⊆D ⟩ , ⟨ v∈GE v (here refl) , NE-E ⟩ ⟩ ⟩ ⟩
  -}














{- Environments ---------------------------------------------------------------}

Env : Set₁
Env = Var → 𝒫 Value

nonempty-env : Env → Set
nonempty-env ρ = ∀ x → nonempty (ρ x)

infix 5 _⊆ₑ_
_⊆ₑ_ : Env → Env → Set
ρ₁ ⊆ₑ ρ₂ = ∀ x → ρ₁ x ⊆ ρ₂ x

⊆ₑ-trans : ∀{ρ₁ ρ₂ ρ₃} → ρ₁ ⊆ₑ ρ₂ → ρ₂ ⊆ₑ ρ₃ → ρ₁ ⊆ₑ ρ₃
⊆ₑ-trans {ρ₁}{ρ₂}{ρ₃} r12 r23 x = λ d z → r23 x d (r12 x d z)

extend-nonempty-env : ∀{ρ}{X}
   → nonempty-env ρ  →  nonempty X  →  nonempty-env (X • ρ)
extend-nonempty-env {ρ} {X} NE-ρ NE-X zero = NE-X
extend-nonempty-env {ρ} {X} NE-ρ V≢[] (suc x) = NE-ρ x

env-ext : ∀{ρ ρ′}{X} → ρ ⊆ₑ ρ′ → (x : Var) → (X • ρ) x ⊆ (X • ρ′) x
env-ext ρ<ρ′ zero d d∈ = d∈
env-ext ρ<ρ′ (suc x) = ρ<ρ′ x

{- environments whose codomain are finite nonempty sets -}
finite-env : Env → Set
finite-env ρ = ∀ x → Σ[ E ∈ List Value ] ρ x ≃ mem E × E ≢ []

infix 6 _⊔ₑ_
_⊔ₑ_ : Env → Env → Env
(ρ₁ ⊔ₑ ρ₂) x v = ρ₁ x v ⊎ ρ₂ x v

join-finite-env : ∀{ρ₁ ρ₂}  → finite-env ρ₁  →  finite-env ρ₂
   → finite-env (ρ₁ ⊔ₑ ρ₂)
join-finite-env {ρ₁}{ρ₂} f1 f2 x
    with f1 x
... | ⟨ E1 , ⟨ ρ₁=E1 , NE-E1 ⟩ ⟩
    with f2 x
... | ⟨ E2 , ⟨ ρ₂=E2 , NE-E2 ⟩ ⟩ =
    ⟨ (E1 ++ E2) , ⟨ ⟨ G , (H {E1} λ d z → z) ⟩ ,
      (λ E12=[] → NE-E1 (++-conicalˡ E1 E2 E12=[])) ⟩ ⟩
    where
    G : (v : Value) → ρ₁ x v ⊎ ρ₂ x v → mem (E1 ++ E2) v
    G v (inj₁ ρ1x) = ∈-++⁺ˡ ((proj₁ ρ₁=E1) v ρ1x)
    G v (inj₂ ρ2x) = ∈-++⁺ʳ E1 ((proj₁ ρ₂=E2) v ρ2x)

    H : ∀{E} → mem E ⊆ mem E1 → mem (E ++ E2) ⊆ (λ v → ρ₁ x v ⊎ ρ₂ x v)
    H {[]} E<E1 v v∈E++E2 = inj₂ ((proj₂ ρ₂=E2) v v∈E++E2)
    H {x ∷ E} E<E1 .x (here refl) = inj₁ ((proj₂ ρ₁=E1) x (E<E1 x (here refl)))
    H {x ∷ E} E<E1 v (there v∈E++E2) =
       H (λ v z → E<E1 v (there z)) v v∈E++E2

join-lub : ∀{ρ ρ₁ ρ₂} → ρ₁ ⊆ₑ ρ → ρ₂ ⊆ₑ ρ → ρ₁ ⊔ₑ ρ₂ ⊆ₑ ρ
join-lub {ρ} {ρ₁} {ρ₂} ρ₁⊆ρ ρ₂⊆ρ x v (inj₁ v∈ρ₁x) = ρ₁⊆ρ x v v∈ρ₁x
join-lub {ρ} {ρ₁} {ρ₂} ρ₁⊆ρ ρ₂⊆ρ x v (inj₂ v∈ρ₂x) = ρ₂⊆ρ x v v∈ρ₂x

join-⊆-left : ∀{ρ₁ ρ₂} → ρ₁ ⊆ₑ ρ₁ ⊔ₑ ρ₂
join-⊆-left {ρ₁}{ρ₂} = λ x d z → inj₁ z

join-⊆-right : ∀{ρ₁ ρ₂} → ρ₂ ⊆ₑ ρ₁ ⊔ₑ ρ₂
join-⊆-right {ρ₁}{ρ₂} = λ x d z → inj₂ z

monotone-env : (Env → 𝒫 Value) → Set₁
monotone-env D = ∀ {ρ ρ′} → (∀ x → ρ x ⊆ ρ′ x)  →  D ρ ⊆ D ρ′

{- Relations on Results and Products ------------------------------------------}

rel-results : ∀{ℓ}{T : Set ℓ}
   → (∀ b → Result T b → Result T b → Set₁)
   → ∀ bs → Tuple bs (Result T) → Tuple bs (Result T) → Set₁
rel-results R [] xs ys = Lift (lsuc lzero) True
rel-results R (b ∷ bs) ⟨ x , xs ⟩ ⟨ y , ys ⟩ =
    (R b x y) × (rel-results R bs xs ys)

⊆-result : ∀ b → Result (𝒫 Value) b → Result (𝒫 Value) b → Set₁
⊆-result ■ x y = Lift (lsuc lzero) (x ⊆ y)
⊆-result ν b) f g = ∀ X → ⊆-result b (f X) (g X)
⊆-result (∁ b) x y = ⊆-result b x y

⊆-results = rel-results ⊆-result

⊆-result⇒⊆ : ∀ D E → ⊆-result ■ D E → D ⊆ E
⊆-result⇒⊆ D E (lift D⊆E) = D⊆E

rel-results⇒rel-Π : ∀{n}{xs ys : Π n (𝒫 Value)}
    {R : ∀ b → Result (𝒫 Value) b → Result (𝒫 Value) b → Set₁}
    {R′ : 𝒫 Value → 𝒫 Value → Set}
  → (∀ x y → R ■ x y → R′ x y)
  → rel-results R (replicate n ■) xs ys
  → rel-Π R′ xs ys
rel-results⇒rel-Π {zero} R⇒R′ (ptt) = tt
rel-results⇒rel-Π {suc n}{⟨ x , xs ⟩}{⟨ y , ys ⟩} R⇒R′ ⟨ Rxy , R[xs,ys] ⟩ =
    ⟨ R⇒R′ x y Rxy , (rel-results⇒rel-Π R⇒R′ R[xs,ys]) ⟩


{- Continuous -----------------------------------------------------------------}

continuous-∈ : (Env → 𝒫 Value) → Env → Value → Set₁
continuous-∈ D ρ v = v ∈ D ρ
   → Σ[ ρ′ ∈ Env ] finite-env ρ′ × ρ′ ⊆ₑ ρ  × v ∈ D ρ′

continuous-env : (Env → 𝒫 Value) → Env → Set₁
continuous-env D ρ = ∀ v → v ∈ D ρ
                     → Σ[ ρ′ ∈ Env ] finite-env ρ′ × ρ′ ⊆ₑ ρ  × v ∈ D ρ′

{- creates an environment that maps each variable x to
   a singleton set of some element in ρ x.  -}
initial-finite-env : (ρ : Env) → (NE-ρ : nonempty-env ρ) → Env
initial-finite-env ρ NE-ρ x
    with NE-ρ x
... | ⟨ v , v∈ρx ⟩ = ⌈ v ⌉

initial-fin : (ρ : Env) → (NE-ρ : nonempty-env ρ)
   → finite-env (initial-finite-env ρ NE-ρ)
initial-fin ρ NE-ρ x
    with NE-ρ x
... | ⟨ v , v∈ρx ⟩ =
      ⟨ v ∷ [] ,
      ⟨ ⟨ (λ {w refl → (here refl)}) , (λ {w (here refl) → refl}) ⟩ , (λ ()) ⟩ ⟩

initial-fin-⊆ : (ρ : Env) → (NE-ρ : nonempty-env ρ)
  → initial-finite-env ρ NE-ρ ⊆ₑ ρ
initial-fin-⊆ ρ NE-ρ x v v∈initial
    with NE-ρ x
... | ⟨ w , w∈ρx ⟩ rewrite v∈initial = w∈ρx

{- single-env maps x to D and any other variable y to something in ρ y. -}
single-env : Var → 𝒫 Value → (ρ : Env) → (NE-ρ : nonempty-env ρ) → Env
single-env x D ρ NE-ρ y
    with x ≟ y
... | yes refl = D
... | no neq
    with NE-ρ y
... | ⟨ v , v∈ρy ⟩ = ⌈ v ⌉    

single-fin : ∀{v}{x}{ρ}{NE-ρ} → finite-env (single-env x ⌈ v ⌉ ρ NE-ρ)
single-fin {v}{x}{ρ}{NE-ρ} y
    with x ≟ y
... | yes refl =
    ⟨ v ∷ [] ,
    ⟨ ⟨ (λ{v₁ refl → (here refl)}) , (λ{v₁ (here refl) → refl}) ⟩ , (λ ()) ⟩ ⟩
... | no neq
    with NE-ρ y
... | ⟨ w , w∈ρy ⟩ =
    ⟨ w ∷ [] ,
    ⟨ ⟨ (λ{v₁ refl → here refl}) , (λ{v₁ (here refl) → refl}) ⟩ , (λ ()) ⟩ ⟩

single-⊆ : ∀{ρ x v}{NE-ρ : nonempty-env ρ}
  →  v ∈ ρ x  →  single-env x ⌈ v ⌉ ρ NE-ρ ⊆ₑ ρ
single-⊆ {ρ}{x}{v}{NE-ρ} v∈ρx y w sing 
    with x ≟ y
... | yes refl rewrite sing = v∈ρx
... | no neq
    with NE-ρ y
... | ⟨ u , u∈ρy ⟩ rewrite sing = u∈ρy

v∈single[xv]x : ∀{v}{x}{ρ}{NE-ρ} → v ∈ single-env x ⌈ v ⌉ ρ NE-ρ x
v∈single[xv]x {v}{x}
    with x ≟ x
... | yes refl = refl
... | no neq = ⊥-elim (neq refl)

continuous-∈⇒⊆ : ∀ E ρ (NE-ρ : nonempty-env ρ)
   → monotone-env E
   → ∀ V → mem V ⊆ E ρ
   → (∀ v → v ∈ mem V → continuous-∈ E ρ v)
   → Σ[ ρ′ ∈ Env ] finite-env ρ′ × ρ′ ⊆ₑ ρ  × mem V ⊆ E ρ′
continuous-∈⇒⊆ E ρ NE-ρ mE [] V⊆E ∀v∈V⇒cont =
   ⟨ initial-finite-env ρ NE-ρ , ⟨ initial-fin ρ NE-ρ ,
   ⟨ initial-fin-⊆ ρ NE-ρ , (λ d ()) ⟩ ⟩ ⟩
continuous-∈⇒⊆ E ρ NE-ρ mE (v ∷ V) v∷V⊆Eρ v∈V⇒cont
    with continuous-∈⇒⊆ E ρ NE-ρ mE V (λ d z → v∷V⊆Eρ d (there z))
                (λ w w∈V w∈Mρ → v∈V⇒cont w (there w∈V) w∈Mρ)
... | ⟨ ρ₁ , ⟨ fρ₁ , ⟨ ρ₁⊆ρ , V⊆Eρ₁ ⟩ ⟩ ⟩
    with v∈V⇒cont v (here refl) (v∷V⊆Eρ v (here refl))
... | ⟨ ρ₂ , ⟨ fρ₂ , ⟨ ρ₂⊆ρ , v∈Eρ₂ ⟩ ⟩ ⟩ =    
    ⟨ ρ₃ , ⟨ (join-finite-env fρ₁ fρ₂) , ⟨ (join-lub ρ₁⊆ρ ρ₂⊆ρ) ,
    G ⟩ ⟩ ⟩
    where
    ρ₃ = ρ₁ ⊔ₑ ρ₂
    G : (d : Value) → mem (v ∷ V) d → d ∈ E ρ₃
    G d (here refl) = mE {ρ₂}{ρ₃} join-⊆-right v v∈Eρ₂
    G d (there m) = mE {ρ₁}{ρ₃} join-⊆-left d (V⊆Eρ₁ d m)

▪-continuous : ∀{D E : Env → 𝒫 Value}{ρ}{NE-ρ : nonempty-env ρ}{w}
  → w ∈ (D ρ) ▪ (E ρ)
  → continuous-env D ρ → continuous-env E ρ
  → monotone-env D → monotone-env E
  → Σ[ ρ₃ ∈ Env ] finite-env ρ₃ × ρ₃ ⊆ₑ ρ × w ∈ (D ρ₃) ▪ (E ρ₃)
▪-continuous {D}{E}{ρ}{NE-ρ}{w} ⟨ V , ⟨ fvs , ⟨ V↦w∈Dρ , ⟨ V⊆Eρ , V≢[] ⟩ ⟩ ⟩ ⟩
    IH-D IH-E mD mE
    with IH-D (V ↦ w) V↦w∈Dρ 
... | ⟨ ρ₁ , ⟨ fρ₁ , ⟨ ρ₁⊆ρ , V↦w∈Dρ₁ ⟩ ⟩ ⟩
    with ((continuous-∈⇒⊆ E ρ NE-ρ mE) V V⊆Eρ (λ v v∈V → IH-E v))
... | ⟨ ρ₂ , ⟨ fρ₂ , ⟨ ρ₂⊆ρ , V⊆Eρ₂ ⟩ ⟩ ⟩ =
   ⟨ ρ₃ , ⟨ join-finite-env fρ₁ fρ₂ , ⟨ join-lub ρ₁⊆ρ ρ₂⊆ρ , w∈D▪Eρ₃ ⟩ ⟩ ⟩ 
    where
    ρ₃ = ρ₁ ⊔ₑ ρ₂
    ρ₁⊆ρ₃ = λ x v z → inj₁ z
    V↦w∈Dρ₃ : (V ↦ w ∈ D ρ₃
    V↦w∈Dρ₃ = mD ρ₁⊆ρ₃ (V ↦ w) V↦w∈Dρ₁
    ρ₂⊆ρ₄ = λ x v z → inj₂ z
    V⊆Eρ₃ : mem V ⊆ E ρ₃
    V⊆Eρ₃ v v∈V = mE ρ₂⊆ρ₄ v (V⊆Eρ₂ v v∈V)
    w∈D▪Eρ₃ : w ∈ (D ρ₃) ▪ (E ρ₃)
    w∈D▪Eρ₃ = ⟨ V , ⟨ fvs , ⟨ V↦w∈Dρ₃ , ⟨ V⊆Eρ₃ , V≢[] ⟩ ⟩ ⟩ ⟩

Λ-continuous : ∀{E : Env  → 𝒫 Value}{ρ}{NE-ρ}{v}
  → v ∈ Λ (λ D → E (D • ρ))
  → (∀ V → V ≢ [] → continuous-env E (mem V • ρ))
  → monotone-env E
  → Σ[ ρ′ ∈ Env ] finite-env ρ′ × ρ′ ⊆ₑ ρ × v ∈ Λ (λ D → E (D • ρ′))
Λ-continuous {E}{ρ}{NE-ρ(V ↦ w} ⟨ w∈EV•ρ , ⟨ V≢[] , fvs≡[] ⟩ ⟩ IH mE
    with IH V V≢[] w w∈EV•ρ
... | ⟨ ρ′ , ⟨ fρ′ , ⟨ ρ′⊆V•ρ , w∈Eρ′ ⟩ ⟩ ⟩ =
    ⟨ (λ x → ρ′ (suc x)) , ⟨ (λ x → fρ′ (suc x)) , ⟨ (λ x → ρ′⊆V•ρ (suc x)) ,
    ⟨ mE{ρ′}{mem V • (λ x → ρ′ (suc x))} G w w∈Eρ′ , ⟨ V≢[] , {!!} ⟩ ⟩ ⟩ ⟩ ⟩
    where G : (x : Var) → ρ′ x ⊆ (mem V • (λ x₁ → ρ′ (suc x₁))) x
          G zero v v∈ρ′x = ρ′⊆V•ρ 0 v v∈ρ′x
          G (suc x) v v∈ρ′x = v∈ρ′x
Λ-continuous {E}{ρ}{NE-ρ}{fv ∷ FV ⊢ν} v∈Λ IH mE =
  ⟨ initial-finite-env ρ NE-ρ , ⟨ initial-fin ρ NE-ρ , ⟨ initial-fin-⊆ ρ NE-ρ ,
      tt ⟩ ⟩ ⟩

cons-continuous : ∀{D E : Env → 𝒫 Value}{ρ}{NE-ρ : nonempty-env ρ}{w : Value}
  → w ∈ 〘 D ρ , E ρ 〙
  → continuous-env D ρ → continuous-env E ρ → monotone-env D → monotone-env E
  → Σ[ ρ₃ ∈ Env ] finite-env ρ₃ × ρ₃ ⊆ₑ ρ × w ∈ 〘 D ρ₃ , E ρ₃ 〙
cons-continuous {D} {E} {ρ} {NE-ρ} {⦅ u , v ⦆} ⟨ u∈Dρ , v∈Eρ ⟩ cD cE mD mE
    with cD u u∈Dρ 
... | ⟨ ρ₁ , ⟨ fρ₁ , ⟨ ρ₁⊆ρ , u∈Dρ₁ ⟩ ⟩ ⟩
    with cE v v∈Eρ 
... | ⟨ ρ₂ , ⟨ fρ₂ , ⟨ ρ₂⊆ρ , v∈Eρ₂ ⟩ ⟩ ⟩ =
    ⟨ ρ₃ , ⟨ join-finite-env fρ₁ fρ₂ , ⟨ join-lub ρ₁⊆ρ ρ₂⊆ρ ,
    ⟨ u∈Dρ₃ , v∈Dρ₃ ⟩ ⟩ ⟩ ⟩
    where
    ρ₃ = ρ₁ ⊔ₑ ρ₂
    ρ₁⊆ρ₃ = λ x v z → inj₁ z
    u∈Dρ₃ = mD ρ₁⊆ρ₃ u u∈Dρ₁
    ρ₂⊆ρ₃ = λ x v z → inj₂ z
    v∈Dρ₃ = mE ρ₂⊆ρ₃ v v∈Eρ₂

car-continuous : ∀{D : Env → 𝒫 Value}{ρ}{NE-ρ : nonempty-env ρ}{u : Value}
  → u ∈ car (D ρ) → continuous-env D ρ → monotone-env D
  → Σ[ ρ₃ ∈ Env ] finite-env ρ₃ × ρ₃ ⊆ₑ ρ × u ∈ car (D ρ₃)
car-continuous {D} {ρ} {NE-ρ} {u} ⟨ v , uv∈Dρ ⟩ cD mD
    with cD ⦅ u , v ⦆ uv∈Dρ 
... | ⟨ ρ₁ , ⟨ fρ₁ , ⟨ ρ₁⊆ρ , uv∈Dρ₁ ⟩ ⟩ ⟩ =
      ⟨ ρ₁ , ⟨ fρ₁ , ⟨ ρ₁⊆ρ , ⟨ v , mD (λ x d z → z) ⦅ u , v ⦆ uv∈Dρ₁ ⟩ ⟩ ⟩ ⟩

cdr-continuous : ∀{D : Env → 𝒫 Value}{ρ}{NE-ρ : nonempty-env ρ}{u : Value}
  → u ∈ cdr (D ρ) → continuous-env D ρ → monotone-env D
  → Σ[ ρ₃ ∈ Env ] finite-env ρ₃ × ρ₃ ⊆ₑ ρ × u ∈ cdr (D ρ₃)
cdr-continuous {D} {ρ} {NE-ρ} {v} ⟨ u , uv∈Dρ ⟩ cD mD
    with cD ⦅ u , v ⦆ uv∈Dρ 
... | ⟨ ρ₁ , ⟨ fρ₁ , ⟨ ρ₁⊆ρ , uv∈Dρ₁ ⟩ ⟩ ⟩ =
      ⟨ ρ₁ , ⟨ fρ₁ , ⟨ ρ₁⊆ρ , ⟨ u , mD (λ x d z → z) ⦅ u , v ⦆ uv∈Dρ₁ ⟩ ⟩ ⟩ ⟩

mono-envs : ∀{n} → (Env → Π n (𝒫 Value)) → Set₁
mono-envs {n} Ds = ∀{ρ ρ′} → ρ ⊆ₑ ρ′ → ⊆-results (replicate n ■) (Ds ρ) (Ds ρ′)

continuous-envs : ∀{n} → (Env → Π n (𝒫 Value)) → Env → Set₁
continuous-envs {n} Ds ρ = ∀ v → v ∈ 𝒯 n (Ds ρ)
                     → Σ[ ρ′ ∈ Env ] finite-env ρ′ × ρ′ ⊆ₑ ρ  × v ∈ 𝒯 n (Ds ρ′)

next-Ds : ∀{n} → (Env → Π (suc n) (𝒫 Value)) → (Env → Π n (𝒫 Value))
next-Ds Ds ρ
    with Ds ρ
... | ⟨ D , Ds′ ⟩ = Ds′

next-Ds-proj₂ : ∀{n}{Ds : Env → Π (suc n) (𝒫 Value)}{ρ}
   → next-Ds Ds ρ ≡ proj₂ (Ds ρ)
next-Ds-proj₂ {n} {Ds} {ρ}
    with Ds ρ
... | ⟨ a , b ⟩ = refl

next-mono-envs : ∀{n}{Ds : Env → Π (suc n) (𝒫 Value)}
   → mono-envs Ds → mono-envs (next-Ds Ds)
next-mono-envs {zero} {Ds} mDs {ρ} {ρ′} _ = ptt
next-mono-envs {suc n} {Ds} mDs {ρ} {ρ′} ρ⊆ρ′
    with Ds ρ | Ds ρ′ | mDs {ρ} {ρ′} ρ⊆ρ′
... | ⟨ Dρ , Dsρ ⟩ | ⟨ Dρ′ , Dsρ′ ⟩ | ⟨ _ , mDs′ ⟩ = mDs′

proj₁-mono-envs : ∀{n}{Ds : Env → Π (suc n) (𝒫 Value)}{ρ}{ρ′}
   → ρ ⊆ₑ ρ′  → mono-envs Ds → proj₁ (Ds ρ) ⊆ proj₁ (Ds ρ′)
proj₁-mono-envs {n}{Ds}{ρ}{ρ′} ρ⊆ρ′ mDs
    with Ds ρ | mDs {ρ}{ρ′} ρ⊆ρ′
... | ⟨ Dρ , Dsρ ⟩ | ⟨ lift mD , _ ⟩ = mD

next-NE-Ds : ∀{n}{Ds : Env → Π (suc n) (𝒫 Value)}{ρ}
  → NE-Π (Ds ρ)
  → NE-Π (next-Ds Ds ρ)
next-NE-Ds{n}{Ds}{ρ} NE-Ds
    with Ds ρ | NE-Ds
... | ⟨ Dρ , Dsρ ⟩ | ⟨ NE-D , NE-Ds′ ⟩ = NE-Ds′

next-cont-envs : ∀{n}{Ds : Env → Π (suc n) (𝒫 Value)}
     {ρ}{NE-ρ : nonempty-env ρ}{w}
   → proj₁ (Ds ρ) w
   → continuous-envs Ds ρ
   → continuous-envs (next-Ds Ds) ρ
next-cont-envs {n} {Ds} {ρ}{NE-ρ}{w} w∈Dsρ cDs u u∈
    with Ds ρ | cDs | u∈ 
... | ⟨ D , Ds′ ⟩ | cDDs | u∈′ 
    with v∈𝒯⇒v≡∥vs∥ u∈′
... | ⟨ vs , refl ⟩
    with cDDs ∥ w ∷ vs ∥ ⟨ w∈Dsρ , u∈′ ⟩
... | ⟨ ρ′ , ⟨ fρ′ , ⟨ ρ′⊆ρ , ⟨ aaa , vs∈Dsρ′ ⟩ ⟩ ⟩ ⟩ =
    ⟨ ρ′ , ⟨ fρ′ , ⟨ ρ′⊆ρ , vs∈Dsρ′ ⟩ ⟩ ⟩

𝒯-continuous : ∀{n}{Ds : Env → Π n (𝒫 Value)}{ρ}{NE-ρ : nonempty-env ρ}
    {u : Value}
  → u ∈ 𝒯 n (Ds ρ) → continuous-envs Ds ρ → mono-envs Ds
  → Σ[ ρ₃ ∈ Env ] finite-env ρ₃ × ρ₃ ⊆ₑ ρ × u ∈ 𝒯 n (Ds ρ₃)
𝒯-continuous {zero} {Ds} {ρ} {NE-ρ} {u} u∈𝒯Ds cDs mDs 
    with Ds (initial-finite-env ρ NE-ρ) | u
... | ptt | ∥ [] ∥ =
  ⟨ (initial-finite-env ρ NE-ρ) , ⟨ initial-fin ρ NE-ρ ,
  ⟨ initial-fin-⊆ ρ NE-ρ , tt ⟩ ⟩ ⟩
𝒯-continuous {suc n} {Ds} {ρ} {NE-ρ} {∥ v ∷ vs ∥} ⟨ v∈Dρ , vs∈𝒯Dsρ ⟩ cDs mDs 
    with 𝒯-continuous{n}{next-Ds Ds}{ρ}{NE-ρ}{∥ vs ∥}
       (subst (λ X → ∥ vs ∥ ∈ 𝒯 n X) (sym (next-Ds-proj₂{n}{Ds}{ρ})) vs∈𝒯Dsρ)
       (next-cont-envs{NE-ρ = NE-ρ}{w = v} v∈Dρ cDs)
       (λ {ρ}{ρ′} → next-mono-envs mDs {ρ}{ρ′})
... | ⟨ ρ₁ , ⟨ fρ₁ , ⟨ ρ₁⊆ρ , vs∈𝒯Dsρ₁ ⟩ ⟩ ⟩
    with cDs ∥ v ∷ vs ∥ ⟨ v∈Dρ , vs∈𝒯Dsρ ⟩ 
... | ⟨ ρ₂ , ⟨ fρ₂ , ⟨ ρ₂⊆ρ , ⟨ v∈Dρ₂ , vs∈Dsρ₂ ⟩ ⟩ ⟩ ⟩
    with  mDs {ρ₁}{ρ₁ ⊔ₑ ρ₂} (λ x d z → inj₁ z)
... | ⟨ _ , Dsρ₁⊆Dsρ₃ ⟩ 
    with  mDs {ρ₂}{ρ₁ ⊔ₑ ρ₂} (λ x d z → inj₂ z)
... | ⟨ lift Dρ₂⊆Dρ₃ , _ ⟩ =
    let v∈Dρ₃ = Dρ₂⊆Dρ₃ v v∈Dρ₂ in
    let vs∈Dsρ₃ = 𝒯-mono-⊆ (rel-results⇒rel-Π ⊆-result⇒⊆ Dsρ₁⊆Dsρ₃)
                            ∥ vs ∥ vs∈𝒯Dsρ₁ in
    ⟨ ρ₃ , ⟨ (join-finite-env fρ₁ fρ₂) , ⟨ (join-lub ρ₁⊆ρ ρ₂⊆ρ) ,
    ⟨ v∈Dρ₃ , vs∈Dsρ₃ ⟩ ⟩ ⟩ ⟩
    where
    ρ₃ = ρ₁ ⊔ₑ ρ₂

proj-continuous : ∀{D : Env → 𝒫 Value}{ρ}{NE-ρ : nonempty-env ρ}{u : Value}{i}
  → u ∈ proj (D ρ) i → continuous-env D ρ → monotone-env D
  → Σ[ ρ₃ ∈ Env ] finite-env ρ₃ × ρ₃ ⊆ₑ ρ × u ∈ proj (D ρ₃) i
proj-continuous {D} {ρ} {NE-ρ} {u} {i} ⟨ vs , ⟨ lt , ⟨ vs∈Dρ , refl ⟩ ⟩ ⟩ cD mD
    with cD ∥ vs ∥ vs∈Dρ
... | ⟨ ρ′ , ⟨ fρ′ , ⟨ ρ′⊆ρ , vs∈Dρ′ ⟩ ⟩ ⟩ =     
    ⟨ ρ′ , ⟨ fρ′ , ⟨ ρ′⊆ρ ,
    ⟨ vs , ⟨ lt , ⟨ mD (λ x d z → z) ∥ vs ∥ vs∈Dρ′ , refl ⟩ ⟩ ⟩ ⟩ ⟩ ⟩

ℒ-continuous : ∀{D : Env → 𝒫 Value}{ρ}{NE-ρ : nonempty-env ρ}{u : Value}
  → u ∈ ℒ (D ρ)  →  continuous-env D ρ  →  monotone-env D
  → Σ[ ρ₃ ∈ Env ] finite-env ρ₃ × ρ₃ ⊆ₑ ρ × u ∈ ℒ (D ρ₃)
ℒ-continuous {D} {ρ} {NE-ρ} {left U} ⟨ U≢[] , U⊆Dρ ⟩ cD mD
    with continuous-∈⇒⊆ D ρ NE-ρ mD U U⊆Dρ (λ v v∈Dρ → cD v)
... | ⟨ ρ₁ , ⟨ fρ₁ , ⟨ ρ₁⊆ρ , U⊆Dρ₁ ⟩ ⟩ ⟩ =
    ⟨ ρ₁ , ⟨ fρ₁ , ⟨ ρ₁⊆ρ , ⟨ U≢[] , U⊆Dρ₁ ⟩ ⟩ ⟩ ⟩

ℛ-continuous : ∀{D : Env → 𝒫 Value}{ρ}{NE-ρ : nonempty-env ρ}{u : Value}
  → u ∈ ℛ (D ρ)  →  continuous-env D ρ  →  monotone-env D
  → Σ[ ρ₃ ∈ Env ] finite-env ρ₃ × ρ₃ ⊆ₑ ρ × u ∈ ℛ (D ρ₃)
ℛ-continuous {D} {ρ} {NE-ρ} {right U} ⟨ U≢[] , U⊆Dρ ⟩ cD mD
    with continuous-∈⇒⊆ D ρ NE-ρ mD U U⊆Dρ (λ v v∈Dρ → cD v)
... | ⟨ ρ₁ , ⟨ fρ₁ , ⟨ ρ₁⊆ρ , U⊆Dρ₁ ⟩ ⟩ ⟩ =
    ⟨ ρ₁ , ⟨ fρ₁ , ⟨ ρ₁⊆ρ , ⟨ U≢[] , U⊆Dρ₁ ⟩ ⟩ ⟩ ⟩

𝒞-continuous : ∀{D E F : Env → 𝒫 Value}{ρ : Env}{NE-ρ : nonempty-env ρ}{u}
  → u ∈ 𝒞 (D ρ) (Λ (λ X → E (X • ρ))) (Λ (λ X → F (X • ρ)))
  → continuous-env D ρ → monotone-env D
  → (∀ V → V ≢ [] → continuous-env E (mem V • ρ)) → monotone-env E
  → (∀ V → V ≢ [] → continuous-env F (mem V • ρ)) → monotone-env F
  → Σ[ ρ′ ∈ Env ] finite-env ρ′ × ρ′ ⊆ₑ ρ
      × u ∈ 𝒞 (D ρ′) (Λ (λ X → E (X • ρ′))) (Λ (λ X → F (X • ρ′)))
𝒞-continuous {D}{E}{F} {ρ} {NE-ρ} {w}
    (inj₁ ⟨ V , ⟨ fvs , ⟨ inlV∈D , ⟨ w∈EV•ρ , ⟨ V≢[] , fvs≡[] ⟩ ⟩ ⟩ ⟩ ⟩)
    cD mD cE mE cF mF 
    with cD (left v) inlV∈D
... | ⟨ ρ₁ , ⟨ fρ₁ , ⟨ ρ₁⊆ρ , inlV∈Dρ₁ ⟩ ⟩ ⟩
    with cE V V≢[] w w∈EV•ρ
... | ⟨ ρ₂ , ⟨ fρ₂ , ⟨ ρ₂⊆V•ρ , w∈Eρ₂ ⟩ ⟩ ⟩ =
    ⟨ ρ₃ , ⟨ join-finite-env fρ₁ fρ₂′ , ⟨ join-lub ρ₁⊆ρ ρ₂′⊆ρ , u∈𝒞ρ₃ ⟩ ⟩ ⟩
    where
    ρ₂′ = (λ x → ρ₂ (suc x))
    ρ₃ = ρ₁ ⊔ₑ ρ₂′ 
    fρ₂′ : finite-env ρ₂′
    fρ₂′ x = fρ₂ (suc x)
    ρ₂′⊆ρ : ρ₂′ ⊆ₑ ρ
    ρ₂′⊆ρ x = ρ₂⊆V•ρ (suc x)
    G : (x : ℕ) (d : Value) → ρ₂ x d → (mem V • ρ₃) x d
    G zero d d∈ρ₂x = ρ₂⊆V•ρ zero d d∈ρ₂x
    G (suc x) d d∈ρ₂x = inj₂ d∈ρ₂x
    u∈𝒞ρ₃ = inj₁ ⟨ V , ⟨ fvs , ⟨ (mD (λ x d z → inj₁ z) (left v) inlV∈Dρ₁) ,
                  ⟨ (mE G w w∈Eρ₂) ,
                    ⟨ V≢[] , {!!} ⟩ ⟩ ⟩ ⟩ ⟩
𝒞-continuous {D}{E}{F} {ρ} {NE-ρ} {w}
    (inj₂ ⟨ V , ⟨ fvs , ⟨ inrV∈D , ⟨ w∈FV•ρ , ⟨ V≢[] , fvs≡[] ⟩ ⟩ ⟩ ⟩ ⟩)
    cD mD cE mE cF mF 
    with cD (right v) inrV∈D
... | ⟨ ρ₁ , ⟨ fρ₁ , ⟨ ρ₁⊆ρ , inrV∈Dρ₁ ⟩ ⟩ ⟩
    with cF V V≢[] w w∈FV•ρ
... | ⟨ ρ₂ , ⟨ fρ₂ , ⟨ ρ₂⊆V•ρ , w∈Fρ₂ ⟩ ⟩ ⟩ =
    ⟨ ρ₃ , ⟨ join-finite-env fρ₁ fρ₂′ , ⟨ join-lub ρ₁⊆ρ ρ₂′⊆ρ , u∈𝒞ρ₃ ⟩ ⟩ ⟩
    where
    ρ₂′ = (λ x → ρ₂ (suc x))
    ρ₃ = ρ₁ ⊔ₑ ρ₂′ 
    fρ₂′ : finite-env ρ₂′
    fρ₂′ x = fρ₂ (suc x)
    ρ₂′⊆ρ : ρ₂′ ⊆ₑ ρ
    ρ₂′⊆ρ x = ρ₂⊆V•ρ (suc x)
    G : (x : ℕ) (d : Value) → ρ₂ x d → (mem V • ρ₃) x d
    G zero d d∈ρ₂x = ρ₂⊆V•ρ zero d d∈ρ₂x
    G (suc x) d d∈ρ₂x = inj₂ d∈ρ₂x
    u∈𝒞ρ₃ = inj₂ ⟨ V , ⟨ fvs , ⟨ (mD (λ x d z → inj₁ z) (right v) inrV∈Dρ₁) ,
                  ⟨ (mF G w w∈Fρ₂) ,
                    ⟨ V≢[] , {!!} ⟩ ⟩ ⟩ ⟩ ⟩



-}
-}

module proof.Compiler.Model.Graph.Prim where

open import Compiler.Model.Graph.Prim public

open import Framework.Primitives using (Int)
open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.DOpSig
open import proof.Framework.GraphModel.DenotProperties
open import proof.Framework.GraphModel.Domain
open import proof.Framework.GraphModel.Continuity using (Mono; Cont; one; done; approx-join; join-l; join-r)
open import Compiler.Lang.Prim using (Prim; Out; int; bool; δ)

open import Data.Bool using (true; false)
open import Data.Integer using (ℤ)
open import Data.List using (_∷_; [])
open import Data.Product using (_×_; Σ-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Unit using (tt)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Level using (lift)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

{- Monotonicity, consistency and continuity --------------------------------}

primD-mono : ∀ p → monotone (■ ∷ ■ ∷ []) ■ (primD p)
primD-mono p ⟨ D , ⟨ E , _ ⟩ ⟩ ⟨ D' , ⟨ E' , _ ⟩ ⟩ ⟨ lift D⊆ , ⟨ lift E⊆ , _ ⟩ ⟩ =
  lift (λ { v ⟨ n , ⟨ m , ⟨ n∈ , ⟨ m∈ , eq ⟩ ⟩ ⟩ ⟩ → ⟨ n , ⟨ m , ⟨ D⊆ _ n∈ , ⟨ E⊆ _ m∈ , eq ⟩ ⟩ ⟩ ⟩ })

out-~ : ∀ o → out o ~ out o
out-~ (int n) = ⟨ refl , refl ⟩
out-~ (bool true) = tt
out-~ (bool false) = tt

primD-consis : ∀ p → consistent _~_ (■ ∷ ■ ∷ []) ■ (primD p)
primD-consis p ⟨ D , ⟨ E , _ ⟩ ⟩ ⟨ D' , ⟨ E' , _ ⟩ ⟩ ⟨ lift D~ , ⟨ lift E~ , _ ⟩ ⟩ = lift G
  where
  G : Every _~_ (primD p ⟨ D , ⟨ E , ptt ⟩ ⟩) (primD p ⟨ D' , ⟨ E' , ptt ⟩ ⟩)
  G _ _ ⟨ n , ⟨ m , ⟨ n∈ , ⟨ m∈ , refl ⟩ ⟩ ⟩ ⟩ ⟨ n' , ⟨ m' , ⟨ n'∈ , ⟨ m'∈ , refl ⟩ ⟩ ⟩ ⟩
      with D~ _ _ n∈ n'∈ | E~ _ _ m∈ m'∈
  ... | ⟨ refl , refl ⟩ | ⟨ refl , refl ⟩ = out-~ (δ p n m)

primD-cont : ∀ p {E₁ E₂ ρ} → Mono E₁ → Mono E₂ → Cont E₁ ρ → Cont E₂ ρ
  → Cont (λ ρ → primD p ⟨ E₁ ρ , ⟨ E₂ ρ , ptt ⟩ ⟩) ρ
primD-cont p {E₁}{E₂} m₁ m₂ c₁ c₂ v ⟨ n , ⟨ m , ⟨ n∈ , ⟨ m∈ , eq ⟩ ⟩ ⟩ ⟩
    with one E₁ c₁ n∈ | one E₂ c₂ m∈
... | ⟨ a , n∈′ ⟩ | ⟨ b , m∈′ ⟩ =
  done (λ ρ → primD p ⟨ E₁ ρ , ⟨ E₂ ρ , ptt ⟩ ⟩) (approx-join a b) v
    ⟨ n , ⟨ m , ⟨ m₁ (join-l a b) _ n∈′ , ⟨ m₂ (join-r a b) _ m∈′ , eq ⟩ ⟩ ⟩ ⟩

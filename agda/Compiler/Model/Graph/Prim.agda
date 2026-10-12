{-

  The graph-model meaning of this compiler's primitive operations
  (Compiler.Lang.Prim): the value of a primitive's result, the operator
  primD, and its monotonicity, consistency and continuity. The rest of
  the domain and its operators are language independent (GraphModel/).

-}

module Compiler.Model.Graph.Prim where

open import Primitives using (Int)
open import SetsAsPredicates
open import NewDOpSig
open import NewDenotProperties
open import GraphModel.Domain
open import GraphModel.Continuity using (Mono; Cont; one; done; approx-join; join-l; join-r)
open import Compiler.Lang.Prim using (Prim; Out; int; bool; δ)

open import Data.Bool using (true; false)
open import Data.Integer using (ℤ)
open import Data.List using (_∷_; [])
open import Data.Product using (_×_; Σ-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Unit using (tt)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Level using (lift)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

{- the value of the result of a primitive: eq returns left ⟨⟩ for true
   and right ⟨⟩ for false -}
out : Out → Value
out (int n) = const {Int} n
out (bool true) = left ⟨⟩
out (bool false) = right ⟨⟩

{- a primitive applies to the integers in its operands -}
primD : Prim → DOp (𝒫 Value) (■ ∷ ■ ∷ [])
primD p ⟨ D , ⟨ E , _ ⟩ ⟩ v =
  Σ[ n ∈ ℤ ] Σ[ m ∈ ℤ ] const {Int} n ∈ D × const {Int} m ∈ E × v ≡ out (δ p n m)

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

{-

  The semantics of Impᵀ (Language/Typed/Imp.agda) in the graph model, in
  continuation-passing style, as Semantics/Graph/ImpK.agda. The frame σ
  gives each slot (a typed index, position idx) a meaning; since the
  frame is typed, an expression never changes the slots it can see, so
  a continuation κ takes only the value of the expression. Atoms and
  simple expressions (𝒜, 𝒮, shared with CFGᵀ) are the operators of
  Clos5ᵀ on atoms (Semantics/Graph/Typed/Clos5.agda).

  x := e₁; e₂ runs e₁ with the continuation that is strict in its value
  D like let in Clos5ᵀ: ⋆ ⟨ Λ F , D ⟩, where F X runs e₂ with X in the
  next slot and then κ; case is 𝒞, each branch running with κ. The code
  of a definition runs its body in a frame with its argument and
  environment, with the continuation that returns the value; definitions
  are given meaning as in Clos5ᵀ (tables).

-}

module Semantics.Graph.Typed.Imp where

open import Framework.GraphModel.SetsAsPredicates
open import Framework.GraphModel.DOpSig
open import Framework.GraphModel.Domain
open import Framework.GraphModel.Ops renaming (inl to inlD; inr to inrD)
open import Framework.GraphModel.Env using (Env)
open import Semantics.Graph.Prim using (primD)
open import Semantics.Graph.Typed.Ops
open import Language.Typed.Type
open import Language.Typed.Imp

open import Data.List using (List; []; _∷_; replicate)
open import Data.List.Relation.Unary.All using (All)
open import Data.Nat using (ℕ)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Product using () renaming (_,_ to ⟨_,_⟩)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)

𝒜 : ∀ {Σ Δ A} → Atm Σ Δ A → Table Σ → Env Value → 𝒫 Value
𝒜 (var x) T σ = σ (idx x)
𝒜 (lit B c) T σ = ℬ B c ptt
𝒜 (ref f) T σ = T f

𝒜s : ∀ {Σ Δ n} → Vec (Atm Σ Δ Any) n → Table Σ → Env Value → Results (𝒫 Value) (replicate n ■)
𝒜s [] T σ = ptt
𝒜s (a ∷ as) T σ = ⟨ 𝒜 a T σ , 𝒜s as T σ ⟩

𝒮 : ∀ {Σ Δ A} → Simple Σ Δ A → Table Σ → Env Value → 𝒫 Value
𝒮 (atm a) T σ = 𝒜 a T σ
𝒮 (pack a b) T σ = pair ⟨ 𝒜 a T σ , ⟨ 𝒜 b T σ , ptt ⟩ ⟩
𝒮 (callc f a) T σ = ⋆ ⟨ ⋆ ⟨ car ⟨ 𝒜 f T σ , ptt ⟩ , ⟨ cdr ⟨ 𝒜 f T σ , ptt ⟩ , ptt ⟩ ⟩ , ⟨ 𝒜 a T σ , ptt ⟩ ⟩
𝒮 (tuple {n = n} as) T σ = 𝒯 n (𝒜s as T σ)
𝒮 (get i a) T σ = proj i ⟨ 𝒜 a T σ , ptt ⟩
𝒮 (inl a) T σ = inlD ⟨ 𝒜 a T σ , ptt ⟩
𝒮 (inr a) T σ = inrD ⟨ 𝒜 a T σ , ptt ⟩
𝒮 (prim p a b) T σ = primD p ⟨ 𝒜 a T σ , ⟨ 𝒜 b T σ , ptt ⟩ ⟩
𝒮 (inject G a) T σ = 𝒜 a T σ
𝒮 (project t a) T σ = projectᵍ fun₄ t (𝒜 a T σ)

⟦_⟧ᴷ : ∀ {Σ Δ A} → Exp Σ Δ A → Table Σ → Env Value → (𝒫 Value → 𝒫 Value) → 𝒫 Value
⟦ simple s ⟧ᴷ T σ κ = κ (𝒮 s T σ)
⟦ assign e₁ e₂ ⟧ᴷ T σ κ = ⟦ e₁ ⟧ᴷ T σ λ D → ⋆ ⟨ Λ ⟨ (λ X → ⟦ e₂ ⟧ᴷ T (X • σ) κ) , ptt ⟩ , ⟨ D , ptt ⟩ ⟩
⟦ case a e₁ e₂ ⟧ᴷ T σ κ =
  𝒞 ⟨ 𝒜 a T σ , ⟨ (λ X → ⟦ e₁ ⟧ᴷ T (X • σ) κ) , ⟨ (λ X → ⟦ e₂ ⟧ᴷ T (X • σ) κ) , ptt ⟩ ⟩ ⟩

{- the function whose body is e, given the table T -}
code′ : ∀ {Σ} → Table Σ → ∀ {n} → Exp Σ (Any ∷ ⟪ tup n ⟫ ∷ []) Any → 𝒫 Value
code′ T e = Λ ⟨ (λ X → Λ ⟨ (λ Y → ⟦ e ⟧ᴷ T (Y • X • λ _ → init) (λ D → D)) , ptt ⟩) , ptt ⟩

table : ∀ {Σ} → All (λ n → Exp Σ (Any ∷ ⟪ tup n ⟫ ∷ []) Any) Σ → Table Σ
table = tables code′

{- the meaning of a whole program: the value of main -}
⟦_⟧ₚ : Program → 𝒫 Value
⟦ program ds e ⟧ₚ = ⟦ e ⟧ᴷ (table ds) (λ _ → init) (λ D → D)

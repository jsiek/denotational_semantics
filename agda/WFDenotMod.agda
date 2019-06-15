open import Data.Nat using (ℕ; zero; suc)

open import Structures
import ValueStructAux
import OrderingAux
import ConsistentAux

module WFDenotMod (D : ValueStruct) (V : ValueOrdering D) (C : Consistent D V)
  where

  open ValueStruct D
  open ValueOrdering V
  open Consistent C
  open ValueStructAux D
  open OrderingAux D V using (_`⊑_)
  open ConsistentAux D V C using (_~′_)

  record Ideal (𝒟 : Value → Set) : Set₁ where
    field
      ⊑-closed : ∀{v w} → 𝒟 v → w ⊑ v → 𝒟 w
      ⊔-closed : ∀{u v} → 𝒟 u → 𝒟 v → 𝒟 (u ⊔ v)
      ~-closed : ∀{u v} → 𝒟 u → 𝒟 v → u ~ v
      

  record WFDenot (Γ : ℕ) (D : Denotation Γ) : Set₁ where
    field
      ⊑-env : ∀{γ δ}{v} → D γ v → γ `⊑ δ → D δ v
      ⊑-closed : ∀{γ}{v w} → D γ v → w ⊑ v → D γ w
      ⊔-closed : ∀{γ δ u v} → γ ~′ δ
               → D γ u → D δ v → D γ (u ⊔ v)
      ~-closed : ∀{γ δ u v} → γ ~′ δ
               → D γ u → D δ v → u ~ v



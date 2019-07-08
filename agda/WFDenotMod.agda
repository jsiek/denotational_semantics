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
  open ConsistentAux D V C using (_~′_; WFEnv)

  record Ideal (𝒟 : Value → Set) : Set₁ where
    field
      ⊑-closed : ∀{v w} → 𝒟 v → w ⊑ v → 𝒟 w
      ⊔-closed : ∀{u v} → 𝒟 u → 𝒟 v → 𝒟 (u ⊔ v)
      ~-closed : ∀{u v} → 𝒟 u → 𝒟 v → u ~ v
      


  record WFDenot (Γ : ℕ) (D : Denotation Γ) : Set₁ where
    field
      ⊑-env : ∀{γ δ}{v}
               → WFEnv γ → WFEnv δ → wf v
                → γ `⊑ δ → D γ v → D δ v
      ⊑-closed : ∀{γ}{v w}
               → WFEnv γ → wf v → wf w
               → w ⊑ v → D γ v → D γ w
      ⊔-closed : ∀{γ u v}
               → WFEnv γ → wf u → wf v
               → D γ u → D γ v → D γ (u ⊔ v)
      ~-closed : ∀{γ δ u v}
               → WFEnv γ → WFEnv δ → γ ~′ δ → wf u → wf v
               → D γ u → D δ v → u ~ v



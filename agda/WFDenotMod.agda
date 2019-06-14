open import Structures
import DomainAux
import OrderingAux

module WFDenotMod (D : Domain) (V : ValueOrdering D) where

  open Domain D
  open ValueOrdering V
  open DomainAux D
  open OrderingAux D V

  record WFDenot (Γ : ℕ) (D : Denotation Γ) : Set₁ where
    field
      ⊑-env : ∀{γ δ}{v} → D γ v → γ `⊑ δ → D δ v
      ⊑-closed : ∀{γ}{v w} → D γ v → w ⊑ v → D γ w
      ⊔-closed : ∀{γ δ u v} → γ ~′ δ
               → D γ u → D δ v → D γ (u ⊔ v)
      ~-closed : ∀{γ δ u v} → γ ~′ δ
               → D γ u → D δ v → u ~ v



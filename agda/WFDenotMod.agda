open import Data.Nat using (ℕ; zero; suc)

open import Structures
import ValueStructAux
import OrderingAux
import ConsistentAux

module WFDenotMod (D : ValueStruct) (V : ValueOrdering D) where

  open ValueStruct D
  open ValueOrdering V
  open ValueStructAux D using (_⊑′_)
  open OrderingAux D V

  record WFDenot (Γ : ℕ) (D : Denotation Γ) : Set₁ where
    field
      ⊑-env : ∀{γ δ}{v} → D γ v → γ `⊑ δ → D δ v
      ⊑-closed : ∀{γ}{v w} → D γ v → w ⊑ v → D γ w
      ⊔-closed : ∀{γ δ u v} → γ ~′ δ
               → D γ u → D δ v → D γ (u ⊔ v)
      ~-closed : ∀{γ δ u v} → γ ~′ δ
               → D γ u → D δ v → u ~ v



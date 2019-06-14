module ConsistentAux (D : Domain) (V : ValueOrdering D) (C : Consistent D V)
  where
  open Domain D
  open ValueOrdering V
  open Consistent C
  open DomainAux D

  _~′_ : ∀{Γ} → Env Γ → Env Γ → Set
  _~′_ {Γ} γ δ = ∀{x : Var Γ} → γ x ~ δ x

  app-consistency : ∀{u₁ u₂ v₁ w₁ v₂ w₂}
        → u₁ ~ u₂
        → v₁ ~ v₂
        → v₁ ↦ w₁ ⊑ u₁
        → v₂ ↦ w₂ ⊑ u₂
        → w₁ ~ w₂
  app-consistency {u₁}{u₂}{v₁}{w₁}{v₂}{w₂} u₁~u₂ v₁~v₂ v₁↦w₁⊑u₁ v₂↦w₂⊑u₂
      with ~-⊑ u₁~u₂ v₁↦w₁⊑u₁ v₂↦w₂⊑u₂
  ... | v₁↦w₁~v₂↦w₂ 
      with ~-↦ {v₁}{w₁}{v₂}{w₂} v₁↦w₁~v₂↦w₂ 
  ... | inj₁ ⟨ _ , w₁~w₂ ⟩ = w₁~w₂
  ... | inj₂ v₁~̸v₂ = ⊥-elim (contradiction v₁~v₂ v₁~̸v₂)



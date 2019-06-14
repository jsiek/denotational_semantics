module CurryApplyCong
  (D : Domain) (V : ValueOrdering D) 
  (_●_ : ∀{Γ} → DomainAux.Denotation D Γ
       → DomainAux.Denotation D Γ → DomainAux.Denotation D Γ)
  (ℱ : ∀{Γ} → DomainAux.Denotation D (suc Γ) → DomainAux.Denotation D Γ)
  (MB : ModelMod.LambdaModelBasics D V _●_ ℱ)
  where
  open Domain D
  open DomainAux D
  open OrderingAux D V

  open ModelMod.LambdaModelBasics MB
  open ModelMod.ModelCurry model_curry


  ℱ-cong : ∀{Γ}{D D′ : Denotation (suc Γ)}
         → D ≃ D′
           -----------
         → ℱ D ≃ ℱ D′
  ℱ-cong {Γ}{D}{D′} D≃D′ γ v =
    ⟨ (ℱ-≲ λ {w} {v'} x → proj₁ (D≃D′ (γ `, w) v') x) {v} ,
      (ℱ-≲ λ {w} {v'} x → proj₂ (D≃D′ (γ `, w) v') x) {v} ⟩

  ●-cong : ∀{Γ}{D₁ D₁′ D₂ D₂′ : Denotation Γ}
     → D₁ ≃ D₁′ → D₂ ≃ D₂′
     → (D₁ ● D₂) ≃ (D₁′ ● D₂′)
  ●-cong {Γ}{D₁}{D₁′}{D₂}{D₂′} d1 d2 γ v =
     let to = ●-≲ {Γ}{Γ}{γ}{γ}{D₁}{D₂}{D₁′}{D₂′}
                 (λ {w} D₁γw → proj₁ (d1 γ w) D₁γw)
                 (λ {w} D₂γw → proj₁ (d2 γ w) D₂γw) {v} in
     let from = ●-≲ {Γ}{Γ}{γ}{γ}{D₁′}{D₂′}{D₁}{D₂}
                 (λ {w} D₁γw → proj₂ (d1 γ w) D₁γw)
                 (λ {w} D₂γw → proj₂ (d2 γ w) D₂γw) {v} in
     ⟨ to , from ⟩


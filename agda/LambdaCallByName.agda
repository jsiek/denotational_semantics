
module LambdaCallByName where

  infixl 7 _●_
  _●_ : ∀{Γ} → Denotation Γ → Denotation Γ → Denotation Γ
  _●_ {Γ} D₁ D₂ γ w = w ⊑ ⊥ ⊎ Σ[ v ∈ Value ] D₁ γ (v ↦ w) × D₂ γ v 

  ●-≲ : ∀{Γ Δ}{γ : Env Γ}{δ : Env  Δ}{D₁ D₂ : Denotation Γ}
            {D₁′ D₂′ : Denotation Δ}
         → D₁ γ ≲ D₁′ δ  →  D₂ γ ≲ D₂′ δ
         → (D₁ ● D₂) γ ≲ (D₁′ ● D₂′) δ
  ●-≲ {γ = γ} {δ} {D₁} {D₂} {D₁′} {D₂′} D₁γ≲D₁′δ D₂γ≲D₂′δ {w} (inj₁ w⊑⊥) =
     inj₁ w⊑⊥
  ●-≲ {γ = γ} {δ} {D₁} {D₂} {D₁′} {D₂′} D₁γ≲D₁′δ D₂γ≲D₂′δ {w}
      (inj₂ ⟨ v , ⟨ fst₁ , snd ⟩ ⟩)
      with D₁γ≲D₁′δ {w} | D₂γ≲D₂′δ {w}
  ... | a | b = inj₂ ⟨ v , ⟨ (D₁γ≲D₁′δ fst₁) , (D₂γ≲D₂′δ snd) ⟩ ⟩

  Cong : ModelCong _●_
  Cong = record { ●-≲ = λ {Γ}{Δ}{γ}{δ}{D₁}{D₂}{D₁′}{D₂′} x y →
                         ●-≲ {D₁ = D₁}{D₂ = D₂}{D₁′ = D₁′}{D₂′ = D₂′} x y }

  module RP = RenamePreserveReflect _●_ Cong
  open RP using (⊑-env)  

  ●-⊔ : ∀{Γ}{D₁ D₂ : Denotation Γ}{γ : Env Γ} {u v : Value}
      → WFDenot Γ D₁ → WFDenot Γ D₂
      → (D₁ ● D₂) γ u → (D₁ ● D₂) γ v → (D₁ ● D₂) γ (u ⊔ v)
  ●-⊔ {u = u} {v} wf1 wf2 (inj₁ u⊑⊥) (inj₁ v⊑⊥) = inj₁ (⊑-conj-L u⊑⊥ v⊑⊥)
  ●-⊔ {u = u} {v} wf1 wf2 (inj₁ u⊑⊥) (inj₂ ⟨ v' , ⟨ fst₁ , snd ⟩ ⟩) =
    inj₂ ⟨ v' , ⟨ WFDenot.⊑-closed wf1 fst₁ lt , snd ⟩ ⟩
    where lt : v' ↦ (u ⊔ v) ⊑ v' ↦ v
          lt = ⊑-fun ⊑-refl (⊑-conj-L (⊑-trans u⊑⊥ ⊑-⊥) ⊑-refl)
  ●-⊔ {u = u} {v} wf1 wf2 (inj₂ ⟨ u' , ⟨ fst₁ , snd ⟩ ⟩) (inj₁ v⊑⊥) =
    inj₂ ⟨ u' , ⟨ (WFDenot.⊑-closed wf1 fst₁ lt) , snd ⟩ ⟩
    where lt : u' ↦ (u ⊔ v) ⊑ u' ↦ u
          lt = ⊑-fun ⊑-refl (⊑-conj-L ⊑-refl (⊑-trans v⊑⊥ ⊑-⊥))
  ●-⊔ {Γ}{D₁}{D₂}{γ}{u}{v} wf1 wf2 (inj₂ ⟨ u' , ⟨ fst₁ , snd ⟩ ⟩)
                      (inj₂ ⟨ v' , ⟨ fst₃ , snd₁ ⟩ ⟩) =
    let a = WFDenot.⊔-closed wf1 fst₁ fst₃ in                      
    inj₂ ⟨ (u' ⊔ v') ,
         ⟨ WFDenot.⊑-closed wf1 a Dist⊔↦⊔ ,
           WFDenot.⊔-closed wf2 snd snd₁ ⟩ ⟩


  ●-⊑ : ∀{Γ}{D₁ D₂ : Denotation Γ} {γ : Env Γ} {v w : Value}
      → WFDenot Γ D₁ → (D₁ ● D₂) γ v → w ⊑ v
      → (D₁ ● D₂) γ w
  ●-⊑ d (inj₁ x) w⊑v = inj₁ (⊑-trans w⊑v x)
  ●-⊑ {v = v}{w} d (inj₂ ⟨ v' , ⟨ fst₁ , snd ⟩ ⟩) w⊑v =
    inj₂ ⟨ v' , ⟨ WFDenot.⊑-closed d fst₁ lt  , snd ⟩ ⟩
    where lt : v' ↦ w ⊑ v' ↦ v
          lt = ⊑-fun ⊑-refl w⊑v

  ●-⊥ : ∀{Γ}{D₁ D₂ : Denotation Γ} {γ : Env Γ}
      → (D₁ ● D₂) γ ⊥
  ●-⊥ = inj₁ ⊑-⊥

  ℱ-inv : ∀{Γ}{D : Denotation (suc Γ)}{γ : Env Γ}{u : Value}
        → ℱ D γ u
        → u ⊑ ⊥ ⊎ (Σ[ v ∈ Value ] Σ[ w ∈ Value ] D (γ `, v) w × v ↦ w ⊑ u)
  ℱ-inv {u = ⊥} tt = inj₁ ⊑-refl
  ℱ-inv {u = v ↦ w} ℱDγu = inj₂ ⟨ v , ⟨ w , ⟨ ℱDγu , ⊑-refl ⟩ ⟩ ⟩
  ℱ-inv {u = u ⊔ v} ⟨ fst , snd ⟩
      with ℱ-inv{u = u} fst | ℱ-inv{u = v} snd
  ... | inj₁ u⊑⊥ | inj₁ v⊑⊥ = inj₁ (⊑-conj-L u⊑⊥ v⊑⊥)
  ... | inj₁ u⊑⊥ | inj₂ ⟨ v' , ⟨ w' , ⟨ Dγv'w' , v'↦w'⊑v ⟩ ⟩ ⟩ =
        inj₂ ⟨ v' , ⟨ w' , ⟨ Dγv'w' , ⊑-conj-R2 v'↦w'⊑v ⟩ ⟩ ⟩
  ... | inj₂ ⟨ v' , ⟨ w' , ⟨ Dγv'w' , v'↦w'⊑v ⟩ ⟩ ⟩ | _ =
        inj₂ ⟨ v' , ⟨ w' , ⟨ Dγv'w' , ⊑-conj-R1 v'↦w'⊑v ⟩ ⟩ ⟩


  MB : ModelBasics _●_
  MB = (record { Cong = Cong ;
                 ●-⊑ = λ {Γ}{D₁}{D₂} a b c → ●-⊑ {D₂ = D₂} a b c;
                 ●-⊔ = ●-⊔
                 })

  MBot : ModelBot _●_
  MBot = (record { MB = MB ;
                 ●-⊥ = λ {Γ}{D₁}{D₂} → ●-⊥ {D₁ = D₁}{D₂} })

  ME : ModelExtra _●_
  ME = (record { MBot = MBot ;
                 ●-≡ = refl ;
                 ℱ-inv = ℱ-inv
                 })

  open Reflect _●_ ME





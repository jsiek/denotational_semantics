open import Structures
open import ValueBCD
open DomainAux domain
open OrderingAux domain ordering

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Nat using (suc)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)


module ModelCallByValue where

infixl 7 _●_
_●_ : ∀{Γ} → Denotation Γ → Denotation Γ → Denotation Γ
_●_ {Γ} D₁ D₂ γ w = Σ[ v ∈ Value ] D₁ γ (v ↦ w) × D₂ γ v 

●-≲ : ∀{Γ Δ}{γ : Env Γ}{δ : Env  Δ}{D₁ D₂ : Denotation Γ}
          {D₁′ D₂′ : Denotation Δ}
       → D₁ γ ≲ D₁′ δ  →  D₂ γ ≲ D₂′ δ
       → (D₁ ● D₂) γ ≲ (D₁′ ● D₂′) δ
●-≲ {γ = γ} {δ} {D₁} {D₂} {D₁′} {D₂′} D₁γ≲D₁′δ D₂γ≲D₂′δ {w}
    ⟨ v , ⟨ fst₁ , snd ⟩ ⟩
    with D₁γ≲D₁′δ {w} | D₂γ≲D₂′δ {w}
... | a | b = ⟨ v , ⟨ (D₁γ≲D₁′δ fst₁) , (D₂γ≲D₂′δ snd) ⟩ ⟩



●-⊔ : ∀{Γ}{D₁ D₂ : Denotation Γ}{γ : Env Γ} {u v : Value}
    → WFDenot Γ D₁ → WFDenot Γ D₂
    → (D₁ ● D₂) γ u → (D₁ ● D₂) γ v → (D₁ ● D₂) γ (u ⊔ v)
●-⊔ {Γ}{D₁}{D₂}{γ}{u}{v} wf1 wf2 ⟨ u' , ⟨ fst₁ , snd ⟩ ⟩
                    ⟨ v' , ⟨ fst₃ , snd₁ ⟩ ⟩ =
  let a = WFDenot.⊔-closed wf1 fst₁ fst₃ in                      
  ⟨ (u' ⊔ v') ,
  ⟨ WFDenot.⊑-closed wf1 a Dist⊔↦⊔ ,
    WFDenot.⊔-closed wf2 snd snd₁ ⟩ ⟩

●-⊑ : ∀{Γ}{D₁ D₂ : Denotation Γ} {γ : Env Γ} {v w : Value}
    → WFDenot Γ D₁ → (D₁ ● D₂) γ v → w ⊑ v
    → (D₁ ● D₂) γ w
●-⊑ {v = v}{w} d ⟨ v' , ⟨ fst₁ , snd ⟩ ⟩ w⊑v =
  ⟨ v' , ⟨ WFDenot.⊑-closed d fst₁ lt  , snd ⟩ ⟩
  where lt : v' ↦ w ⊑ v' ↦ v
        lt = ⊑-fun ⊑-refl w⊑v

model_basics : LambdaModelBasics _●_ ℱ
model_basics = record { ℱ-≲ = ℱ-≲ ;
               ●-≲ = λ {Γ}{Δ}{γ}{δ}{D₁}{D₂}{D₁′}{D₂′} x y →
                       ●-≲ {D₁ = D₁}{D₂ = D₂}{D₁′ = D₁′}{D₂′ = D₂′} x y;
               ℱ-⊑ = ℱ-⊑;
               ●-⊑ = λ {Γ}{D₁}{D₂} a b c → ●-⊑ {D₂ = D₂} a b c;
               ℱ-⊔ = λ {Γ}{D}{γ}{u}{v} → ℱ-⊔{D = D}{γ}{u}{v} ;
               ●-⊔ = ●-⊔ ;
               ℱ-⊥ = λ {Γ}{D}{γ} → ℱ-⊥ {Γ}{D}{γ}
               }

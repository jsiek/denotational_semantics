open import Data.Nat using (ℕ; suc ; zero)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (Dec; yes; no)

open import Variables
open import Primitives
open import ValueBCDConst
open import Structures
open DomainAux domain
open OrderingAux domain ordering
open import Consistency
open ConsistentAux domain ordering consistent
open WFDenotMod domain ordering consistent
open ModelMod domain ordering consistent

module CurryBCDConst where

ℱ-⊔ : ∀{Γ}{D : Denotation (suc Γ)}{γ : Env Γ} {u v : Value}
    → ℱ D γ u → ℱ D γ v → ℱ D γ (u ⊔ v)
ℱ-⊔ d1 d2 = ⟨ d1 , d2 ⟩

ℱ-⊥ : ∀{Γ}{D : Denotation (suc Γ)}{γ : Env Γ}
    → ℱ D γ ⊥
ℱ-⊥ = tt

ℱ-≲ : ∀{Γ Δ}{γ : Env Γ}{δ : Env Δ}{D : Denotation (suc Γ)}
          {D′ : Denotation (suc Δ)}
       → (∀{v : Value} → D (γ `, v) ≲ D′ (δ `, v))
       → ℱ D γ ≲ ℱ D′ δ
ℱ-≲ D≲D′ {⊥} = λ _ → tt
ℱ-≲ D≲D′ {const k} = λ x → x
ℱ-≲ D≲D′ {v ↦ w} = D≲D′
ℱ-≲ {D = D}{D′} D≲D′ {u ⊔ v} ℱDγ
    with ℱ-≲{D = D}{D′} D≲D′ {u} | ℱ-≲{D = D}{D′} D≲D′ {v}
... | a | b =
    ⟨ (a (proj₁ ℱDγ)) , (b (proj₂ ℱDγ)) ⟩


ℱ-⊑ : ∀{Γ}{D : Denotation (suc Γ)}{γ : Env Γ} {v w : Value}
       → WFDenot (suc Γ) D
       → ℱ D γ v → w ⊑ v → ℱ D γ w
ℱ-⊑ d ℱDγv ⊑-⊥ = tt
ℱ-⊑ d () ⊑-const
ℱ-⊑ d ℱDγv (⊑-conj-L w⊑v w⊑v₁) = ⟨ (ℱ-⊑ d ℱDγv w⊑v) , (ℱ-⊑ d ℱDγv w⊑v₁) ⟩
ℱ-⊑ d ℱDγv (⊑-conj-R1 w⊑v) = ℱ-⊑ d (proj₁ ℱDγv) w⊑v
ℱ-⊑ d ℱDγv (⊑-conj-R2 w⊑v) = ℱ-⊑ d (proj₂ ℱDγv) w⊑v
ℱ-⊑ d ℱDγv (⊑-trans w⊑v w⊑v₁) = ℱ-⊑ d (ℱ-⊑ d ℱDγv w⊑v₁) w⊑v
ℱ-⊑ {Γ}{D}{γ}{v ↦ w}{v' ↦ w'} d ℱDγv (⊑-fun v⊑v' w'⊑w) =
  WFDenot.⊑-closed d (WFDenot.⊑-env d ℱDγv b) w'⊑w
  where b : (γ `, v) `⊑ (γ `, v')
        b Z = v⊑v'
        b (S x) = ⊑-refl 
ℱ-⊑ d ℱDγv ⊑-dist = WFDenot.⊔-closed d (proj₁ ℱDγv) (proj₂ ℱDγv)

ℱ-~ : ∀{Γ}{D : Denotation (suc Γ)}{γ : Env Γ}{δ : Env Γ} {u v : Value}
    → WFDenot (suc Γ) D → WFEnv γ → WFEnv δ → γ ~′ δ → wf u → wf v
    → ℱ D γ u → ℱ D δ v → u ~ v
ℱ-~ {D = D} {γ} {δ} {⊥} {v} wfd wfγ wfδ γ~δ wfu wfv d1 d2 = tt
ℱ-~ {D = D} {γ} {δ} {const k} {v} wfd wfγ wfδ γ~δ wfu wfv () d2
ℱ-~ {D = D} {γ} {δ} {u₁ ↦ u₂} {⊥} wfd wfγ wfδ γ~δ wfu wfv d1 d2 = tt
ℱ-~ {D = D} {γ} {δ} {u₁ ↦ u₂} {const x} wfd wfγ wfδ γ~δ wfu wfv d1 ()
ℱ-~ {Γ} {D} {γ} {δ} {u₁ ↦ u₂} {v₁ ↦ v₂} wfd wfγ wfδ γ~δ (wf-fun wfu₁ wfu₂)
  (wf-fun wfv₁ wfv₂) d1 d2
    with consistent? u₁ v₁
... | no u₁~̸v₁ = inj₂ u₁~̸v₁
... | yes u₁~v₁ = inj₁ ⟨ u₁~v₁ , u₂~v₂ ⟩
      where
      wfγu₁ : WFEnv (γ `, u₁)
      wfγu₁ {Z} = wfu₁
      wfγu₁ {S x} = wfγ
      wfδv₁ : WFEnv (δ `, v₁)
      wfδv₁ {Z} = wfv₁
      wfδv₁ {S x} = wfδ
      γu₁~δv₁ : (γ `, u₁) ~′ (δ `, v₁)
      γu₁~δv₁ {Z} = u₁~v₁
      γu₁~δv₁ {S x} = γ~δ {x}
      u₂~v₂ = WFDenot.~-closed wfd (λ {x} → wfγu₁ {x}) (λ {x} → wfδv₁ {x})
                 (λ {x} → γu₁~δv₁ {x}) wfu₂ wfv₂ d1 d2 
  
ℱ-~ {Γ}{D} {γ} {δ} {u₁ ↦ u₂} {v₁ ⊔ v₂} wfd wfγ wfδ γ~δ 
    (wf-fun wfu₁ wfu₂) (wf-⊔ v₁~v₂ wfv₁ wfv₂) d1 ⟨ fst , snd ⟩ =
    ⟨ ℱ-~ {Γ}{D}{γ}{δ}{u₁ ↦ u₂}{v₁} wfd wfγ wfδ γ~δ
           (wf-fun wfu₁ wfu₂) wfv₁ d1 fst ,
      ℱ-~ {Γ}{D}{γ}{δ}{u₁ ↦ u₂}{v₂} wfd wfγ wfδ γ~δ
           (wf-fun wfu₁ wfu₂) wfv₂ d1 snd ⟩
ℱ-~ {D = D} {γ} {δ} {u₁ ⊔ u₂} {v} wfd wfγ wfδ γ~δ
    (wf-⊔ u₁~u₂ wfu₁ wfu₂) wfv ⟨ fst , snd ⟩ d2 =
    ⟨ ℱ-~ {D = D}{γ}{δ}{u₁}{v} wfd wfγ wfδ γ~δ wfu₁ wfv fst d2 ,
      ℱ-~ {D = D}{γ}{δ}{u₂}{v} wfd wfγ wfδ γ~δ wfu₂ wfv snd d2 ⟩

model_curry : ModelCurry ℱ
model_curry = record { ℱ-≲ = ℱ-≲ ; ℱ-⊑ = ℱ-⊑ ;
                       ℱ-⊔ = λ {Γ}{D}{γ}{u}{v} → ℱ-⊔ {D = D}{γ}{u}{v} ;
                       ℱ-⊥ = λ {Γ}{D}{γ} → ℱ-⊥ {Γ}{D}{γ} ;
                       ℱ-~ = λ {Γ}{D}{γ}{u}{v} → ℱ-~ {D = D}{γ}{u}{v}
                     }

open import Structures
open import ValueBCD
open DomainAux domain
open OrderingAux domain ordering
open import Lambda
open ASTMod using (`_; _⦅_⦆; cons; bind; nil)
open import Structures

open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)

module ModelCallByName where

infixl 7 _●_
_●_ : ∀{Γ} → Denotation Γ → Denotation Γ → Denotation Γ
_●_ {Γ} D₁ D₂ γ w = w ⊑ ⊥ ⊎ Σ[ v ∈ Value ] D₁ γ (v ↦ w) × D₂ γ v 

model : LambdaModel
model = record { _●_ = _●_ ; ℱ = ℱ }

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

model_basics : LambdaModelBasics model
model_basics = (record { ℱ-≲ = ℱ-≲ ;
               ●-≲ = λ {Γ}{Δ}{γ}{δ}{D₁}{D₂}{D₁′}{D₂′} x y →
                       ●-≲ {D₁ = D₁}{D₂ = D₂}{D₁′ = D₁′}{D₂′ = D₂′} x y;
               ℱ-⊑ = ℱ-⊑;
               ●-⊑ = λ {Γ}{D₁}{D₂} a b c → ●-⊑ {D₂ = D₂} a b c;
               ℱ-⊔ = λ {Γ}{D}{γ}{u}{v} → ℱ-⊔{D = D}{γ}{u}{v} ;
               ●-⊔ = ●-⊔
               })

open LambdaDenot domain ordering model

ℰ-⊥ : ∀{Γ}{γ : Env Γ}{M : Term Γ}
    → ℰ M γ ⊥
ℰ-⊥ {M = ` x} = ⊑-⊥
ℰ-⊥ {Γ}{γ}{M = lam ⦅ bind N nil ⦆} = ℱ-⊥ {Γ}{ℰ N}{γ}
ℰ-⊥ {M = app ⦅ cons L (cons M nil) ⦆} = inj₁ ⊑-⊥


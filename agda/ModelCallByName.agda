open import Structures
open import ValueBCD
open import ValueStructAux value_struct
open import OrderingAux value_struct ordering
open import Lambda
open ASTMod using (`_; _⦅_⦆; cons; bind; nil)
open import Structures
open import WFDenotMod value_struct ordering consistent
import CurryApplyStruct
open import ConsistentAux value_struct ordering consistent

open import Data.Nat using (suc)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

module ModelCallByName where

infixl 7 _●_
_●_ : Denotation → Denotation → Denotation
_●_ D₁ D₂ γ w = w ⊑ ⊥ ⊎ Σ[ v ∈ Value ] D₁ γ (v ↦ w) × D₂ γ v

●-≲ : ∀{γ : Env}{δ : Env}{D₁ D₂ : Denotation}
          {D₁′ D₂′ : Denotation}
       → D₁ γ ≲ D₁′ δ  →  D₂ γ ≲ D₂′ δ
       → (D₁ ● D₂) γ ≲ (D₁′ ● D₂′) δ
●-≲ {γ = γ} {δ} {D₁} {D₂} {D₁′} {D₂′} D₁γ≲D₁′δ D₂γ≲D₂′δ {w} wfw (inj₁ w⊑⊥) =
   inj₁ w⊑⊥
●-≲ {γ = γ} {δ} {D₁} {D₂} {D₁′} {D₂′} D₁γ≲D₁′δ D₂γ≲D₂′δ {w} wfw
    (inj₂ ⟨ v , ⟨ fst₁ , snd ⟩ ⟩)
    with D₁γ≲D₁′δ {w} | D₂γ≲D₂′δ {w}
... | a | b = inj₂ ⟨ v , ⟨ (D₁γ≲D₁′δ tt fst₁) , (D₂γ≲D₂′δ tt snd) ⟩ ⟩


●-⊔ : ∀{D₁ D₂ : Denotation}{γ : Env}{u v : Value}
    → WFDenot D₁ → WFDenot D₂
    → WFEnv γ → wf u → wf v
    → (D₁ ● D₂) γ u → (D₁ ● D₂) γ v → (D₁ ● D₂) γ (u ⊔ v)
●-⊔ {u = u} {v} wf1 wf2 wfγ wfu wfv (inj₁ u⊑⊥) (inj₁ v⊑⊥) =
    inj₁ (⊑-conj-L u⊑⊥ v⊑⊥)
●-⊔ {u = u} {v} wf1 wf2 wfγ wfu wfv (inj₁ u⊑⊥) (inj₂ ⟨ v' , ⟨ fst₁ , snd ⟩ ⟩) =
  inj₂ ⟨ v' , ⟨ WFDenot.⊑-closed wf1 (λ x → tt) tt tt lt fst₁ , snd ⟩ ⟩
  where lt : v' ↦ (u ⊔ v) ⊑ v' ↦ v
        lt = ⊑-fun ⊑-refl (⊑-conj-L (⊑-trans u⊑⊥ ⊑-⊥) ⊑-refl)
●-⊔ {u = u} {v} wf1 wf2 wfγ wfu wfv (inj₂ ⟨ u' , ⟨ fst₁ , snd ⟩ ⟩) (inj₁ v⊑⊥) =
  inj₂ ⟨ u' , ⟨ (WFDenot.⊑-closed wf1 (λ x → tt) tt tt lt fst₁) , snd ⟩ ⟩
  where lt : u' ↦ (u ⊔ v) ⊑ u' ↦ u
        lt = ⊑-fun ⊑-refl (⊑-conj-L ⊑-refl (⊑-trans v⊑⊥ ⊑-⊥))
●-⊔ {D₁}{D₂}{γ}{u}{v} wf1 wf2 wfγ wfu wfv (inj₂ ⟨ u' , ⟨ fst₁ , snd ⟩ ⟩)
                    (inj₂ ⟨ v' , ⟨ fst₃ , snd₁ ⟩ ⟩) =
  let a = WFDenot.⊔-closed wf1 (λ x → tt) tt tt fst₁ fst₃ in
  inj₂ ⟨ (u' ⊔ v') ,
       ⟨ WFDenot.⊑-closed wf1 (λ x → tt) tt tt Dist⊔↦⊔ a ,
         WFDenot.⊔-closed wf2 (λ x → tt) tt tt snd snd₁ ⟩ ⟩

●-⊑ : ∀{D₁ D₂ : Denotation} {γ : Env} {v w : Value}
    → WFDenot D₁
    → WFEnv γ → wf v → wf w
    → w ⊑ v
    → (D₁ ● D₂) γ v
    → (D₁ ● D₂) γ w
●-⊑ d wfγ wfv wfw w⊑v  (inj₁ x) = inj₁ (⊑-trans w⊑v x)
●-⊑ {v = v}{w} d wfγ wfv wfw w⊑v (inj₂ ⟨ v' , ⟨ fst₁ , snd ⟩ ⟩) =
  inj₂ ⟨ v' , ⟨ WFDenot.⊑-closed d (λ x → tt) tt tt lt fst₁  , snd ⟩ ⟩
  where lt : v' ↦ w ⊑ v' ↦ v
        lt = ⊑-fun ⊑-refl w⊑v

●-⊥ : ∀{D₁ D₂ : Denotation} {γ : Env}
    → (D₁ ● D₂) γ ⊥
●-⊥ = inj₁ ⊑-⊥

model_curry_apply : CurryApplyStruct.CurryApplyStruct value_struct ordering consistent _●_ ℱ
model_curry_apply =
      record { model_curry = model_curry ;
               ●-≲ = λ {γ}{δ}{D₁}{D₂}{D₁′}{D₂′} x y →
                       ●-≲ {D₁ = D₁}{D₂ = D₂}{D₁′ = D₁′}{D₂′ = D₂′} x y;
               ●-⊑ = λ {D₁}{D₂} a b c → ●-⊑ {D₂ = D₂} a b c;
               ●-⊔ = λ {a}{b}{c}{d}{e} → ●-⊔ {a}{b}{c}{d}{e}
               }

open import LambdaDenot value_struct ordering _●_ ℱ

ℰ-⊥ : ∀{γ : Env}{M : Term}
    → ℰ M γ ⊥
ℰ-⊥ {M = ` x} = ⊑-⊥
ℰ-⊥ {γ}{M = lam ⦅ cons (bind (ast N)) nil ⦆} = ℱ-⊥ {ℰ N}{γ}
ℰ-⊥ {M = app ⦅ cons (ast L) (cons (ast M) nil) ⦆} = inj₁ ⊑-⊥


open import Structures
import ValueStructAux
import OrderingAux
import ModelMod
import ConsistentAux
import WFDenotMod

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Nat using (suc)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥-elim) renaming (⊥ to Bot)
open import Relation.Nullary.Negation using (contradiction)


module ModelCallByValue
  (D : ValueStruct)
  (V : ValueOrdering D)
  (ℱ : ∀{Γ} → ValueStructAux.Denotation D (suc Γ)
            → ValueStructAux.Denotation D Γ)
  (C : Consistent D V)
  (MC : ModelMod.ModelCurry D V C ℱ)
  where

open ValueStruct D
open ValueOrdering V
open Consistent C
open ValueStructAux D
open OrderingAux D V
open ConsistentAux D V C
open WFDenotMod D V C
open ModelMod D V C
open ModelCurry MC

infixl 7 _●_
_●_ : ∀{Γ} → Denotation Γ → Denotation Γ → Denotation Γ
_●_ {Γ} D₁ D₂ γ w = Σ[ v ∈ Value ] wf v × D₁ γ (v ↦ w) × D₂ γ v 

●-≲ : ∀{Γ Δ}{γ : Env Γ}{δ : Env  Δ}{D₁ D₂ : Denotation Γ}
          {D₁′ D₂′ : Denotation Δ}
       → D₁ γ ≲ D₁′ δ  →  D₂ γ ≲ D₂′ δ
       → (D₁ ● D₂) γ ≲ (D₁′ ● D₂′) δ
●-≲ {γ = γ} {δ} {D₁} {D₂} {D₁′} {D₂′} D₁γ≲D₁′δ D₂γ≲D₂′δ {w}
    ⟨ v , ⟨ wfv , ⟨ fst₁ , snd ⟩ ⟩ ⟩
    with D₁γ≲D₁′δ {w} | D₂γ≲D₂′δ {w}
... | a | b = ⟨ v , ⟨ wfv , ⟨ (D₁γ≲D₁′δ fst₁) , (D₂γ≲D₂′δ snd) ⟩ ⟩ ⟩


●-⊔ : ∀{Γ}{D₁ D₂ : Denotation Γ}{γ : Env Γ} {u v : Value}
    → WFDenot Γ D₁ → WFDenot Γ D₂ → WFEnv γ
    → (D₁ ● D₂) γ u → (D₁ ● D₂) γ v → (D₁ ● D₂) γ (u ⊔ v)
●-⊔ {Γ}{D₁}{D₂}{γ}{u}{v} wf1 wf2 wfγ
    ⟨ u' , ⟨ wfu' , ⟨ fst₁ , snd ⟩ ⟩ ⟩
    ⟨ v' , ⟨ wfv' , ⟨ fst₃ , snd₁ ⟩ ⟩ ⟩ = 
  let a = WFDenot.⊔-closed wf1 {!!} {!!} {!!} {!!} {!!} {!!} {!!} {- fst₁ fst₃ -} in
  let u'~v' = WFDenot.~-closed wf2 wfγ wfγ (λ {x} → wfγ{x})
                 wfu' wfv' snd snd₁ in
  ⟨ (u' ⊔ v') ,
  ⟨ wf-⊔ u'~v' wfu' wfv' ,
  ⟨ WFDenot.⊑-closed wf1 {!!} {!!} {!!} a Dist⊔↦⊔ ,
    WFDenot.⊔-closed wf2 {!!} {!!} {!!} {!!} {!!} snd snd₁ ⟩ ⟩ ⟩


●-~ : ∀{Γ}{D₁ D₂ : Denotation Γ}{γ : Env Γ}{δ : Env Γ} {u v : Value}
    → WFEnv γ → WFEnv δ → γ ~′ δ → wf u → wf v → WFDenot Γ D₁ → WFDenot Γ D₂
    → (D₁ ● D₂) γ u → (D₁ ● D₂) δ v → u ~ v
●-~ {Γ}{D₁}{D₂}{γ}{δ}{u}{v} wfγ wfδ γ~δ wfu wfv wf1 wf2
    ⟨ u' , ⟨ wfu' , ⟨ fst₁ , snd ⟩ ⟩ ⟩ ⟨ v' , ⟨ wfv' , ⟨ fst₃ , snd₁ ⟩ ⟩ ⟩
    with WFDenot.~-closed wf1 wfγ wfδ γ~δ (wf-fun wfu' wfu) (wf-fun wfv' wfv)
        fst₁ fst₃
... | u'↦u~v'↦v
    with ~-↦ {u'}{u}{v'}{v} u'↦u~v'↦v
... | inj₁ ⟨ _ , u~v ⟩ = u~v
... | inj₂ u'~̸v' = 
    let u'~v' = WFDenot.~-closed wf2 wfγ wfδ γ~δ wfu' wfv' snd snd₁ in
    ⊥-elim (contradiction u'~v' u'~̸v')


●-⊑ : ∀{Γ}{D₁ D₂ : Denotation Γ} {γ : Env Γ} {v w : Value}
    → WFDenot Γ D₁ → (D₁ ● D₂) γ v → w ⊑ v
    → (D₁ ● D₂) γ w
●-⊑ {v = v}{w} d ⟨ v' , ⟨ wfv' , ⟨ fst₁ , snd ⟩ ⟩ ⟩ w⊑v =
  ⟨ v' , ⟨ wfv' , ⟨ WFDenot.⊑-closed d {!!} {!!} {!!} fst₁ lt  , snd ⟩ ⟩ ⟩
  where lt : v' ↦ w ⊑ v' ↦ v
        lt = ⊑-fun ⊑-refl w⊑v

model_basics : LambdaModelBasics _●_ ℱ
model_basics = record {
               model_curry = MC ;
               ●-≲ = λ {Γ}{Δ}{γ}{δ}{D₁}{D₂}{D₁′}{D₂′} x y →
                       ●-≲ {D₁ = D₁}{D₂ = D₂}{D₁′ = D₁′}{D₂′ = D₂′} x y ;
               ●-⊑ = λ {Γ}{D₁}{D₂} a b c → ●-⊑ {D₂ = D₂} a b c ;
               ●-⊔ = {!!} ;
               ●-~ = {!!} 
               }

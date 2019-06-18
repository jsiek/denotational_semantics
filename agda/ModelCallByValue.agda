open import Structures
import ValueStructAux
import OrderingAux
import CurryApplyStruct
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
  (MC : CurryApplyStruct.CurryStruct D V C ℱ)
  where

open ValueStruct D
open ValueOrdering V
open Consistent C
open ValueStructAux D
open OrderingAux D V
open ConsistentAux D V C
open WFDenotMod D V C
open CurryApplyStruct D V C
open CurryStruct MC

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

●-~ : ∀{Γ}{D₁ D₂ : Denotation Γ}{γ : Env Γ}{δ : Env Γ} {u v : Value}
    → WFDenot Γ D₁ → WFDenot Γ D₂ → WFEnv γ → WFEnv δ → γ ~′ δ → wf u → wf v 
    → (D₁ ● D₂) γ u → (D₁ ● D₂) δ v → u ~ v
●-~ {Γ}{D₁}{D₂}{γ}{δ}{u}{v} wf1 wf2 wfγ wfδ γ~δ wfu wfv 
    ⟨ u' , ⟨ wfu' , ⟨ fst₁ , snd ⟩ ⟩ ⟩ ⟨ v' , ⟨ wfv' , ⟨ fst₃ , snd₁ ⟩ ⟩ ⟩
    with WFDenot.~-closed wf1 wfγ wfδ γ~δ (wf-fun wfu' wfu) (wf-fun wfv' wfv)
        fst₁ fst₃
... | u'↦u~v'↦v
    with ~-↦ {u'}{u}{v'}{v} u'↦u~v'↦v
... | inj₁ ⟨ _ , u~v ⟩ = u~v
... | inj₂ u'~̸v' = 
    let u'~v' = WFDenot.~-closed wf2 wfγ wfδ γ~δ wfu' wfv' snd snd₁ in
    ⊥-elim (contradiction u'~v' u'~̸v')

●-⊔ : ∀{Γ}{D₁ D₂ : Denotation Γ}{γ : Env Γ} {u v : Value}
    → WFDenot Γ D₁ → WFDenot Γ D₂ → WFEnv γ → wf u → wf v
    → (D₁ ● D₂) γ u → (D₁ ● D₂) γ v → (D₁ ● D₂) γ (u ⊔ v)
●-⊔ {Γ}{D₁}{D₂}{γ}{u}{v} wf1 wf2 wfγ wfu wfv
    ⟨ u' , ⟨ wfu' , ⟨ D₁γu'↦u , D₂γu' ⟩ ⟩ ⟩
    ⟨ v' , ⟨ wfv' , ⟨ D₁γv'↦v , D₂γv' ⟩ ⟩ ⟩ =
  let wf-u'↦u = wf-fun wfu' wfu in
  let wf-v'↦v = wf-fun wfv' wfv in
  let a : D₁ γ (u' ↦ u ⊔ v' ↦ v)
      a = WFDenot.⊔-closed wf1 wfγ (wf-fun wfu' wfu) (wf-fun wfv' wfv)
                           D₁γu'↦u D₁γv'↦v in
  let u'↦u~v'↦v = WFDenot.~-closed wf1 {γ}{γ} wfγ wfγ
                   (~′-refl{Γ} (λ {y} → wfγ {y}))
                   wf-u'↦u wf-v'↦v D₁γu'↦u D₁γv'↦v in
  let u'~v' = WFDenot.~-closed wf2 {γ}{γ} wfγ wfγ (~′-refl{Γ} (λ {y} → wfγ {y}))
                 wfu' wfv' D₂γu' D₂γv' in
  let u~v = ~-↦-~ u'↦u~v'↦v u'~v' in
  let wf-u'⊔v' = wf-⊔ u'~v' wfu' wfv' in
  let wf-u⊔v = wf-⊔ u~v wfu wfv in
  let D₁γu'⊔v'↦u⊔v : D₁ γ ((u' ⊔ v') ↦ (u ⊔ v))
      D₁γu'⊔v'↦u⊔v = WFDenot.⊑-closed wf1 wfγ (wf-⊔ u'↦u~v'↦v wf-u'↦u wf-v'↦v)
                         (wf-fun wf-u'⊔v' wf-u⊔v) Dist⊔↦⊔ a in
  ⟨ (u' ⊔ v') ,
  ⟨ wf-⊔ u'~v' wfu' wfv' ,
  ⟨ D₁γu'⊔v'↦u⊔v ,
    WFDenot.⊔-closed wf2 wfγ wfu' wfv' D₂γu' D₂γv' ⟩ ⟩ ⟩


●-⊑ : ∀{Γ}{D₁ D₂ : Denotation Γ} {γ : Env Γ} {v w : Value}
    → WFDenot Γ D₁
    → WFEnv γ → wf v → wf w
    → w ⊑ v
    → (D₁ ● D₂) γ v
    → (D₁ ● D₂) γ w
●-⊑ {v = v}{w} d wfγ wfv wfw w⊑v ⟨ v' , ⟨ wfv' , ⟨ D₁γv'↦v , D₂γv' ⟩ ⟩ ⟩ =
  ⟨ v' ,
  ⟨ wfv' ,
  ⟨ WFDenot.⊑-closed d wfγ (wf-fun wfv' wfv) (wf-fun wfv' wfw)
                     (⊑-fun ⊑-refl w⊑v) D₁γv'↦v  ,
    D₂γv' ⟩ ⟩ ⟩
  where lt : v' ↦ w ⊑ v' ↦ v
        lt = ⊑-fun ⊑-refl w⊑v


model_curry_apply : CurryApplyStruct _●_ ℱ
model_curry_apply =
    record {
           model_curry = MC ;
           ●-≲ = λ {Γ}{Δ}{γ}{δ}{D₁}{D₂}{D₁′}{D₂′} x y →
                   ●-≲ {D₁ = D₁}{D₂ = D₂}{D₁′ = D₁′}{D₂′ = D₂′} x y ;
           ●-⊑ = λ {Γ}{D₁}{D₂} a b c → ●-⊑ {D₂ = D₂} a b c ;
           ●-⊔ = ●-⊔ ;
           ●-~ = ●-~ 
           }

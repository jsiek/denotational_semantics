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
  (C : Consistent D V)
  (ℱ : ValueStructAux.Denotation D → ValueStructAux.Denotation D)
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
_●_ : Denotation → Denotation → Denotation
_●_ D₁ D₂ γ w = Σ[ v ∈ Value ] wf v × D₁ γ (v ↦ w) × D₂ γ v 

●-≲ : ∀{γ : Env}{δ : Env}{D₁ D₂ : Denotation}
          {D₁′ D₂′ : Denotation}
       → D₁ γ ≲ D₁′ δ  →  D₂ γ ≲ D₂′ δ
       → (D₁ ● D₂) γ ≲ (D₁′ ● D₂′) δ
●-≲ {γ = γ} {δ} {D₁} {D₂} {D₁′} {D₂′} D₁γ≲D₁′δ D₂γ≲D₂′δ {w} wfw
    ⟨ v , ⟨ wfv , ⟨ fst₁ , snd ⟩ ⟩ ⟩
    with D₁γ≲D₁′δ {w} | D₂γ≲D₂′δ {w}
... | a | b =
    ⟨ v , ⟨ wfv , ⟨ (D₁γ≲D₁′δ (wf-fun wfv wfw) fst₁) , (D₂γ≲D₂′δ wfv snd) ⟩ ⟩ ⟩

●-~ : ∀{D₁ D₂ : Denotation}{γ : Env}{δ : Env} {u v : Value}
    → WFDenot D₁ → WFDenot D₂ → WFEnv γ → WFEnv δ → γ ~′ δ → wf u → wf v 
    → (D₁ ● D₂) γ u → (D₁ ● D₂) δ v → u ~ v
●-~ {D₁}{D₂}{γ}{δ}{u}{v} wf1 wf2 wfγ wfδ γ~δ wfu wfv 
    ⟨ u' , ⟨ wfu' , ⟨ fst₁ , snd ⟩ ⟩ ⟩ ⟨ v' , ⟨ wfv' , ⟨ fst₃ , snd₁ ⟩ ⟩ ⟩
    with WFDenot.~-closed wf1 wfγ wfδ γ~δ (wf-fun wfu' wfu) (wf-fun wfv' wfv)
        fst₁ fst₃
... | u'↦u~v'↦v
    with ~-↦ {u'}{u}{v'}{v} u'↦u~v'↦v
... | inj₁ ⟨ _ , u~v ⟩ = u~v
... | inj₂ u'~̸v' = 
    let u'~v' = WFDenot.~-closed wf2 wfγ wfδ γ~δ wfu' wfv' snd snd₁ in
    ⊥-elim (contradiction u'~v' u'~̸v')

●-⊔ : ∀{D₁ D₂ : Denotation}{γ : Env} {u v : Value}
    → WFDenot D₁ → WFDenot D₂ → WFEnv γ → wf u → wf v
    → (D₁ ● D₂) γ u → (D₁ ● D₂) γ v → (D₁ ● D₂) γ (u ⊔ v)
●-⊔ {D₁}{D₂}{γ}{u}{v} wf1 wf2 wfγ wfu wfv
    ⟨ u' , ⟨ wfu' , ⟨ D₁γu'↦u , D₂γu' ⟩ ⟩ ⟩
    ⟨ v' , ⟨ wfv' , ⟨ D₁γv'↦v , D₂γv' ⟩ ⟩ ⟩ =
  let wf-u'↦u = wf-fun wfu' wfu in
  let wf-v'↦v = wf-fun wfv' wfv in
  let a : D₁ γ (u' ↦ u ⊔ v' ↦ v)
      a = WFDenot.⊔-closed wf1 wfγ (wf-fun wfu' wfu) (wf-fun wfv' wfv)
                           D₁γu'↦u D₁γv'↦v in
  let u'↦u~v'↦v = WFDenot.~-closed wf1 {γ}{γ} wfγ wfγ
                   (~′-refl (λ y → wfγ y))
                   wf-u'↦u wf-v'↦v D₁γu'↦u D₁γv'↦v in
  let u'~v' = WFDenot.~-closed wf2 {γ}{γ} wfγ wfγ (~′-refl (λ y → wfγ y))
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


●-⊑ : ∀{D₁ D₂ : Denotation} {γ : Env} {v w : Value}
    → WFDenot D₁
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
           ●-≲ = λ {γ}{δ}{D₁}{D₂}{D₁′}{D₂′} x y →
                   ●-≲ {D₁ = D₁}{D₂ = D₂}{D₁′ = D₁′}{D₂′ = D₂′} x y ;
           ●-⊑ = λ {D₁}{D₂} a b c → ●-⊑ {D₂ = D₂} a b c ;
           ●-⊔ = ●-⊔ ;
           ●-~ = ●-~ 
           }

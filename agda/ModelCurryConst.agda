open import Data.Nat using (ℕ; suc ; zero)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥-elim) renaming (⊥ to Bot)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; inspect; [_])

open import Primitives
open import ValueConst
open import CurryConst
open import Values
open import ValueStructAux value_struct
open import OrderingAux value_struct ordering
open import Consistency
open import ConsistentAux value_struct ordering consistent
open import WFDenotMod value_struct ordering consistent
open import CurryApplyStruct value_struct ordering consistent

module ModelCurryConst where

ℱ-⊔ : ∀{D : Denotation}{γ : Env} {u v : Value}
    → ℱ D γ u → ℱ D γ v → ℱ D γ (u ⊔ v)
ℱ-⊔ d1 d2 = ⟨ d1 , d2 ⟩

ℱ-⊥ : ∀{D : Denotation}{γ : Env}
    → ℱ D γ ⊥
ℱ-⊥ = tt

ℱ-≲ : ∀{D : Denotation}
          {D′ : Denotation}{γ : Env}{δ : Env}
       → (∀{v : Value} → wf v → D (γ `, v) ≲ D′ (δ `, v))
       → ℱ D γ ≲ ℱ D′ δ
ℱ-≲ D≲D′ {⊥} wfv _ = tt
ℱ-≲ D≲D′ {const k} wfv = λ z → z
ℱ-≲ D≲D′ {v ↦ w} (wf-fun wfv wfw) Dγv-w = D≲D′ wfv wfw Dγv-w
ℱ-≲ {D = D}{D′} D≲D′ {u ⊔ v} (wf-⊔ u~v wfu wfv) ℱDγ
    with ℱ-≲{D = D}{D′} D≲D′ {u} | ℱ-≲{D = D}{D′} D≲D′ {v}
... | a | b =
   ⟨ (a wfu (proj₁ ℱDγ)) , (b wfv (proj₂ ℱDγ)) ⟩

ℱ-∈ : ∀{D : Denotation}{γ : Env} {v w : Value}
        → w ∈ v → ℱ D γ v → ℱ D γ w
ℱ-∈ {D} {γ} {⊥} {w} refl ℱv = tt
ℱ-∈ {D} {γ} {const x} {w} w∈v ()
ℱ-∈ {D} {γ} {v₁ ↦ v₂} {w} refl ℱv = ℱv
ℱ-∈ {D} {γ} {v₁ ⊔ v₂} {w} (inj₁ x) ⟨ ℱv₁ , ℱv₂ ⟩ = ℱ-∈ x ℱv₁
ℱ-∈ {D} {γ} {v₁ ⊔ v₂} {w} (inj₂ y) ⟨ ℱv₁ , ℱv₂ ⟩ = ℱ-∈ y ℱv₂

¬k∈ℱ : ∀{D : Denotation}{γ : Env} {v : Value}
         {b : Base}{k : base-rep b}
        → const {b} k ∈ v → ¬ ℱ D γ v
¬k∈ℱ {v = ⊥} () ℱv
¬k∈ℱ {v = const k′} k∈v ℱv = ℱv
¬k∈ℱ {v = v₁ ↦ v₂} () ℱv
¬k∈ℱ {v = v₁ ⊔ v₂} (inj₁ x) ⟨ fst₁ , snd₁ ⟩ = ¬k∈ℱ x fst₁
¬k∈ℱ {v = v₁ ⊔ v₂} (inj₂ y) ⟨ fst₁ , snd₁ ⟩ = ¬k∈ℱ y snd₁


ℱ-⊆ : ∀{D : Denotation}{γ : Env} {v w : Value}
        → w ⊆ v → ℱ D γ v → ℱ D γ w
ℱ-⊆ {D} {γ} {v} {⊥} w⊆v ℱv = tt
ℱ-⊆ {D} {γ} {v} {const k} w⊆v ℱv =
    ⊥-elim (contradiction ℱv (¬k∈ℱ (w⊆v refl)))
ℱ-⊆ {D} {γ} {v} {w₁ ↦ w₂} w⊆v ℱv = ℱ-∈ (w⊆v refl) ℱv
ℱ-⊆ {D} {γ} {v} {w₁ ⊔ w₂} w⊆v ℱv
    with ⊔⊆-inv w⊆v
... | ⟨ w₁⊆v , w₂⊆v ⟩ =    
  ⟨ ℱ-⊆ w₁⊆v ℱv , ℱ-⊆ w₂⊆v ℱv ⟩

ℱ-dom-cod : ∀ {D : Denotation}{γ : Env}{v w : Value}{fv : AllFun v}
       → WFDenot D → WFEnv γ → wf v → wf w
       → dom v {fv} ⊑ w → ℱ D γ v → ℱ D γ (dom v {fv} ↦ cod v {fv})
ℱ-dom-cod {v = ⊥} {w} {()} wfd wfγ wfv wfw dv⊑w ℱv
ℱ-dom-cod {v = const k} {w} {()} wfd wfγ wfv wfw dv⊑w ℱv
ℱ-dom-cod {v = v₁ ↦ v₂} {w} {fv} wfd wfγ wfv wfw dv⊑w ℱv = ℱv
ℱ-dom-cod {D}{γ}{v₁ ⊔ v₂} {w} {⟨ fv₁ , fv₂ ⟩} wfd wfγ (wf-⊔ v₁~v₂ wfv₁ wfv₂) wfw
    dv⊑w ⟨ ℱv₁ , ℱv₂ ⟩ =
  let dv₁⊑w = ⊔⊑R dv⊑w in
  let dv₂⊑w = ⊔⊑L dv⊑w in
  let D-γdv₁-cv₁ = ℱ-dom-cod{v = v₁} wfd wfγ wfv₁ wfw dv₁⊑w ℱv₁ in
  let D-γdv₂-cv₂ = ℱ-dom-cod{v = v₂} wfd wfγ wfv₂ wfw dv₂⊑w ℱv₂ in
  let wf-dv₁ = wf-dom{v₁}{w} wfv₁ wfw fv₁ dv₁⊑w in
  let wf-dv₂ = wf-dom{v₂}{w} wfv₂ wfw fv₂ dv₂⊑w  in
  let wf-cv₁ = (wf-cod{v₁}{w} wfv₁ wfw fv₁ dv₁⊑w) in
  let wf-cv₂ = (wf-cod{v₂}{w} wfv₂ wfw fv₂ dv₂⊑w) in
  let wf-γdv₁ = WFEnv-extend wfγ wf-dv₁ in
  let wf-γdv₂ = WFEnv-extend wfγ wf-dv₂ in
  let dv₁~dv₂ = consistent-⊑ (~-refl{w}{wfw}) dv₁⊑w dv₂⊑w in
  let wf-γdv₁⊔dv₂ = WFEnv-extend wfγ (wf-⊔ dv₁~dv₂ wf-dv₁ wf-dv₂) in
  let Dγdv₁⊔dv₂-cv₁ = WFDenot.⊑-env wfd {γ `, dom v₁}
                        {γ `, (dom v₁ {fv₁} ⊔ dom v₂ {fv₂})}
                        (wf-γdv₁)
                        (wf-γdv₁⊔dv₂)
                        wf-cv₁
                        (`⊑-extend `⊑-refl (⊑-conj-R1 ⊑-refl))
                        D-γdv₁-cv₁ in
  let Dγdv₁⊔dv₂-cv₂ = WFDenot.⊑-env wfd {γ `, dom v₂}
                        {γ `, (dom v₁ {fv₁} ⊔ dom v₂ {fv₂})}
                        (wf-γdv₂)
                        (wf-γdv₁⊔dv₂)
                        wf-cv₂
                        (`⊑-extend `⊑-refl (⊑-conj-R2 ⊑-refl))
                        D-γdv₂-cv₂ in
  WFDenot.⊔-closed wfd (wf-γdv₁⊔dv₂) wf-cv₁ wf-cv₂
      Dγdv₁⊔dv₂-cv₁ Dγdv₁⊔dv₂-cv₂ 
        

ℱ-⊑ : ∀{D : Denotation}{γ : Env} {v w : Value}
       → WFDenot D → WFEnv γ → wf v → wf w
        → w ⊑ v → ℱ D γ v → ℱ D γ w
ℱ-⊑ d wfγ wfv wfw ⊑-⊥ ℱDγv = tt
ℱ-⊑ d wfγ wfv wfw ⊑-const ()
ℱ-⊑ d wfγ wfv (wf-⊔ c xx yy) (⊑-conj-L w⊑v w⊑v₁) ℱDγv =
    ⟨ (ℱ-⊑ d wfγ wfv xx w⊑v ℱDγv) , (ℱ-⊑ d wfγ wfv yy w⊑v₁ ℱDγv) ⟩
ℱ-⊑ d wfγ (wf-⊔ x wfv wfv₁) wfw (⊑-conj-R1 w⊑v) ⟨ fst₁ , snd₁ ⟩ =
    ℱ-⊑ d wfγ wfv wfw w⊑v fst₁
ℱ-⊑ d wfγ (wf-⊔ x wfv wfv₁) wfw (⊑-conj-R2 w⊑v) ⟨ fst₁ , snd₁ ⟩ =
    ℱ-⊑ d wfγ wfv₁ wfw w⊑v snd₁
ℱ-⊑ {D} {γ} d wfγ wfv (wf-fun wfw₁ wfw₂)
    (⊑-fun {v} {v′} {w₁} {w₂} v′⊆v fv′ dv′⊑w₁ w₂⊑cv′) ℱDγv =
    let wfv′ = wf-⊆ v′⊆v wfv in
    let wfdv′ = wf-dom wfv′ wfw₁ fv′ dv′⊑w₁ in
    let wfcv′ = wf-cod wfv′ wfw₁ fv′ dv′⊑w₁ in
    let Dγv′ = ℱ-⊆ v′⊆v ℱDγv in
    let Dγdv′cv′ = ℱ-dom-cod{v = v′} d wfγ wfv′ wfw₁ dv′⊑w₁ Dγv′ in
    let wfγw₁ = WFEnv-extend wfγ wfw₁ in
    let Dγw₁cv′ = WFDenot.⊑-env d {γ `, dom v′}{γ `, w₁}
                    (WFEnv-extend wfγ wfdv′)
                    (wfγw₁)
                    wfcv′ (`⊑-extend `⊑-refl dv′⊑w₁) Dγdv′cv′ in
    let Dγw₁w₂ = WFDenot.⊑-closed d {γ `, w₁} {cod v′}{w₂} (wfγw₁)
                   wfcv′ wfw₂ w₂⊑cv′ Dγw₁cv′ in
    Dγw₁w₂


ℱ-~ : ∀{D : Denotation}{γ : Env}{δ : Env} {u v : Value}
    → WFDenot D → WFEnv γ → WFEnv δ → γ ~′ δ → wf u → wf v
    → ℱ D γ u → ℱ D δ v → u ~ v
ℱ-~ {D} {γ} {δ} {⊥} {v} wfd wfγ wfδ γ~δ wfu wfv d1 d2 = tt
ℱ-~ {D} {γ} {δ} {const k} {v} wfd wfγ wfδ γ~δ wfu wfv () d2
ℱ-~ {D} {γ} {δ} {u₁ ↦ u₂} {⊥} wfd wfγ wfδ γ~δ wfu wfv d1 d2 = tt
ℱ-~ {D} {γ} {δ} {u₁ ↦ u₂} {const x} wfd wfγ wfδ γ~δ wfu wfv d1 ()
ℱ-~ {D} {γ} {δ} {u₁ ↦ u₂} {v₁ ↦ v₂} wfd wfγ wfδ γ~δ (wf-fun wfu₁ wfu₂) (wf-fun wfv₁ wfv₂) d1 d2
    with consistent? u₁ v₁
... | no u₁~̸v₁ = inj₂ u₁~̸v₁
... | yes u₁~v₁ = inj₁ ⟨ u₁~v₁ , u₂~v₂ ⟩
      where
      wfγu₁ = WFEnv-extend wfγ wfu₁
      wfδv₁ = WFEnv-extend wfδ wfv₁
      γu₁~δv₁ = ~′-extend γ~δ u₁~v₁
      u₂~v₂ = WFDenot.~-closed wfd (wfγu₁) (wfδv₁)
                 (γu₁~δv₁) wfu₂ wfv₂ d1 d2 
ℱ-~ {D} {γ} {δ} {u₁ ↦ u₂} {v₁ ⊔ v₂} wfd wfγ wfδ γ~δ 
    (wf-fun wfu₁ wfu₂) (wf-⊔ v₁~v₂ wfv₁ wfv₂) d1 ⟨ fst' , snd' ⟩ =
    ⟨ ℱ-~ {D}{γ}{δ}{u₁ ↦ u₂}{v₁} wfd wfγ wfδ γ~δ
           (wf-fun wfu₁ wfu₂) wfv₁ d1 fst' ,
      ℱ-~ {D}{γ}{δ}{u₁ ↦ u₂}{v₂} wfd wfγ wfδ γ~δ
           (wf-fun wfu₁ wfu₂) wfv₂ d1 snd' ⟩
ℱ-~ {D = D} {γ} {δ} {u₁ ⊔ u₂} {v} wfd wfγ wfδ γ~δ
    (wf-⊔ u₁~u₂ wfu₁ wfu₂) wfv ⟨ fst' , snd' ⟩ d2 =
    ⟨ ℱ-~ {D = D}{γ}{δ}{u₁}{v} wfd wfγ wfδ γ~δ wfu₁ wfv fst' d2 ,
      ℱ-~ {D = D}{γ}{δ}{u₂}{v} wfd wfγ wfδ γ~δ wfu₂ wfv snd' d2 ⟩


model_curry : CurryStruct ℱ
model_curry = record { ℱ-≲ = ℱ-≲ ;
                       ℱ-⊑ = ℱ-⊑ ;
                       ℱ-⊔ = λ {D}{γ}{u}{v} → ℱ-⊔ {D}{γ}{u}{v} ;
                       ℱ-⊥ = λ {D}{γ} → ℱ-⊥ {D}{γ} ;
                       ℱ-~ = λ {D}{γ}{u}{v} → ℱ-~ {D}{γ}{u}{v}
                     }


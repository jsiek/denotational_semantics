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

open import Variables
open import Primitives
open import ValueConst
open import CurryConst
open import Structures
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

domu↦codu⊑u : ∀{u} → (fu : AllFun u) → dom u {fu} ↦ cod u {fu} ⊑ u
domu↦codu⊑u {⊥} ()
domu↦codu⊑u {const k} ()
domu↦codu⊑u {v ↦ w} fu = ⊑-refl
domu↦codu⊑u {u₁ ⊔ u₂} ⟨ fu₁ , fu₂ ⟩ =
  let du₁↦cu₁⊑u₁ = domu↦codu⊑u {u₁} fu₁ in
  let du₂↦cu₂⊑u₂ = (domu↦codu⊑u {u₂} fu₂) in
    (dom u₁ ⊔ dom u₂) ↦ (cod u₁ ⊔ cod u₂)
  ⊑⟨ Dist⊔↦⊔ ⟩
    (dom u₁ {fu₁} ↦ cod u₁ {fu₁}) ⊔ (dom u₂ {fu₂} ↦ cod u₂ {fu₂})
  ⊑⟨ ⊑-conj-L (⊑-conj-R1{w = u₂} du₁↦cu₁⊑u₁) (⊑-conj-R2{v = u₁} du₂↦cu₂⊑u₂) ⟩
    u₁ ⊔ u₂
  ◼


wf-dom : ∀{u v}
       → wf u → wf v
       → (fu : AllFun u) → dom u {fu} ⊑ v
       → wf (dom u {fu})
wf-dom {⊥} wfu wfv () du⊑v
wf-dom {const k} wfu wfv () du⊑v
wf-dom {v ↦ w} (wf-fun wfv wfw) wf-v fu du⊑v = wfv
wf-dom {u₁ ⊔ u₂}{v} (wf-⊔ u₁~u₂ wfu₁ wfu₂) wfv ⟨ fu₁ , fu₂ ⟩ du⊑v =
  let du₁⊑v = ⊔⊑R du⊑v in
  let du₂⊑v = ⊔⊑L du⊑v in
  wf-⊔ (consistent-⊑ {v}{v} (~-refl{v}{wfv}) du₁⊑v du₂⊑v)
       (wf-dom wfu₁ wfv fu₁ du₁⊑v)
       (wf-dom wfu₂ wfv fu₂ du₂⊑v)

↦~dom→cod : ∀{u₁ u₂ v}
      → (fv : AllFun v)
      → u₁ ~ dom v {fv}
      → u₁ ↦ u₂ ~ v
      → u₂ ~ cod v {fv}
↦~dom→cod {u₁} {u₂} {⊥} () u₁~dv u₁↦u₂~v
↦~dom→cod {u₁} {u₂} {const k} () u₁~dv u₁↦u₂~v
↦~dom→cod {u₁} {u₂} {v₁ ↦ v₂} fv u₁~dv (inj₁ ⟨ fst₁ , snd₁ ⟩) = snd₁
↦~dom→cod {u₁} {u₂} {v₁ ↦ v₂} fv u₁~dv (inj₂ y) = ⊥-elim (y u₁~dv)
↦~dom→cod {u₁} {u₂} {v₁ ⊔ v₂} ⟨ fv₁ , fv₂ ⟩ u₁~dv ⟨ u₁↦u₂~v₁ , u₁↦u₂~v₂ ⟩ =
  let u₁~dv₁ = u~v⊔w→u~v{u₁} u₁~dv in
  let u₁~dv₂ = u~v⊔w→u~w{u₁} u₁~dv in
  u~v⊔w{u₂}{cod v₁}{cod v₂}
      (↦~dom→cod fv₁ u₁~dv₁ u₁↦u₂~v₁)
      (↦~dom→cod fv₂ u₁~dv₂ u₁↦u₂~v₂)

dom~→cod~ : ∀{u v}
          → (fu : AllFun u)
          → (fv : AllFun v)
          → u ~ v
          → dom u {fu} ~ dom v {fv}
          → cod u {fu} ~ cod v {fv}
dom~→cod~ {⊥} {v} () fv u~v du~dv
dom~→cod~ {const k} {v} () fv u~v du~dv
dom~→cod~ {u₁ ↦ u₂} {⊥} fu () u~v du~dv
dom~→cod~ {u₁ ↦ u₂} {const k} fu () u~v du~dv
dom~→cod~ {u₁ ↦ u₂} {v₁ ↦ v₂} fu fv (inj₁ ⟨ _ , u₂~v₂ ⟩) du~dv = u₂~v₂
dom~→cod~ {u₁ ↦ u₂} {v₁ ↦ v₂} fu fv (inj₂ ¬u₁~v₁) du~dv = ⊥-elim (¬u₁~v₁ du~dv)
dom~→cod~ {u₁ ↦ u₂} {v₁ ⊔ v₂} fu ⟨ fv₁ , fv₂ ⟩ ⟨ u₁↦u₂~v₁ , u₁↦u₂~v₂ ⟩ du~dv =
  let u₁~dv₁ = u~v⊔w→u~v{u₁} du~dv in
  let u₂~cv₁ = ↦~dom→cod fv₁ u₁~dv₁ u₁↦u₂~v₁ in
  let u₁~dv₂ = u~v⊔w→u~w{u₁} du~dv in
  let u₂~cv₂ = ↦~dom→cod fv₂ u₁~dv₂ u₁↦u₂~v₂ in  
  u~v⊔w{u₂}{cod v₁}{cod v₂} u₂~cv₁ u₂~cv₂
dom~→cod~ {u₁ ⊔ u₂} {v} ⟨ fu₁ , fu₂ ⟩ fv ⟨ u₁~v , u₂~v ⟩ ⟨ du₁~dv , du₂~dv ⟩ =
  ⟨ dom~→cod~ fu₁ fv u₁~v du₁~dv , dom~→cod~ fu₂ fv u₂~v du₂~dv ⟩


wf-cod : ∀{u v}
       → wf u → wf v
       → (fu : AllFun u)
       → dom u {fu} ⊑ v
       → wf (cod u {fu})
wf-cod {⊥} wfu wfv () du⊑v
wf-cod {const k} wfu wfv () du⊑v
wf-cod {v ↦ w} (wf-fun wfv wfw) wf-v fu du⊑v = wfw
wf-cod {u₁ ⊔ u₂}{v} (wf-⊔ u₁~u₂ wfu₁ wfu₂) wfv ⟨ fu₁ , fu₂ ⟩ du⊑v =
  let du₁⊑v = ⊔⊑R du⊑v in
  let du₂⊑v = ⊔⊑L du⊑v in
  let du₁~du₂ = (consistent-⊑ {v}{v} (~-refl{v}{wfv}) du₁⊑v du₂⊑v) in
  wf-⊔ (dom~→cod~ fu₁ fu₂ u₁~u₂ du₁~du₂)
       (wf-cod wfu₁ wfv fu₁ du₁⊑v)
       (wf-cod wfu₂ wfv fu₂ du₂⊑v)

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
                        (λ {x} → wf-γdv₁ {x})
                        (λ {x} → wf-γdv₁⊔dv₂ {x})
                        wf-cv₁
                        (`⊑-extend `⊑-refl (⊑-conj-R1 ⊑-refl))
                        D-γdv₁-cv₁ in
  let Dγdv₁⊔dv₂-cv₂ = WFDenot.⊑-env wfd {γ `, dom v₂}
                        {γ `, (dom v₁ {fv₁} ⊔ dom v₂ {fv₂})}
                        (λ {x} → wf-γdv₂ {x})
                        (λ {x} → wf-γdv₁⊔dv₂ {x})
                        wf-cv₂
                        (`⊑-extend `⊑-refl (⊑-conj-R2 ⊑-refl))
                        D-γdv₂-cv₂ in
  WFDenot.⊔-closed wfd (λ {x} → wf-γdv₁⊔dv₂ {x}) wf-cv₁ wf-cv₂
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
                    (λ {x} → WFEnv-extend wfγ wfdv′ {x})
                    (λ {x} → wfγw₁ {x})
                    wfcv′ (`⊑-extend `⊑-refl dv′⊑w₁) Dγdv′cv′ in
    let Dγw₁w₂ = WFDenot.⊑-closed d {γ `, w₁} {cod v′}{w₂} (λ {x} → wfγw₁{x})
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
      wfγu₁ = λ {x} → WFEnv-extend wfγ wfu₁ {x}
      wfδv₁ = λ {x} → WFEnv-extend wfδ wfv₁ {x}
      γu₁~δv₁ = λ {x} → ~′-extend γ~δ u₁~v₁ {x}
      u₂~v₂ = WFDenot.~-closed wfd (λ {x} → wfγu₁ {x}) (λ {x} → wfδv₁ {x})
                 (λ {x} → γu₁~δv₁ {x}) wfu₂ wfv₂ d1 d2 
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


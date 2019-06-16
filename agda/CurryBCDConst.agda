open import Data.Nat using (ℕ; suc ; zero)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; inspect; [_])

open import Variables
open import Primitives
open import ValueConst
open import Curry
open import Structures
open import ValueStructAux value_struct
open import OrderingAux value_struct ordering
open import Consistency
open import ConsistentAux value_struct ordering consistent
open import WFDenotMod value_struct ordering consistent
open import ModelMod value_struct ordering consistent

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

u~v⊔w→u~v : ∀{u v w}
          → u ~ v ⊔ w
          → u ~ v
u~v⊔w→u~v {⊥} {v} {w} u~v⊔w = tt
u~v⊔w→u~v {const k} {v} {w} u~v⊔w = proj₁ u~v⊔w
u~v⊔w→u~v {u₁ ↦ u₂} {v} {w} u~v⊔w = proj₁ u~v⊔w
u~v⊔w→u~v {u₁ ⊔ u₂} {v} {w} ⟨ fst₁ , snd₁ ⟩ =
    ⟨ u~v⊔w→u~v {u₁} fst₁ , u~v⊔w→u~v {u₂} snd₁ ⟩

u~v⊔w→u~w : ∀{u v w}
          → u ~ v ⊔ w
          → u ~ w
u~v⊔w→u~w {⊥} {v} {w} u~v⊔w = tt
u~v⊔w→u~w {const x} {v} {w} u~v⊔w = proj₂ u~v⊔w
u~v⊔w→u~w {u ↦ u₁} {v} {w} u~v⊔w = proj₂ u~v⊔w
u~v⊔w→u~w {u₁ ⊔ u₂} {v} {w} ⟨ fst₁ , snd₁ ⟩ =
    ⟨ u~v⊔w→u~w {u₁} fst₁ , u~v⊔w→u~w {u₂} snd₁ ⟩


wf-⊆ : ∀{v v′} → v′ ⊆ v → wf v → wf v′
wf-⊆ {⊥} {⊥} v′⊆v wfv = tt
wf-⊆ {⊥} {const {b} k} v′⊆v wfv
    with v′⊆v refl
... | ()     
wf-⊆ {⊥} {v′ ↦ v′₁} v′⊆v wfv
    with v′⊆v refl
... | ()     
wf-⊆ {⊥} {v′₁ ⊔ v′₂} v′⊆v wfv
    with ⊔⊆-inv {v′₁}{v′₂}{⊥} v′⊆v
... | ⟨ v′₁⊆⊥ , v′₂⊆⊥ ⟩ =
    let ih1 = wf-⊆ {⊥} {v′₁} v′₁⊆⊥ tt in
    let ih2 = wf-⊆ {⊥} {v′₂} v′₂⊆⊥ tt in
     ⟨ {!!} , {!!} ⟩
wf-⊆ {const x} {v′} v′⊆v wfv = {!!}
wf-⊆ {v ↦ v₁} {v′} v′⊆v wfv = {!!}
wf-⊆ {v ⊔ v₁} {v′} v′⊆v wfv = {!!}

ℱ-⊑ : ∀{Γ}{D : Denotation (suc Γ)}{γ : Env Γ} {v w : Value}
       → WFDenot (suc Γ) D → WFEnv γ → wf v
        → w ⊑ v → ℱ D γ v → ℱ D γ w
ℱ-⊑ {Γ} {D} {γ} {⊥} {⊥} wfd wfγ wfv w⊑v ℱv = tt
ℱ-⊑ {Γ} {D} {γ} {⊥} {const x} wfd wfγ wfv w⊑v ℱv
    with v⊑⊥→Below⊥ w⊑v
... | ()
ℱ-⊑ {Γ} {D} {γ} {⊥} {w ↦ w₁} wfd wfγ wfv w⊑v ℱv
    with v⊑⊥→Below⊥ w⊑v
... | ()
ℱ-⊑ {Γ} {D} {γ} {⊥} {w₁ ⊔ w₂} wfd wfγ wfv w₁⊔w₂⊑v ℱv =
  let w₁⊑v = ⊔⊑R w₁⊔w₂⊑v in
  let w₂⊑v = ⊔⊑L w₁⊔w₂⊑v in
    ⟨ ℱ-⊑ wfd wfγ wfv w₁⊑v ℱv  , ℱ-⊑ wfd wfγ wfv w₂⊑v ℱv ⟩
ℱ-⊑ {Γ} {D} {γ} {const k} {w} wfd wfγ wfv w⊑v ()
ℱ-⊑ {Γ} {D} {γ} {v₁ ↦ v₂} {w} wfd wfγ wfv w⊑v ℱv = {!!}
ℱ-⊑ {Γ} {D} {γ} {v₁ ⊔ v₂} {w} wfd wfγ wfv w⊑v₁⊔v₂ ⟨ ℱv₁ , ℱv₂ ⟩ = {!!}


{-
ℱ-⊑ : ∀{Γ}{D : Denotation (suc Γ)}{γ : Env Γ} {v w : Value}
       → WFDenot (suc Γ) D → WFEnv γ → wf v
        → w ⊑ v → ℱ D γ v → ℱ D γ w
ℱ-⊑ d wfγ wfv ⊑-⊥ ℱDγv  = tt
ℱ-⊑ d wfγ wfv ⊑-const () 
ℱ-⊑ d wfγ wfv (⊑-conj-L w⊑v w⊑v₁) ℱDγv  =
    ⟨ (ℱ-⊑ d wfγ wfv w⊑v ℱDγv) , (ℱ-⊑ d wfγ wfv w⊑v₁ ℱDγv) ⟩
ℱ-⊑ {Γ}{D}{γ}{v₁ ⊔ v₂}{w} d wfγ ⟨ v₁~v₁⊔v₂ , _ ⟩ (⊑-conj-R1 w⊑v) ℱDγv =
    ℱ-⊑ d wfγ (u~v⊔w→u~v{v₁}{v₁} v₁~v₁⊔v₂) w⊑v (proj₁ ℱDγv)
ℱ-⊑ {Γ}{D}{γ}{v₁ ⊔ v₂}{w} d wfγ ⟨ _ , v₂~v₁⊔v₂ ⟩ (⊑-conj-R2 w⊑v) ℱDγv =
    ℱ-⊑ d wfγ (u~v⊔w→u~w {v₂} v₂~v₁⊔v₂) w⊑v (proj₂ ℱDγv) 
ℱ-⊑ {Γ}{D}{γ}{v}{w₁ ↦ w₂}wfd wfγ wfv (⊑-fun{u′ = v′} v′⊆v fv′ dv′⊑w₁ w₂⊑cv′)d =
  {!!}
-}
{-
  let dv′↦cv′⊑v : (dom v′ {fv′}) ↦ (cod v′ {fv′}) ⊑ v
      dv′↦cv′⊑v = {!!} in
  let ih : D (γ `, dom v′) (cod v′)
      ih = {!!} {- ℱ-⊑ wfd wfγ wfv dv′↦cv′⊑v d -} in
  let Dγw₁cv′ : D (γ `, w₁) (cod v′)
      Dγw₁cv′ = WFDenot.⊑-env wfd {γ `, (dom v′ {fv′})} {γ `, w₁} {cod v′ {fv′}}
         ((λ {x} → WFEnv-extend{Γ}{γ}{v = dom v′ {fv′}} wfγ {!!} {x}))
         (λ {x} → WFEnv-extend{Γ}{γ}{v = w₁} wfγ {!!} {x})
         {!!}
         (`⊑-extend `⊑-refl dv′⊑w₁)
         ih in 
  WFDenot.⊑-closed wfd {!!} {!!} {!!} w₂⊑cv′ Dγw₁cv′
-}
{-
ℱ-⊑ {v = v}{w} d wfγ wfv ℱDγv (⊑-trans{v = v₁} w⊑v w⊑v₁) =
    {- Need subformula property!! Or add wf requirement to ⊑-trans? -}
    ℱ-⊑ d wfγ {!!} (ℱ-⊑ d wfγ wfv ℱDγv w⊑v₁) w⊑v
ℱ-⊑ {Γ}{D}{γ}{v ↦ w}{v' ↦ w'} d wfγ wfv ℱDγv (⊑-fun v⊑v' w'⊑w) =
  WFDenot.⊑-closed d (WFDenot.⊑-env d ℱDγv b) w'⊑w
  where b : (γ `, v) `⊑ (γ `, v')
        b Z = v⊑v'
        b (S x) = ⊑-refl 
ℱ-⊑ {γ = γ} d wfγ (wf-⊔ a (wf-fun wfv wfw) c) ℱDγv (⊑-dist{v = v}) =
  WFDenot.⊔-closed d (λ {x} → G {x}) (proj₁ ℱDγv) (proj₂ ℱDγv)
  where
  G : WFEnv (γ `, v)
  G {Z} = wfv
  G {S x} = wfγ
-}

ℱ-~ : ∀{Γ}{D : Denotation (suc Γ)}{γ : Env Γ}{δ : Env Γ} {u v : Value}
    → WFDenot (suc Γ) D → WFEnv γ → WFEnv δ → γ ~′ δ → wf u → wf v
    → ℱ D γ u → ℱ D δ v → u ~ v
ℱ-~ {D = D} {γ} {δ} {⊥} {v} wfd wfγ wfδ γ~δ wfu wfv d1 d2 = tt
ℱ-~ {D = D} {γ} {δ} {const k} {v} wfd wfγ wfδ γ~δ wfu wfv () d2
ℱ-~ {D = D} {γ} {δ} {u₁ ↦ u₂} {⊥} wfd wfγ wfδ γ~δ wfu wfv d1 d2 = tt
ℱ-~ {D = D} {γ} {δ} {u₁ ↦ u₂} {const x} wfd wfγ wfδ γ~δ wfu wfv d1 ()
ℱ-~ {Γ} {D} {γ} {δ} {u₁ ↦ u₂} {v₁ ↦ v₂} wfd wfγ wfδ γ~δ wfu wfv d1 d2
    with consistent? u₁ v₁
... | no u₁~̸v₁ = inj₂ u₁~̸v₁
... | yes u₁~v₁ = inj₁ ⟨ u₁~v₁ , u₂~v₂ ⟩
      where
      wfγu₁ : WFEnv (γ `, u₁)
      wfγu₁ {Z} = {!!}
      wfγu₁ {S x} = wfγ
      wfδv₁ : WFEnv (δ `, v₁)
      wfδv₁ {Z} = {!!}
      wfδv₁ {S x} = wfδ
      γu₁~δv₁ : (γ `, u₁) ~′ (δ `, v₁)
      γu₁~δv₁ {Z} = u₁~v₁
      γu₁~δv₁ {S x} = γ~δ {x}
      u₂~v₂ = WFDenot.~-closed wfd (λ {x} → wfγu₁ {x}) (λ {x} → wfδv₁ {x})
                 (λ {x} → γu₁~δv₁ {x}) {!!} {!!} d1 d2 
  
ℱ-~ {Γ}{D} {γ} {δ} {u₁ ↦ u₂} {v₁ ⊔ v₂} wfd wfγ wfδ γ~δ 
    wfu wfv d1 ⟨ fst' , snd' ⟩ =
    ⟨ ℱ-~ {Γ}{D}{γ}{δ}{u₁ ↦ u₂}{v₁} wfd wfγ wfδ γ~δ
           (wf-fun {!!} {!!}) {!!} d1 fst' ,
      ℱ-~ {Γ}{D}{γ}{δ}{u₁ ↦ u₂}{v₂} wfd wfγ wfδ γ~δ
           (wf-fun {!!} {!!}) {!!} d1 snd' ⟩
ℱ-~ {D = D} {γ} {δ} {u₁ ⊔ u₂} {v} wfd wfγ wfδ γ~δ
    wfu wfv ⟨ fst' , snd' ⟩ d2 =
    ⟨ ℱ-~ {D = D}{γ}{δ}{u₁}{v} wfd wfγ wfδ γ~δ {!!} wfv fst' d2 ,
      ℱ-~ {D = D}{γ}{δ}{u₂}{v} wfd wfγ wfδ γ~δ {!!} wfv snd' d2 ⟩

{-
model_curry : ModelCurry ℱ
model_curry = record { ℱ-≲ = ℱ-≲ ;
                       ℱ-⊑ = ℱ-⊑ ;
                       ℱ-⊔ = λ {Γ}{D}{γ}{u}{v} → ℱ-⊔ {Γ}{D}{γ}{u}{v} ;
                       ℱ-⊥ = λ {Γ}{D}{γ} → ℱ-⊥ {Γ}{D}{γ} ;
                       ℱ-~ = λ {Γ}{D}{γ}{u}{v} → ℱ-~ {Γ}{D}{γ}{u}{v}
                     }
-}

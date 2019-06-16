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
open import CurryConst
open import Structures
open import ValueStructAux value_struct
open import OrderingAux value_struct ordering
open import Consistency
open import ConsistentAux value_struct ordering consistent
open import WFDenotMod value_struct ordering consistent
open import ModelMod value_struct ordering consistent

module CurryConstProps where

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



{-
ℱ-⊑ : ∀{Γ}{D : Denotation (suc Γ)}{γ : Env Γ} {v w : Value}
       → WFDenot (suc Γ) D → WFEnv γ → wf v → wf w 
        → w ⊑ v → ℱ D γ v → ℱ D γ w
ℱ-⊑ {Γ} {D} {γ} {⊥} {⊥} wfd wfγ wfv wfw w⊑v ℱv = tt
ℱ-⊑ {Γ} {D} {γ} {⊥} {const x} wfd wfγ wfv wfw w⊑v ℱv
    with v⊑⊥→Below⊥ w⊑v
... | ()
ℱ-⊑ {Γ} {D} {γ} {⊥} {w ↦ w₁} wfd wfγ wfv wfw w⊑v ℱv
    with v⊑⊥→Below⊥ w⊑v
... | ()
ℱ-⊑ {Γ} {D} {γ} {⊥} {w₁ ⊔ w₂} wfd wfγ wfv (wf-⊔ w₁~w₂ wfw₁ wfw₂) w₁⊔w₂⊑v ℱv =
  let w₁⊑v = ⊔⊑R w₁⊔w₂⊑v in
  let w₂⊑v = ⊔⊑L w₁⊔w₂⊑v in
    ⟨ ℱ-⊑ wfd wfγ wfv wfw₁ w₁⊑v ℱv  , ℱ-⊑ wfd wfγ wfv wfw₂ w₂⊑v ℱv ⟩
ℱ-⊑ {Γ} {D} {γ} {const k} {w} wfd wfγ wfv wfw w⊑v ()
ℱ-⊑ {Γ} {D} {γ} {v₁ ↦ v₂} {⊥} wfd wfγ wfv wfw w⊑v ℱv = tt
ℱ-⊑ {Γ} {D} {γ} {v₁ ↦ v₂} {const x} wfd wfγ wfv wfw w⊑v ℱv
    with ⊑↦→BelowFun w⊑v
... | ()
ℱ-⊑ {Γ} {D} {γ} {v₁ ↦ v₂} {w₁ ↦ w₂} wfd wfγ
    (wf-fun wfv₁ wfv₂) (wf-fun wfw₁ wfw₂) w⊑v ℱv
    with ⊑-fun-inv′ w⊑v
... | ⟨ v₁⊑w₁ , w₂⊑v₂ ⟩ =
    let Dw₁v₂ : D (γ `, w₁) v₂
        Dw₁v₂ = WFDenot.⊑-env wfd {γ `, v₁} {γ `, w₁}{v₂}
                (λ {x} → WFEnv-extend wfγ wfv₁ {x})
                (λ {x} → WFEnv-extend wfγ wfw₁ {x})
                wfv₂ (`⊑-extend `⊑-refl v₁⊑w₁)
                ℱv in
    WFDenot.⊑-closed wfd (λ {x} → WFEnv-extend wfγ wfw₁ {x})
                     wfv₂ wfw₂ w₂⊑v₂ Dw₁v₂
ℱ-⊑ {Γ} {D} {γ} {v₁ ↦ v₂} {w₁ ⊔ w₂} wfd wfγ wfv wfw w⊑v ℱv = {!!}
ℱ-⊑ {Γ} {D} {γ} {v₁ ⊔ v₂} {w} wfd wfγ wfv wfw w⊑v₁⊔v₂ ⟨ ℱv₁ , ℱv₂ ⟩ = {!!}
   {- this case looks hard -}
-}

ℱ-⊑ : ∀{Γ}{D : Denotation (suc Γ)}{γ : Env Γ} {v w : Value}
       → WFDenot (suc Γ) D → WFEnv γ → wf v → wf w
        → w ⊑ v → ℱ D γ v → ℱ D γ w
ℱ-⊑ d wfγ wfv wfw ⊑-⊥ ℱDγv = tt
ℱ-⊑ d wfγ wfv wfw ⊑-const ()
ℱ-⊑ d wfγ wfv (wf-⊔ c xx yy) (⊑-conj-L w⊑v w⊑v₁) ℱDγv =
    ⟨ (ℱ-⊑ d wfγ wfv xx w⊑v ℱDγv) , (ℱ-⊑ d wfγ wfv yy w⊑v₁ ℱDγv) ⟩
ℱ-⊑ d wfγ (wf-⊔ x wfv wfv₁) wfw (⊑-conj-R1 w⊑v) ⟨ fst₁ , snd₁ ⟩ =
    ℱ-⊑ d wfγ wfv wfw w⊑v fst₁
ℱ-⊑ d wfγ (wf-⊔ x wfv wfv₁) wfw (⊑-conj-R2 w⊑v) ⟨ fst₁ , snd₁ ⟩ =
    ℱ-⊑ d wfγ wfv₁ wfw w⊑v snd₁
ℱ-⊑ {Γ} {D} {γ} d wfγ wfv (wf-fun wfw₁ wfw₂) (⊑-fun {v} {v′} {w₁} {w₂} v′∈v fv′ dv′⊑w₁ w₂⊑cv′) ℱDγv = {!!}

{-
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

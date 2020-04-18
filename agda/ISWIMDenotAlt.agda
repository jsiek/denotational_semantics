open import Primitives
open import Structures
open import ValueConst
open import EvalISWIM
open import ISWIM
open import ValueConst
open import ValueStructAux value_struct
open import OrderingAux value_struct ordering
open import Consistency
open import ConsistentAux value_struct ordering consistent
open import CurryConst
open import PrimConst
open import ModelCurryConst
open import ModelCallByValue value_struct ordering consistent ℱ model_curry
open import ISWIMDenot value_struct ordering _●_ ℱ (λ {P} k v → ℘ {P} k v)
import Filter
open Filter.ForISWIM value_struct ordering consistent _●_ ℱ model_curry_apply
   (λ {P} k v → ℘ {P} k v)
   (λ {P} {k} {u} {v} → ℘-⊔ {P} {k} {u} {v})
   ℘-⊑
   (λ {P} {k} {u} {v} → ℘-~ {P} {k} {u} {v})

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; trans; sym; cong; cong₂; cong-app)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum
open import Data.Empty using (⊥-elim) renaming (⊥ to Bot)
open import Data.Unit
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Nullary using (Dec; yes; no)

module ISWIMDenotAlt where
  
infixl 7 _●′_
_●′_ : Denotation → Denotation → Denotation
_●′_ D₁ D₂ γ w = Σ[ v₁ ∈ Value ] Σ[ v₂ ∈ Value ] Σ[ v₃ ∈ Value ]
    wf v₁ × wf v₂ × wf v₃ × D₁ γ v₁ × D₂ γ v₂
    × v₃ ↦ w ⊑ v₁ × v₃ ⊑ v₂

ℰ′ : Term → Denotation
ℰ′ ($ P k) γ v = ℘ {P} k v
ℰ′ (` x) γ v = v ≡ γ x
ℰ′ (ƛ N) = ℱ (ℰ′ N)
ℰ′ (L · M) = (ℰ′ L) ●′ (ℰ′ M)

AllFun⊥ : (u : Value) → Set
AllFun⊥ ⊥ = ⊤
AllFun⊥ (const k) = Bot
AllFun⊥ (v ↦ w) = ⊤
AllFun⊥ (u ⊔ v) = AllFun⊥ u × AllFun⊥ v 

ℱ-inv : ∀{D : Denotation}{ρ : Env}{u : Value}
      → ℱ D ρ u
      → (∀{v w} → v ↦ w ∈ u → D (ρ `, v) w) × AllFun⊥ u
ℱ-inv {D} {ρ} {⊥} ℱDu = ⟨ (λ {v} {w} ()) , tt ⟩
ℱ-inv {D} {ρ} {const k} ()
ℱ-inv {D} {ρ} {u₁ ↦ u₂} ℱDu = ⟨ (λ {refl → ℱDu}) , tt ⟩
ℱ-inv {D} {ρ} {u₁ ⊔ u₂} ⟨ ℱDu1 , ℱDu2 ⟩
    with ℱ-inv {D} {ρ} {u₁} ℱDu1
      | ℱ-inv {D} {ρ} {u₂} ℱDu2
... | ⟨ all1 , fu1 ⟩ | ⟨ all2 , fu2 ⟩ =
      ⟨ G , ⟨ fu1 , fu2 ⟩ ⟩
   where
   G : ∀{v w : Value} → v ↦ w ∈ u₁ ⊎ v ↦ w ∈ u₂ → D (ρ `, v) w
   G (inj₁ x) = all1 x
   G (inj₂ y) = all2 y

ℱ-intro : ∀{D : Denotation}{ρ : Env}{u : Value}
      → (∀{v w} → v ↦ w ∈ u → D (ρ `, v) w)
      → AllFun⊥ u
      → ℱ D ρ u
ℱ-intro {D} {ρ} {⊥} Dvw fu = tt
ℱ-intro {D} {ρ} {const k} Dvw ()
ℱ-intro {D} {ρ} {u₁ ↦ u₂} Dvw fu = Dvw refl
ℱ-intro {D} {ρ} {u₁ ⊔ u₂} Dvw ⟨ fu1 , fu2 ⟩ =
   ⟨ ℱ-intro (λ {v} {w} z → Dvw (inj₁ z)) fu1 ,
     ℱ-intro (λ {v} {w} z → Dvw (inj₂ z)) fu2 ⟩


ℰ′→ℰ : ∀{M : Term}{ρ : Env}{v : Value}
     → WFEnv ρ → wf v
     → ℰ′ M ρ v → ℰ M ρ v
ℰ′→ℰ {` x} {ρ} {v} wfρ wfv refl = ⊑-refl
ℰ′→ℰ {$ P k} {ρ} {v} wfρ wfv v∈ℰ′Mρ = v∈ℰ′Mρ
ℰ′→ℰ {ƛ N} {ρ} {v} wfρ wfv v∈ℰ′Mρ
    with ℱ-inv{ℰ′ N}{ρ}{v} v∈ℰ′Mρ
... | ⟨ all , fv ⟩ =
    ℱ-intro IH fv
    where
    IH : ∀{u w} → u ↦ w ∈ v → ℰ N (ρ `, u) w
    IH {u}{w} u↦w∈v
        with wf-∈ u↦w∈v wfv
    ... | wf-fun wfu wfw =
        let wfρ' = WFEnv-extend {ρ} wfρ wfu in
        ℰ′→ℰ {N} (λ {x} → wfρ' {x}) wfw (all {u}{w} u↦w∈v)
ℰ′→ℰ {L · M} {ρ} {v} wfρ wfv
  ⟨ v₁ , ⟨ v₂ , ⟨ v₃ , ⟨ wfv1 , ⟨ wfv2 , ⟨ wfv3 , 
  ⟨ Lv1 , ⟨ Mv2 , ⟨ v3↦v4⊑v1 , v3⊑v2 ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ =
  let Lv1 = ℰ′→ℰ {L} wfρ wfv1 Lv1 in  
  let Mv2 = ℰ′→ℰ {M} wfρ wfv2 Mv2 in
  let Lv3↦v = ℰ-⊑ {ρ}{L} wfρ wfv1 (wf-fun wfv3 wfv) v3↦v4⊑v1 Lv1 in
  let Mv3 = ℰ-⊑ {ρ}{M} wfρ wfv2 wfv3 v3⊑v2 Mv2 in
  ⟨ v₃ , ⟨ wfv3 , ⟨ Lv3↦v , Mv3 ⟩ ⟩ ⟩


ℰ′-~ : ∀ {γ : Env} {δ : Env} {M : Term} {u v : Value}
        → WFEnv γ → WFEnv δ → γ ~′ δ → wf u → wf v
        → ℰ′ M γ u → ℰ′ M δ v → u ~ v

Closed-~  : Denotation → Set
Closed-~ D = ∀{γ δ u v}
               → WFEnv γ → WFEnv δ → γ ~′ δ → wf u → wf v
               → D γ u → D δ v → u ~ v


ℱ-~′ : ∀{D : Denotation}{γ : Env}{δ : Env} {u v : Value}
    → Closed-~ D → WFEnv γ → WFEnv δ → γ ~′ δ → wf u → wf v
    → ℱ D γ u → ℱ D δ v → u ~ v
ℱ-~′ {D = D} {γ} {δ} {⊥} {v} D~ wfγ wfδ γ~δ wfu wfv d1 d2 = tt
ℱ-~′ {D = D} {γ} {δ} {const k} {v} D~ wfγ wfδ γ~δ wfu wfv () d2
ℱ-~′ {D = D} {γ} {δ} {u₁ ↦ u₂} {⊥} D~ wfγ wfδ γ~δ wfu wfv d1 d2 = tt
ℱ-~′ {D = D} {γ} {δ} {u₁ ↦ u₂} {const x} D~ wfγ wfδ γ~δ wfu wfv d1 ()
ℱ-~′ {D} {γ} {δ} {u₁ ↦ u₂} {v₁ ↦ v₂} D~ wfγ wfδ γ~δ (wf-fun wfu₁ wfu₂) (wf-fun wfv₁ wfv₂) d1 d2
    with consistent? u₁ v₁
... | no u₁~̸v₁ = inj₂ u₁~̸v₁
... | yes u₁~v₁ = inj₁ ⟨ u₁~v₁ , u₂~v₂ ⟩
      where
      wfγu₁ = λ {x} → WFEnv-extend {γ}{u₁} wfγ wfu₁ {x}
      wfδv₁ = λ {x} → WFEnv-extend wfδ wfv₁ {x}
      γu₁~δv₁ = λ {x} → ~′-extend γ~δ u₁~v₁ {x}
      u₂~v₂ = D~ (λ {x} → wfγu₁ {x}) (λ {x} → wfδv₁ {x})
                 (λ {x} → γu₁~δv₁ {x}) wfu₂ wfv₂ d1 d2 
ℱ-~′ {D} {γ} {δ} {u₁ ↦ u₂} {v₁ ⊔ v₂} D~ wfγ wfδ γ~δ 
    (wf-fun wfu₁ wfu₂) (wf-⊔ v₁~v₂ wfv₁ wfv₂) d1 ⟨ fst' , snd' ⟩ =
    ⟨ ℱ-~′ {D}{γ}{δ}{u₁ ↦ u₂}{v₁} D~ wfγ wfδ γ~δ
           (wf-fun wfu₁ wfu₂) wfv₁ d1 fst' ,
      ℱ-~′ {D}{γ}{δ}{u₁ ↦ u₂}{v₂} D~ wfγ wfδ γ~δ
           (wf-fun wfu₁ wfu₂) wfv₂ d1 snd' ⟩
ℱ-~′ {D = D} {γ} {δ} {u₁ ⊔ u₂} {v} D~ wfγ wfδ γ~δ
    (wf-⊔ u₁~u₂ wfu₁ wfu₂) wfv ⟨ fst' , snd' ⟩ d2 =
    ⟨ ℱ-~′ {D = D}{γ}{δ}{u₁}{v} D~ wfγ wfδ γ~δ wfu₁ wfv fst' d2 ,
      ℱ-~′ {D = D}{γ}{δ}{u₂}{v} D~ wfγ wfδ γ~δ wfu₂ wfv snd' d2 ⟩


●-~′ : ∀{D₁ D₂ : Denotation}{γ : Env}{δ : Env} {u v : Value}
    → Closed-~ D₁ → Closed-~ D₂ → WFEnv γ → WFEnv δ → γ ~′ δ → wf u → wf v 
    → (D₁ ●′ D₂) γ u → (D₁ ●′ D₂) δ v → u ~ v
●-~′{D₁}{D₂}{γ}{δ}{u}{v} wf1 wf2 wfγ wfδ γ~δ wfu wfv
    ⟨ u1 , ⟨ u2 , ⟨ u3 , 
    ⟨ wfu1 , ⟨ wfu2 , ⟨ wfu3 , 
    ⟨ d11 , ⟨ d12 , ⟨ lt1 , lt2 ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ 
    ⟨ v1 , ⟨ v2 , ⟨ v3 , 
    ⟨ wfv1 , ⟨ wfv2 , ⟨ wfv3 ,
    ⟨ d21 , ⟨ d22 , ⟨ lt4 , lt5 ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
    with consistent-⊑ (wf1 wfγ wfδ γ~δ wfu1 wfv1 d11 d21) lt1 lt4 
... | inj₁ ⟨ _ , u4~v4 ⟩ = u4~v4
... | inj₂ u'~̸v' = 
    let u'~v' = consistent-⊑ (wf2 wfγ wfδ γ~δ wfu2 wfv2 d12 d22) lt2 lt5 in
    ⊥-elim (contradiction u'~v' u'~̸v')

ℰ′-~ {γ}{δ}{` x}{u}{v} wfγ wfδ γ~δ wfu wfv ℰMγu ℰMδv
     rewrite ℰMγu | ℰMδv = γ~δ {x}
ℰ′-~ {M = $ P k}{u}{v} wfγ wfδ γ~δ wfu wfv ℰMγu ℰMδv =
     ℘-~{P}{k}{u}{v} ℰMγu ℰMδv
ℰ′-~ {γ}{δ}{ƛ N}{u}{v} wfγ wfδ γ~δ wfu wfv
     ℰMγu ℰMγv =
     ℱ-~′ {ℰ′ N}{γ}{δ}{u}{v} (ℰ′-~{M = N}) wfγ wfδ γ~δ wfu wfv ℰMγu ℰMγv
ℰ′-~ {γ}{δ}{L · M}{u}{v} wfγ wfδ γ~δ
      wfu wfv ℰMγu ℰMδv =
      ●-~′ {ℰ′ L}{ℰ′ M}{γ}{δ}{u}{v} (ℰ′-~{M = L}) (ℰ′-~{M = M}) wfγ wfδ γ~δ
      wfu wfv ℰMγu ℰMδv

ℰ→ℰ′ : ∀{M : Term}{ρ ρ' : Env}{v : Value}
     → WFEnv ρ → WFEnv ρ' → ρ `⊑ ρ' → wf v 
     → ℰ M ρ v
     → Σ[ v′ ∈ Value ] wf v′ × ℰ′ M ρ' v′ × v ⊑ v′
ℰ→ℰ′ {` x}{ρ}{ρ'}{v} wfρ wfρ' ρ⊑ρ' wfv ℰMρv =
    ⟨ ρ' x , ⟨ wfρ' , ⟨ refl , ⊑-trans ℰMρv (ρ⊑ρ' x) ⟩ ⟩ ⟩
ℰ→ℰ′ {$ P k}{ρ}{ρ'}{v} wfρ wfρ' ρ⊑ρ' wfv ℰMρv =
    ⟨ v , ⟨ wfv , ⟨ ℰMρv , ⊑-refl ⟩ ⟩ ⟩
ℰ→ℰ′ {ƛ N}{ρ}{ρ'}{v} wfρ wfρ' ρ⊑ρ' wfv ℰMρv =
   G wfv ℰMρv
   where
   G : ∀{v} → wf v → ℱ (ℰ N) ρ v
     → Σ[ v′ ∈ Value ] wf v′ × ℱ (ℰ′ N) ρ' v′ × v ⊑ v′
   G {⊥} wfv ℱNv = ⟨ ⊥ , ⟨ wf-bot , ⟨ tt , ⊑-⊥ ⟩ ⟩ ⟩
   G {const k} wfv ()
   G {v₁ ↦ v₂} (wf-fun wfv1 wfv2) ℱNv
       with ℰ→ℰ′ {N}{ρ `, v₁}{ρ' `, v₁}{v₂}
                  (λ {x} → WFEnv-extend wfρ wfv1 {x})
                  (λ {x} → WFEnv-extend wfρ' wfv1 {x})
                  (`⊑-extend ρ⊑ρ' ⊑-refl) wfv2 ℱNv
   ... | ⟨ v′ , ⟨ wfv′ , ⟨ Mv′ , v⊑v′ ⟩ ⟩ ⟩ =
         ⟨ v₁ ↦ v′ , ⟨ wf-fun wfv1 wfv′ , ⟨ Mv′ , ⊑-fun′ ⊑-refl v⊑v′ ⟩ ⟩ ⟩
   G {v₁ ⊔ v₂} (wf-⊔ v₁~v₂ wfv1 wfv2) ⟨ ℱNv1 , ℱNv2 ⟩
       with G {v₁} wfv1 ℱNv1
          | G {v₂} wfv2 ℱNv2
   ... | ⟨ v1′ , ⟨ wfv1′ , ⟨ Mv1′ , v⊑v1′ ⟩ ⟩ ⟩
       | ⟨ v2′ , ⟨ wfv2′ , ⟨ Mv2′ , v⊑v2′ ⟩ ⟩ ⟩ =
         let v1′~v2′ : v1′ ~ v2′
             v1′~v2′ = ℱ-~′ {ℰ′ N}{u = v1′}{v = v2′}
                           (ℰ′-~{M = N}) wfρ' wfρ' (~′-refl {ρ'} wfρ')
                           wfv1′ wfv2′ Mv1′ Mv2′ in
         ⟨ (v1′ ⊔ v2′) ,
         ⟨ (wf-⊔ v1′~v2′ wfv1′ wfv2′) , ⟨ ⟨ Mv1′ , Mv2′ ⟩ ,
           (⊑-conj-L (⊑-conj-R1 v⊑v1′) (⊑-conj-R2 v⊑v2′)) ⟩ ⟩ ⟩
ℰ→ℰ′ {L · M}{ρ}{ρ'}{v} wfρ wfρ' ρ⊑ρ' wfv
   ⟨ u , ⟨ wfu , ⟨ Luw , Mu ⟩ ⟩ ⟩
    with ℰ→ℰ′ {L} wfρ wfρ' ρ⊑ρ' (wf-fun wfu wfv) Luw
       | ℰ→ℰ′ {M} wfρ wfρ' ρ⊑ρ' wfu Mu
... | ⟨ v1 , ⟨ wfv1 , ⟨ Lv1 , uv⊑v1 ⟩ ⟩ ⟩
    | ⟨ u1 , ⟨ wfu1 , ⟨ Mu1 , u⊑u1 ⟩ ⟩ ⟩ =
      ⟨ v ,
      ⟨ wfv ,
      ⟨ ⟨ v1 , ⟨ u1 , ⟨ u , ⟨ wfv1 , ⟨ wfu1 , ⟨ wfu , 
        ⟨ Lv1 , ⟨ Mu1 , ⟨ uv⊑v1 , u⊑u1 ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ,
        ⊑-refl ⟩ ⟩ ⟩

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
open import Compositionality
open ISWIMDenotAux value_struct ordering _●_ ℱ consistent model_curry_apply (λ {P} k v → ℘ {P} k v)
open import SoundnessISWIM using (soundness; ℰ-⊥)

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


module AdequacyISWIM where


𝕍 : Value → Val → Set
𝕍 ⊥ v = ⊤
𝕍 (const {B} k) (val-const {P} p) = ℘ {P} p (const {B} k)
𝕍 (const {B} k) (val-clos N γ) = Bot
𝕍 (v ↦ w) (val-const {P} p) = ℘ {P} p (v ↦ w)
𝕍 (v ↦ w) (val-clos N γ) =
    (∀{c : Val} → 𝕍 v c → Σ[ c' ∈ Val ] (γ ,' c) ⊢ N ⇓ c'  ×  𝕍 w c')
𝕍 (u ⊔ v) c = 𝕍 u c × 𝕍 v c


𝔾 : ∀{Γ} → Env Γ → ValEnv Γ → Set
𝔾 {Γ} γ γ' = ∀{x : Var Γ} → 𝕍 (γ x) (γ' x)

𝔾-∅ : 𝔾 `∅ ∅'
𝔾-∅ {()}

𝔾-ext : ∀{Γ}{γ : Env Γ}{γ' : ValEnv Γ}{v c}
      → 𝔾 γ γ' → 𝕍 v c → 𝔾 (γ `, v) (γ' ,' c)
𝔾-ext {Γ} {γ} {γ'} g e {Z} = e
𝔾-ext {Γ} {γ} {γ'} g e {S x} = g

sub-𝕍 : ∀{c : Val}{v v'} → wf v → wf v' → 𝕍 v c → v' ⊑ v → 𝕍 v' c

sub-𝕍 {c} wfv wfv' vc ⊑-⊥ = tt
sub-𝕍 {val-const {base B} k} wfv wfv' vc (⊑-const {B′} {k′})
    with base-eq? B B′
... | yes eq rewrite eq = vc
... | no neq = vc
sub-𝕍 {val-const {B ⇒ P} p} wfv wfv' () (⊑-const {B′} {k}) 
sub-𝕍 {val-clos N x} wfv wfv' () ⊑-const
sub-𝕍 wfu (wf-⊔ v~w wfv wfw) vc (⊑-conj-L lt1 lt2) =
    ⟨ sub-𝕍 wfu wfv vc lt1 , sub-𝕍 wfu wfw vc lt2 ⟩
sub-𝕍 (wf-⊔ v₁~v₂ wfv₁ wfv₂) wfv' ⟨ vv1 , vv2 ⟩ (⊑-conj-R1 lt) =
    sub-𝕍 wfv₁ wfv' vv1 lt
sub-𝕍 (wf-⊔ v₁~v₂ wfv₁ wfv₂) wfv' ⟨ vv1 , vv2 ⟩ (⊑-conj-R2 lt) =
    sub-𝕍 wfv₂ wfv' vv2 lt
sub-𝕍 {c}{u}{v' = v ↦ w} wfu (wf-fun wfv wfw) 𝕍uc
   (⊑-fun{u′ = u′} u′⊆u fu′ du′⊑v w⊑cu′) =
   let 𝕍u′c = 𝕍-⊆ 𝕍uc u′⊆u in
   let 𝕍du′↦cu′c = 𝕍-dom-cod wfv fu′ du′⊑v 𝕍u′c in
   lemma {dom u′}{cod u′}{v}{w}{c} wfv wfw
         (wf-dom (wf-⊆ u′⊆u wfu) wfv fu′ du′⊑v)
         (wf-cod (wf-⊆ u′⊆u wfu) wfv fu′ du′⊑v)
         du′⊑v w⊑cu′ 𝕍du′↦cu′c  

   where
   𝕍-∈ : ∀{c}{u v} → 𝕍 u c → v ∈ u → 𝕍 v c
   𝕍-∈ {c} {⊥} {v} 𝕍uc refl = tt
   𝕍-∈ {c} {const k} {v} 𝕍uc refl = 𝕍uc
   𝕍-∈ {c} {u₁ ↦ u₂} {v} 𝕍uc refl = 𝕍uc
   𝕍-∈ {c} {u₁ ⊔ u₂} {v} ⟨ fst₁ , snd₁ ⟩ (inj₁ x) = 𝕍-∈ fst₁ x
   𝕍-∈ {c} {u₁ ⊔ u₂} {v} ⟨ fst₁ , snd₁ ⟩ (inj₂ y) = 𝕍-∈ snd₁ y
   
   𝕍-⊆ : ∀{c}{u v} → 𝕍 u c → v ⊆ u → 𝕍 v c
   𝕍-⊆ {c} {u} {⊥} 𝕍uc v⊆u = tt
   𝕍-⊆ {c} {u} {const k} 𝕍uc v⊆u = 𝕍-∈ 𝕍uc (v⊆u refl) 
   𝕍-⊆ {c} {u} {v₁ ↦ v₂} 𝕍uc v⊆u = 𝕍-∈ 𝕍uc (v⊆u refl) 
   𝕍-⊆ {c} {u} {v₁ ⊔ v₂} 𝕍uc v⊆u
       with ⊔⊆-inv v⊆u
   ... | ⟨ v₁⊆u , v₂⊆u ⟩ = ⟨ 𝕍-⊆ 𝕍uc v₁⊆u , 𝕍-⊆ 𝕍uc v₂⊆u ⟩

   dist : ∀{c}{v w v' w' u}
        → wf u → v ⊑ u → v' ⊑ u
        → 𝕍 (v ↦ w) c
        → 𝕍 (v' ↦ w') c
        → 𝕍 ((v ⊔ v') ↦ (w ⊔ w')) c
   dist {val-const {p} f} {v} {w} {v'} {w'} {u} wfu v⊑u v'⊑u 𝕍v↦wc 𝕍v'↦w'c
       with p
   ... | base b = ⊥-elim 𝕍v↦wc
   ... | b ⇒ p'
       with 𝕍v↦wc | 𝕍v'↦w'c
   ... | ⟨ k , ⟨ k⊑v , ℘pkw ⟩ ⟩ | ⟨ k′ , ⟨ k′⊑v' , ℘pk′w' ⟩ ⟩ 
       rewrite sym (k⊑v→k′⊑v→k′≡k wfu (⊑-trans k⊑v v⊑u) (⊑-trans k′⊑v' v'⊑u)) =
       ⟨ k , ⟨ (⊑-conj-R1 k⊑v) , ⟨ ℘pkw , ℘pk′w' ⟩ ⟩ ⟩
   dist {val-clos N γ} {v} {w} {v'} {w'} {u} wfu v⊑u v'⊑u 𝕍v↦wc 𝕍v'↦w'c
        {c} ⟨ 𝕍vc , 𝕍v'c ⟩
       with 𝕍v↦wc 𝕍vc | 𝕍v'↦w'c 𝕍v'c 
   ... | ⟨ c₁ , ⟨ L⇓c₁ , 𝕍wc₁ ⟩ ⟩
       | ⟨ c₂ , ⟨ L⇓c₂ , 𝕍w'c₂ ⟩ ⟩
       rewrite sym (⇓-determ L⇓c₁ L⇓c₂) =
       ⟨ c₁ , ⟨ L⇓c₁ , ⟨ 𝕍wc₁ , 𝕍w'c₂ ⟩ ⟩ ⟩
       
   𝕍-dom-cod : ∀{c}{u v}
             → wf v
             → (fu : AllFun u)
             → dom u {fu} ⊑ v
             → 𝕍 u c
             → 𝕍 (dom u {fu} ↦ cod u {fu}) c
   𝕍-dom-cod {c} {⊥} {v} wfv () du⊑v 𝕍uc
   𝕍-dom-cod {c} {const k} {v} wfv () du⊑v 𝕍uc
   𝕍-dom-cod {c} {u₁ ↦ u₂} {v} wfv fu du⊑v 𝕍uc = 𝕍uc
   𝕍-dom-cod {c} {u₁ ⊔ u₂} {v} wfv ⟨ fu₁ , fu₂ ⟩ du⊑v ⟨ 𝕍u₁c , 𝕍u₂c ⟩
       with ⊔⊑-inv du⊑v
   ... | ⟨ du₁⊑v , du₂⊑v ⟩ =
       let ih1 = 𝕍-dom-cod wfv fu₁ du₁⊑v 𝕍u₁c in
       let ih2 = 𝕍-dom-cod wfv fu₂ du₂⊑v 𝕍u₂c in
       dist{c} wfv du₁⊑v du₂⊑v ih1 ih2

   lemma : ∀{du cu v w}{c}
         → wf v → wf w → wf du → wf cu
         → du ⊑ v → w ⊑ cu → 𝕍 (du ↦ cu) c
         → 𝕍 (v ↦ w) c
   lemma {du} {cu} {v} {w} {val-const {p} f} wfv wfw wfdu wfcu
       du′⊑v w⊑cu′ 𝕍du′↦cu′c
       with p
   ... | base b = ⊥-elim 𝕍du′↦cu′c
   ... | b ⇒ p′
       with 𝕍du′↦cu′c
   ... | ⟨ k , ⟨ k⊑du , ℘-fk-cu ⟩ ⟩ =
         ⟨ k , ⟨ ⊑-trans k⊑du du′⊑v , ℘-⊑ wfw ℘-fk-cu w⊑cu′ ⟩ ⟩
   lemma {du}{cu}{v}{w}{val-clos N γ} wfv wfw wfdu wfcu
        du′⊑v w⊑cu′ 𝕍du′↦cu′c {c} 𝕍vc 
        with  𝕍du′↦cu′c (sub-𝕍 wfv wfdu 𝕍vc du′⊑v)
   ... | ⟨ v' , ⟨ N⇓v' , 𝕍-cu-v' ⟩ ⟩ =
         ⟨ v' , ⟨ N⇓v' , sub-𝕍 wfcu wfw 𝕍-cu-v' w⊑cu′ ⟩ ⟩



{-
sub-𝕍 vc (⊑-trans {v = v₂} lt1 lt2) = sub-𝕍 (sub-𝕍 vc lt2) lt1
-}
{-
sub-𝕍 {val-const {P} f} vc (⊑-fun{v}{w}{v′}{w′} lt1 lt2)
    with P
... | base B = ⊥-elim vc
... | B ⇒ P′ 
    with vc
... | ⟨ k , ⟨ k⊑v′ , ℘fkw′ ⟩ ⟩ =
      ⟨ k , ⟨ (⊑-trans k⊑v′ lt1) , ℘-⊑ ℘fkw′ lt2 ⟩ ⟩
sub-𝕍 {val-clos N γ} vc (⊑-fun lt1 lt2) ev1
    with vc (sub-𝕍 ev1 lt1)
... | ⟨ c , ⟨ Nc , v4 ⟩ ⟩ = ⟨ c , ⟨ Nc , sub-𝕍 v4 lt2 ⟩ ⟩
sub-𝕍 {val-const {P} p} {v ↦ w ⊔ v ↦ w′} ⟨ vc1 , vc2 ⟩ ⊑-dist
    with P
... | base B = ⊥-elim vc1
... | B ⇒ P′
    with vc1 | vc2
... | ⟨ k , ⟨ k⊑v , ℘pkw ⟩ ⟩ | ⟨ k′ , ⟨ k′⊑v , ℘pk′w′ ⟩ ⟩ 
    rewrite k⊑v→k′⊑v→k′≡k ? k⊑v k′⊑v =
      ⟨ k , ⟨ k⊑v , ⟨ ℘pkw , ℘pk′w′ ⟩ ⟩ ⟩

sub-𝕍 {val-clos N γ} {v ↦ w ⊔ v ↦ w'} ⟨ vcw , vcw' ⟩ ⊑-dist ev1c
    with vcw ev1c | vcw' ev1c
... | ⟨ c , ⟨ L⇓c₂ , 𝕍w ⟩ ⟩
    | ⟨ c₃ , ⟨ L⇓c₃ , 𝕍w' ⟩ ⟩ rewrite ⇓-determ L⇓c₃ L⇓c₂ =
      ⟨ c , ⟨ L⇓c₂ , ⟨ 𝕍w , 𝕍w' ⟩ ⟩ ⟩
-}

℘pv→𝕍vp : ∀ {P : Prim} {p : rep P} {v : Value}
        → ℘ {P} p v
        → 𝕍 v (val-const {P} p)
℘pv→𝕍vp {v = ⊥} ℘pv = tt
℘pv→𝕍vp {v = const x} ℘pv = ℘pv
℘pv→𝕍vp {base b} {v = v ↦ v₁} ()
℘pv→𝕍vp {b ⇒ p} {v = v ↦ v₁} ℘pv = ℘pv
℘pv→𝕍vp {P} {p} {v₁ ⊔ v₂} ⟨ ℘pv₁ , ℘pv₂ ⟩ =
  ⟨ ℘pv→𝕍vp {P}{p}{v₁} ℘pv₁ , ℘pv→𝕍vp {P}{p}{v₂} ℘pv₂ ⟩

𝔼 : ∀{Γ} → Value → Term Γ → ValEnv Γ → Set
𝔼 v M γ = Σ[ c ∈ Val ] γ ⊢ M ⇓ c × 𝕍 v c

ℰ→𝔼 : ∀{Γ}{γ : Env Γ}{γ' : ValEnv Γ}{M : Term Γ }{v : Value}
    → WFEnv γ → wf v
    → 𝔾 γ γ' → ℰ M γ v → 𝔼 v M γ'
ℰ→𝔼 {Γ} {γ} {γ'} { $ P p} {v} wfγ wfv 𝔾γγ' ℰMγv =
   ⟨ (val-const {P} p) , ⟨ ⇓-lit , ℘pv→𝕍vp {P}{p}{v} ℰMγv ⟩ ⟩
ℰ→𝔼 {Γ} {γ} {γ'} {` x} {v} wfγ wfv 𝔾γγ' ℰMγv =
   ⟨ γ' x , ⟨ ⇓-var , sub-𝕍 wfγ wfv (𝔾γγ' {x}) ℰMγv ⟩ ⟩
ℰ→𝔼 {Γ} {γ} {γ'} {ƛ N} {v} wfγ wfv 𝔾γγ' ℰMγv =
   ⟨ val-clos N γ' , ⟨ ⇓-lam , G {v} wfv ℰMγv ⟩ ⟩
   where
   G : ∀{v} → wf v → ℱ (ℰ N) γ v → 𝕍 v (val-clos N γ')
   G {⊥} wfv ℱℰNγv = tt
   G {const {B} k} wfv ()
   G {v ↦ w} (wf-fun wfv wfw) ℱℰNγv {c} vc =
      ℰ→𝔼 {M = N} {w} (λ {x} → WFEnv-extend wfγ wfv {x}) wfw
          (λ {x} → 𝔾-ext 𝔾γγ' vc {x}) ℱℰNγv
   G {v₁ ⊔ v₂} (wf-⊔ _ wfv₁ wfv₂) ⟨ ℱℰNγv₁ , ℱℰNγv₂ ⟩ =
      ⟨ G {v₁} wfv₁ ℱℰNγv₁ , G {v₂} wfv₂ ℱℰNγv₂ ⟩
ℰ→𝔼 {Γ} {γ} {γ'} {L · M} {v} wfγ wfv 𝔾γγ'
    ⟨ v₁ , ⟨ wfv₁ , ⟨ d₁ , d₂ ⟩ ⟩ ⟩
    with ℰ→𝔼 {M = L} wfγ (wf-fun wfv₁ wfv) 𝔾γγ' d₁
       | ℰ→𝔼 {M = M} wfγ wfv₁ 𝔾γγ' d₂
... | ⟨ val-clos L' δ₁ , ⟨ L⇓L' , 𝕍v₁↦v ⟩ ⟩ | ⟨ c , ⟨ M⇓c , 𝕍v₁ ⟩ ⟩ 
    with 𝕍v₁↦v {c} 𝕍v₁
... | ⟨ c' , ⟨ L'⇓c' , 𝕍v ⟩ ⟩ =
    ⟨ c' , ⟨ (⇓-app L⇓L' M⇓c L'⇓c') , 𝕍v ⟩ ⟩
ℰ→𝔼 {Γ} {γ} {γ'} {L · M} {v} wfγ wfv 𝔾γγ'
    ⟨ v₁ , ⟨ wfv₁ , ⟨ d₁ , d₂ ⟩ ⟩ ⟩ 
    | ⟨ val-const {P} f , ⟨ L⇓f , 𝕍v₁↦v ⟩ ⟩ | ⟨ c , ⟨ M⇓c , 𝕍v₁ ⟩ ⟩
    with P
... | base B = ⊥-elim 𝕍v₁↦v
... | B ⇒ P′
    with 𝕍v₁↦v
... | ⟨ k , ⟨ k⊑v₁ , ℘fkv ⟩ ⟩
    with c
... | val-clos N γ₁ = ⊥-elim (sub-𝕍 wfv₁ wf-const 𝕍v₁ k⊑v₁)
... | val-const {B₁ ⇒ P₁} f′ = ⊥-elim (sub-𝕍 wfv₁ wf-const 𝕍v₁ k⊑v₁)
... | val-const {base B′} k′
    with base-eq? B′ B | sub-𝕍 wfv₁ wf-const 𝕍v₁ k⊑v₁
... | no neq | ()
... | yes eq | 𝕍kc rewrite eq | 𝕍kc =
    ⟨ val-const {P′} (f k) , ⟨ ⇓-prim L⇓f M⇓c , ℘pv→𝕍vp {P′}{f k}{v} ℘fkv ⟩ ⟩ 

adequacy : ∀{M : Term zero}{N : Term zero}
         → TermValue N
         → ℰ M ≃ ℰ N
           ----------------------------------------------------------
         → Σ[ c ∈ Val ] ∅' ⊢ M ⇓ c
adequacy{M}{N} Nv eq 
    with ℰ→𝔼 (λ {}) wf-bot 𝔾-∅ (proj₂ (eq `∅ ⊥ (λ {}) wf-bot) (ℰ-⊥ {M = N} Nv))
... | ⟨ c , ⟨ M⇓c , Vc ⟩ ⟩ = ⟨ c , M⇓c ⟩


reduce→⇓ : ∀ {M : Term zero} {N : Term zero}
           → TermValue N
           → M —↠ N
           → Σ[ c ∈ Val ] ∅' ⊢ M ⇓ c
reduce→⇓ {M}{N} Nv M—↠N = adequacy {M}{N} Nv (soundness Nv M—↠N)


⇓↔reduce : ∀ {M : Term zero}
           → (Σ[ N ∈ Term zero ] TermValue N × (M —↠ N))
             iff
             (Σ[ c ∈ Val ] ∅' ⊢ M ⇓ c)
⇓↔reduce {M} = ⟨ (λ x → reduce→⇓ (proj₁ (proj₂ x)) (proj₂ (proj₂ x))) ,
                 (λ x → ⇓→—↠ (proj₂ x)) ⟩


denot-equal-terminates : ∀{Γ} {M N : Term Γ} {C : Ctx Γ zero}
  → ℰ M ≃ ℰ N  →  terminates (plug C M)
    -----------------------------------
  → terminates (plug C N)
denot-equal-terminates {Γ}{M}{N}{C} ℰM≃ℰN ⟨ N′ , ⟨ Nv , CM—↠N′ ⟩ ⟩ =
  let ℰCM≃ℰƛN′ = soundness Nv CM—↠N′ in
  let ℰCM≃ℰCN = compositionality{Γ = Γ}{Δ = zero}{C = C} ℰM≃ℰN in
  let ℰCN≃ℰƛN′ = ≃-trans (≃-sym ℰCM≃ℰCN) ℰCM≃ℰƛN′ in
    ⇓→—↠ (proj₂ (adequacy{N = N′} Nv ℰCN≃ℰƛN′))


denot-equal-contex-equal : ∀{Γ} {M N : Term Γ}
  → ℰ M ≃ ℰ N
    ---------
  → M ≅ N
denot-equal-contex-equal{Γ}{M}{N} eq {C} =
   ⟨ (λ tm → denot-equal-terminates{M = M} eq tm) ,
     (λ tn → denot-equal-terminates{M = N} (≃-sym eq) tn) ⟩



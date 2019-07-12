open import Variables
open import Lambda
open Reduction
  using (_—↠_; terminates; _≅_)

open import ValueBCD
open import EvalCallByName
open Lambda.ASTMod
   using (`_; _⦅_⦆; Subst; Ctx; plug;
          exts; cons; bind; nil; rename; ⟪_⟫; subst-zero; _[_]; rename-id)
open import Structures
open import ModelCallByName
open import ValueStructAux value_struct
open import OrderingAux value_struct ordering
open import ConsistentAux value_struct ordering consistent
open import LambdaDenot value_struct ordering _●_ ℱ
open import Compositionality
open DenotAux value_struct ordering _●_ ℱ consistent model_curry_apply
open import SoundnessCallByName using (soundness)

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


module AdequacyCallByName where


𝕍 : Value → Clos → Set
𝔼 : Value → Clos → Set

𝕍 v (clos (` x₁) γ) = Bot
𝕍 v (clos (app ⦅ cons M (cons M₁ nil) ⦆) γ) = Bot
𝕍 ⊥ (clos (lam ⦅ cons (bind (ast M)) nil ⦆) γ) = ⊤
𝕍 (v ↦ w) (clos (lam ⦅ cons (bind (ast N)) nil ⦆) γ) =
    (∀{c : Clos} → 𝔼 v c → AboveFun w → Σ[ c' ∈ Clos ]
        (γ ,' c) ⊢ N ⇓ c'  ×  𝕍 w c')
𝕍 (u ⊔ v) (clos (lam ⦅ cons (bind (ast N)) nil ⦆) γ) =
   𝕍 u (clos (ƛ N) γ) × 𝕍 v (clos (ƛ N) γ)

𝔼 v (clos M γ') = AboveFun v → Σ[ c ∈ Clos ] γ' ⊢ M ⇓ c × 𝕍 v c

𝔾 : ∀{Γ} → Env Γ → ClosEnv Γ → Set
𝔾 {Γ} γ γ' = ∀{x : Var Γ} → 𝔼 (γ x) (γ' x)

𝔾-∅ : 𝔾 `∅ ∅'
𝔾-∅ {()}

𝔾-ext : ∀{Γ}{γ : Env Γ}{γ' : ClosEnv Γ}{v c}
      → 𝔾 γ γ' → 𝔼 v c → 𝔾 (γ `, v) (γ' ,' c)
𝔾-ext {Γ} {γ} {γ'} g e {Z} = e
𝔾-ext {Γ} {γ} {γ'} g e {S x} = g

data WHNF : ∀ {Γ} → Term Γ → Set where
  ƛ_ : ∀ {Γ} {N : Term (suc Γ)}
     → WHNF (ƛ N)

𝕍→WHNF : ∀{Γ}{γ : ClosEnv Γ}{M : Term Γ}{v}
       → 𝕍 v (clos M γ) → WHNF M
𝕍→WHNF {M = ` x} {v} ()
𝕍→WHNF {M = lam ⦅ cons (bind (ast N)) nil ⦆} {v} vc = ƛ_
𝕍→WHNF {M = app ⦅ cons (ast L) (cons (ast M) nil) ⦆} {v} ()

𝕍⊔-intro : ∀{c u v}
         → 𝕍 u c → 𝕍 v c
           ---------------
         → 𝕍 (u ⊔ v) c
𝕍⊔-intro {clos (` x) γ} () vc
𝕍⊔-intro {clos (lam ⦅ cons (bind (ast N)) nil ⦆) γ} uc vc = ⟨ uc , vc ⟩
𝕍⊔-intro {clos (app ⦅ cons (ast L) (cons (ast M) nil) ⦆) γ} () vc

not-AboveFun-𝕍 : ∀{v : Value}{Γ}{γ' : ClosEnv Γ}{N : Term (suc Γ) }
    → ¬ AboveFun v
      -------------------
    → 𝕍 v (clos (lam ⦅ cons (bind (ast N)) nil ⦆) γ')
not-AboveFun-𝕍 {⊥} af = tt
not-AboveFun-𝕍 {v ↦ v'} af = ⊥-elim (contradiction ⟨ v , ⟨ v' , ⊑-refl ⟩ ⟩ af)
not-AboveFun-𝕍 {v₁ ⊔ v₂} af
    with not-AboveFun-⊔-inv af
... | ⟨ af1 , af2 ⟩ = ⟨ not-AboveFun-𝕍 af1 , not-AboveFun-𝕍 af2 ⟩


sub-𝕍 : ∀{c : Clos}{v v'} → 𝕍 v c → v' ⊑ v → 𝕍 v' c
sub-𝔼 : ∀{c : Clos}{v v'} → 𝔼 v c → v' ⊑ v → 𝔼 v' c


sub-𝕍 {clos (` x) γ} {v} () lt
sub-𝕍 {clos (app ⦅ cons L (cons M nil) ⦆) γ} () lt
sub-𝕍 {clos (lam ⦅ cons (bind (ast N)) nil ⦆) γ} vc ⊑-⊥ = tt
sub-𝕍 {clos (lam ⦅ cons (bind (ast N)) nil ⦆) γ} vc (⊑-conj-L lt1 lt2) = ⟨ (sub-𝕍 vc lt1) , sub-𝕍 vc lt2 ⟩
sub-𝕍 {clos (lam ⦅ cons (bind (ast N)) nil ⦆) γ} ⟨ vv1 , vv2 ⟩ (⊑-conj-R1 lt) = sub-𝕍 vv1 lt
sub-𝕍 {clos (lam ⦅ cons (bind (ast N)) nil ⦆) γ} ⟨ vv1 , vv2 ⟩ (⊑-conj-R2 lt) = sub-𝕍 vv2 lt
sub-𝕍 {clos (lam ⦅ cons (bind (ast N)) nil ⦆) γ} vc (⊑-trans {v = v₂} lt1 lt2) = sub-𝕍 (sub-𝕍 vc lt2) lt1
sub-𝕍 {clos (lam ⦅ cons (bind (ast N)) nil ⦆) γ} vc (⊑-fun lt1 lt2) ev1 sf
    with vc (sub-𝔼 ev1 lt1) (AboveFun-⊑ sf lt2)
... | ⟨ c , ⟨ Nc , v4 ⟩ ⟩ = ⟨ c , ⟨ Nc , sub-𝕍 v4 lt2 ⟩ ⟩
sub-𝕍 {clos (lam ⦅ cons (bind (ast N)) nil ⦆) γ} {v ↦ w ⊔ v ↦ w'} ⟨ vcw , vcw' ⟩ ⊑-dist ev1c sf
    with AboveFun? w | AboveFun? w'
... | yes af2 | yes af3
    with vcw ev1c af2 | vcw' ev1c af3
... | ⟨ clos L δ , ⟨ L⇓c₂ , 𝕍w ⟩ ⟩
    | ⟨ c₃ , ⟨ L⇓c₃ , 𝕍w' ⟩ ⟩ rewrite ⇓-determ L⇓c₃ L⇓c₂ with 𝕍→WHNF 𝕍w
... | ƛ_ =
      ⟨ clos L δ , ⟨ L⇓c₂ , ⟨ 𝕍w , 𝕍w' ⟩ ⟩ ⟩
sub-𝕍 {c} {v ↦ w ⊔ v ↦ w'} ⟨ vcw , vcw' ⟩ ⊑-dist ev1c sf
    | yes af2 | no naf3
    with vcw ev1c af2
... | ⟨ clos {Γ'} L γ₁ , ⟨ L⇓c2 , 𝕍w ⟩ ⟩
    with 𝕍→WHNF 𝕍w
... | ƛ_ {N = N'} =
      let 𝕍w' = not-AboveFun-𝕍{w'}{Γ'}{γ₁}{N'} naf3 in
      ⟨ clos (lam ⦅ cons (bind (ast N')) nil ⦆) γ₁ , ⟨ L⇓c2 , 𝕍⊔-intro 𝕍w 𝕍w' ⟩ ⟩
sub-𝕍 {c} {v ↦ w ⊔ v ↦ w'} ⟨ vcw , vcw' ⟩ ⊑-dist ev1c sf
    | no naf2 | yes af3
    with vcw' ev1c af3
... | ⟨ clos {Γ'} L γ₁ , ⟨ L⇓c3 , 𝕍w'c ⟩ ⟩ 
    with 𝕍→WHNF 𝕍w'c
... | ƛ_ {N = N'} =
      let 𝕍wc = not-AboveFun-𝕍{w}{Γ'}{γ₁}{N'} naf2 in
      ⟨ clos (lam ⦅ cons (bind (ast N')) nil ⦆) γ₁ , ⟨ L⇓c3 , 𝕍⊔-intro 𝕍wc 𝕍w'c ⟩ ⟩
sub-𝕍 {c} {v ↦ w ⊔ v ↦ w'} ⟨ vcw , vcw' ⟩ Dist⊑ ev1c ⟨ v' , ⟨ w'' , lt ⟩ ⟩
    | no naf2 | no naf3
    with AboveFun-⊔ ⟨ v' , ⟨ w'' , lt ⟩ ⟩
... | inj₁ af2 = ⊥-elim (contradiction af2 naf2)
... | inj₂ af3 = ⊥-elim (contradiction af3 naf3)


sub-𝔼 {clos M γ} {v} {v'} 𝔼v v'⊑v fv'
    with 𝔼v (AboveFun-⊑ fv' v'⊑v)
... | ⟨ c , ⟨ M⇓c , 𝕍v ⟩ ⟩ =
      ⟨ c , ⟨ M⇓c , sub-𝕍 𝕍v v'⊑v ⟩ ⟩


kth-x : ∀{Γ}{γ' : ClosEnv Γ}{x : Var Γ}
     → Σ[ Δ ∈ Context ] Σ[ δ ∈ ClosEnv Δ ] Σ[ M ∈ Term Δ ]
                 γ' x ≡ clos M δ
kth-x{γ' = γ'}{x = x} with γ' x
... | clos{Γ = Δ} M δ = ⟨ Δ , ⟨ δ , ⟨ M , refl ⟩ ⟩ ⟩


ℰ→𝔼 : ∀{Γ}{γ : Env Γ}{γ' : ClosEnv Γ}{M : Term Γ }{v}
            → 𝔾 γ γ' → ℰ M γ v → 𝔼 v (clos M γ')
ℰ→𝔼 {Γ} {γ} {γ'} {` x} {v} 𝔾γγ' v⊑γx fγx
    with kth-x{Γ}{γ'}{x} | 𝔾γγ'{x = x}
... | ⟨ Δ , ⟨ δ , ⟨ M' , eq ⟩ ⟩ ⟩ | 𝔾γγ'x
    rewrite eq
    with 𝔾γγ'x (AboveFun-⊑ fγx v⊑γx)
... | ⟨ c , ⟨ M'⇓c , 𝕍γx ⟩ ⟩ =
      ⟨ c , ⟨ (⇓-var eq M'⇓c) , sub-𝕍 𝕍γx v⊑γx ⟩ ⟩
ℰ→𝔼 {Γ} {γ} {γ'} {lam ⦅ cons (bind (ast N)) nil ⦆} {v} 𝔾γγ' ℰMγv fγx = G ℰMγv fγx
  where
  G : ∀{v}
    → ℱ (ℰ N) γ v
    → AboveFun v
    → Σ[ c ∈ Clos ] (γ' ⊢ lam ⦅ cons (bind (ast N)) nil ⦆ ⇓ c) × 𝕍 v c
  G {⊥} tt fv = ⊥-elim (AboveFun⊥ fv)
  G {v ↦ w} ℱℰNγv fv = ⟨ (clos (lam ⦅ cons (bind (ast N)) nil ⦆) γ') , ⟨ ⇓-lam , E ⟩ ⟩
    where E : {c : Clos} → 𝔼 v c → AboveFun w
            → Σ[ c' ∈ Clos ] (γ' ,' c) ⊢ N ⇓ c'  ×  𝕍 w c'
          E {c} 𝔼vc fw = ℰ→𝔼 (λ {x} → 𝔾-ext 𝔾γγ' 𝔼vc {x}) ℱℰNγv fw
  G {v₁ ⊔ v₂} ⟨ d₁ , d₂ ⟩ fv
      with AboveFun? v₁ | AboveFun? v₂
  ... | yes fv1 | yes fv2
      with G d₁ fv1 | G d₂ fv2 
  ... | ⟨ c₁ , ⟨ M⇓c₁ , 𝕍v₁ ⟩ ⟩ | ⟨ c₂ , ⟨ M⇓c₂ , 𝕍v₂ ⟩ ⟩
      rewrite ⇓-determ M⇓c₂ M⇓c₁ =
      ⟨ c₁ , ⟨ M⇓c₁ , 𝕍⊔-intro 𝕍v₁ 𝕍v₂ ⟩ ⟩
  G {v₁ ⊔ v₂} ⟨ d₁ , d₂ ⟩ fv | yes fv1 | no nfv2
      with G d₁ fv1 
  ... | ⟨ clos {Γ'} M' γ₁ , ⟨ M⇓c₁ , 𝕍v₁ ⟩ ⟩
      with 𝕍→WHNF 𝕍v₁
  ... | ƛ_ {N = N} =
      let 𝕍v₂ = not-AboveFun-𝕍{v₂}{Γ'}{γ₁}{N} nfv2 in
      ⟨ clos (lam ⦅ cons (bind (ast N)) nil ⦆) γ₁ , ⟨ M⇓c₁ , 𝕍⊔-intro 𝕍v₁ 𝕍v₂ ⟩ ⟩
  G {v₁ ⊔ v₂} ⟨ d₁ , d₂ ⟩ fv | no nfv1  | yes fv2
      with G d₂ fv2
  ... | ⟨ clos {Γ'} M' γ₁ , ⟨ M'⇓c₂ , 𝕍2c ⟩ ⟩
      with 𝕍→WHNF 𝕍2c
  ... | ƛ_ {N = N} =
      let 𝕍1c = not-AboveFun-𝕍{v₁}{Γ'}{γ₁}{N} nfv1 in
      ⟨ clos (lam ⦅ cons (bind (ast N)) nil ⦆) γ₁ , ⟨ M'⇓c₂ , 𝕍⊔-intro 𝕍1c 𝕍2c ⟩ ⟩
  G {v₁ ⊔ v₂} ℱℰNγv fv12 | no nfv1  | no nfv2
      with AboveFun-⊔ fv12
  ... | inj₁ fv1 = ⊥-elim (contradiction fv1 nfv1)
  ... | inj₂ fv2 = ⊥-elim (contradiction fv2 nfv2)
ℰ→𝔼 {Γ} {γ} {γ'} {app ⦅ cons (ast L) (cons (ast M) nil) ⦆} {v} 𝔾γγ' (inj₁ v⊑⊥) fγx =
   ⊥-elim (contradiction (AboveFun-⊑ fγx v⊑⊥) AboveFun⊥ )
ℰ→𝔼 {Γ} {γ} {γ'} {app ⦅ cons (ast L) (cons (ast M) nil) ⦆} {v} 𝔾γγ'
   (inj₂ ⟨ v₁ , ⟨ d₁ , d₂ ⟩ ⟩ ) fv
    with ℰ→𝔼 𝔾γγ' d₁ ⟨ v₁ , ⟨ v , ⊑-refl ⟩ ⟩
... | ⟨ clos L' δ , ⟨ L⇓L' , 𝕍v₁↦v ⟩ ⟩ 
    with 𝕍→WHNF 𝕍v₁↦v
... | ƛ_ {N = N} 
    with 𝕍v₁↦v {clos M γ'} (ℰ→𝔼 𝔾γγ' d₂) fv
... | ⟨ c' , ⟨ N⇓c' , 𝕍v ⟩ ⟩ =
    ⟨ c' , ⟨ ⇓-app L⇓L' N⇓c' , 𝕍v ⟩ ⟩

adequacy : ∀{M : Term zero}{N : Term (suc zero)}
         → ℰ M ≃ ℰ (lam ⦅ cons (bind (ast N)) nil ⦆)
           ----------------------------------------------------------
         → Σ[ Γ ∈ Context ] Σ[ N′ ∈ Term (suc Γ) ] Σ[ γ ∈ ClosEnv Γ ]
            ∅' ⊢ M ⇓ clos (lam ⦅ cons (bind (ast N′)) nil ⦆) γ
adequacy{M}{N} eq
    with ℰ→𝔼 𝔾-∅ ((proj₂ (eq `∅ (⊥ ↦ ⊥) (λ {x} → tt) tt)) (ℰ-⊥{M = N}))
                 ⟨ ⊥ , ⟨ ⊥ , ⊑-refl ⟩ ⟩
... | ⟨ clos {Γ} M′ γ , ⟨ M⇓c , Vc ⟩ ⟩
    with 𝕍→WHNF Vc
... | ƛ_ {N = N′} = 
    ⟨ Γ , ⟨ N′ , ⟨ γ , M⇓c ⟩  ⟩ ⟩

reduce→cbn : ∀ {M : Term zero} {N : Term (suc zero)}
           → M —↠ lam ⦅ cons (bind (ast N)) nil ⦆
           → Σ[ Δ ∈ ℕ ] Σ[ N′ ∈ Term (suc Δ) ] Σ[ δ ∈ ClosEnv Δ ] 
             ∅' ⊢ M ⇓ clos (lam ⦅ cons (bind (ast N′)) nil ⦆) δ
reduce→cbn {M}{N} M—↠ƛN = adequacy {M}{N} (soundness M—↠ƛN)


cbn↔reduce : ∀ {M : Term zero}
           → (Σ[ N ∈ Term (suc zero) ] (M —↠ lam ⦅ cons (bind (ast N)) nil ⦆))
             iff
             (Σ[ Δ ∈ ℕ ] Σ[ N′ ∈ Term (suc Δ) ] Σ[ δ ∈ ClosEnv Δ ]
               ∅' ⊢ M ⇓ clos (lam ⦅ cons (bind (ast N′)) nil ⦆) δ)
cbn↔reduce {M} = ⟨ (λ x → reduce→cbn (proj₂ x)) ,
                   (λ x → cbn→reduce (proj₂ (proj₂ (proj₂ x)))) ⟩

denot-equal-terminates : ∀{Γ} {M N : Term Γ} {C : Ctx Γ zero}
  → ℰ M ≃ ℰ N  →  terminates (plug C M)
    -----------------------------------
  → terminates (plug C N)
denot-equal-terminates {Γ}{M}{N}{C} ℰM≃ℰN ⟨ N′ , CM—↠ƛN′ ⟩ =
  let ℰCM≃ℰƛN′ = soundness CM—↠ƛN′ in
  let ℰCM≃ℰCN = compositionality{Γ = Γ}{Δ = zero}{C = C} ℰM≃ℰN in
  let ℰCN≃ℰƛN′ = ≃-trans (≃-sym ℰCM≃ℰCN) ℰCM≃ℰƛN′ in
    cbn→reduce (proj₂ (proj₂ (proj₂ (adequacy{N = N′} ℰCN≃ℰƛN′))))

denot-equal-contex-equal : ∀{Γ} {M N : Term Γ}
  → ℰ M ≃ ℰ N
    ---------
  → M ≅ N
denot-equal-contex-equal{Γ}{M}{N} eq {C} =
   ⟨ (λ tm → denot-equal-terminates{M = M} eq tm) ,
     (λ tn → denot-equal-terminates{M = N} (≃-sym eq) tn) ⟩

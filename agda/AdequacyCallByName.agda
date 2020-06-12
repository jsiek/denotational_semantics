open import Lambda
open import Utilities using (_iff_)
open Reduction
  using (_—↠_; terminates; _≅_)

open import ValueBCD
open import Data.List using (List; []; _∷_; length)
open import EvalCallByName
open Lambda.ASTMod
   using (`_; _⦅_⦆; Subst; Ctx; plug;
          exts; cons; bind; nil; rename; ⟪_⟫; subst-zero; _[_]; rename-id;
          WF; WF-var; WF-op; WF-cons; WF-nil; WF-ast; WF-bind; WF-Ctx; WF-plug;
          ctx-depth)
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
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc; _<_; s≤s)
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

data 𝔾 : Env → ClosEnv → Set where
  𝔾-∅ : 𝔾 `∅ ∅'
  𝔾-ext : ∀{γ : Env}{γ' : ClosEnv}{v c}
        → 𝔾 γ γ' → 𝔼 v c 
        → 𝔾 (γ `, v) (γ' ,' c)

{-
𝔾 : Env → ClosEnv → Set
𝔾 γ γ' = ∀{x : Var} → 𝔼 (γ x) (nth γ' x)

𝔾-∅ : 𝔾 `∅ ∅'
𝔾-∅ {()}

𝔾-ext : ∀{γ : Env}{γ' : ClosEnv}{v c}
      → 𝔾 γ γ' → 𝔼 v c → 𝔾 (γ `, v) (γ' ,' c)
𝔾-ext {γ} {γ'} g e {0} = e
𝔾-ext {γ} {γ'} g e {suc x} = g
-}

𝔾→𝔼 : (γ : Env) → (γ' : ClosEnv)
    → 𝔾 γ γ'
    → (x : Var) → (lt : x < length γ')
    → 𝔼 (γ x) (nth γ' x)
𝔾→𝔼 .(λ x₁ → ⊥) .[] 𝔾-∅ x ()
𝔾→𝔼 .(_ `, _) .(_ ∷ _) (𝔾-ext 𝔾γγ' 𝔼vc) zero (s≤s lt) = 𝔼vc
𝔾→𝔼 γ₂ (c ∷ γ') (𝔾-ext {γ}{γ'}{v}{c} 𝔾γγ' 𝔼vc) (suc x) (s≤s lt) =
    𝔾→𝔼 γ γ' 𝔾γγ' x lt

data WHNF : Term → Set where
  ƛ_ : ∀ {N : Term}
     → WHNF (ƛ N)

𝕍→WHNF : ∀{γ : ClosEnv}{M : Term}{v}
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

not-AboveFun-𝕍 : ∀{v : Value}{γ' : ClosEnv}{N : Term }
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
sub-𝕍 {clos (lam ⦅ cons (bind (ast N)) nil ⦆) γ} vc (⊑-conj-L lt1 lt2) =
    ⟨ (sub-𝕍 vc lt1) , sub-𝕍 vc lt2 ⟩
sub-𝕍 {clos (lam ⦅ cons (bind (ast N)) nil ⦆) γ} ⟨ vv1 , vv2 ⟩ (⊑-conj-R1 lt) =
    sub-𝕍 vv1 lt
sub-𝕍 {clos (lam ⦅ cons (bind (ast N)) nil ⦆) γ} ⟨ vv1 , vv2 ⟩ (⊑-conj-R2 lt) =
    sub-𝕍 vv2 lt
sub-𝕍 {clos (lam ⦅ cons (bind (ast N)) nil ⦆) γ} vc (⊑-trans {v = v₂} lt1 lt2) =
    sub-𝕍 (sub-𝕍 vc lt2) lt1
sub-𝕍 {clos (lam ⦅ cons (bind (ast N)) nil ⦆) γ} vc (⊑-fun lt1 lt2) ev1 sf
    with vc (sub-𝔼 ev1 lt1) (AboveFun-⊑ sf lt2)
... | ⟨ c , ⟨ Nc , v4 ⟩ ⟩ = ⟨ c , ⟨ Nc , sub-𝕍 v4 lt2 ⟩ ⟩
sub-𝕍 {clos (lam ⦅ cons (bind (ast N)) nil ⦆) γ} {v ↦ w ⊔ v ↦ w'} ⟨ vcw , vcw' ⟩
    ⊑-dist ev1c sf
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
... | ⟨ clos L γ₁ , ⟨ L⇓c2 , 𝕍w ⟩ ⟩
    with 𝕍→WHNF 𝕍w
... | ƛ_ {N = N'} =
      let 𝕍w' = not-AboveFun-𝕍{w'}{γ₁}{N'} naf3 in
      ⟨ clos (lam ⦅ cons (bind (ast N')) nil ⦆) γ₁ , ⟨ L⇓c2 , 𝕍⊔-intro 𝕍w 𝕍w' ⟩ ⟩
sub-𝕍 {c} {v ↦ w ⊔ v ↦ w'} ⟨ vcw , vcw' ⟩ ⊑-dist ev1c sf
    | no naf2 | yes af3
    with vcw' ev1c af3
... | ⟨ clos L γ₁ , ⟨ L⇓c3 , 𝕍w'c ⟩ ⟩ 
    with 𝕍→WHNF 𝕍w'c
... | ƛ_ {N = N'} =
      let 𝕍wc = not-AboveFun-𝕍{w}{γ₁}{N'} naf2 in
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

kth-x : ∀{γ' : ClosEnv}{x : Var}
     → Σ[ δ ∈ ClosEnv ] Σ[ M ∈ Term ]
           nth γ' x ≡ clos M δ
kth-x{γ' = γ'}{x = x} with nth γ' x
... | clos M δ = ⟨ δ , ⟨ M , refl ⟩ ⟩

ℰ→𝔼 : ∀{γ : Env}{γ' : ClosEnv}{M : Term}{v}{wf : WF (length γ') M }
            → 𝔾 γ γ' → ℰ M γ v → 𝔼 v (clos M γ')
ℰ→𝔼 {γ} {γ'} {` x} {v}{WF-var x lt} 𝔾γγ' v⊑γx fγx
    with kth-x{γ'}{x} | 𝔾→𝔼 γ γ' 𝔾γγ' x lt
... | ⟨ δ , ⟨ M' , eq ⟩ ⟩ | 𝔾γγ'x
    rewrite eq
    with 𝔾γγ'x (AboveFun-⊑ fγx v⊑γx)
... | ⟨ c , ⟨ M'⇓c , 𝕍γx ⟩ ⟩ =
      ⟨ c , ⟨ (⇓-var eq M'⇓c) , sub-𝕍 𝕍γx v⊑γx ⟩ ⟩
ℰ→𝔼 {γ}{γ'}{lam ⦅ cons (bind (ast N)) nil ⦆}{v}{WF-op (WF-cons (WF-bind (WF-ast wfN)) WF-nil)} 𝔾γγ' ℰMγv fγx = G ℰMγv fγx
  where
  G : ∀{v}
    → ℱ (ℰ N) γ v
    → AboveFun v
    → Σ[ c ∈ Clos ] (γ' ⊢ lam ⦅ cons (bind (ast N)) nil ⦆ ⇓ c) × 𝕍 v c
  G {⊥} tt fv = ⊥-elim (AboveFun⊥ fv)
  G {v ↦ w} ℱℰNγv fv =
      ⟨ (clos (lam ⦅ cons (bind (ast N)) nil ⦆) γ') , ⟨ ⇓-lam , E ⟩ ⟩
    where E : {c : Clos} → 𝔼 v c → AboveFun w
            → Σ[ c' ∈ Clos ] (γ' ,' c) ⊢ N ⇓ c'  ×  𝕍 w c'
          E {c} 𝔼vc fw = ℰ→𝔼 {wf = wfN} (𝔾-ext 𝔾γγ' 𝔼vc) ℱℰNγv fw
  G {v₁ ⊔ v₂} ⟨ d₁ , d₂ ⟩ fv
      with AboveFun? v₁ | AboveFun? v₂
  ... | yes fv1 | yes fv2
      with G d₁ fv1 | G d₂ fv2 
  ... | ⟨ c₁ , ⟨ M⇓c₁ , 𝕍v₁ ⟩ ⟩ | ⟨ c₂ , ⟨ M⇓c₂ , 𝕍v₂ ⟩ ⟩
      rewrite ⇓-determ M⇓c₂ M⇓c₁ =
      ⟨ c₁ , ⟨ M⇓c₁ , 𝕍⊔-intro 𝕍v₁ 𝕍v₂ ⟩ ⟩
  G {v₁ ⊔ v₂} ⟨ d₁ , d₂ ⟩ fv | yes fv1 | no nfv2
      with G d₁ fv1 
  ... | ⟨ clos M' γ₁ , ⟨ M⇓c₁ , 𝕍v₁ ⟩ ⟩
      with 𝕍→WHNF 𝕍v₁
  ... | ƛ_ {N = N} =
      let 𝕍v₂ = not-AboveFun-𝕍{v₂}{γ₁}{N} nfv2 in
      ⟨ clos (lam ⦅ cons (bind (ast N)) nil ⦆) γ₁ , ⟨ M⇓c₁ , 𝕍⊔-intro 𝕍v₁ 𝕍v₂ ⟩ ⟩
  G {v₁ ⊔ v₂} ⟨ d₁ , d₂ ⟩ fv | no nfv1  | yes fv2
      with G d₂ fv2
  ... | ⟨ clos M' γ₁ , ⟨ M'⇓c₂ , 𝕍2c ⟩ ⟩
      with 𝕍→WHNF 𝕍2c
  ... | ƛ_ {N = N} =
      let 𝕍1c = not-AboveFun-𝕍{v₁}{γ₁}{N} nfv1 in
      ⟨ clos (lam ⦅ cons (bind (ast N)) nil ⦆) γ₁ , ⟨ M'⇓c₂ , 𝕍⊔-intro 𝕍1c 𝕍2c ⟩ ⟩
  G {v₁ ⊔ v₂} ℱℰNγv fv12 | no nfv1  | no nfv2
      with AboveFun-⊔ fv12
  ... | inj₁ fv1 = ⊥-elim (contradiction fv1 nfv1)
  ... | inj₂ fv2 = ⊥-elim (contradiction fv2 nfv2)
ℰ→𝔼 {γ}{γ'}{app ⦅ cons (ast L) (cons (ast M) nil) ⦆}{v}{wf}𝔾γγ' (inj₁ v⊑⊥) fγx =
   ⊥-elim (contradiction (AboveFun-⊑ fγx v⊑⊥) AboveFun⊥ )
ℰ→𝔼 {γ} {γ'} {app ⦅ cons (ast L) (cons (ast M) nil) ⦆} {v}
    {WF-op (WF-cons (WF-ast wfL) (WF-cons (WF-ast wfM) WF-nil))} 𝔾γγ'
   (inj₂ ⟨ v₁ , ⟨ d₁ , d₂ ⟩ ⟩ ) fv
    with ℰ→𝔼 {wf = wfL} 𝔾γγ' d₁ ⟨ v₁ , ⟨ v , ⊑-refl ⟩ ⟩
... | ⟨ clos L' δ , ⟨ L⇓L' , 𝕍v₁↦v ⟩ ⟩ 
    with 𝕍→WHNF 𝕍v₁↦v
... | ƛ_ {N = N} 
    with 𝕍v₁↦v {clos M γ'} (ℰ→𝔼 {wf = wfM} 𝔾γγ' d₂) fv
... | ⟨ c' , ⟨ N⇓c' , 𝕍v ⟩ ⟩ =
    ⟨ c' , ⟨ ⇓-app L⇓L' N⇓c' , 𝕍v ⟩ ⟩

adequacy : ∀{M : Term}{N : Term}{wf : WF 0 M}
         → ℰ M ≃ ℰ (lam ⦅ cons (bind (ast N)) nil ⦆)
           ----------------------------------------------------------
         → Σ[ N′ ∈ Term ] Σ[ γ ∈ ClosEnv ]
             ∅' ⊢ M ⇓ clos (lam ⦅ cons (bind (ast N′)) nil ⦆) γ
adequacy{M}{N}{wf} eq
    with ℰ→𝔼 {wf = wf} 𝔾-∅
              ((proj₂ (eq `∅ (⊥ ↦ ⊥) (λ x → tt) tt)) (ℰ-⊥{M = N}))
              ⟨ ⊥ , ⟨ ⊥ , ⊑-refl ⟩ ⟩
... | ⟨ clos M′ γ , ⟨ M⇓c , Vc ⟩ ⟩
    with 𝕍→WHNF Vc
... | ƛ_ {N = N′} = 
    ⟨ N′ , ⟨ γ , M⇓c ⟩ ⟩

reduce→cbn : ∀ {M : Term} {N : Term}{wf : WF 0 M}
           → M —↠ lam ⦅ cons (bind (ast N)) nil ⦆
           → Σ[ N′ ∈ Term ] Σ[ δ ∈ ClosEnv ] 
             ∅' ⊢ M ⇓ clos (lam ⦅ cons (bind (ast N′)) nil ⦆) δ
reduce→cbn {M}{N}{wf} M—↠ƛN = adequacy {M}{N}{wf} (soundness M—↠ƛN)


cbn↔reduce : ∀ {M : Term}{wf : WF 0 M}
           → (Σ[ N ∈ Term ] (M —↠ lam ⦅ cons (bind (ast N)) nil ⦆))
             iff
             (Σ[ N′ ∈ Term ] Σ[ δ ∈ ClosEnv ]
               ∅' ⊢ M ⇓ clos (lam ⦅ cons (bind (ast N′)) nil ⦆) δ)
cbn↔reduce {M}{wf} = ⟨ (λ x → reduce→cbn{wf = wf} (proj₂ x)) ,
                   (λ x → cbn→reduce (proj₂ (proj₂ x))) ⟩

denot-equal-terminates : ∀ {M N : Term} {C : Ctx}
    {wfC : WF-Ctx 0 C} {wfN : WF (ctx-depth C) N}
  → ℰ M ≃ ℰ N  →  terminates (plug C M)
    -----------------------------------
  → terminates (plug C N)
denot-equal-terminates {M}{N}{C}{wfC}{wfM} ℰM≃ℰN ⟨ N′ , CM—↠ƛN′ ⟩ =
  let ℰCM≃ℰƛN′ = soundness CM—↠ƛN′ in
  let ℰCM≃ℰCN = compositionality{C = C} ℰM≃ℰN in
  let ℰCN≃ℰƛN′ = ≃-trans (≃-sym ℰCM≃ℰCN) ℰCM≃ℰƛN′ in
    cbn→reduce (proj₂ (proj₂ (adequacy{N = N′}{WF-plug wfC wfM} ℰCN≃ℰƛN′)))

denot-equal-contex-equal : ∀ {M N : Term}
  → ℰ M ≃ ℰ N
    ---------
  → M ≅ N
denot-equal-contex-equal{M}{N} eq {C}{wfC}{wfM}{wfN} =
   ⟨ (λ tm → denot-equal-terminates{M = M}{wfC = wfC}{wfN = wfN} eq tm) ,
     (λ tn → denot-equal-terminates{M = N}{wfC = wfC}{wfN = wfM} (≃-sym eq) tn) ⟩


open import Lambda
open import LambdaCallByValue
open import Utilities using (_iff_)
open import ValueBCD
open import EvalCallByValue
open Lambda.ASTMod
   using (`_; _⦅_⦆; Subst; Ctx; plug;
          exts; cons; bind; nil; rename; ⟪_⟫; subst-zero; _[_]; rename-id;
          WF; WF-var; WF-op; WF-cons; WF-nil; WF-ast; WF-bind;
          WF-rel; WF-Ctx; WF-plug; ctx-depth; len-mk-list)
open import Values
open import ValueStructAux value_struct
open import OrderingAux value_struct ordering
open import ConsistentAux value_struct ordering consistent
open import ModelCallByValue value_struct ordering consistent ℱ model_curry
open import LambdaDenot value_struct ordering _●_ ℱ
open import Compositionality
open DenotAux value_struct ordering _●_ ℱ consistent model_curry_apply
open import SoundnessCallByValue using (soundness; ℰ-⊥)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; trans; sym; cong; cong₂; cong-app; subst)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc; s≤s; _<_)
open import Data.List using (List; []; _∷_; length)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum
open import Data.Empty using (⊥-elim) renaming (⊥ to Bot)
open import Data.Unit
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Nullary using (Dec; yes; no)

module AdequacyCallByValue where

𝕍 : Value → Clos → Set
𝕍 ⊥ (clos N γ {wf}) = ⊤
𝕍 (v ↦ w) (clos N γ {wf}) =
    (∀{c : Clos} → 𝕍 v c → Σ[ c' ∈ Clos ] (γ ,' c) ⊢ N ⇓ c'  ×  𝕍 w c')
𝕍 (u ⊔ v) (clos N γ {wf}) = 𝕍 u (clos N γ {wf}) × 𝕍 v (clos N γ {wf})
𝕍 _ bogus = Bot


data 𝔾 : Env → ClosEnv → Set where
  𝔾-∅ : 𝔾 `∅ ∅'
  𝔾-ext : ∀{γ : Env}{γ' : ClosEnv}{v c}
        → 𝔾 γ γ' → 𝕍 v c 
        → 𝔾 (γ `, v) (γ' ,' c)

𝔾→𝕍 : (γ : Env) → (γ' : ClosEnv)
    → 𝔾 γ γ'
    → (x : Var) → (lt : x < length γ')
    → 𝕍 (γ x) (nth γ' x)
𝔾→𝕍 .(λ x₁ → ⊥) .[] 𝔾-∅ x ()
𝔾→𝕍 .(_ `, _) .(_ ∷ _) (𝔾-ext 𝔾γγ' 𝔼vc) zero (s≤s lt) = 𝔼vc
𝔾→𝕍 γ₂ (c ∷ γ') (𝔾-ext {γ}{γ'}{v}{c} 𝔾γγ' 𝔼vc) (suc x) (s≤s lt) =
    𝔾→𝕍 γ γ' 𝔾γγ' x lt

¬𝕍[bogus] : ∀ v → ¬ 𝕍 v bogus
¬𝕍[bogus] ⊥ ()
¬𝕍[bogus] (v ↦ v₁) ()
¬𝕍[bogus] (v ⊔ v₁) ()

sub-𝕍 : ∀{c : Clos}{v v'} → 𝕍 v c → v' ⊑ v → 𝕍 v' c

sub-𝕍 {bogus}{v}{v'} 𝕍[bogus] ⊑-⊥ = ¬𝕍[bogus] _ 𝕍[bogus]
sub-𝕍 {bogus} 𝕍[bogus] (⊑-conj-L x₁ x₂) = ¬𝕍[bogus] _ 𝕍[bogus]
sub-𝕍 {bogus} vc (⊑-trans lt1 lt2) = sub-𝕍 (sub-𝕍 vc lt2) lt1
sub-𝕍 {clos N γ} vc ⊑-⊥ = tt
sub-𝕍 {clos N γ} vc (⊑-conj-L lt1 lt2) = ⟨ (sub-𝕍 vc lt1) , sub-𝕍 vc lt2 ⟩
sub-𝕍 {clos N γ} ⟨ vv1 , vv2 ⟩ (⊑-conj-R1 lt) = sub-𝕍 vv1 lt
sub-𝕍 {clos N γ} ⟨ vv1 , vv2 ⟩ (⊑-conj-R2 lt) = sub-𝕍 vv2 lt
sub-𝕍 {clos N γ} vc (⊑-trans {v = v₂} lt1 lt2) = sub-𝕍 (sub-𝕍 vc lt2) lt1
sub-𝕍 {clos N γ} vc (⊑-fun lt1 lt2) ev1
    with vc (sub-𝕍 ev1 lt1)
... | ⟨ c , ⟨ Nc , v4 ⟩ ⟩ = ⟨ c , ⟨ Nc , sub-𝕍 v4 lt2 ⟩ ⟩
sub-𝕍 {clos N γ} {v ↦ w ⊔ v ↦ w'} ⟨ vcw , vcw' ⟩ ⊑-dist ev1c {-sf-} 
    with vcw ev1c | vcw' ev1c
... | ⟨ clos L δ , ⟨ L⇓c₂ , 𝕍w ⟩ ⟩
    | ⟨ c₃ , ⟨ L⇓c₃ , 𝕍w' ⟩ ⟩ rewrite ⇓-determ L⇓c₃ L⇓c₂ =
      ⟨ clos L δ , ⟨ L⇓c₂ , ⟨ 𝕍w , 𝕍w' ⟩ ⟩ ⟩
... | ⟨ bogus , ⟨ L⇓c₂ , 𝕍w ⟩ ⟩
    | ⟨ c₃ , ⟨ L⇓c₃ , 𝕍w' ⟩ ⟩ = ⊥-elim (¬𝕍[bogus] _ 𝕍w)


𝔼 : Value → Term → ClosEnv → Set
𝔼 v M γ = Σ[ c ∈ Clos ] γ ⊢ M ⇓ c × 𝕍 v c

ℰ→𝔼 : {γ : Env}{γ' : ClosEnv}{M : Term}{wf : WF (length γ') M }{v : Value}
    → 𝔾 γ γ' → ℰ M γ v → 𝔼 v M γ'
ℰ→𝔼 {γ} {γ'} {` x}{WF-var ∋x lt} {v} 𝔾γγ' ℰMγv =
   let lt' = subst (λ X → x < X) (len-mk-list (length γ')) lt in
   ⟨ nth γ' x , ⟨ ⇓-var , sub-𝕍 (𝔾→𝕍 _ _ 𝔾γγ' x lt') ℰMγv ⟩ ⟩
ℰ→𝔼 {γ} {γ'} {lam ⦅ cons (bind (ast N)) nil ⦆}
             {WF-op (WF-cons (WF-bind (WF-ast wfN)) WF-nil) _} {v} 𝔾γγ' ℰMγv =
   ⟨ clos N γ' , ⟨ ⇓-lam {wf = wfN} , G ℰMγv ⟩ ⟩
   where
   G : ∀{v} → ℱ (ℰ N) γ v → 𝕍 v (clos N γ' {wfN})
   G {⊥} ℱℰNγv = tt
   G {v ↦ w} ℱℰNγv {c} vc =
      ℰ→𝔼 {M = N} {wfN} {w} (𝔾-ext 𝔾γγ' vc) ℱℰNγv
   G {v₁ ⊔ v₂} ⟨ ℱℰNγv₁ , ℱℰNγv₂ ⟩ = ⟨ G {v₁} ℱℰNγv₁ , G {v₂} ℱℰNγv₂ ⟩
ℰ→𝔼 {γ} {γ'} {app ⦅ cons (ast L) (cons (ast M) nil) ⦆}
             {WF-op (WF-cons (WF-ast wfL) (WF-cons (WF-ast wfM) WF-nil)) _}
             {v} 𝔾γγ'
    ⟨ v₁ , ⟨ wfv , ⟨ d₁ , d₂ ⟩ ⟩ ⟩ 
    with ℰ→𝔼 {M = L} {wfL} 𝔾γγ' d₁ 
... | ⟨ clos L' δ₁  {wfL'} , ⟨ L⇓L' , 𝕍v₁↦v ⟩ ⟩
    with ℰ→𝔼 {M = M} {wfM} 𝔾γγ' d₂
... | ⟨ clos M' δ₂ , ⟨ M⇓M' , 𝕍v₁ ⟩ ⟩ 
    with 𝕍v₁↦v {clos M' δ₂} 𝕍v₁
... | ⟨ c , ⟨ L'⇓c , 𝕍v ⟩ ⟩ =
    ⟨ c , ⟨ (⇓-app {wf = WF-rel L' wfL'} L⇓L' M⇓M' L'⇓c) , 𝕍v ⟩ ⟩
ℰ→𝔼 {γ} {γ'} {app ⦅ cons (ast L) (cons (ast M) nil) ⦆} {wf} {v} 𝔾γγ'
    ⟨ v₁ , ⟨ wfv , ⟨ d₁ , d₂ ⟩ ⟩ ⟩ 
    | ⟨ clos L' δ₁ , ⟨ L⇓L' , 𝕍v₁↦v ⟩ ⟩
    | ⟨ bogus , ⟨ M⇓M' , 𝕍v₁ ⟩ ⟩ = ⊥-elim (¬𝕍[bogus] _ 𝕍v₁)

adequacy : ∀{M : Term}{N : Term}{wfM : WF 0 M}
         → ℰ M ≃ ℰ (lam ⦅ cons (bind (ast N)) nil ⦆)
           ----------------------------------------------------------
         → Σ[ N′ ∈ Term ] Σ[ γ ∈ ClosEnv ] Σ[ wf ∈ WF (suc (length γ)) N′ ]
            ∅' ⊢ M ⇓ clos N′ γ {wf}
adequacy{M}{N}{wfM} eq 
    with ℰ→𝔼 {wf = wfM} 𝔾-∅ (proj₂ (eq `∅ ⊥ (λ x → tt) tt)
                  (ℰ-⊥ {γ = λ _ → ⊥}{M = lam ⦅ cons (bind (ast N)) nil ⦆} V-ƛ))
... | ⟨ clos N′ γ {wfN′} , ⟨ M⇓c , Vc ⟩ ⟩ =
    ⟨ N′ , ⟨ γ , ⟨ WF-rel N′ wfN′ , M⇓c ⟩ ⟩ ⟩


reduce→cbv : ∀ {M : Term} {N : Term}{wfM : WF 0 M}
           → M —↠ lam ⦅ cons (bind (ast N)) nil ⦆
           → Σ[ N′ ∈ Term ] Σ[ δ ∈ ClosEnv ] Σ[ wf ∈ WF (suc (length δ)) N′ ]
             ∅' ⊢ M ⇓ clos N′ δ {wf}
reduce→cbv {M}{N}{wfM} M—↠ƛN = adequacy {M}{N}{wfM} (soundness M—↠ƛN)


cbv↔reduce : ∀ {M : Term}{wfM : WF 0 M}
           → (Σ[ N ∈ Term ] (M —↠ lam ⦅ cons (bind (ast N)) nil ⦆))
             iff
             (Σ[ N′ ∈ Term ] Σ[ δ ∈ ClosEnv ] Σ[ wf ∈ WF (suc (length δ)) N′ ]
               ∅' ⊢ M ⇓ clos N′ δ {wf})
cbv↔reduce {M}{wfM} =
    ⟨ (λ x → reduce→cbv {wfM = wfM} (proj₂ x)) ,
      (λ x → cbv→reduce {wfM = wfM}{wfN′ = proj₁ (proj₂ (proj₂ x))}
              (proj₂ (proj₂ (proj₂ x))) ) ⟩

denot-equal-terminates : ∀{M N : Term} {C : Ctx}{wfM : WF (ctx-depth C) M}
    {wfN : WF (ctx-depth C) N}{wfC : WF-Ctx 0 C}
  → ℰ M ≃ ℰ N  →  terminates (plug C M)
    -----------------------------------
  → terminates (plug C N)
denot-equal-terminates {M}{N}{C}{wfM}{wfN}{wfC} ℰM≃ℰN ⟨ N′ , CM—↠ƛN′ ⟩ =
  let ℰCM≃ℰƛN′ = soundness CM—↠ƛN′ in
  let ℰCM≃ℰCN = compositionality{C = C}{N = N} ℰM≃ℰN in
  let ℰCN≃ℰƛN′ = ≃-trans (≃-sym ℰCM≃ℰCN) ℰCM≃ℰƛN′ in
  let adeq = adequacy{N = N′}{wfM = WF-plug wfC wfN} ℰCN≃ℰƛN′ in
  let wfN′′ = proj₁ (proj₂ (proj₂ adeq)) in
  let CN⇓N′′ = proj₂ (proj₂ (proj₂ adeq)) in
    cbv→reduce {wfM = WF-plug wfC wfN}{wfN′ = wfN′′} CN⇓N′′

denot-equal-contex-equal : ∀{M N : Term}
  → ℰ M ≃ ℰ N
    ---------
  → M ≅ N
denot-equal-contex-equal{M}{N} eq {C}{wfC}{wfM}{wfN} =
   ⟨ (λ tm → denot-equal-terminates{M = M}{wfM = wfM}{wfN}{wfC} eq tm) ,
     (λ tn → denot-equal-terminates{M = N}{wfM = wfN}{wfM}{wfC} (≃-sym eq) tn) ⟩

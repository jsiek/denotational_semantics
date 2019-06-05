open import Variables
open import Primitives
open import Structures
open import ValueBCDConst
open import EvalISWIM
open import ISWIM
open DomainAux domain
open OrderingAux domain ordering
open import ModelCallByValue domain ordering ℱ model_curry
open ISWIMDenot domain ordering _●_ ℱ (λ {P} k v → ℘ {P} k v)
open ISWIMDenotAux domain ordering _●_ ℱ model_basics (λ {P} k v → ℘ {P} k v)
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


sub-𝕍 : ∀{c : Val}{v v'} → 𝕍 v c → v' ⊑ v → 𝕍 v' c

sub-𝕍 {c} vc ⊑-⊥ = tt
sub-𝕍 {val-const {base B} k} vc (⊑-const {B′} {k′})
    with base-eq? B B′
... | yes eq rewrite eq = vc
... | no neq = vc
sub-𝕍 {val-const {B ⇒ P} p} () (⊑-const {B′} {k}) 
sub-𝕍 {val-clos N x} () ⊑-const
sub-𝕍 vc (⊑-conj-L lt1 lt2) = ⟨ (sub-𝕍 vc lt1) , sub-𝕍 vc lt2 ⟩
sub-𝕍 ⟨ vv1 , vv2 ⟩ (⊑-conj-R1 lt) = sub-𝕍 vv1 lt
sub-𝕍 ⟨ vv1 , vv2 ⟩ (⊑-conj-R2 lt) = sub-𝕍 vv2 lt
sub-𝕍 vc (⊑-trans {v = v₂} lt1 lt2) = sub-𝕍 (sub-𝕍 vc lt2) lt1
sub-𝕍 {val-const {P} p} vc (⊑-fun lt1 lt2) = {!!}
sub-𝕍 {val-clos N γ} vc (⊑-fun lt1 lt2) ev1
    with vc (sub-𝕍 ev1 lt1)
... | ⟨ c , ⟨ Nc , v4 ⟩ ⟩ = ⟨ c , ⟨ Nc , sub-𝕍 v4 lt2 ⟩ ⟩
sub-𝕍 {val-const {P} p} {v ↦ w ⊔ v ↦ w'} ⟨ vc1 , vc2 ⟩ ⊑-dist = {!!}
sub-𝕍 {val-clos N γ} {v ↦ w ⊔ v ↦ w'} ⟨ vcw , vcw' ⟩ ⊑-dist ev1c
    with vcw ev1c | vcw' ev1c
... | ⟨ c , ⟨ L⇓c₂ , 𝕍w ⟩ ⟩
    | ⟨ c₃ , ⟨ L⇓c₃ , 𝕍w' ⟩ ⟩ rewrite ⇓-determ L⇓c₃ L⇓c₂ =
      ⟨ c , ⟨ L⇓c₂ , ⟨ 𝕍w , 𝕍w' ⟩ ⟩ ⟩


℘pv→𝕍vp : ∀ {P : Prim} {p : rep P} {v : Value}
        → ℘ {P} p v
        → 𝕍 v (val-const {P} p)
℘pv→𝕍vp {v = ⊥} ℘pv = tt
℘pv→𝕍vp {v = const x} ℘pv = ℘pv
℘pv→𝕍vp {base x} {v = v ↦ v₁} ()
℘pv→𝕍vp {x ⇒ P} {v = v ↦ v₁} ℘pv = ℘pv
℘pv→𝕍vp {P}{p}{v = v ⊔ v₁} ⟨ fst , snd ⟩ =
  ⟨ ℘pv→𝕍vp {P}{p}{v} fst , ℘pv→𝕍vp {P}{p}{v₁} snd ⟩


𝔼 : ∀{Γ} → Value → Term Γ → ValEnv Γ → Set
𝔼 v M γ = Σ[ c ∈ Val ] γ ⊢ M ⇓ c × 𝕍 v c

ℰ→𝔼 : ∀{Γ}{γ : Env Γ}{γ' : ValEnv Γ}{M : Term Γ }{v}
            → 𝔾 γ γ' → ℰ M γ v → 𝔼 v M γ'
ℰ→𝔼 {Γ} {γ} {γ'} { lit {P} p ⦅ nil ⦆ } {v} 𝔾γγ' ℰMγv =
   ⟨ (val-const {P} p) , ⟨ ⇓-lit , ℘pv→𝕍vp {P}{p}{v} ℰMγv ⟩ ⟩
ℰ→𝔼 {Γ} {γ} {γ'} {` x} {v} 𝔾γγ' ℰMγv =
   ⟨ γ' x , ⟨ ⇓-var , sub-𝕍 (𝔾γγ' {x}) ℰMγv ⟩ ⟩
ℰ→𝔼 {Γ} {γ} {γ'} {lam ⦅ bind N nil ⦆} {v} 𝔾γγ' ℰMγv =
   ⟨ val-clos N γ' , ⟨ ⇓-lam , G {v} ℰMγv ⟩ ⟩
   where
   G : ∀{v} → ℱ (ℰ N) γ v → 𝕍 v (val-clos N γ')
   G {⊥} ℱℰNγv = tt
   G {const {B} k} ()
   G {v ↦ w} ℱℰNγv {c} vc =
      ℰ→𝔼 {M = N} {w} (λ {x} → 𝔾-ext 𝔾γγ' vc {x}) ℱℰNγv
   G {v₁ ⊔ v₂} ⟨ ℱℰNγv₁ , ℱℰNγv₂ ⟩ = ⟨ G {v₁} ℱℰNγv₁ , G {v₂} ℱℰNγv₂ ⟩
ℰ→𝔼 {Γ} {γ} {γ'} {app ⦅ cons L (cons M nil) ⦆} {v} 𝔾γγ' ⟨ v₁ , ⟨ d₁ , d₂ ⟩ ⟩
    with ℰ→𝔼 {M = L} 𝔾γγ' d₁ | ℰ→𝔼 {M = M} 𝔾γγ' d₂
... | ⟨ val-clos L' δ₁ , ⟨ L⇓L' , 𝕍v₁↦v ⟩ ⟩ | ⟨ c , ⟨ M⇓c , 𝕍v₁ ⟩ ⟩ 
    with 𝕍v₁↦v {c} 𝕍v₁
... | ⟨ c' , ⟨ L'⇓c' , 𝕍v ⟩ ⟩ =
    ⟨ c' , ⟨ (⇓-app L⇓L' M⇓c L'⇓c') , 𝕍v ⟩ ⟩
ℰ→𝔼 {Γ} {γ} {γ'} {app ⦅ cons L (cons M nil) ⦆} {v} 𝔾γγ' ⟨ v₁ , ⟨ d₁ , d₂ ⟩ ⟩
    | ⟨ val-const {P} f , ⟨ L⇓f , 𝕍v₁↦v ⟩ ⟩ | ⟨ c , ⟨ M⇓c , 𝕍v₁ ⟩ ⟩
    with P
... | base B = ⊥-elim 𝕍v₁↦v
... | B ⇒ P′ = {!!}     

adequacy : ∀{M : Term zero}{N : Term zero}
         → TermValue N
         → ℰ M ≃ ℰ N
           ----------------------------------------------------------
         → Σ[ c ∈ Val ] ∅' ⊢ M ⇓ c
adequacy{M}{N} Nv eq 
    with ℰ→𝔼 𝔾-∅ (proj₂ (eq `∅ ⊥) (ℰ-⊥ {M = N} Nv))
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



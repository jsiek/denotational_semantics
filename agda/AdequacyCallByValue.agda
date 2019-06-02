open import Variables
open import Lambda
open import LambdaCallByValue

open import ValueBCD
open import EvalCallByValue
open Lambda.ASTMod
   using (`_; _⦅_⦆; Subst; Ctx; plug;
          exts; cons; bind; nil; rename; ⟪_⟫; subst-zero; _[_]; rename-id)
open import Structures
open import ModelCallByValue
open DomainAux domain
open OrderingAux domain ordering
open LambdaDenot domain ordering _●_ ℱ
open DenotAux domain ordering _●_ ℱ model_basics
open import PreserveReflectCallByValue using (soundness; ℰ-⊥)

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


module AdequacyCallByValue where


𝕍 : Value → Clos → Set
𝕍 ⊥ (clos N γ) = ⊤
𝕍 (v ↦ w) (clos N γ) =
    (∀{c : Clos} → 𝕍 v c → Σ[ c' ∈ Clos ] (γ ,' c) ⊢ N ⇓ c'  ×  𝕍 w c')
𝕍 (u ⊔ v) (clos N γ) = 𝕍 u (clos N γ) × 𝕍 v (clos N γ)


𝔾 : ∀{Γ} → Env Γ → ClosEnv Γ → Set
𝔾 {Γ} γ γ' = ∀{x : Var Γ} → 𝕍 (γ x) (γ' x)

𝔾-∅ : 𝔾 `∅ ∅'
𝔾-∅ {()}

𝔾-ext : ∀{Γ}{γ : Env Γ}{γ' : ClosEnv Γ}{v c}
      → 𝔾 γ γ' → 𝕍 v c → 𝔾 (γ `, v) (γ' ,' c)
𝔾-ext {Γ} {γ} {γ'} g e {Z} = e
𝔾-ext {Γ} {γ} {γ'} g e {S x} = g


sub-𝕍 : ∀{c : Clos}{v v'} → 𝕍 v c → v' ⊑ v → 𝕍 v' c

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

kth-x : ∀{Γ}{γ' : ClosEnv Γ}{x : Var Γ}
     → Σ[ Δ ∈ Context ] Σ[ δ ∈ ClosEnv Δ ] Σ[ N ∈ Term (suc Δ) ]
                 γ' x ≡ clos N δ
kth-x{γ' = γ'}{x = x} with γ' x
... | clos{Γ = Δ} N δ = ⟨ Δ , ⟨ δ , ⟨ N , refl ⟩ ⟩ ⟩


𝔼 : ∀{Γ} → Value → Term Γ → ClosEnv Γ → Set
𝔼 v M γ = Σ[ c ∈ Clos ] γ ⊢ M ⇓ c × 𝕍 v c

ℰ→𝔼 : ∀{Γ}{γ : Env Γ}{γ' : ClosEnv Γ}{M : Term Γ }{v}
            → 𝔾 γ γ' → ℰ M γ v → 𝔼 v M γ'
ℰ→𝔼 {Γ} {γ} {γ'} {` x} {v} 𝔾γγ' ℰMγv =
   ⟨ γ' x , ⟨ ⇓-var , sub-𝕍 (𝔾γγ' {x}) ℰMγv ⟩ ⟩
ℰ→𝔼 {Γ} {γ} {γ'} {lam ⦅ bind N nil ⦆} {v} 𝔾γγ' ℰMγv =
   ⟨ clos N γ' , ⟨ ⇓-lam , G ℰMγv ⟩ ⟩
   where
   G : ∀{v} → ℱ (ℰ N) γ v → 𝕍 v (clos N γ')
   G {⊥} ℱℰNγv = tt
   G {v ↦ w} ℱℰNγv {c} vc =
      ℰ→𝔼 {M = N} {w} (λ {x} → 𝔾-ext 𝔾γγ' vc {x}) ℱℰNγv
   G {v₁ ⊔ v₂} ⟨ ℱℰNγv₁ , ℱℰNγv₂ ⟩ = ⟨ G {v₁} ℱℰNγv₁ , G {v₂} ℱℰNγv₂ ⟩
ℰ→𝔼 {Γ} {γ} {γ'} {app ⦅ cons L (cons M nil) ⦆} {v} 𝔾γγ' ⟨ v₁ , ⟨ d₁ , d₂ ⟩ ⟩
    with ℰ→𝔼 {M = L} 𝔾γγ' d₁ | ℰ→𝔼 {M = M} 𝔾γγ' d₂
... | ⟨ clos L' δ₁ , ⟨ L⇓L' , 𝕍v₁↦v ⟩ ⟩
    | ⟨ clos M' δ₂ , ⟨ M⇓M' , 𝕍v₁ ⟩ ⟩ 
    with 𝕍v₁↦v {clos M' δ₂} 𝕍v₁
... | ⟨ c , ⟨ L'⇓c , 𝕍v ⟩ ⟩ =
    ⟨ c , ⟨ (⇓-app L⇓L' M⇓M' L'⇓c) , 𝕍v ⟩ ⟩
  

adequacy : ∀{M : Term zero}{N : Term (suc zero)}
         → ℰ M ≃ ℰ (lam ⦅ bind N nil ⦆)
           ----------------------------------------------------------
         → Σ[ Γ ∈ Context ] Σ[ N′ ∈ Term (suc Γ) ] Σ[ γ ∈ ClosEnv Γ ]
            ∅' ⊢ M ⇓ clos N′ γ
adequacy{M}{N} eq 
    with ℰ→𝔼 𝔾-∅ (proj₂ (eq `∅ ⊥) (ℰ-⊥ {γ = λ ()}{M = lam ⦅ bind N nil ⦆} V-ƛ))
... | ⟨ clos {Γ} N′ γ , ⟨ M⇓c , Vc ⟩ ⟩ =
    ⟨ Γ , ⟨ N′ , ⟨ γ , M⇓c ⟩ ⟩ ⟩


reduce→cbv : ∀ {M : Term zero} {N : Term (suc zero)}
           → M —↠ lam ⦅ bind N nil ⦆
           → Σ[ Δ ∈ ℕ ] Σ[ N′ ∈ Term (suc Δ) ] Σ[ δ ∈ ClosEnv Δ ] 
             ∅' ⊢ M ⇓ clos N′ δ
reduce→cbv {M}{N} M—↠ƛN = adequacy {M}{N} (soundness M—↠ƛN)


cbv↔reduce : ∀ {M : Term zero}
           → (Σ[ N ∈ Term (suc zero) ] (M —↠ lam ⦅ bind N nil ⦆))
             iff
             (Σ[ Δ ∈ ℕ ] Σ[ N′ ∈ Term (suc Δ) ] Σ[ δ ∈ ClosEnv Δ ]
               ∅' ⊢ M ⇓ clos N′ δ)
cbv↔reduce {M} = ⟨ (λ x → reduce→cbv (proj₂ x)) ,
                   (λ x → cbv→reduce (proj₂ (proj₂ (proj₂ x)))) ⟩


denot-equal-terminates : ∀{Γ} {M N : Term Γ} {C : Ctx Γ zero}
  → ℰ M ≃ ℰ N  →  terminates (plug C M)
    -----------------------------------
  → terminates (plug C N)
denot-equal-terminates {Γ}{M}{N}{C} ℰM≃ℰN ⟨ N′ , CM—↠ƛN′ ⟩ =
  let ℰCM≃ℰƛN′ = soundness CM—↠ƛN′ in
  let ℰCM≃ℰCN = compositionality{Γ = Γ}{Δ = zero}{C = C} ℰM≃ℰN in
  let ℰCN≃ℰƛN′ = ≃-trans (≃-sym ℰCM≃ℰCN) ℰCM≃ℰƛN′ in
    cbv→reduce (proj₂ (proj₂ (proj₂ (adequacy{N = N′} ℰCN≃ℰƛN′))))

denot-equal-contex-equal : ∀{Γ} {M N : Term Γ}
  → ℰ M ≃ ℰ N
    ---------
  → M ≅ N
denot-equal-contex-equal{Γ}{M}{N} eq {C} =
   ⟨ (λ tm → denot-equal-terminates{M = M} eq tm) ,
     (λ tn → denot-equal-terminates{M = N} (≃-sym eq) tn) ⟩

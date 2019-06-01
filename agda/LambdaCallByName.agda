open import Variables
open import Structures
open import Lambda
open Lambda.ASTMod
   using (`_; _⦅_⦆; Subst;
          exts; cons; bind; nil; rename; ⟪_⟫; subst-zero; _[_]; rename-id)
open Lambda.Reduction using (_—→_; ξ₁-rule; ξ₂-rule; β-rule; ζ-rule)
open import ValueBCD
open DomainAux domain
open OrderingAux domain ordering

open import ModelCallByName
open import Filter domain ordering model model_basics
open import SubstitutionPreserve domain ordering model model_basics
open LambdaDenot domain ordering model
open import RenamePreserveReflect domain ordering model model_basics
  using (⊑-env)  

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; sym; cong; cong₂; cong-app)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥-elim) renaming (⊥ to Bot)
open import Function using (_∘_)
open import Data.Unit using (⊤; tt)
open import Data.Empty renaming (⊥ to Bot)
open import Relation.Nullary using (¬_; Dec; yes; no)

import SubstitutionReflect
open SubstitutionReflect.CallByName

module LambdaCallByName where

{-


  substitution-reflect : ∀ {Δ} {δ : Env Δ} {N : Term (suc Δ)} {M : Term Δ} {v}
    → ℰ (N [ M ]) δ v  → ℰ M δ ⊥
      ------------------------------------------------
    → Σ[ w ∈ Value ] ℰ M δ w  ×  ℰ N (δ `, w) v
  substitution-reflect{N = N}{M = M} ℰNMδv ℰMδ⊥
       with subst-reflect {M = N} ℰNMδv refl (subst-zero-⊥ ℰMδ⊥)
  ...  | ⟨ γ , ⟨ δσγ , γNv ⟩ ⟩
       with subst-zero-reflect δσγ
  ...  | ⟨ w , ⟨ γ⊑δw , δMw ⟩ ⟩ =
         ⟨ w , ⟨ δMw , ⊑-env {M = N} γNv γ⊑δw ⟩ ⟩


module Reflect
  (_●_ : ∀{Γ} → Denotation Γ → Denotation Γ → Denotation Γ)
  (ME : ModelExtra _●_)
  where

  open Denot _●_
  open ModelExtra ME
  open ModelBot MBot
  open ModelBasics MB
  open ModelCong Cong

  cong-● : ∀{Γ Δ}{γ : Env Γ}{δ : Env  Δ}{D₁ D₂ : Denotation Γ}
            {D₁′ D₂′ : Denotation Δ}
         → D₁ γ ≃ D₁′ δ → D₂ γ ≃ D₂′ δ → (D₁ ● D₂) γ ≃ (D₁′ ● D₂′) δ
  cong-● {γ = γ}{δ}{D₁}{D₂}{D₁′}{D₂′} eq1 eq2 {w} =
    ⟨ (●-≲{D₁ = D₁}{D₂}{D₁′}{D₂′} (proj₁ eq1) (proj₁ eq2)) {v = w} ,
      (●-≲{D₁ = D₁′}{D₂′}{D₁}{D₂} (proj₂ eq1) (proj₂ eq2)) {v = w} ⟩


  module RP = RenamePreserveReflect _●_ Cong
  open RP using (⊑-env; EnvExt⊑; rename-pres; rename-inc-reflect)  

  module F = Filter _●_ MB
  open F using (ℰ-⊑; ℰ-⊔; WF)

  open Preservation _●_ ME using (ℰ-⊥)

  open SubstReflect _●_ ME

  reflect-beta : ∀{Γ}{γ : Env Γ}{M N}{v}
      → ℰ (N [ M ]) γ v
      → ℰ ((ƛ N) · M) γ v
  reflect-beta {Γ}{γ}{M}{N}{v} d 
      with substitution-reflect{N = N}{M = M} d (ℰ-⊥ {M = M})
  ... | ⟨ v₂′ , ⟨ d₁′ , d₂′ ⟩ ⟩ rewrite ●-≡ {Γ}{ℱ (ℰ N)}{ℰ M}{γ}{v} =
        inj₂ ⟨ v₂′ , ⟨ d₂′ , d₁′ ⟩ ⟩

  reflect : ∀ {Γ} {γ : Env Γ} {M M′ N v}
    →  M —→ M′  →   M′ ≡ N  →  ℰ N γ v
      --------------------------------
    → ℰ M γ v    
  reflect {γ = γ} (ξ₁-rule {L = L}{L′}{M} L—→L′) L′·M≡N
      rewrite sym L′·M≡N =
      ●-≲ (reflect L—→L′ refl) (≲-refl {d = ℰ M γ})
  reflect {γ = γ} (ξ₂-rule {L = L}{M}{M′} M—→M′) L·M′≡N
      rewrite sym L·M′≡N =
      ●-≲ (≲-refl {d = ℰ L γ}) (reflect M—→M′ refl)
  reflect (β-rule {N = N}{M = M}) M′≡N rewrite sym M′≡N =
      reflect-beta {M = M}{N}
  reflect {v = v} (ζ-rule {Γ}{N}{N′} N—→N′) M′≡N rewrite sym M′≡N =
      ℱ-≲ (reflect N—→N′ refl) {v}
-}




ℱ-inv : ∀{Γ}{D : Denotation (suc Γ)}{γ : Env Γ}{u : Value}
      → ℱ D γ u
      → u ⊑ ⊥ ⊎ (Σ[ v ∈ Value ] Σ[ w ∈ Value ] D (γ `, v) w × v ↦ w ⊑ u)
ℱ-inv {u = ⊥} tt = inj₁ ⊑-refl
ℱ-inv {u = v ↦ w} ℱDγu = inj₂ ⟨ v , ⟨ w , ⟨ ℱDγu , ⊑-refl ⟩ ⟩ ⟩
ℱ-inv {u = u ⊔ v} ⟨ fst , snd ⟩
    with ℱ-inv{u = u} fst | ℱ-inv{u = v} snd
... | inj₁ u⊑⊥ | inj₁ v⊑⊥ = inj₁ (⊑-conj-L u⊑⊥ v⊑⊥)
... | inj₁ u⊑⊥ | inj₂ ⟨ v' , ⟨ w' , ⟨ Dγv'w' , v'↦w'⊑v ⟩ ⟩ ⟩ =
      inj₂ ⟨ v' , ⟨ w' , ⟨ Dγv'w' , ⊑-conj-R2 v'↦w'⊑v ⟩ ⟩ ⟩
... | inj₂ ⟨ v' , ⟨ w' , ⟨ Dγv'w' , v'↦w'⊑v ⟩ ⟩ ⟩ | _ =
      inj₂ ⟨ v' , ⟨ w' , ⟨ Dγv'w' , ⊑-conj-R1 v'↦w'⊑v ⟩ ⟩ ⟩



ℱ●-inv : ∀{Γ} {D₁ : Denotation (suc Γ)}{D₂ : Denotation Γ}{γ : Env Γ}
          {w : Value}
        → (ℱ D₁ ● D₂) γ w
        → w ⊑ ⊥ ⊎ (Σ[ v ∈ Value ] D₁ (γ `, v) w × D₂ γ v)
ℱ●-inv {Γ}{D₁}{D₂}{γ}{w} ℱD₁●D₂γw
    with ℱD₁●D₂γw
... | inj₁ w⊑⊥ = inj₁ w⊑⊥ 
... | inj₂ ⟨ v , ⟨ ℱD₁γv↦w , D₂γv ⟩ ⟩ =
      inj₂ ⟨ v , ⟨ ℱD₁γv↦w , D₂γv ⟩ ⟩

preserve : ∀ {Γ} {γ : Env Γ} {M N v}
  → M —→ N
  → ℰ M γ v
    ----------
  → ℰ N γ v
preserve {γ = γ} (ξ₁-rule{L = L}{L´}{M} L—→L′) =
  ●-≲ {γ = γ}{γ}{D₁ = ℰ L}{D₂ = ℰ M}{D₁′ = ℰ L´}{D₂′ = ℰ M}
              (λ x → preserve L—→L′ x)
              (λ x → x)
preserve {γ = γ} (ξ₂-rule{L = L}{M}{M′} M—→M′) =
  ●-≲ {γ = γ}{γ}{D₁ = ℰ L}{D₂ = ℰ M}{D₁′ = ℰ L}{D₂′ = ℰ M′}
              (λ x → x)
              (λ x → preserve M—→M′ x)
preserve {Γ}{γ}{app ⦅ cons (lam ⦅ bind N nil ⦆) (cons M nil) ⦆}{_}
               {v} (β-rule{N = N}{M = M}) ℰƛN·Mγw
    with ℰƛN·Mγw
... | inj₁ w⊑⊥ =
      ℰ-⊑ {M = ⟪ subst-zero M ⟫ N} (ℰ-⊥{M = ⟪ subst-zero M ⟫ N}) w⊑⊥
... | inj₂ ⟨ v' , ⟨ ℰNγvw , ℰMγv ⟩ ⟩ = 
      substitution{N = N}{M = M} {v'} ℰNγvw ℰMγv
preserve {v = v} (ζ-rule {Γ}{N}{N′} N—→N′) = ℱ-≲ (preserve N—→N′) {v}


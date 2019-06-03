open import Primitives
open import Structures
open import ISWIM

open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥-elim) renaming (⊥ to Bot)
open import Relation.Nullary using (¬_; Dec; yes; no)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong; cong₂; cong-app)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)

module ModelISWIM where

  open import ValueBCDConst public
  open DomainAux domain public
  open OrderingAux domain ordering public
  open import ModelCallByValue domain ordering ℱ model_curry public

  ℘ : ∀{P : Prim} → rep P → Value → Set
  ℘ {base B} k (const {B′} k′)
      with base-eq? B B′
  ... | yes eq rewrite eq = k ≡ k′
  ... | no neq = Bot
  ℘ {B ⇒ P} f (const x₂) = Bot
  ℘ {P} k ⊥ = ⊤
  ℘ {base B} f (v ↦ w) = Bot
  ℘ {B ⇒ P} f (v ↦ w) = ∀{k : base-rep B} → v ⊑ const {B} k → ℘ {P} (f k) w
  ℘ {P} f (u ⊔ v) = ℘ {P} f u × ℘ {P} f v

  ℰ : ∀{Γ} → Term Γ → Denotation Γ
  ℰ (lit {P} k ⦅ nil ⦆) γ v = ℘ {P} k v
  ℰ {Γ} (` x) γ v = v ⊑ γ x
  ℰ {Γ} (lam ⦅ bind N nil ⦆) = ℱ (ℰ N)
  ℰ {Γ} (app ⦅ cons L (cons M nil) ⦆) = (ℰ L) ● (ℰ M)

  ℘-⊑ : ∀{P}{k : rep P}{v w : Value}
     → ℘ {P} k v
     → w ⊑ v
       ------------
     → ℘ {P} k w
  ℘-⊑ ℘kv w⊑v = {!!}

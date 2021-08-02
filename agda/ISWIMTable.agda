
module ISWIMTable where

open import Primitives
open import Syntax using (Rename; extensionality)
open import ISWIM hiding (subst-zero; _[_]; id; _—→_)
open import Fold2 Op sig
open import ValueTable
open import ScopedTuple hiding (𝒫)
open import Sig

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
    renaming (_,_ to ⟨_,_⟩)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; sym; cong; cong₂; cong-app; subst)

interp  : (op : Op) → Tuple (sig op) (ArgTy (𝒫 Value)) → 𝒫 Value
interp lam ⟨ F , _ ⟩ = Λ F
interp app ⟨ D₁ , ⟨ D₂ , _ ⟩ ⟩ = D₁ ▪ D₂
interp (lit P k) _ = ℘ {P} k

infix 7 ⟦_⟧_
⟦_⟧_ : Term → (Var → 𝒫 Value) → 𝒫 Value
⟦ M ⟧ ρ = fold interp ∅ ρ M


{- Substitution Lemma -}

⟦⟧-rename : ∀ {M : Term}{σ : Rename}{ρ : Var → 𝒫 Value}
  → ⟦ rename σ M ⟧ ρ ≡ ⟦ M ⟧ (λ x → ⟦ ` σ x ⟧ ρ)
⟦⟧-rename {M}{ρ} = fold-rename-fusion M

⟦⟧-subst : ∀ {M : Term}{σ : Subst}{ρ : Var → 𝒫 Value}
  → ⟦ ⟪ σ ⟫ M ⟧ ρ ≡ ⟦ M ⟧ (λ x → ⟦ σ x ⟧ ρ)
⟦⟧-subst {M}{ρ} = fold-subst-fusion M

id : Subst
id = (λ x → ` x)

_[_] : Term → Term → Term
N [ M ] =  ⟪ M • id ⟫ N

⟦⟧-substitution : ∀ {M N : Term}{ρ : Var → 𝒫 Value}
  → ⟦ M [ N ] ⟧ ρ ≡ ⟦ M ⟧ ((⟦ N ⟧ ρ) • ρ)
⟦⟧-substitution {M}{N}{ρ} =
  subst (λ X → ⟦ M [ N ] ⟧ ρ ≡ ⟦ M ⟧ X) (extensionality EQ)
        (⟦⟧-subst {M}{N • id})
  where 
  EQ : (x : Var) → ⟦ (N • id) x ⟧ ρ ≡ (⟦ N ⟧ ρ • ρ) x
  EQ zero = refl
  EQ (suc x) = refl


{- Join Closed -}
⟦⟧-join-closed : ∀ {M : Term}{ρ}
   → (∀ x → join-closed (ρ x) )
   → join-closed (⟦ M ⟧ ρ)
⟦⟧-join-closed {` x} {ρ} ρ-closed = ρ-closed x
⟦⟧-join-closed {L · M} {ρ} ρ-closed =
  let IH1 = ⟦⟧-join-closed{L} ρ-closed in
  let IH2 = ⟦⟧-join-closed{M} ρ-closed in
  {!!}
⟦⟧-join-closed {ƛ N} {ρ} ρ-closed = {!!}
⟦⟧-join-closed {$ p k} {ρ} ρ-closed = {!!}


infix 2 _—→_

data _—→_ : Term → Term → Set where

  ξ₁-rule : ∀  {L L′ M : Term}
    → L —→ L′
      ----------------
    → L · M —→ L′ · M

  ξ₂-rule : ∀  {L M M′ : Term}
    → TermValue L
    → M —→ M′
      ----------------
    → L · M —→ L · M′

  β-rule : ∀  {N : Term} {M : Term}
    → TermValue M
      ---------------------------------
    → (ƛ N) · M —→ N [ M ]

  δ-rule : ∀ {B}{P} {f : base-rep B → rep P} {k : base-rep B}
      ------------------------------------------------------------
    → _—→_  (($ (B ⇒ P) f) · ($ (base B) k)) ($ P (f k))


⟦⟧—→ : ∀{M N : Term}{ρ : Var → 𝒫 Value}
   → M —→ N
   → ⟦ M ⟧ ρ ≃ ⟦ N ⟧ ρ
   
⟦⟧—→ {L · M} {L′ · M} {ρ} (ξ₁-rule L—→L′) =
  let IH = ⟦⟧—→{ρ = ρ} L—→L′ in
    ⟦ L · M ⟧ ρ
  ≃⟨ ≃-refl ⟩
    (⟦ L ⟧ ρ) ▪ (⟦ M ⟧ ρ)
  ≃⟨ ▪-cong IH ≃-refl ⟩
    (⟦ L′ ⟧ ρ) ▪ (⟦ M ⟧ ρ)
  ≃⟨ ≃-refl ⟩
    ⟦ L′ · M ⟧ ρ
  ∎
  where open ≃-Reasoning  
⟦⟧—→ {V · M} {.(_ · _)} {ρ} (ξ₂-rule {M′ = M′} v M—→M′) =
  let IH = ⟦⟧—→{ρ = ρ} M—→M′ in
    ⟦ V · M ⟧ ρ
  ≃⟨ ≃-refl ⟩
    (⟦ V ⟧ ρ) ▪ (⟦ M ⟧ ρ)
  ≃⟨ ▪-cong (≃-refl{D = ⟦ V ⟧ ρ}) IH ⟩
    (⟦ V ⟧ ρ) ▪ (⟦ M′ ⟧ ρ)
  ≃⟨ ≃-refl ⟩
    ⟦ V · M′ ⟧ ρ
  ∎
  where open ≃-Reasoning  
⟦⟧—→ {ƛ N · V} {_} {ρ} (β-rule v) =
    ⟦ ƛ N · V ⟧ ρ
  ≃⟨ {!!} ⟩
     (Λ (λ D → ⟦ N ⟧ (D • ρ))) ▪ (⟦ V ⟧ ρ)
  ≃⟨ {!!} ⟩
     ⟦ N ⟧ (⟦ V ⟧ ρ • ρ)
  ≃⟨ {!!} {- sym (⟦⟧-substitution {N} {V} {ρ}) -} ⟩
    ⟦ N [ V ] ⟧ ρ
  ∎
  where open ≃-Reasoning
⟦⟧—→ {($ (B ⇒ P) f · $ (base B) k)} {_} {ρ} δ-rule = {!!}

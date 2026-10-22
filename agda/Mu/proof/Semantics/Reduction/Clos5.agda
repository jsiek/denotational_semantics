{-

  The values of the Clos5μ reduction semantics
  (Mu/Semantics/Reduction/Clos5.agda), which reduce to val, and the
  laws of its substitution, as for Clos5ᵀ
  (proof/Semantics/Reduction/Typed/Clos5.agda): two traversals fuse
  into one, substitution by variables is the identity, and so a
  substitution under a binder and then one for the bound variable is
  one substitution (exts-[]).

-}

module Mu.proof.Semantics.Reduction.Clos5 where

open import Mu.Semantics.Reduction.Clos5 public
open import Mu.Language.Type hiding (_[_])
open import Mu.Language.Clos5 hiding (wk; wks)
open import Mu.Framework.AllUtil using (All; []; _∷_)
open import Semantics.Observation using (Obs; o-error)
open import Mu.proof.Framework.ReductionAll Obs o-error using (Each; []; _∷_)
open import Semantics.Reduction.Smallstep using (val)
open import proof.Framework.ReductionVec Obs o-error using (cong₃)

open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)

module _ {Σ : List DSig} where

  {- Values -----------------------------------------------------------------}

  data Value {Γ} : ∀ {A} → Tm Σ Γ A → Set where
    fun-ref : ∀ {Δ A B} {f : Σ ∋ sig Δ A B} → Value (fun-ref f)
    pack : ∀ {Δ A B} {L : Tm Σ Γ (code Δ A B)} {M} → Value L → Value M → Value (pack L M)
    lit : ∀ {B c} → Value (lit B c)
    tuple : ∀ {Δ} {Vs : All (Tm Σ Γ) Δ} → Each Value Vs → Value (tuple Vs)
    inl : ∀ {A B} {V : Tm Σ Γ A} → Value V → Value (inl {B = B} V)
    inr : ∀ {A B} {V : Tm Σ Γ B} → Value V → Value (inr {A = A} V)
    fold : ∀ {A} {V : Tm Σ Γ (unroll A)} → Value V → Value (fold {A = A} V)

  value-red : ∀ {ds A} {V : Tm Σ [] A} → Value V → red ds V ≡ val
  values-red : ∀ {ds Δ} {Vs : All (Tm Σ []) Δ} → Each Value Vs → reds ds Vs ≡ val
  value-red fun-ref = refl
  value-red {ds} (pack v w) rewrite value-red {ds} v | value-red {ds} w = refl
  value-red lit = refl
  value-red {ds} (tuple vs) rewrite values-red {ds} vs = refl
  value-red {ds} (inl v) rewrite value-red {ds} v = refl
  value-red {ds} (inr v) rewrite value-red {ds} v = refl
  value-red {ds} (fold v) rewrite value-red {ds} v = refl
  values-red [] = refl
  values-red {ds} (v ∷ vs) rewrite value-red {ds} v | values-red {ds} vs = refl

  {- Fusion -------------------------------------------------------------------}

  module _ (𝒦₁ 𝒦₂ 𝒦₃ : Kit)
    (R : ∀ {Γ Δ Θ} → Sub 𝒦₁ Γ Δ → Sub 𝒦₂ Δ Θ → Sub 𝒦₃ Γ Θ → Set)
    (R-exts : ∀ {Γ Δ Θ B} {σ₁ : Sub 𝒦₁ Γ Δ} {σ₂ : Sub 𝒦₂ Δ Θ} {σ₃ : Sub 𝒦₃ Γ Θ} → R σ₁ σ₂ σ₃ → R (exts 𝒦₁ {B = B} σ₁) (exts 𝒦₂ σ₂) (exts 𝒦₃ σ₃))
    (R-var : ∀ {Γ Δ Θ} {σ₁ : Sub 𝒦₁ Γ Δ} {σ₂ : Sub 𝒦₂ Δ Θ} {σ₃ : Sub 𝒦₃ Γ Θ} → R σ₁ σ₂ σ₃ → ∀ {A} (x : Γ ∋ A)
      → trav 𝒦₂ σ₂ (Kit.tm 𝒦₁ (σ₁ x)) ≡ Kit.tm 𝒦₃ (σ₃ x)) where

    fuse : ∀ {Γ Δ Θ} {σ₁ : Sub 𝒦₁ Γ Δ} {σ₂ : Sub 𝒦₂ Δ Θ} {σ₃ : Sub 𝒦₃ Γ Θ} → R σ₁ σ₂ σ₃ → ∀ {A} (M : Tm Σ Γ A) → trav 𝒦₂ σ₂ (trav 𝒦₁ σ₁ M) ≡ trav 𝒦₃ σ₃ M
    fuses : ∀ {Γ Δ Θ Δ'} {σ₁ : Sub 𝒦₁ Γ Δ} {σ₂ : Sub 𝒦₂ Δ Θ} {σ₃ : Sub 𝒦₃ Γ Θ} → R σ₁ σ₂ σ₃ → (Ms : All (Tm Σ Γ) Δ')
      → travs 𝒦₂ σ₂ (travs 𝒦₁ σ₁ Ms) ≡ travs 𝒦₃ σ₃ Ms
    fuse r (` x) = R-var r x
    fuse r (fun-ref f) = refl
    fuse r (pack L M) = cong₂ pack (fuse r L) (fuse r M)
    fuse r (callc L M) = cong₂ callc (fuse r L) (fuse r M)
    fuse r (lit B c) = refl
    fuse r (tuple Ms) = cong tuple (fuses r Ms)
    fuse r (get i M) = cong (get i) (fuse r M)
    fuse r (inl M) = cong inl (fuse r M)
    fuse r (inr M) = cong inr (fuse r M)
    fuse r (case L M N) rewrite fuse r L | fuse (R-exts r) M | fuse (R-exts r) N = refl
    fuse r (prim p L M) = cong₂ (prim p) (fuse r L) (fuse r M)
    fuse r (let′ M N) = cong₂ let′ (fuse r M) (fuse (R-exts r) N)
    fuse r (fold M) = cong fold (fuse r M)
    fuse r (unfold M) = cong unfold (fuse r M)
    fuses r [] = refl
    fuses r (M ∷ Ms) = cong₂ _∷_ (fuse r M) (fuses r Ms)

  {- a renaming, then a traversal -}
  ren-trav : ∀ 𝒦 {Γ Δ Θ} {r : ∀ {A} → Γ ∋ A → Δ ∋ A} {σ : Sub 𝒦 Δ Θ} {τ : Sub 𝒦 Γ Θ}
    → (∀ {A} (x : Γ ∋ A) → σ (r x) ≡ τ x) → ∀ {A} (M : Tm Σ Γ A) → trav 𝒦 σ (ren r M) ≡ trav 𝒦 τ M
  ren-trav 𝒦 = fuse varK 𝒦 𝒦 (λ r σ τ → ∀ {A} x → σ {A} (r x) ≡ τ x)
    (λ { h Z → refl ; h (S x) → cong (Kit.wk 𝒦) (h x) }) (λ h x → cong (Kit.tm 𝒦) (h x))

  {- a substitution, then a renaming -}
  sub-ren : ∀ {Γ Δ Θ} {σ : Sub tmK Γ Δ} {r : ∀ {A} → Δ ∋ A → Θ ∋ A} {τ : Sub tmK Γ Θ}
    → (∀ {A} (x : Γ ∋ A) → ren r (σ x) ≡ τ x) → ∀ {A} (M : Tm Σ Γ A) → ren r (sub σ M) ≡ sub τ M
  sub-ren = fuse tmK varK tmK (λ σ r τ → ∀ {A} x → ren r (σ {A} x) ≡ τ x)
    (λ { h Z → refl
       ; {σ₁ = σ} h (S x) → trans (ren-trav varK (λ _ → refl) (σ x))
                              (trans (sym (ren-trav varK (λ _ → refl) (σ x))) (cong (ren S) (h x))) })
    (λ h x → h x)

  {- a substitution, then another -}
  sub-sub : ∀ {Γ Δ Θ} {σ : Sub tmK Γ Δ} {τ : Sub tmK Δ Θ} {ρ : Sub tmK Γ Θ}
    → (∀ {A} (x : Γ ∋ A) → sub τ (σ x) ≡ ρ x) → ∀ {A} (M : Tm Σ Γ A) → sub τ (sub σ M) ≡ sub ρ M
  sub-sub = fuse tmK tmK tmK (λ σ τ ρ → ∀ {A} x → sub τ (σ {A} x) ≡ ρ x)
    (λ { h Z → refl
       ; {σ₁ = σ} {τ} h (S x) → trans (ren-trav tmK (λ _ → refl) (σ x))
                                  (trans (sym (sub-ren (λ _ → refl) (σ x))) (cong (ren S) (h x))) })
    (λ h x → h x)

  {- substituting variables for themselves -}
  sub-id : ∀ {Γ A} {σ : Sub tmK Γ Γ} → (∀ {B} (x : Γ ∋ B) → σ x ≡ ` x) → (M : Tm Σ Γ A) → sub σ M ≡ M
  sub-ids : ∀ {Γ Δ} {σ : Sub tmK Γ Γ} → (∀ {B} (x : Γ ∋ B) → σ x ≡ ` x) → (Ms : All (Tm Σ Γ) Δ) → travs tmK σ Ms ≡ Ms
  sub-id-exts : ∀ {Γ B} {σ : Sub tmK Γ Γ} → (∀ {C} (x : Γ ∋ C) → σ x ≡ ` x) → ∀ {C} (x : (B ∷ Γ) ∋ C) → exts tmK σ x ≡ ` x
  sub-id-exts h Z = refl
  sub-id-exts h (S x) = cong (ren S) (h x)
  sub-id h (` x) = h x
  sub-id h (fun-ref f) = refl
  sub-id h (pack L M) = cong₂ pack (sub-id h L) (sub-id h M)
  sub-id h (callc L M) = cong₂ callc (sub-id h L) (sub-id h M)
  sub-id h (lit B c) = refl
  sub-id h (tuple Ms) = cong tuple (sub-ids h Ms)
  sub-id h (get i M) = cong (get i) (sub-id h M)
  sub-id h (inl M) = cong inl (sub-id h M)
  sub-id h (inr M) = cong inr (sub-id h M)
  sub-id h (case L M N) = cong₃ case (sub-id h L) (sub-id (sub-id-exts h) M) (sub-id (sub-id-exts h) N)
  sub-id h (prim p L M) = cong₂ (prim p) (sub-id h L) (sub-id h M)
  sub-id h (let′ M N) = cong₂ let′ (sub-id h M) (sub-id (sub-id-exts h) N)
  sub-id h (fold M) = cong fold (sub-id h M)
  sub-id h (unfold M) = cong unfold (sub-id h M)
  sub-ids h [] = refl
  sub-ids h (M ∷ Ms) = cong₂ _∷_ (sub-id h M) (sub-ids h Ms)

  {- under a binder, then for the bound variable: closed values for the rest -}
  exts-[] : ∀ {Γ A B} (σ : Sub tmK Γ []) (W : Tm Σ [] A) (N : Tm Σ (A ∷ Γ) B) → sub (exts tmK σ) N [ W ] ≡ sub (W • σ) N
  exts-[] σ W = sub-sub λ { Z → refl ; (S x) → trans (ren-trav tmK {τ = `_} (λ ()) (σ x)) (sub-id (λ ()) (σ x)) }

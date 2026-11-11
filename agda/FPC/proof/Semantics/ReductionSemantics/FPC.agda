{-

  The values of the FPC reduction semantics
  (FPC/Semantics/ReductionSemantics/FPC.agda), which reduce to val, and the
  laws of its renaming and substitution, as for ISWIMᵀ
  (ISWIM/proof/Semantics/Reduction/Typed/ISWIM.agda): the two by induction on
  its terms, that two traversals fuse into one (fuse) and that
  substitution by variables is the identity (sub-id), and from them the
  rest (proof/Framework/Syntax/TypedSubst.agda); in particular a
  substitution under a binder and then one for the bound variable is one
  substitution (exts-[]).

-}

module FPC.proof.Semantics.ReductionSemantics.FPC where

open import FPC.Semantics.ReductionSemantics.FPC public
open import FPC.Language.Type hiding (_[_])
open import FPC.Language.FPC
open import FPC.Framework.AllUtil using (All; []; _∷_)
open import Semantics.Observation using (Obs; o-error)
open import FPC.proof.Framework.ReductionAll Obs o-error using (Each; []; _∷_)
open import Semantics.Reduction.Smallstep using (val)
open import proof.Framework.Syntax.TypedSubst Tm `_

open import Data.List using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)

{- Values -------------------------------------------------------------------}

data Value {Γ} : ∀ {A} → Tm Γ A → Set where
  lam : ∀ {A B} {N : Tm (A ∷ Γ) B} → Value (lam N)
  lit : ∀ {B c} → Value (lit B c)
  tuple : ∀ {Δ} {Vs : All (Tm Γ) Δ} → Each Value Vs → Value (tuple Vs)
  inl : ∀ {A B} {V : Tm Γ A} → Value V → Value (inl {B = B} V)
  inr : ∀ {A B} {V : Tm Γ B} → Value V → Value (inr {A = A} V)
  fold : ∀ {A} {V : Tm Γ (unroll A)} → Value V → Value (fold {A = A} V)

value-red : ∀ {A} {V : Tm [] A}
  → Value V
  → red V ≡ val
values-red : ∀ {Δ} {Vs : All (Tm []) Δ}
  → Each Value Vs
  → reds Vs ≡ val
value-red lam = refl
value-red lit = refl
value-red (tuple vs) rewrite values-red vs = refl
value-red (inl v) rewrite value-red v = refl
value-red (inr v) rewrite value-red v = refl
value-red (fold v) rewrite value-red v = refl
values-red [] = refl
values-red (v ∷ vs) rewrite value-red v | values-red vs = refl

{- Substitution: fusion and the identity, by induction on terms ------------}

open Traversal trav (λ _ _ _ → refl) public

module _ (𝒦₁ 𝒦₂ 𝒦₃ : Kit)
  (R : ∀ {Γ Δ Θ} → Sub 𝒦₁ Γ Δ → Sub 𝒦₂ Δ Θ → Sub 𝒦₃ Γ Θ → Set)
  (R-exts : ∀ {Γ Δ Θ B} {σ₁ : Sub 𝒦₁ Γ Δ} {σ₂ : Sub 𝒦₂ Δ Θ} {σ₃ : Sub 𝒦₃ Γ Θ} → R σ₁ σ₂ σ₃ → R (exts 𝒦₁ {B = B} σ₁) (exts 𝒦₂ σ₂) (exts 𝒦₃ σ₃))
  (R-var : ∀ {Γ Δ Θ} {σ₁ : Sub 𝒦₁ Γ Δ} {σ₂ : Sub 𝒦₂ Δ Θ} {σ₃ : Sub 𝒦₃ Γ Θ} → R σ₁ σ₂ σ₃ → ∀ {A} (x : Γ ∋ A) → trav 𝒦₂ σ₂ (Kit.tm 𝒦₁ (σ₁ x)) ≡ Kit.tm 𝒦₃ (σ₃ x)) where

  fuse : ∀ {Γ Δ Θ} {σ₁ : Sub 𝒦₁ Γ Δ} {σ₂ : Sub 𝒦₂ Δ Θ} {σ₃ : Sub 𝒦₃ Γ Θ}
    → R σ₁ σ₂ σ₃
    → ∀ {A} (M : Tm Γ A)
    → trav 𝒦₂ σ₂ (trav 𝒦₁ σ₁ M) ≡ trav 𝒦₃ σ₃ M
  fuses : ∀ {Γ Δ Θ Δ'} {σ₁ : Sub 𝒦₁ Γ Δ} {σ₂ : Sub 𝒦₂ Δ Θ} {σ₃ : Sub 𝒦₃ Γ Θ}
    → R σ₁ σ₂ σ₃
    → (Ms : All (Tm Γ) Δ')
    → travs 𝒦₂ σ₂ (travs 𝒦₁ σ₁ Ms) ≡ travs 𝒦₃ σ₃ Ms
  fuse r (` x) = R-var r x
  fuse r (lam N) = cong lam (fuse (R-exts r) N)
  fuse r (app L M) = cong₂ app (fuse r L) (fuse r M)
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

sub-id : SubId
sub-ids : ∀ {Γ Δ} {σ : Sub tmK Γ Γ}
  → (∀ {B} (x : Γ ∋ B) → σ x ≡ ` x)
  → (Ms : All (Tm Γ) Δ)
  → travs tmK σ Ms ≡ Ms
sub-id h (` x) = h x
sub-id h (lam N) = cong lam (sub-id (sub-id-exts h) N)
sub-id h (app L M) = cong₂ app (sub-id h L) (sub-id h M)
sub-id h (lit B c) = refl
sub-id h (tuple Ms) = cong tuple (sub-ids h Ms)
sub-id h (get i M) = cong (get i) (sub-id h M)
sub-id h (inl M) = cong inl (sub-id h M)
sub-id h (inr M) = cong inr (sub-id h M)
sub-id h (case L M N) rewrite sub-id h L | sub-id (sub-id-exts h) M | sub-id (sub-id-exts h) N = refl
sub-id h (prim p L M) = cong₂ (prim p) (sub-id h L) (sub-id h M)
sub-id h (let′ M N) = cong₂ let′ (sub-id h M) (sub-id (sub-id-exts h) N)
sub-id h (fold M) = cong fold (sub-id h M)
sub-id h (unfold M) = cong unfold (sub-id h M)
sub-ids h [] = refl
sub-ids h (M ∷ Ms) = cong₂ _∷_ (sub-id h M) (sub-ids h Ms)

open Lemmas fuse sub-id public

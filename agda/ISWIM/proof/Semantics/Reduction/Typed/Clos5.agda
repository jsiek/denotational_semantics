{-

  The values of the Clos5ᵀ reduction semantics
  (ISWIM/Semantics/Reduction/Typed/Clos5.agda), which reduce to val, and the
  laws of its substitution, as for ISWIMᵀ
  (ISWIM/proof/Semantics/Reduction/Typed/ISWIM.agda): the two by induction on
  its terms, that two traversals fuse into one (fuse) and that
  substitution by variables is the identity (sub-id), and from them the
  rest (proof/Framework/Syntax/TypedSubst.agda); in particular a
  substitution under a binder and then one for the bound variable is one
  substitution (exts-[]).

-}

module ISWIM.proof.Semantics.Reduction.Typed.Clos5 where

open import ISWIM.Semantics.Reduction.Typed.Clos5 public
open import ISWIM.Language.Typed.Type
open import ISWIM.Language.Typed.Clos5 hiding (wk; wks)
open import Semantics.Observation using (Obs; o-error)
open import proof.Framework.Reduction Obs o-error using (val)

open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All)
open import Data.Nat using (ℕ)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Vec.Relation.Unary.All using () renaming (All to Allᵥ; [] to []ᵥ; _∷_ to _∷ᵥ_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)

module _ {Σ : List ℕ} where

  {- Values -----------------------------------------------------------------}

  data Value {Γ} : ∀ {A} → Tm Σ Γ A → Set where
    fun-ref : ∀ {n} {f : Σ ∋ n} → Value (fun-ref f)
    pack : ∀ {n} {L : Tm Σ Γ (code n)} {M} → Value L → Value M → Value (pack L M)
    lit : ∀ {B c} → Value (lit B c)
    tuple : ∀ {n} {Vs : Vec (Tm Σ Γ Any) n} → Allᵥ Value Vs → Value (tuple Vs)
    inl : ∀ {V} → Value V → Value (inl V)
    inr : ∀ {V} → Value V → Value (inr V)
    inject : ∀ {G V} → Value V → Value (inject G V)

  value-red : ∀ {ds A} {V : Tm Σ [] A}
    → Value V
    → red ds V ≡ val
  values-red : ∀ {ds n} {Vs : Vec (Tm Σ [] Any) n}
    → Allᵥ Value Vs
    → reds ds Vs ≡ val
  value-red fun-ref = refl
  value-red {ds} (pack v w) rewrite value-red {ds} v | value-red {ds} w = refl
  value-red lit = refl
  value-red {ds} (tuple vs) rewrite values-red {ds} vs = refl
  value-red {ds} (inl v) rewrite value-red {ds} v = refl
  value-red {ds} (inr v) rewrite value-red {ds} v = refl
  value-red {ds} (inject v) rewrite value-red {ds} v = refl
  values-red []ᵥ = refl
  values-red {ds} (v ∷ᵥ vs) rewrite value-red {ds} v | values-red {ds} vs = refl

  {- Substitution: fusion and the identity, by induction on terms ----------}

  open import proof.Framework.Syntax.TypedSubst (Tm Σ) `_
  open Traversal trav (λ _ _ _ → refl) public

  module _ (𝒦₁ 𝒦₂ 𝒦₃ : Kit)
    (R : ∀ {Γ Δ Θ} → Sub 𝒦₁ Γ Δ → Sub 𝒦₂ Δ Θ → Sub 𝒦₃ Γ Θ → Set)
    (R-exts : ∀ {Γ Δ Θ B} {σ₁ : Sub 𝒦₁ Γ Δ} {σ₂ : Sub 𝒦₂ Δ Θ} {σ₃ : Sub 𝒦₃ Γ Θ} → R σ₁ σ₂ σ₃ → R (exts 𝒦₁ {B = B} σ₁) (exts 𝒦₂ σ₂) (exts 𝒦₃ σ₃))
    (R-var : ∀ {Γ Δ Θ} {σ₁ : Sub 𝒦₁ Γ Δ} {σ₂ : Sub 𝒦₂ Δ Θ} {σ₃ : Sub 𝒦₃ Γ Θ} → R σ₁ σ₂ σ₃ → ∀ {A} (x : Γ ∋ A)
      → trav 𝒦₂ σ₂ (Kit.tm 𝒦₁ (σ₁ x)) ≡ Kit.tm 𝒦₃ (σ₃ x)) where

    fuse : ∀ {Γ Δ Θ} {σ₁ : Sub 𝒦₁ Γ Δ} {σ₂ : Sub 𝒦₂ Δ Θ} {σ₃ : Sub 𝒦₃ Γ Θ}
      → R σ₁ σ₂ σ₃
      → ∀ {A} (M : Tm Σ Γ A)
      → trav 𝒦₂ σ₂ (trav 𝒦₁ σ₁ M) ≡ trav 𝒦₃ σ₃ M
    fuses : ∀ {Γ Δ Θ n} {σ₁ : Sub 𝒦₁ Γ Δ} {σ₂ : Sub 𝒦₂ Δ Θ} {σ₃ : Sub 𝒦₃ Γ Θ}
      → R σ₁ σ₂ σ₃
      → (Ms : Vec (Tm Σ Γ Any) n)
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
    fuse r (inject G M) = cong (inject G) (fuse r M)
    fuse r (project t M) = cong (project t) (fuse r M)
    fuses r [] = refl
    fuses r (M ∷ Ms) = cong₂ _∷_ (fuse r M) (fuses r Ms)

  sub-id : SubId
  sub-ids : ∀ {Γ n} {σ : Sub tmK Γ Γ}
    → (∀ {B} (x : Γ ∋ B) → σ x ≡ ` x)
    → (Ms : Vec (Tm Σ Γ Any) n)
    → travs tmK σ Ms ≡ Ms
  sub-id h (` x) = h x
  sub-id h (fun-ref f) = refl
  sub-id h (pack L M) = cong₂ pack (sub-id h L) (sub-id h M)
  sub-id h (callc L M) = cong₂ callc (sub-id h L) (sub-id h M)
  sub-id h (lit B c) = refl
  sub-id h (tuple Ms) = cong tuple (sub-ids h Ms)
  sub-id h (get i M) = cong (get i) (sub-id h M)
  sub-id h (inl M) = cong inl (sub-id h M)
  sub-id h (inr M) = cong inr (sub-id h M)
  sub-id h (case L M N) = case≡ (sub-id h L) (sub-id (sub-id-exts h) M) (sub-id (sub-id-exts h) N)
    where case≡ : ∀ {L L' M M' N N'} → L ≡ L' → M ≡ M' → N ≡ N' → case {Σ} {_} L M N ≡ case L' M' N'
          case≡ refl refl refl = refl
  sub-id h (prim p L M) = cong₂ (prim p) (sub-id h L) (sub-id h M)
  sub-id h (let′ M N) = cong₂ let′ (sub-id h M) (sub-id (sub-id-exts h) N)
  sub-id h (inject G M) = cong (inject G) (sub-id h M)
  sub-id h (project t M) = cong (project t) (sub-id h M)
  sub-ids h [] = refl
  sub-ids h (M ∷ Ms) = cong₂ _∷_ (sub-id h M) (sub-ids h Ms)

  open Lemmas fuse sub-id public

{-

  The values of the ISWIMμ reduction semantics
  (Mu/Semantics/Reduction/ISWIM.agda), which reduce to val, and the
  laws of its renaming and substitution, as for ISWIMᵀ
  (proof/Semantics/Reduction/Typed/ISWIM.agda): two traversals fuse
  into one (fuse), and substitution by variables is the identity
  (sub-id); in particular a substitution under a binder and then one
  for the bound variable is one substitution (exts-[]).

-}

module Mu.proof.Semantics.Reduction.ISWIM where

open import Mu.Semantics.Reduction.ISWIM public
open import Mu.Language.Type hiding (_[_])
open import Mu.Language.ISWIM
open import Mu.Framework.AllUtil using (All; []; _∷_)
open import Semantics.Observation using (Obs; o-error)
open import Mu.proof.Framework.ReductionAll Obs o-error using (Each; []; _∷_)
open import Semantics.Reduction.Smallstep using (val)

open import Data.List using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)

{- Values -------------------------------------------------------------------}

data Value {Γ} : ∀ {A} → Tm Γ A → Set where
  lam : ∀ {A B} {N : Tm (A ∷ Γ) B} → Value (lam N)
  lit : ∀ {B c} → Value (lit B c)
  tuple : ∀ {Δ} {Vs : All (Tm Γ) Δ} → Each Value Vs → Value (tuple Vs)
  inl : ∀ {A B} {V : Tm Γ A} → Value V → Value (inl {B = B} V)
  inr : ∀ {A B} {V : Tm Γ B} → Value V → Value (inr {A = A} V)
  fold : ∀ {A c} {V : Tm Γ (unroll A {c})} → Value V → Value (fold {A = A} {c} V)

value-red : ∀ {A} {V : Tm [] A} → Value V → red V ≡ val
values-red : ∀ {Δ} {Vs : All (Tm []) Δ} → Each Value Vs → reds Vs ≡ val
value-red lam = refl
value-red lit = refl
value-red (tuple vs) rewrite values-red vs = refl
value-red (inl v) rewrite value-red v = refl
value-red (inr v) rewrite value-red v = refl
value-red (fold v) rewrite value-red v = refl
values-red [] = refl
values-red (v ∷ vs) rewrite value-red v | values-red vs = refl

{- Fusion -------------------------------------------------------------------}

module _ (𝒦₁ 𝒦₂ 𝒦₃ : Kit)
  (R : ∀ {Γ Δ Θ} → Sub 𝒦₁ Γ Δ → Sub 𝒦₂ Δ Θ → Sub 𝒦₃ Γ Θ → Set)
  (R-exts : ∀ {Γ Δ Θ B} {σ₁ : Sub 𝒦₁ Γ Δ} {σ₂ : Sub 𝒦₂ Δ Θ} {σ₃ : Sub 𝒦₃ Γ Θ} → R σ₁ σ₂ σ₃ → R (exts 𝒦₁ {B = B} σ₁) (exts 𝒦₂ σ₂) (exts 𝒦₃ σ₃))
  (R-var : ∀ {Γ Δ Θ} {σ₁ : Sub 𝒦₁ Γ Δ} {σ₂ : Sub 𝒦₂ Δ Θ} {σ₃ : Sub 𝒦₃ Γ Θ} → R σ₁ σ₂ σ₃ → ∀ {A} (x : Γ ∋ A) → trav 𝒦₂ σ₂ (Kit.tm 𝒦₁ (σ₁ x)) ≡ Kit.tm 𝒦₃ (σ₃ x)) where

  fuse : ∀ {Γ Δ Θ} {σ₁ : Sub 𝒦₁ Γ Δ} {σ₂ : Sub 𝒦₂ Δ Θ} {σ₃ : Sub 𝒦₃ Γ Θ} → R σ₁ σ₂ σ₃ → ∀ {A} (M : Tm Γ A) → trav 𝒦₂ σ₂ (trav 𝒦₁ σ₁ M) ≡ trav 𝒦₃ σ₃ M
  fuses : ∀ {Γ Δ Θ Δ'} {σ₁ : Sub 𝒦₁ Γ Δ} {σ₂ : Sub 𝒦₂ Δ Θ} {σ₃ : Sub 𝒦₃ Γ Θ} → R σ₁ σ₂ σ₃ → (Ms : All (Tm Γ) Δ') → travs 𝒦₂ σ₂ (travs 𝒦₁ σ₁ Ms) ≡ travs 𝒦₃ σ₃ Ms
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

{- a renaming, then a traversal -}
ren-trav : ∀ 𝒦 {Γ Δ Θ} {r : ∀ {B} → Γ ∋ B → Δ ∋ B} {σ : Sub 𝒦 Δ Θ} {τ : Sub 𝒦 Γ Θ} → (∀ {B} (x : Γ ∋ B) → σ (r x) ≡ τ x)
  → ∀ {A} (M : Tm Γ A) → trav 𝒦 σ (ren r M) ≡ trav 𝒦 τ M
ren-trav 𝒦 = fuse varK 𝒦 𝒦 (λ r σ τ → ∀ {B} (x : _ ∋ B) → σ (r x) ≡ τ x)
  (λ { h Z → refl ; h (S x) → cong (Kit.wk 𝒦) (h x) }) (λ h x → cong (Kit.tm 𝒦) (h x))

{- a substitution, then a renaming -}
sub-ren : ∀ {Γ Δ Θ} {σ : ∀ {B} → Γ ∋ B → Tm Δ B} {r : ∀ {B} → Δ ∋ B → Θ ∋ B} {τ : ∀ {B} → Γ ∋ B → Tm Θ B}
  → (∀ {B} (x : Γ ∋ B) → ren r (σ x) ≡ τ x) → ∀ {A} (M : Tm Γ A) → ren r (sub σ M) ≡ sub τ M
sub-ren = fuse tmK varK tmK (λ σ r τ → ∀ {B} (x : _ ∋ B) → ren r (σ x) ≡ τ x)
  (λ { h Z → refl
     ; {σ₁ = σ} h (S x) → trans (ren-trav varK (λ _ → refl) (σ x))
                              (trans (sym (ren-trav varK (λ _ → refl) (σ x))) (cong (ren S) (h x))) })
  (λ h x → h x)

{- what both kits satisfy -}
record Laws (𝒦 : Kit) : Set where
  field
    tm-vr : ∀ {Γ A} (x : Γ ∋ A) → Kit.tm 𝒦 (Kit.vr 𝒦 x) ≡ ` x
    exts-ren : ∀ {Γ Δ A B} (τ : Sub 𝒦 Γ Δ) (M : Tm Γ A) → trav 𝒦 (exts 𝒦 {B = B} τ) (ren S M) ≡ ren S (trav 𝒦 τ M)

varL : Laws varK
varL = record { tm-vr = λ _ → refl
              ; exts-ren = λ τ M → trans (ren-trav varK (λ _ → refl) M) (sym (ren-trav varK (λ _ → refl) M)) }

tmL : Laws tmK
tmL = record { tm-vr = λ _ → refl
             ; exts-ren = λ τ M → trans (ren-trav tmK (λ _ → refl) M) (sym (sub-ren (λ _ → refl) M)) }

{- a substitution, then a traversal -}
trav-sub : ∀ {𝒦} → Laws 𝒦 → ∀ {Γ Δ Θ} {σ : ∀ {B} → Γ ∋ B → Tm Δ B} {τ : Sub 𝒦 Δ Θ} {ρ : ∀ {B} → Γ ∋ B → Tm Θ B}
  → (∀ {B} (x : Γ ∋ B) → trav 𝒦 τ (σ x) ≡ ρ x) → ∀ {A} (M : Tm Γ A) → trav 𝒦 τ (sub σ M) ≡ sub ρ M
trav-sub {𝒦} L = fuse tmK 𝒦 tmK (λ σ τ ρ → ∀ {B} (x : _ ∋ B) → trav 𝒦 τ (σ x) ≡ ρ x)
  (λ { h Z → Laws.tm-vr L Z ; {σ₁ = σ} {τ} h (S x) → trans (Laws.exts-ren L τ (σ x)) (cong (ren S) (h x)) })
  (λ h x → h x)

{- substituting variables for themselves -}
sub-id : ∀ {Γ A} {σ : ∀ {B} → Γ ∋ B → Tm Γ B} → (∀ {B} (x : Γ ∋ B) → σ x ≡ ` x) → (M : Tm Γ A) → sub σ M ≡ M
sub-ids : ∀ {Γ Δ} {σ : ∀ {B} → Γ ∋ B → Tm Γ B} → (∀ {B} (x : Γ ∋ B) → σ x ≡ ` x) → (Ms : All (Tm Γ) Δ) → travs tmK σ Ms ≡ Ms
sub-id-exts : ∀ {Γ C} {σ : ∀ {B} → Γ ∋ B → Tm Γ B} → (∀ {B} (x : Γ ∋ B) → σ x ≡ ` x) → ∀ {B} (x : (C ∷ Γ) ∋ B) → exts tmK σ x ≡ ` x
sub-id-exts h Z = refl
sub-id-exts h (S x) = cong (ren S) (h x)
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

{- a closed term, weakened and then substituted -}
wk-[] : ∀ {A C} (V : Tm [] A) (W : Tm [] C) → ren S V [ W ] ≡ V
wk-[] V W = trans (ren-trav tmK {τ = `_} (λ ()) V) (sub-id (λ ()) V)

{- under a binder, then for the bound variable: closed values for the rest -}
exts-[] : ∀ {Γ A C} (σ : ∀ {B} → Γ ∋ B → Tm [] B) (W : Tm [] C) (N : Tm (C ∷ Γ) A) → sub (exts tmK σ) N [ W ] ≡ sub (W • σ) N
exts-[] σ W = trav-sub tmL λ { Z → refl ; (S x) → wk-[] (σ x) W }

{- a traversal keeps values -}
value-trav : ∀ {𝒦 Γ Δ A} {σ : Sub 𝒦 Γ Δ} {V : Tm Γ A} → Value V → Value (trav 𝒦 σ V)
values-trav : ∀ {𝒦 Γ Δ Δ'} {σ : Sub 𝒦 Γ Δ} {Vs : All (Tm Γ) Δ'} → Each Value Vs → Each Value (travs 𝒦 σ Vs)
value-trav lam = lam
value-trav lit = lit
value-trav (tuple vs) = tuple (values-trav vs)
value-trav (inl v) = inl (value-trav v)
value-trav (inr v) = inr (value-trav v)
value-trav (fold v) = fold (value-trav v)
values-trav [] = []
values-trav (v ∷ vs) = value-trav v ∷ values-trav vs

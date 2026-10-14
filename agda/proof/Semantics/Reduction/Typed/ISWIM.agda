{-

  The values of the ISWIMᵀ reduction semantics
  (Semantics/Reduction/Typed/ISWIM.agda), which reduce to val, and the
  laws of its renaming and substitution: two traversals fuse into one
  (fuse, for any relation of the three maps that is kept under binders),
  and substitution by variables is the identity (sub-id); in particular
  a substitution under a binder and then one for the bound variable is
  one substitution (exts-[]).

-}

module proof.Semantics.Reduction.Typed.ISWIM where

open import Semantics.Reduction.Typed.ISWIM public
open import Language.Typed.Type
open import Language.Typed.ISWIM
open import Semantics.Observation using (Obs; o-error)
open import proof.Framework.Reduction Obs o-error using (val)

open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ; suc)
open import Data.Unit using (tt)
open import Data.Vec using (Vec; []; _∷_; lookup)
open import Data.Vec.Relation.Unary.All using (All; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)

{- Values -------------------------------------------------------------------}

data Value {k} : ∀ {A} → Tm k A → Set where
  lam : ∀ {N} → Value (lam N)
  lit : ∀ {B c} → Value (lit B c)
  tuple : ∀ {n} {Vs : Vec (Tm k Any) n} → All Value Vs → Value (tuple Vs)
  inl : ∀ {V} → Value V → Value (inl V)
  inr : ∀ {V} → Value V → Value (inr V)
  inject : ∀ {G V} → Value V → Value (inject G V)

value-red : ∀ {A} {V : Tm 0 A} → Value V → red V ≡ val
values-red : ∀ {n} {Vs : Vec (Tm 0 Any) n} → All Value Vs → reds Vs ≡ val
value-red lam = refl
value-red lit = refl
value-red (tuple vs) rewrite values-red vs = refl
value-red (inl v) rewrite value-red v = refl
value-red (inr v) rewrite value-red v = refl
value-red (inject v) rewrite value-red v = refl
values-red [] = refl
values-red (v ∷ vs) rewrite value-red v | values-red vs = refl

{- Fusion -------------------------------------------------------------------}

module _ (𝒦₁ 𝒦₂ 𝒦₃ : Kit)
  (R : ∀ {k j m} → Sub 𝒦₁ k j → Sub 𝒦₂ j m → Sub 𝒦₃ k m → Set)
  (R-exts : ∀ {k j m σ₁ σ₂ σ₃} → R {k} {j} {m} σ₁ σ₂ σ₃ → R (exts 𝒦₁ σ₁) (exts 𝒦₂ σ₂) (exts 𝒦₃ σ₃))
  (R-var : ∀ {k j m σ₁ σ₂ σ₃} → R {k} {j} {m} σ₁ σ₂ σ₃ → ∀ x → trav 𝒦₂ σ₂ (Kit.tm 𝒦₁ (σ₁ x)) ≡ Kit.tm 𝒦₃ (σ₃ x)) where

  fuse : ∀ {k j m σ₁ σ₂ σ₃} → R {k} {j} {m} σ₁ σ₂ σ₃ → ∀ {A} (M : Tm k A) → trav 𝒦₂ σ₂ (trav 𝒦₁ σ₁ M) ≡ trav 𝒦₃ σ₃ M
  fuses : ∀ {k j m n σ₁ σ₂ σ₃} → R {k} {j} {m} σ₁ σ₂ σ₃ → (Ms : Vec (Tm k Any) n) → travs 𝒦₂ σ₂ (travs 𝒦₁ σ₁ Ms) ≡ travs 𝒦₃ σ₃ Ms
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
  fuse r (inject G M) = cong (inject G) (fuse r M)
  fuse r (project t M) = cong (project t) (fuse r M)
  fuses r [] = refl
  fuses r (M ∷ Ms) = cong₂ _∷_ (fuse r M) (fuses r Ms)

{- a renaming, then a traversal -}
ren-trav : ∀ 𝒦 {k j m} {r : Fin k → Fin j} {σ : Sub 𝒦 j m} {τ : Sub 𝒦 k m} → (∀ x → σ (r x) ≡ τ x)
  → ∀ {A} (M : Tm k A) → trav 𝒦 σ (ren r M) ≡ trav 𝒦 τ M
ren-trav 𝒦 = fuse varK 𝒦 𝒦 (λ r σ τ → ∀ x → σ (r x) ≡ τ x)
  (λ { h zero → refl ; h (suc x) → cong (Kit.wk 𝒦) (h x) }) (λ h x → cong (Kit.tm 𝒦) (h x))

{- a substitution, then a renaming -}
sub-ren : ∀ {k j m} {σ : Fin k → Tm j Any} {r : Fin j → Fin m} {τ} → (∀ x → ren r (σ x) ≡ τ x)
  → ∀ {A} (M : Tm k A) → ren r (sub σ M) ≡ sub τ M
sub-ren = fuse tmK varK tmK (λ σ r τ → ∀ x → ren r (σ x) ≡ τ x)
  (λ { h zero → refl
     ; {σ₁ = σ} h (suc x) → trans (ren-trav varK (λ _ → refl) (σ x))
                              (trans (sym (ren-trav varK (λ _ → refl) (σ x))) (cong (ren suc) (h x))) })
  (λ h x → h x)

{- what both kits satisfy -}
record Laws (𝒦 : Kit) : Set where
  field
    tm-vr : ∀ {k} (x : Fin k) → Kit.tm 𝒦 (Kit.vr 𝒦 x) ≡ ` x
    exts-ren : ∀ {k j A} (τ : Sub 𝒦 k j) (M : Tm k A) → trav 𝒦 (exts 𝒦 τ) (ren suc M) ≡ ren suc (trav 𝒦 τ M)

varL : Laws varK
varL = record { tm-vr = λ _ → refl
              ; exts-ren = λ τ M → trans (ren-trav varK (λ _ → refl) M) (sym (ren-trav varK (λ _ → refl) M)) }

tmL : Laws tmK
tmL = record { tm-vr = λ _ → refl
             ; exts-ren = λ τ M → trans (ren-trav tmK (λ _ → refl) M) (sym (sub-ren (λ _ → refl) M)) }

{- a substitution, then a traversal -}
trav-sub : ∀ {𝒦} → Laws 𝒦 → ∀ {k j m} {σ : Fin k → Tm j Any} {τ : Sub 𝒦 j m} {ρ} → (∀ x → trav 𝒦 τ (σ x) ≡ ρ x)
  → ∀ {A} (M : Tm k A) → trav 𝒦 τ (sub σ M) ≡ sub ρ M
trav-sub {𝒦} L = fuse tmK 𝒦 tmK (λ σ τ ρ → ∀ x → trav 𝒦 τ (σ x) ≡ ρ x)
  (λ { h zero → Laws.tm-vr L zero ; {σ₁ = σ} {τ} h (suc x) → trans (Laws.exts-ren L τ (σ x)) (cong (ren suc) (h x)) })
  (λ h x → h x)

{- substituting variables for themselves -}
sub-id : ∀ {k A} {σ : Fin k → Tm k Any} → (∀ x → σ x ≡ ` x) → (M : Tm k A) → sub σ M ≡ M
sub-ids : ∀ {k n} {σ : Fin k → Tm k Any} → (∀ x → σ x ≡ ` x) → (Ms : Vec (Tm k Any) n) → subs σ Ms ≡ Ms
sub-id-exts : ∀ {k} {σ : Fin k → Tm k Any} → (∀ x → σ x ≡ ` x) → ∀ x → exts tmK σ x ≡ ` x
sub-id-exts h zero = refl
sub-id-exts h (suc x) = cong (ren suc) (h x)
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
sub-id h (inject G M) = cong (inject G) (sub-id h M)
sub-id h (project t M) = cong (project t) (sub-id h M)
sub-ids h [] = refl
sub-ids h (M ∷ Ms) = cong₂ _∷_ (sub-id h M) (sub-ids h Ms)

{- under a binder, then for the bound variable: closed values for the rest -}
exts-[] : ∀ {k A} (σ : Fin k → Tm 0 Any) W (N : Tm (suc k) A) → sub (exts tmK σ) N [ W ] ≡ sub (W • σ) N
exts-[] σ W = trav-sub tmL λ { zero → refl ; (suc x) → trans (ren-trav tmK {τ = `_} (λ ()) (σ x)) (sub-id (λ _ → refl) (σ x)) }

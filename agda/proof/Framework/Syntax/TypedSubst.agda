{-

  Laws of the substitution of intrinsically typed terms
  (Framework/Syntax/TypedSubst.agda), for a language's traversal trav,
  whose clause for a variable is trav-var. Two laws are by induction on
  the language's terms, so each language proves them: two traversals
  fuse into one (Fuse: for a relation between the two substitutions and
  the one that is kept under a binder and agrees on variables), and
  substituting variables for themselves is the identity (SubId); what
  the identity needs under a binder is here (sub-id-exts). From the two,
  Lemmas derives the rest: a renaming and then a traversal (ren-trav), a
  substitution and then a renaming (sub-ren), a traversal (trav-sub, for
  a kit with Laws, which both have) or a substitution (sub-sub), a
  closed term weakened and then substituted (wk-[]), and a substitution
  under a binder followed by one for the bound variable (exts-[]).

-}

open import Data.List using (List; []; _∷_)
open import Framework.Membership using (_∋_; Z; S)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

module proof.Framework.Syntax.TypedSubst {T : Set} (Tm : List T → T → Set) (`_ : ∀ {Γ A} → Γ ∋ A → Tm Γ A) where

open import Framework.Syntax.TypedSubst Tm `_

module Traversal (trav : (𝒦 : Kit) → ∀ {Γ Δ A} → Sub 𝒦 Γ Δ → Tm Γ A → Tm Δ A)
                 (trav-var : ∀ 𝒦 {Γ Δ A} (σ : Sub 𝒦 Γ Δ) (x : Γ ∋ A) → trav 𝒦 σ (` x) ≡ Kit.tm 𝒦 (σ x)) where

  open Substitution trav

  {- What a language proves by induction on its terms -----------------------}

  Fuse : Set₁
  Fuse = ∀ (𝒦₁ 𝒦₂ 𝒦₃ : Kit) (R : ∀ {Γ Δ Θ} → Sub 𝒦₁ Γ Δ → Sub 𝒦₂ Δ Θ → Sub 𝒦₃ Γ Θ → Set)
    → (∀ {Γ Δ Θ B} {σ₁ : Sub 𝒦₁ Γ Δ} {σ₂ : Sub 𝒦₂ Δ Θ} {σ₃ : Sub 𝒦₃ Γ Θ} → R σ₁ σ₂ σ₃ → R (exts 𝒦₁ {B = B} σ₁) (exts 𝒦₂ σ₂) (exts 𝒦₃ σ₃))
    → (∀ {Γ Δ Θ} {σ₁ : Sub 𝒦₁ Γ Δ} {σ₂ : Sub 𝒦₂ Δ Θ} {σ₃ : Sub 𝒦₃ Γ Θ} → R σ₁ σ₂ σ₃ → ∀ {A} (x : Γ ∋ A) → trav 𝒦₂ σ₂ (Kit.tm 𝒦₁ (σ₁ x)) ≡ Kit.tm 𝒦₃ (σ₃ x))
    → ∀ {Γ Δ Θ} {σ₁ : Sub 𝒦₁ Γ Δ} {σ₂ : Sub 𝒦₂ Δ Θ} {σ₃ : Sub 𝒦₃ Γ Θ} → R σ₁ σ₂ σ₃ → ∀ {A} (M : Tm Γ A) → trav 𝒦₂ σ₂ (trav 𝒦₁ σ₁ M) ≡ trav 𝒦₃ σ₃ M

  SubId : Set
  SubId = ∀ {Γ A} {σ : Sub tmK Γ Γ} → (∀ {B} (x : Γ ∋ B) → σ x ≡ ` x) → (M : Tm Γ A) → sub σ M ≡ M

  {- what the identity needs under a binder -}
  sub-id-exts : ∀ {Γ C} {σ : Sub tmK Γ Γ}
    → (∀ {B} (x : Γ ∋ B) → σ x ≡ ` x)
    → ∀ {B} (x : (C ∷ Γ) ∋ B)
    → exts tmK σ x ≡ ` x
  sub-id-exts h Z = refl
  sub-id-exts h (S x) = trans (cong (ren S) (h x)) (trav-var varK S x)

  {- what both kits satisfy -}
  record Laws (𝒦 : Kit) : Set where
    field
      tm-vr : ∀ {Γ A} (x : Γ ∋ A) → Kit.tm 𝒦 (Kit.vr 𝒦 x) ≡ ` x
      exts-ren : ∀ {Γ Δ A B} (τ : Sub 𝒦 Γ Δ) (M : Tm Γ A) → trav 𝒦 (exts 𝒦 {B = B} τ) (ren S M) ≡ ren S (trav 𝒦 τ M)

  {- The consequences --------------------------------------------------------}

  module Lemmas (fuse : Fuse) (sub-id : SubId) where

    {- a renaming, then a traversal -}
    ren-trav : ∀ 𝒦 {Γ Δ Θ} {r : ∀ {B} → Γ ∋ B → Δ ∋ B} {σ : Sub 𝒦 Δ Θ} {τ : Sub 𝒦 Γ Θ}
      → (∀ {B} (x : Γ ∋ B) → σ (r x) ≡ τ x)
      → ∀ {A} (M : Tm Γ A)
      → trav 𝒦 σ (ren r M) ≡ trav 𝒦 τ M
    ren-trav 𝒦 = fuse varK 𝒦 𝒦 (λ r σ τ → ∀ {B} (x : _ ∋ B) → σ (r x) ≡ τ x)
      (λ { h Z → refl ; h (S x) → cong (Kit.wk 𝒦) (h x) })
      (λ { {σ₁ = r} {σ} h x → trans (trav-var 𝒦 σ (r x)) (cong (Kit.tm 𝒦) (h x)) })

    {- a substitution, then a renaming -}
    sub-ren : ∀ {Γ Δ Θ} {σ : Sub tmK Γ Δ} {r : ∀ {B} → Δ ∋ B → Θ ∋ B} {τ : Sub tmK Γ Θ}
      → (∀ {B} (x : Γ ∋ B) → ren r (σ x) ≡ τ x)
      → ∀ {A} (M : Tm Γ A)
      → ren r (sub σ M) ≡ sub τ M
    sub-ren = fuse tmK varK tmK (λ σ r τ → ∀ {B} (x : _ ∋ B) → ren r (σ x) ≡ τ x)
      (λ { {σ₂ = r} h Z → trav-var varK (exts varK r) Z
         ; {σ₁ = σ} h (S x) → trans (ren-trav varK (λ _ → refl) (σ x))
                                  (trans (sym (ren-trav varK (λ _ → refl) (σ x))) (cong (ren S) (h x))) })
      (λ h x → h x)

    varL : Laws varK
    varL = record { tm-vr = λ _ → refl
                  ; exts-ren = λ τ M → trans (ren-trav varK (λ _ → refl) M) (sym (ren-trav varK (λ _ → refl) M)) }

    tmL : Laws tmK
    tmL = record { tm-vr = λ _ → refl
                 ; exts-ren = λ τ M → trans (ren-trav tmK (λ _ → refl) M) (sym (sub-ren (λ _ → refl) M)) }

    {- a substitution, then a traversal -}
    trav-sub : ∀ {𝒦}
      → Laws 𝒦
      → ∀ {Γ Δ Θ} {σ : Sub tmK Γ Δ} {τ : Sub 𝒦 Δ Θ} {ρ : Sub tmK Γ Θ}
      → (∀ {B} (x : Γ ∋ B) → trav 𝒦 τ (σ x) ≡ ρ x)
      → ∀ {A} (M : Tm Γ A)
      → trav 𝒦 τ (sub σ M) ≡ sub ρ M
    trav-sub {𝒦} L = fuse tmK 𝒦 tmK (λ σ τ ρ → ∀ {B} (x : _ ∋ B) → trav 𝒦 τ (σ x) ≡ ρ x)
      (λ { {σ₂ = τ} h Z → trans (trav-var 𝒦 (exts 𝒦 τ) Z) (Laws.tm-vr L Z)
         ; {σ₁ = σ} {τ} h (S x) → trans (Laws.exts-ren L τ (σ x)) (cong (ren S) (h x)) })
      (λ h x → h x)

    {- a substitution, then another -}
    sub-sub : ∀ {Γ Δ Θ} {σ : Sub tmK Γ Δ} {τ : Sub tmK Δ Θ} {ρ : Sub tmK Γ Θ}
      → (∀ {B} (x : Γ ∋ B) → sub τ (σ x) ≡ ρ x)
      → ∀ {A} (M : Tm Γ A)
      → sub τ (sub σ M) ≡ sub ρ M
    sub-sub = trav-sub tmL

    {- a closed term, weakened and then substituted -}
    wk-[] : ∀ {A C} (V : Tm [] A) (W : Tm [] C) → ren S V [ W ] ≡ V
    wk-[] V W = trans (ren-trav tmK {τ = `_} (λ ()) V) (sub-id (λ ()) V)

    {- under a binder, then for the bound variable: closed values for the rest -}
    exts-[] : ∀ {Γ A C} (σ : Sub tmK Γ []) (W : Tm [] C) (N : Tm (C ∷ Γ) A) → sub (exts tmK σ) N [ W ] ≡ sub (W • σ) N
    exts-[] σ W = sub-sub λ { Z → trav-var tmK (W • ∅) Z ; (S x) → wk-[] (σ x) W }

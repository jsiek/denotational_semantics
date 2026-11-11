{-

  The frame of the X86μ interpreter (FPC/Semantics/ClockedInterpreters/X86.agda)
  and the frame of the Scott-domain semantics of X86μ
  (FPC/Semantics/ScottDomains/X86.agda), for the soundness and adequacy
  proofs (X86Soundness.agda, X86LogRel.agda).

  The interpreter's frame (Slots) holds a value for each initialized
  slot, and the semantics' frame is an environment whose position idx x
  is slot x. The two are related on the initialized slots (Frames.FR,
  for a relation P between elements and values): position idx x of the
  environment is related to the value that slot x holds. A write to the
  same slot of both keeps them related (fr-write), and so does forgetting
  slots (fr-restrict); no slot of the empty frame is initialized
  (fr-empty).

-}

open import MLTT.Spartan hiding (inl; inr; cases; Type)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons

open import FPC.Language.Type using (Type; Ctx; _⇒_; _∋_; Z; S; idx)
open import FPC.Language.X86 using (Inits; _∈_;
  _⊕_; _⊆_) renaming (none to none-init)
open import FPC.Language.Frame using (∈-⊆)
open import FPC.Framework.AllUtil using ([]; _∷_)
open import FPC.Semantics.Slots using (Slots; []; _∷_; ∙_; read; write;
  restrict; empty)

open import Agda.Primitive using (Level)
open import Data.Bool using (true; false)
open import Data.Empty using (⊥; ⊥-elim-irr)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (_≟_)
open import Data.Product using (proj₁; proj₂)
open import Data.Unit using (tt)
open import Relation.Nullary using (Dec; yes; no)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_)

module FPC.proof.Adequacy.ScottDomains.X86Frame
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : propext 𝓤₀)
       where

open import Framework.Scott.Base pt fe using (⟨_⟩)
open import Framework.Scott.Domain pt fe pe using (𝔻)
open import Framework.Scott.Ops pt fe pe using (Env)
open import FPC.Semantics.ScottDomains.Ops pt fe pe using (write-same;
  write-other) renaming (write to writeᵈ)

{- Slots ----------------------------------------------------------------------}

{- no slot is initialized in none-init Δ (none Δ of Frame.agda) -}
none-∉ : ∀ {Δ A} (x : Δ ∋ A) → x ∈ none-init Δ → ⊥
none-∉ Z ()
none-∉ (S x) i = none-∉ x i

{- a slot initialized after a write to x, at another position, was
   initialized before -}
∈-⊕-other : ∀ {Δ A B} {I : Inits Δ} (x : Δ ∋ A) (y : Δ ∋ B)
  → y ∈ I ⊕ x
  → idx x ≢ idx y
  → y ∈ I
∈-⊕-other {I = b ∷ I} Z Z i ne = Data.Empty.⊥-elim (ne Eq.refl)
∈-⊕-other {I = b ∷ I} Z (S y) i ne = i
∈-⊕-other {I = b ∷ I} (S x) Z i ne = i
∈-⊕-other {I = b ∷ I} (S x) (S y) i ne =
  ∈-⊕-other {I = I} x y i (λ e → ne (Eq.cong Data.Nat.suc e))

module _ {V : Type → Set} where

  {- a read at the position of the slot written finds the value written -}
  read-write-≡ : ∀ {ℓ : Level} (Q : ∀ {C} → V C → Set ℓ) {Δ I A B}
    (φ : Slots V Δ I) (x : Δ ∋ A) (y : Δ ∋ B) (v : V A)
    → .(i : y ∈ I ⊕ x)
    → idx x ≡ idx y
    → Q v
    → Q (read (write φ x v) y i)
  read-write-≡ Q (u ∷ φ) Z Z v i e q = q
  read-write-≡ Q (∙ φ) Z Z v i e q = q
  read-write-≡ Q (u ∷ φ) (S x) (S y) v i e q =
    read-write-≡ Q φ x y v i (Eq.cong Data.Nat.pred e) q
  read-write-≡ Q (∙ φ) (S x) (S y) v i e q =
    read-write-≡ Q φ x y v i (Eq.cong Data.Nat.pred e) q

  {- a read at another position finds the old value -}
  read-write-≢ : ∀ {Δ I A B} (φ : Slots V Δ I) (x : Δ ∋ A) (y : Δ ∋ B)
    (v : V A)
    → .(yi : y ∈ I)
    → .(i : y ∈ I ⊕ x)
    → idx x ≢ idx y
    → read (write φ x v) y i ≡ read φ y yi
  read-write-≢ (u ∷ φ) Z Z v yi i ne = Data.Empty.⊥-elim (ne Eq.refl)
  read-write-≢ (∙ φ) Z Z v yi i ne = Data.Empty.⊥-elim (ne Eq.refl)
  read-write-≢ (u ∷ φ) Z (S y) v yi i ne = Eq.refl
  read-write-≢ (∙ φ) Z (S y) v yi i ne = Eq.refl
  read-write-≢ (u ∷ φ) (S x) Z v yi i ne = Eq.refl
  read-write-≢ (∙ φ) (S x) Z v yi i ne = ⊥-elim-irr yi
  read-write-≢ (u ∷ φ) (S x) (S y) v yi i ne =
    read-write-≢ φ x y v yi i (λ e → ne (Eq.cong Data.Nat.suc e))
  read-write-≢ (∙ φ) (S x) (S y) v yi i ne =
    read-write-≢ φ x y v yi i (λ e → ne (Eq.cong Data.Nat.suc e))

  {- a read of a frame whose other slots are forgotten -}
  read-restrict : ∀ {Δ} {I J : Inits Δ} {A} (φ : Slots V Δ I) .(p : J ⊆ I)
    (y : Δ ∋ A)
    → .(j : y ∈ J)
    → read (restrict p φ) y j ≡ read φ y (∈-⊆ y j p)
  read-restrict {J = true ∷ J} (v ∷ φ) p Z j = Eq.refl
  read-restrict {J = true ∷ J} (∙ φ) p Z j = ⊥-elim-irr (proj₁ p tt)
  read-restrict {J = false ∷ J} φ p Z j = ⊥-elim-irr j
  read-restrict {J = true ∷ J} (v ∷ φ) p (S y) j =
    read-restrict φ (proj₂ p) y j
  read-restrict {J = true ∷ J} (∙ φ) p (S y) j = ⊥-elim-irr (proj₁ p tt)
  read-restrict {J = false ∷ J} (v ∷ φ) p (S y) j =
    read-restrict φ (proj₂ p) y j
  read-restrict {J = false ∷ J} (∙ φ) p (S y) j =
    read-restrict φ (proj₂ p) y j

{- Related frames -------------------------------------------------------------}

module Frames {V : Type → Set} (P : ∀ {A} → ⟨ 𝔻 ⟩ → V A → 𝓤₁ ̇) where

  {- the environment σ and the frame φ are related on the initialized
     slots -}
  record FR {Δ} {I : Inits Δ} (σ : ⟨ Env ⟩) (φ : Slots V Δ I) : 𝓤₁ ̇ where
    constructor mk-fr
    field
      slot-at : ∀ {A} (x : Δ ∋ A) → .(i : x ∈ I) → P (σ (idx x)) (read φ x i)
  open FR public

  fr-write : ∀ {Δ} {I : Inits Δ} {A} {σ : ⟨ Env ⟩} {φ : Slots V Δ I}
    (x : Δ ∋ A) {D : ⟨ 𝔻 ⟩} {v : V A}
    → P D v
    → FR σ φ
    → FR (writeᵈ (idx x) σ D) (write φ x v)
  fr-write {I = I} {σ = σ} {φ} x {D} {v} r h =
    mk-fr λ y i → go y i (idx x ≟ idx y)
   where
    go : ∀ {B} (y : _ ∋ B) .(i : y ∈ I ⊕ x) → Dec (idx x ≡ idx y)
      → P (writeᵈ (idx x) σ D (idx y)) (read (write φ x v) y i)
    go y i (yes e) =
      transport (λ - → P - (read (write φ x v) y i))
        (Eq.subst (λ j → writeᵈ (idx x) σ D j ＝ D) e
          (write-same (idx x) σ D) ⁻¹)
        (read-write-≡ (P D) φ x y v i e r)
    go y i (no ne) =
      transport (λ - → P - (read (write φ x v) y i))
        (write-other (idx x) (idx y) σ D ne ⁻¹)
        (Eq.subst (P (σ (idx y)))
          (Eq.sym (read-write-≢ φ x y v (∈-⊕-other {I = I} x y i ne) i ne))
          (slot-at h y (∈-⊕-other {I = I} x y i ne)))

  fr-restrict : ∀ {Δ} {I J : Inits Δ} {σ : ⟨ Env ⟩} {φ : Slots V Δ I}
    .(p : J ⊆ I)
    → FR σ φ
    → FR σ (restrict p φ)
  fr-restrict {σ = σ} {φ} p h = mk-fr λ y j →
    Eq.subst (P (σ (idx y))) (Eq.sym (read-restrict φ p y j))
      (slot-at h y (∈-⊆ y j p))

  fr-empty : ∀ {Δ} {σ : ⟨ Env ⟩} → FR σ (empty Δ)
  fr-empty = mk-fr λ y i → ⊥-elim-irr (none-∉ y i)

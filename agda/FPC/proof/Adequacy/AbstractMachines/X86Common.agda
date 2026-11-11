{-

  Definitions shared by the soundness and adequacy proofs for the X86μ
  machine (see FPC/proof/Adequacy/AbstractMachines/X86.agda), as for X86ᵀ
  (ISWIM/proof/Adequacy/X86Common.agda): runs of the machine of the
  definitions ds from any state, the state that a call of code c starts
  in (start), on any stack of its result type, and how the open
  closure is related to its slot (OpR): the machine keeps the types η
  of its environment and the environment, which are those of the
  closure in the slot, and that slot is initialized.

  The frame is fixed (FPC/Semantics/Slots.agda), and a write may
  overwrite an initialized slot. Two slots are the same or at different
  positions (slot-eq?); a read of a slot other than the one written
  finds the old value (read-write-at), and a read after a restriction
  finds the value before it (read-restrict).

-}

open import Data.List using (List)
open import FPC.Language.X86
open import FPC.Framework.AllUtil using (All)

module FPC.proof.Adequacy.AbstractMachines.X86Common {Σ : List DSig}
  (ds : All (λ s → Body Σ (DSig.cod s) (called s)) Σ) where

open import FPC.Language.Type
open import FPC.Semantics.AbstractMachines.X86
open import proof.Semantics.CEK.Smallstep using (next)
open import proof.Framework.Runs using (module Runs)
open import FPC.Framework.AllUtil using (lookup; _∷_)
open import FPC.Language.Frame using (∈-⊆)
open import FPC.Semantics.Slots using (Slots; read; write; restrict; empty;
  _∷_; ∙_)

open import Data.Bool using (true; false)
open import Data.Empty using (⊥)
open import Data.Empty.Irrelevant using (⊥-elim)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (suc)
open import Data.Nat.Properties using (suc-injective)
open import Data.Product using (proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong)

open Runs (step ds) public

{- Frames ---------------------------------------------------------------------}

{- y is the slot x -}
data Same {Δ : Ctx} {A : Type} (x : Δ ∋ A) : ∀ {B} → Δ ∋ B → Set where
  same : Same x x

{- two slots are the same, or at different positions -}
slot-eq? : ∀ {Δ : Ctx} {A B : Type} (x : Δ ∋ A) (y : Δ ∋ B)
  → Same x y ⊎ idx x ≢ idx y
slot-eq? Z Z = inj₁ same
slot-eq? Z (S y) = inj₂ (λ ())
slot-eq? (S x) Z = inj₂ (λ ())
slot-eq? (S x) (S y) with slot-eq? x y
... | inj₁ same = inj₁ same
... | inj₂ n = inj₂ (λ e → n (suc-injective {idx x} {idx y} e))

{- a slot other than x, initialized after a write to x, was before -}
∈-⊕-other : ∀ {Δ A B} {I : Inits Δ} (x : Δ ∋ A) (y : Δ ∋ B)
  → y ∈ I ⊕ x
  → idx x ≢ idx y
  → y ∈ I
∈-⊕-other {I = b ∷ I} Z Z j n = ⊥-elim (n refl)
∈-⊕-other {I = b ∷ I} Z (S y) j n = j
∈-⊕-other {I = b ∷ I} (S x) Z j n = j
∈-⊕-other {I = b ∷ I} (S x) (S y) j n =
  ∈-⊕-other {I = I} x y j (λ e → n (cong suc e))

module _ {V : Type → Set} where

  {- a read of another slot after a write, initialized or not -}
  read-write-at : ∀ {Δ I A B} (φ : Slots V Δ I) (x : Δ ∋ A) (v : V A)
    (y : Δ ∋ B)
    → .(yi : y ∈ I)
    → .(j : y ∈ I ⊕ x)
    → idx x ≢ idx y
    → read (write φ x v) y j ≡ read φ y yi
  read-write-at (u ∷ φ) Z v Z yi j n = ⊥-elim (n refl)
  read-write-at (∙ φ) Z v Z yi j n = ⊥-elim (n refl)
  read-write-at (u ∷ φ) Z v (S y) yi j n = refl
  read-write-at (∙ φ) Z v (S y) yi j n = refl
  read-write-at (u ∷ φ) (S x) v Z yi j n = refl
  read-write-at (∙ φ) (S x) v Z yi j n = ⊥-elim yi
  read-write-at (u ∷ φ) (S x) v (S y) yi j n =
    read-write-at φ x v y yi j (λ e → n (cong suc e))
  read-write-at (∙ φ) (S x) v (S y) yi j n =
    read-write-at φ x v y yi j (λ e → n (cong suc e))

  {- a read after a restriction -}
  read-restrict : ∀ {Δ} {I J : Inits Δ} {B} (φ : Slots V Δ I) .(p : J ⊆ I)
    (y : Δ ∋ B) .(j : y ∈ J)
    → read (restrict p φ) y j ≡ read φ y (∈-⊆ y j p)
  read-restrict {J = true ∷ J} (v ∷ φ) p Z j = refl
  read-restrict {J = true ∷ J} (∙ φ) p Z j = ⊥-elim (proj₁ p tt)
  read-restrict {J = false ∷ J} φ p Z j = ⊥-elim j
  read-restrict {J = true ∷ J} (v ∷ φ) p (S y) j =
    read-restrict φ (proj₂ p) y j
  read-restrict {J = true ∷ J} (∙ φ) p (S y) j = ⊥-elim (proj₁ p tt)
  read-restrict {J = false ∷ J} (v ∷ φ) p (S y) j =
    read-restrict φ (proj₂ p) y j
  read-restrict {J = false ∷ J} (∙ φ) p (S y) j =
    read-restrict φ (proj₂ p) y j

{- no slot is initialized in the empty frame -}
∉none : ∀ {Δ B} (y : Δ ∋ B) → y ∈ none Δ → ⊥
∉none Z ()
∉none (S y) j = ∉none y j

{- running code c on the environment e and the argument a -}
start : ∀ {η A B} → Val Σ (code η A B) → Val Σ (tup η) → Val Σ A
  → Stack Σ B → State Σ
start {η} (code f) e a σ =
  run (Body.start (lookup ds f)) (Body.blocks (lookup ds f)) σ η
    ⟨ rv tt e a , empty (Body.frame (lookup ds f)) , tt , tt ⟩

enter-start : ∀ {η A B} (c : Val Σ (code η A B)) {e a σ}
  → enter ds c e a σ ≡ next (start c e a σ)
enter-start (code f) = refl

{- the open closure is that of its slot, which is initialized: η and the
   environment are its own -}
data OpR {Δ I} (φ : Frame Σ Δ I) : (O : Maybe (Open Δ)) (η : Ctx)
  → Opened Σ η O → Set where
  unopened : ∀ {η} → OpR φ nothing η tt
  agree : ∀ {A B} {x : Δ ∋ A ⇒ B}
    → .(i : x ∈ I)
    → OpR φ (just (opened x)) (size (read φ x i)) (env-of (read φ x i))

{-

  The values of a fixed frame (FPC/Framework/Slots.agda) against the
  frames of the graph model (Env Value, FPC/Semantics/GraphModel/Ops.agda),
  for the adequacy and soundness proofs of the X86μ interpreter
  (X86LogRel.agda, X86Soundness.agda).

  * A read after a restriction reads the frame before it
    (read-restrict), and a read after a write to a slot at another
    position reads the frame before the write (read-write-ne). Two slots
    at the same position are the same slot (idx-same).
  * The adequacy relation of frames (Fr R I ρ φ) relates the meaning of
    each initialized slot in ρ to its value in φ, and says nothing of
    the other slots. A write to slot x, on both sides, and then a
    restriction keep it (fr-put).
  * The meaning of a frame of values, slot by slot (𝓢 𝒱 φ), is the
    meaning 𝒱 v of the value v of an initialized slot, and nothing (∅)
    for the other slots, as in an empty frame (𝓢-empty). A read finds
    a part of it (𝓢-read); a restriction only forgets slots
    (𝓢-restrict); after a write to x, slot x means a part of the value
    written (𝓢-write-same), and the other slots mean what they meant
    before (𝓢-write-other).

-}

module FPC.proof.Adequacy.X86Slots where

open import proof.Framework.GraphModel.SetsAsPredicates using (𝒫; ∅)
  renaming (_∈_ to _∈ₛ_; _⊆_ to _⊆ₛ_)
open import proof.Framework.GraphModel.Domain using (Value)
open import proof.Framework.GraphModel.Env using (Env)
open import FPC.Semantics.GraphModel.Ops using (_[_≔_])
open import FPC.Language.Type
open import FPC.Language.Frame
open import FPC.Framework.AllUtil using ([]; _∷_)
open import FPC.Framework.Slots
open import FPC.proof.Semantics.GraphModel.CFG using (∈-⊕⁻)

open import Data.Bool using (true; false)
open import Data.List using ([]; _∷_)
open import Data.Empty using (⊥-elim)
open import Data.Empty.Irrelevant using () renaming (⊥-elim to ⊥-elimᵢ)
open import Data.Nat using (ℕ; zero; suc; _≟_)
open import Data.Nat.Properties using (suc-injective)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong;
  subst)
open import Relation.Nullary using (yes; no)

{- two slots at the same position are the same slot -}
data Same {Δ : Ctx} {A} (x : Δ ∋ A) : ∀ {B} → Δ ∋ B → Set where
  same : Same x x

idx-same : ∀ {Δ A B} (x : Δ ∋ A) (z : Δ ∋ B)
  → idx x ≡ idx z
  → Same x z
idx-same Z Z e = same
idx-same Z (S z) ()
idx-same (S x) Z ()
idx-same (S x) (S z) e with idx-same x z (suc-injective e)
... | same = same

module _ {V : Type → Set} where

  read-restrict : ∀ {Δ B} {I J : Inits Δ} (φ : Slots V Δ I) .(p : J ⊆ I)
    (z : Δ ∋ B)
    → .(j : z ∈ J)
    → read (restrict p φ) z j ≡ read φ z (∈-⊆ {I = I} {J} z j p)
  read-restrict {J = true ∷ J} (v ∷ φ) p Z j = refl
  read-restrict {J = false ∷ J} (v ∷ φ) p Z ()
  read-restrict {J = false ∷ J} (∙ φ) p Z ()
  read-restrict {J = true ∷ J} (∙ φ) p Z j = ⊥-elim′ (proj₁ p j)
    where
    open import Data.Empty.Irrelevant renaming (⊥-elim to ⊥-elim′)
  read-restrict {J = true ∷ J} (v ∷ φ) p (S z) j =
    read-restrict φ (proj₂ p) z j
  read-restrict {J = true ∷ J} (∙ φ) p (S z) j =
    ⊥-elim′ (proj₁ p tt′)
    where
    open import Data.Empty.Irrelevant renaming (⊥-elim to ⊥-elim′)
    open import Data.Unit renaming (tt to tt′)
  read-restrict {J = false ∷ J} (v ∷ φ) p (S z) j =
    read-restrict φ (proj₂ p) z j
  read-restrict {J = false ∷ J} (∙ φ) p (S z) j =
    read-restrict φ (proj₂ p) z j

  {- a read of slot z after a write to a slot x at another position -}
  read-write-ne : ∀ {Δ A B} {I : Inits Δ} (φ : Slots V Δ I) (x : Δ ∋ A)
    (v : V A) (z : Δ ∋ B)
    → (n : idx x ≢ idx z)
    → .(i : z ∈ I ⊕ x)
    → read (write φ x v) z i ≡ read φ z (∈-⊕⁻ {I = I} x z i n)
  read-write-ne (u ∷ φ) Z v Z n i = ⊥-elim (n refl)
  read-write-ne (∙ φ) Z v Z n i = ⊥-elim (n refl)
  read-write-ne (u ∷ φ) Z v (S z) n i = refl
  read-write-ne (∙ φ) Z v (S z) n i = refl
  read-write-ne (u ∷ φ) (S x) v Z n i = refl
  read-write-ne (∙ φ) (S x) v Z n i = ⊥-elimᵢ i
  read-write-ne (u ∷ φ) (S x) v (S z) n i =
    read-write-ne φ x v z (λ e → n (cong suc e)) i
  read-write-ne (∙ φ) (S x) v (S z) n i =
    read-write-ne φ x v z (λ e → n (cong suc e)) i

  {- The adequacy relation of frames --------------------------------------}

  Fr : (∀ {A} → Value → V A → Set) → ∀ {Δ} (I : Inits Δ) → Env Value
    → Slots V Δ I → Set
  Fr R {Δ} I ρ φ =
    ∀ {A} (x : Δ ∋ A) .(i : x ∈ I) d → d ∈ₛ ρ (idx x) → R d (read φ x i)

  fr-restrict : ∀ {R : ∀ {A} → Value → V A → Set} {Δ} {I J : Inits Δ} {ρ}
    {φ : Slots V Δ I} .(p : J ⊆ I)
    → Fr R I ρ φ
    → Fr R J ρ (restrict p φ)
  fr-restrict {R = R} {φ = φ} p F x j d d∈ =
    subst (R d) (sym′ (read-restrict φ p x j)) (F x _ d d∈)
    where
    sym′ : ∀ {A} {a b : V A} → a ≡ b → b ≡ a
    sym′ refl = refl

  fr-write : ∀ {R : ∀ {A} → Value → V A → Set} {Δ A} {I : Inits Δ} {ρ}
    {φ : Slots V Δ I} (x : Δ ∋ A) {X v}
    → Fr R I ρ φ
    → (∀ d → d ∈ₛ X → R d v)
    → Fr R (I ⊕ x) (ρ [ idx x ≔ X ]) (write φ x v)
  fr-write {R = R} {φ = φ} x {X} {v} F h z i d d∈ with idx x ≟ idx z
  ... | yes e with idx-same x z e
  ...   | same = subst (R d) (sym′ (read-write φ x v i)) (h d d∈)
    where
    open import FPC.proof.Framework.SlotsProp using (read-write)
    sym′ : ∀ {A} {a b : V A} → a ≡ b → b ≡ a
    sym′ refl = refl
  fr-write {R = R} {φ = φ} x {X} {v} F h z i d d∈ | no n =
    subst (R d) (sym′ (read-write-ne φ x v z n i)) (F z _ d d∈)
    where
    sym′ : ∀ {A} {a b : V A} → a ≡ b → b ≡ a
    sym′ refl = refl

  {- a slot write: x := X, then a restriction to J -}
  fr-put : ∀ {R : ∀ {A} → Value → V A → Set} {Δ A} {I J : Inits Δ} {ρ}
    {φ : Slots V Δ I} (x : Δ ∋ A) .(p : J ⊆ I ⊕ x) {X v}
    → Fr R I ρ φ
    → (∀ d → d ∈ₛ X → R d v)
    → Fr R J (ρ [ idx x ≔ X ]) (restrict p (write φ x v))
  fr-put {R = R} {I = I} {ρ = ρ} {φ} x p {X} {v} F h =
    fr-restrict {R = R} {I = I ⊕ x} {ρ = ρ [ idx x ≔ X ]} {write φ x v} p
      (fr-write {R = R} {I = I} {ρ} {φ} x {X} {v} F h)

  {- The meaning of a frame of values -------------------------------------}

  module _ (𝒱 : ∀ {A} → V A → 𝒫 Value) where

    𝓢 : ∀ {Δ} {I : Inits Δ} → Slots V Δ I → ℕ → 𝒫 Value
    𝓢 [] i = ∅
    𝓢 (v ∷ φ) zero = 𝒱 v
    𝓢 (∙ φ) zero = ∅
    𝓢 (v ∷ φ) (suc i) = 𝓢 φ i
    𝓢 (∙ φ) (suc i) = 𝓢 φ i

    𝓢-empty : ∀ Δ j
      → 𝓢 (empty {V = V} Δ) j ⊆ₛ ∅
    𝓢-empty [] j = λ d z → z
    𝓢-empty (A ∷ Δ) zero = λ d z → z
    𝓢-empty (A ∷ Δ) (suc j) = 𝓢-empty Δ j

    𝓢-read : ∀ {Δ A} {I : Inits Δ} (φ : Slots V Δ I) (x : Δ ∋ A)
      → .(i : x ∈ I)
      → 𝒱 (read φ x i) ⊆ₛ 𝓢 φ (idx x)
    𝓢-read (v ∷ φ) Z i = λ d z → z
    𝓢-read (∙ φ) Z ()
    𝓢-read (v ∷ φ) (S x) i = 𝓢-read φ x i
    𝓢-read (∙ φ) (S x) i = 𝓢-read φ x i

    𝓢-restrict : ∀ {Δ} {I J : Inits Δ} (φ : Slots V Δ I) .(p : J ⊆ I) j
      → 𝓢 (restrict p φ) j ⊆ₛ 𝓢 φ j
    𝓢-restrict {J = []} [] p j = λ d z → z
    𝓢-restrict {J = true ∷ J} (v ∷ φ) p zero = λ d z → z
    𝓢-restrict {J = true ∷ J} (v ∷ φ) p (suc j) = 𝓢-restrict φ (proj₂ p) j
    𝓢-restrict {J = true ∷ J} (∙ φ) p j = λ d z → ⊥-elim′ (proj₁ p tt′)
      where
      open import Data.Empty.Irrelevant renaming (⊥-elim to ⊥-elim′)
      open import Data.Unit renaming (tt to tt′)
    𝓢-restrict {J = false ∷ J} (v ∷ φ) p zero = λ d ()
    𝓢-restrict {J = false ∷ J} (v ∷ φ) p (suc j) = 𝓢-restrict φ (proj₂ p) j
    𝓢-restrict {J = false ∷ J} (∙ φ) p zero = λ d ()
    𝓢-restrict {J = false ∷ J} (∙ φ) p (suc j) = 𝓢-restrict φ (proj₂ p) j

    𝓢-write-same : ∀ {Δ A} {I : Inits Δ} (φ : Slots V Δ I) (x : Δ ∋ A)
      (v : V A)
      → 𝓢 (write φ x v) (idx x) ⊆ₛ 𝒱 v
    𝓢-write-same (u ∷ φ) Z v = λ d z → z
    𝓢-write-same (∙ φ) Z v = λ d z → z
    𝓢-write-same (u ∷ φ) (S x) v = 𝓢-write-same φ x v
    𝓢-write-same (∙ φ) (S x) v = 𝓢-write-same φ x v

    𝓢-write-other : ∀ {Δ A} {I : Inits Δ} (φ : Slots V Δ I) (x : Δ ∋ A)
      (v : V A) j
      → j ≢ idx x
      → 𝓢 (write φ x v) j ⊆ₛ 𝓢 φ j
    𝓢-write-other (u ∷ φ) Z v zero n = ⊥-elim (n refl)
    𝓢-write-other (∙ φ) Z v zero n = ⊥-elim (n refl)
    𝓢-write-other (u ∷ φ) Z v (suc j) n = λ d z → z
    𝓢-write-other (∙ φ) Z v (suc j) n = λ d z → z
    𝓢-write-other (u ∷ φ) (S x) v zero n = λ d z → z
    𝓢-write-other (∙ φ) (S x) v zero n = λ d z → z
    𝓢-write-other (u ∷ φ) (S x) v (suc j) n =
      𝓢-write-other φ x v j (λ e → n (cong suc e))
    𝓢-write-other (∙ φ) (S x) v (suc j) n =
      𝓢-write-other φ x v j (λ e → n (cong suc e))

{- a frame below another at each position but i, and below X at i, is
   below the other with X at i -}
≔-⊆ : ∀ {σ σ' : Env Value} {X} i
  → (∀ j → j ≢ i → σ j ⊆ₛ σ' j)
  → σ i ⊆ₛ X
  → ∀ j
  → σ j ⊆ₛ (σ' [ i ≔ X ]) j
≔-⊆ i h hi j with i ≟ j
... | yes refl = hi
... | no n = h j (λ e → n (sym′ e))
  where
  sym′ : ∀ {a b : ℕ} → a ≡ b → b ≡ a
  sym′ refl = refl

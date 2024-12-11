{-# OPTIONS --rewriting #-}

module RecSTLC where

open import Data.List using (List; []; _∷_; length)
open import Data.Nat
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.Product using (_,_;_×_; proj₁; proj₂; Σ-syntax; ∃-syntax)
-- open import Data.Unit using (⊤; tt)
-- open import Data.Unit.Polymorphic renaming (⊤ to topᵖ; tt to ttᵖ)
-- open import Data.Vec using (Vec) renaming ([] to []̌; _∷_ to _∷̌_)
open import Data.Empty using (⊥; ⊥-elim)
-- open import Data.Sum using (_⊎_; inj₁; inj₂)
-- open import Induction using (RecStruct)
-- open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality as Eq
  using (_≡_; _≢_; refl; sym; cong; cong₂; subst; trans)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Sig
open import Var
open import StepIndexedLogic
open import EquivalenceRelation public

data Type : Set where
  `ℕ  : Type
  _⇒_ : Type → Type → Type

data Op : Set where
  op-lam : Op
  op-app : Op
  op-zero : Op
  op-suc : Op
  op-case : Op
  op-rec : Op

sig : Op → List Sig
sig op-lam = (ν ■) ∷ []
sig op-app = ■ ∷ ■ ∷ []
sig op-zero = []
sig op-suc = ■ ∷ []
sig op-case = ■ ∷ ■ ∷ (ν ■) ∷ []
sig op-rec = (ν ■) ∷ []

open import rewriting.AbstractBindingTree Op sig renaming (ABT to Term) public

variable L L′ M M′ N N′ V V′ W W′ : Term

pattern ƛ N  = op-lam ⦅ cons (bind (ast N)) nil ⦆

infixl 7  _·_
pattern _·_ L M = op-app ⦅ cons (ast L) (cons (ast M) nil) ⦆

pattern `zero = op-zero ⦅ nil ⦆
pattern `suc M = op-suc ⦅ cons (ast M) nil ⦆

pattern case L M N = op-case ⦅ cons (ast L) (cons (ast M) (cons (bind (ast N)) nil)) ⦆

pattern μ N = op-rec ⦅ cons (bind (ast N)) nil ⦆

data Value : Term → Set where
  V-ƛ : Value (ƛ N)
  V-zero : Value `zero
  V-suc : Value V → Value (`suc V)
  V-μ : Value V → Value (μ V)

value : Value V → Term
value {V} v = V

Value-μ-inv : Value (μ V) → Value V
Value-μ-inv (V-μ v) = v

subst-preserves-value : ∀ σ V → Value V → Value (⟪ σ ⟫ V)
subst-preserves-value σ .(ƛ _) V-ƛ = V-ƛ
subst-preserves-value σ .`zero V-zero = V-zero
subst-preserves-value σ (`suc V) (V-suc v) = V-suc (subst-preserves-value σ V v)
subst-preserves-value σ (μ V) (V-μ v) = V-μ (subst-preserves-value (ext σ) V v)

infix  6 □·_
infix  6 _·□

data Frame : Set where
  □·_ : Term → Frame
  _·□ : Value V → Frame
  suc□ : Frame
  case□ : Term → Term → Frame

plug : Frame → Term → Term
plug (□· M) L        =  L · M
plug (v ·□) M        =  value v · M
plug suc□ M          = `suc M
plug (case□ M N) L   = case L M N

infix 2 _—→_
data _—→_ : Term → Term → Set where
  β-ƛ : Value W → (ƛ N) · W —→ N [ W ]
  β-zero : case `zero M N —→ M
  β-suc : Value V → case (`suc V) M N —→ N [ V ]
  β-μ : Value V → Value W → (μ V) · W —→ V [ μ V ] · W
  ξξ : (F : Frame) →  M′ ≡ plug F M  →  N′ ≡ plug F N  →  M —→ N  →  M′ —→ N′

pattern ξ F M—→N = ξξ F refl refl M—→N

reducible : (M : Term) → Set
reducible M = ∃[ N ] (M —→ N)

value-irreducible : ∀ {V M : Term} → Value V → ¬ (V —→ M)
value-irreducible V-ƛ (ξξ (□· x₂) () x₁ V—→M)
value-irreducible V-ƛ (ξξ (x₂ ·□) () x₁ V—→M)
value-irreducible V-ƛ (ξξ suc□ () x₁ V—→M)
value-irreducible V-zero (ξξ (□· x₂) () x₁ V—→M)
value-irreducible V-zero (ξξ (x₂ ·□) () x₁ V—→M)
value-irreducible V-zero (ξξ suc□ () x₁ V—→M)
value-irreducible (V-suc v) (ξ suc□ V—→M) = value-irreducible v V—→M
value-irreducible (V-μ v) (ξξ (□· x₂) () x₁ V—→M)
value-irreducible (V-μ v) (ξξ (x₂ ·□) () x₁ V—→M)
value-irreducible (V-μ v) (ξξ suc□ () x₁ V—→M)

β-μ-inv : ∀{V W N} → Value V → Value W → μ V · W —→ N  →  N ≡ V [ μ V ] · W
β-μ-inv v w (ξ (□· x₂) r) = ⊥-elim (value-irreducible (V-μ v) r)
β-μ-inv v w (ξξ (x₂ ·□) refl x₁ r) = ⊥-elim (value-irreducible w r)
β-μ-inv v w (β-μ x x₁) = refl

infix  2 _—↠_
infixr 2 _—→⟨_⟩_
infix  3 _END

data _—↠_ : Term → Term → Set where
  _END : (M : Term) → M —↠ M
  _—→⟨_⟩_ : (L : Term) {M N : Term} → L —→ M  →  M —↠ N  →  L —↠ N

len : ∀{M N : Term} → (M→N : M —↠ N) → ℕ
len (_ END) = 0
len (_ —→⟨ _ ⟩ red) = suc (len red)

infix 3 _⊢ⱽ_⦂_
data _⊢ⱽ_⦂_ : List Type → Term → Type → Set

infix 3 _⊢_⦂_
data _⊢_⦂_ : List Type → Term → Type → Set

data _⊢ⱽ_⦂_ where
  ⊢ⱽzero : ∀ {Γ} → Γ ⊢ⱽ `zero ⦂ `ℕ
  ⊢ⱽsuc : ∀ {Γ V} → Γ ⊢ⱽ V ⦂ `ℕ  →  Γ ⊢ⱽ `suc V ⦂ `ℕ
  ⊢ⱽƛ : ∀ {Γ N A B} → (A ∷ Γ) ⊢ N ⦂ B  →  Γ ⊢ⱽ ƛ N ⦂ (A ⇒ B)
  ⊢ⱽμ : ∀ {Γ V A B} → (A ⇒ B ∷ Γ) ⊢ⱽ V ⦂ A ⇒ B  →  Γ ⊢ⱽ μ V ⦂ A ⇒ B

⊢ⱽ⇒Value : ∀{Γ V A} → Γ ⊢ⱽ V ⦂ A → Value V
⊢ⱽ⇒Value ⊢ⱽzero = V-zero
⊢ⱽ⇒Value (⊢ⱽsuc ⊢V) = V-suc (⊢ⱽ⇒Value ⊢V)
⊢ⱽ⇒Value (⊢ⱽƛ ⊢N) = V-ƛ
⊢ⱽ⇒Value (⊢ⱽμ ⊢V) = V-μ (⊢ⱽ⇒Value ⊢V)

data _⊢_⦂_ where
  ⊢` : ∀ {Γ x A} → Γ ∋ x ⦂ A  →  Γ ⊢ ` x ⦂ A
  ⊢suc : ∀ {Γ M} → Γ ⊢ M ⦂ `ℕ  →  Γ ⊢ `suc M ⦂ `ℕ
  ⊢case : ∀{Γ L M N A} → Γ ⊢ L ⦂ `ℕ  →  Γ ⊢ M ⦂ A  →  `ℕ ∷ Γ ⊢ N ⦂ A  →  Γ ⊢ case L M N ⦂ A
  ⊢· : ∀ {Γ L M A B} → Γ ⊢ L ⦂ (A ⇒ B)  →  Γ ⊢ M ⦂ A  →  Γ ⊢ L · M ⦂ B
  ⊢val : ∀ {Γ V A} → Γ ⊢ⱽ V ⦂ A  →  Γ ⊢ V ⦂ A

_⦂_⇒_ : Subst → List Type → List Type → Set
_⦂_⇒_ σ Γ Δ = ∀ {x : Var} {A : Type} → Γ ∋ x ⦂ A  → Δ ⊢ σ x ⦂ A

{---- Substitution Preserves Types ---}

ext-ren-pres : ∀ {ρ : Rename} {Γ Δ : List Type} {A : Type}
  → ren ρ        ⦂ Γ       ⇒ Δ
  → ext (ren ρ)  ⦂ (A ∷ Γ) ⇒ (A ∷ Δ)
ext-ren-pres {ρ}{Γ}{Δ} ρ⦂ {zero} refl = ⊢` refl
ext-ren-pres {ρ}{Γ}{Δ}{A} ρ⦂ {suc x} {B} ∋x = G
    where
    ρx⦂ : Δ ∋ ρ x ⦂ B
    ρx⦂  with ρ⦂ ∋x
    ... | ⊢ρx rewrite ren-def ρ x
        with ⊢ρx
    ... | ⊢` ∋ρx = ∋ρx

    G : (A ∷ Δ) ⊢ (ren ρ ⨟ ↑) x ⦂ B
    G rewrite seq-def (ren ρ) ↑ x | ren-def ρ x | sub-var (ren suc) (ρ x)
      | ren-def suc (ρ x) = ⊢` ρx⦂

ren-preserveⱽ : ∀ {Γ Δ A}{ρ} (V : Term)
   → Γ ⊢ⱽ V ⦂ A
   → ren ρ ⦂ Γ ⇒ Δ
   → Δ ⊢ⱽ ⟪ ren ρ ⟫ V ⦂ A
ren-preserve : ∀ {Γ Δ A}{ρ} (M : Term)
   → Γ ⊢ M ⦂ A
   → ren ρ ⦂ Γ ⇒ Δ
   → Δ ⊢ ⟪ ren ρ ⟫ M ⦂ A
   
ren-preserveⱽ `zero ⊢ⱽzero ρ⦂ = ⊢ⱽzero
ren-preserveⱽ{ρ = ρ} (`suc V) (⊢ⱽsuc ⊢V) ρ⦂ = ⊢ⱽsuc (ren-preserveⱽ{ρ = ρ} V ⊢V ρ⦂)
ren-preserveⱽ {ρ = ρ} (ƛ N) (⊢ⱽƛ ⊢N) ρ⦂ =
  ⊢ⱽƛ (ren-preserve {ρ = extr ρ} N ⊢N (λ{x} → ext-ren-pres{ρ = ρ} ρ⦂ {x}))
ren-preserveⱽ{Γ}{Δ}{A}{ρ = ρ} (μ V) (⊢ⱽμ ⊢V) ρ⦂ =
  ⊢ⱽμ (ren-preserveⱽ{ρ = extr ρ} V ⊢V (λ{x} → ext-ren-pres{ρ = ρ} ρ⦂ {x}))

ren-preserve{ρ = ρ} (` x) (⊢` ∋x) ρ⦂ rewrite sub-var (ren ρ) x = ρ⦂ ∋x
ren-preserve{ρ = ρ} (`suc M) (⊢suc ⊢M) ρ⦂ = ⊢suc (ren-preserve{ρ = ρ} M ⊢M ρ⦂)
ren-preserve{ρ = ρ} (case L M N) (⊢case ⊢L ⊢M ⊢N) ρ⦂ =
    ⊢case (ren-preserve{ρ = ρ} L ⊢L ρ⦂) (ren-preserve{ρ = ρ} M ⊢M ρ⦂)
          (ren-preserve{ρ = extr ρ} N ⊢N (λ{x} → ext-ren-pres{ρ = ρ} ρ⦂ {x}))
ren-preserve {ρ = ρ} (L · M) (⊢· ⊢L ⊢M) ρ⦂ =
    ⊢· (ren-preserve{ρ = ρ} L ⊢L ρ⦂) (ren-preserve{ρ = ρ} M ⊢M ρ⦂)
ren-preserve {ρ = ρ} V (⊢val ⊢V) ρ⦂ = ⊢val (ren-preserveⱽ{ρ = ρ} V ⊢V ρ⦂)

ext-sub-pres : ∀ {σ : Subst} {Γ Δ : List Type} {A : Type}
    → σ     ⦂ Γ       ⇒ Δ
    → ext σ ⦂ (A ∷ Γ) ⇒ (A ∷ Δ)
ext-sub-pres {σ} σ⦂ {zero} refl = ⊢` refl
ext-sub-pres {σ}{Γ}{Δ}{A} σ⦂ {suc x} {B} ∋x rewrite seq-def σ ↑ x | up-def =
    ren-preserve {ρ = suc} (σ x) (σ⦂ ∋x) ren-suc
    where
    ren-suc : ren suc ⦂ Δ ⇒ (A ∷ Δ)
    ren-suc {y}{C} ∋y rewrite ren-def suc y = ⊢` ∋y

sub-preserveⱽ : ∀ {Γ Δ A}{σ} (V : Term)
   → Γ ⊢ⱽ V ⦂ A
   → σ ⦂ Γ ⇒ Δ
   → Δ ⊢ⱽ ⟪ σ ⟫ V ⦂ A
sub-preserve : ∀ {Γ Δ A}{σ} (M : Term)
   → Γ ⊢ M ⦂ A
   → σ ⦂ Γ ⇒ Δ
   → Δ ⊢ ⟪ σ ⟫ M ⦂ A
   
sub-preserveⱽ `zero ⊢ⱽzero ρ⦂ = ⊢ⱽzero
sub-preserveⱽ{σ = σ} (`suc V) (⊢ⱽsuc ⊢V) σ⦂ = ⊢ⱽsuc (sub-preserveⱽ{σ = σ} V ⊢V σ⦂)
sub-preserveⱽ {σ = σ} (ƛ N) (⊢ⱽƛ ⊢N) σ⦂ =
  ⊢ⱽƛ (sub-preserve {σ = ext σ} N ⊢N (λ{x} → ext-sub-pres{σ = σ} σ⦂ {x}))
sub-preserveⱽ {σ = σ} (μ V) (⊢ⱽμ ⊢V) σ⦂ =
  ⊢ⱽμ (sub-preserveⱽ {σ = ext σ} V ⊢V (λ{x} → ext-sub-pres{σ = σ} σ⦂ {x}))
     
sub-preserve {σ = σ} (` x) (⊢` ∋x) σ⦂ rewrite sub-var σ x = σ⦂ ∋x
sub-preserve (`suc M) (⊢suc ⊢M) σ⦂ = ⊢suc (sub-preserve M ⊢M σ⦂)
sub-preserve {σ = σ} (case L M N) (⊢case ⊢L ⊢M ⊢N) σ⦂ =
  ⊢case (sub-preserve {σ = σ} L ⊢L σ⦂) (sub-preserve {σ = σ} M ⊢M σ⦂)
        (sub-preserve {σ = ext σ} N ⊢N (λ{x} → ext-sub-pres{σ = σ} σ⦂ {x}))
sub-preserve {σ = σ} (L · M) (⊢· ⊢L ⊢M) σ⦂ =
    ⊢· (sub-preserve{σ = σ} L ⊢L σ⦂) (sub-preserve{σ = σ} M ⊢M σ⦂)
sub-preserve {σ = σ} V (⊢val ⊢V) σ⦂ = ⊢val (sub-preserveⱽ{σ = σ} V ⊢V σ⦂)

subst-preserve : ∀{Γ A B}{M N : Term}
  → B ∷ Γ ⊢ M ⦂ A
  → Γ ⊢ N ⦂ B
  → Γ ⊢ M [ N ] ⦂ A
subst-preserve{Γ}{A}{B}{M}{N} ⊢M ⊢N = sub-preserve{σ = N • id } M ⊢M (λ{x} → pf{x})
  where
    pf : (N • id) ⦂ B ∷ Γ ⇒ Γ
    pf {zero} refl = ⊢N
    pf {suc x} ∋x = ⊢` ∋x

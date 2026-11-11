{-

  The fixed frame of Impμ, CFGμ and X86μ. A function body runs in a
  frame of slots whose types (a context Δ, slot x : Δ ∋ A of type A)
  are fixed for the whole body. The typing of a body tracks which
  slots are initialized (Inits Δ, a flag for each slot): a slot is
  read only after it has been written.

  * none Δ: no slot is initialized;
  * x ∈ I, x ∉ I: slot x is, or is not, initialized;
  * I ⊕ x: I with slot x initialized, after a write to x;
  * J ⊆ I: every slot initialized in J is initialized in I, so code
    that starts with J may run where I holds;
  * fill Γ f: the slots f x of the variables x of Γ are initialized
    (the slots of a definition's environment and argument, at the start
    of its body).

  Only p I says that the slots initialized in I are those of the
  suffix D of the frame (p : D ⊑ Δ); lift locals gives a variable a
  slot outside that suffix, which is therefore not initialized.

-}

module FPC.Language.Frame where

open import FPC.Language.Type
open import Framework.Membership using (_⊑_; here⊑; there⊑; ⊑-∋; ⊑-trans)
open import FPC.Framework.AllUtil using (All; []; _∷_; lookup; Flags)

open import Data.Bool using (Bool; true; false; T; not)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; length)
open import Data.Nat using (_≤_)
open import Data.Nat.Properties using (≤-refl; m≤n⇒m≤1+n; n≮n; suc-injective)
open import Relation.Binary.PropositionalEquality using (_≢_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)

{- the initialized slots of a frame of type Δ -}
Inits : Ctx → Set
Inits = Flags

none : ∀ Δ → Inits Δ
none [] = []
none (A ∷ Δ) = false ∷ none Δ

infix 4 _∈_ _∉_ _⊆_
infixl 5 _⊕_

_∈_ : ∀ {Δ A} → Δ ∋ A → Inits Δ → Set
x ∈ I = T (lookup I x)

_∉_ : ∀ {Δ A} → Δ ∋ A → Inits Δ → Set
x ∉ I = T (not (lookup I x))

_⊕_ : ∀ {Δ A} → Inits Δ → Δ ∋ A → Inits Δ
(b ∷ I) ⊕ Z = true ∷ I
(b ∷ I) ⊕ S x = b ∷ (I ⊕ x)

_⊆_ : ∀ {Δ} → Inits Δ → Inits Δ → Set
[] ⊆ [] = ⊤
(b ∷ J) ⊆ (c ∷ I) = (T b → T c) × J ⊆ I

{- the slots f x of the variables x of Γ, initialized in turn, the
   oldest first -}
fill : ∀ {Δ} Γ → (∀ {A} → Γ ∋ A → Δ ∋ A) → Inits Δ
fill {Δ} [] f = none Δ
fill (A ∷ Γ) f = fill Γ (λ x → f (S x)) ⊕ f Z

{- the slots of the parameters Γ of a body, the suffix p of its frame -}
initial : ∀ {Γ Δ} → Γ ⊑ Δ → Inits Δ
initial {Γ} p = fill Γ (⊑-∋ p)

{- Inclusion -----------------------------------------------------------------}

⊆-refl : ∀ {Δ} {I : Inits Δ} → I ⊆ I
⊆-refl {I = []} = tt
⊆-refl {I = b ∷ I} = (λ t → t) , ⊆-refl

⊆-trans : ∀ {Δ} {I J K : Inits Δ}
  → I ⊆ J
  → J ⊆ K
  → I ⊆ K
⊆-trans {I = []} {[]} {[]} p q = tt
⊆-trans {I = a ∷ I} {b ∷ J} {c ∷ K} (f , p) (g , q) =
  (λ t → g (f t)) , ⊆-trans p q

⊆-⊕ : ∀ {Δ A} {I : Inits Δ} (x : Δ ∋ A) → I ⊆ I ⊕ x
⊆-⊕ {I = b ∷ I} Z = (λ _ → tt) , ⊆-refl
⊆-⊕ {I = b ∷ I} (S x) = (λ t → t) , ⊆-⊕ x

⊕-mono : ∀ {Δ A} {I J : Inits Δ} (x : Δ ∋ A)
  → J ⊆ I
  → J ⊕ x ⊆ I ⊕ x
⊕-mono {I = b ∷ I} {c ∷ J} Z (f , p) = (λ _ → tt) , p
⊕-mono {I = b ∷ I} {c ∷ J} (S x) (f , p) = f , ⊕-mono x p

{- code that starts after a write to x may start after writes to y and
   then x -}
⊆-⊕⊕ : ∀ {Δ A B} {I J : Inits Δ} (x : Δ ∋ A) (y : Δ ∋ B)
  → J ⊆ I ⊕ x
  → J ⊆ I ⊕ y ⊕ x
⊆-⊕⊕ {I = I} {J} x y p =
  ⊆-trans {I = J} {I ⊕ x} {I ⊕ y ⊕ x} p
    (⊕-mono {I = I ⊕ y} {I} x (⊆-⊕ {I = I} y))

∈-⊕ : ∀ {Δ A} {I : Inits Δ} (x : Δ ∋ A) → x ∈ I ⊕ x
∈-⊕ {I = b ∷ I} Z = tt
∈-⊕ {I = b ∷ I} (S x) = ∈-⊕ {I = I} x

∈-⊆ : ∀ {Δ A} {I J : Inits Δ} (x : Δ ∋ A)
  → x ∈ J
  → J ⊆ I
  → x ∈ I
∈-⊆ {I = b ∷ I} {c ∷ J} Z t (f , p) = f t
∈-⊆ {I = b ∷ I} {c ∷ J} (S x) t (f , p) = ∈-⊆ {I = I} {J} x t p

∈-⊕ʳ : ∀ {Δ A B} {I : Inits Δ} (x : Δ ∋ A) (y : Δ ∋ B)
  → y ∈ I
  → y ∈ I ⊕ x
∈-⊕ʳ {I = I} x y t = ∈-⊆ {I = I ⊕ x} {I} y t (⊆-⊕ x)

{- an initialized slot and one that is not are at different positions -}
∈∉-idx : ∀ {Δ A B} {I : Inits Δ} (x : Δ ∋ A) (y : Δ ∋ B)
  → x ∈ I
  → y ∉ I
  → idx x ≢ idx y
∈∉-idx {I = true ∷ I} Z Z i () e
∈∉-idx {I = false ∷ I} Z Z () n e
∈∉-idx {I = b ∷ I} Z (S y) i n ()
∈∉-idx {I = b ∷ I} (S x) Z i n ()
∈∉-idx {I = b ∷ I} (S x) (S y) i n e = ∈∉-idx {I = I} x y i n (suc-injective e)

{- Fresh slots ----------------------------------------------------------------}

{- the slots initialized in I are among those of the suffix D -}
Only : ∀ {D Δ : Ctx} → D ⊑ Δ → Inits Δ → Set
Only here⊑ I = ⊤
Only (there⊑ p) (b ∷ I) = T (not b) × Only p I

{- the suffix A ∷ D without its first element -}
⊑-tail : ∀ {D Δ : Ctx} {A} → (A ∷ D) ⊑ Δ → D ⊑ Δ
⊑-tail q = ⊑-trans (there⊑ here⊑) q

only-none : ∀ {D Δ} (p : D ⊑ Δ) → Only p (none Δ)
only-none here⊑ = tt
only-none (there⊑ p) = tt , only-none p

only-grow : ∀ {D D' Δ} {I : Inits Δ} (g : D ⊑ D') (q : D' ⊑ Δ)
  → Only (⊑-trans g q) I
  → Only q I
only-grow g here⊑ o = tt
only-grow {I = b ∷ I} g (there⊑ q) (t , o) = t , only-grow g q o

{- a slot outside D is not initialized -}
only-fresh : ∀ {D Δ A} {I : Inits Δ} (q : (A ∷ D) ⊑ Δ)
  → Only (⊑-tail q) I
  → ⊑-∋ q Z ∉ I
only-fresh {I = b ∷ I} here⊑ (t , o) = t
only-fresh {I = b ∷ I} (there⊑ q) (t , o) = only-fresh {I = I} q o

{- initializing a slot of D keeps the initialized slots in D -}
only-⊕ : ∀ {D Δ A} {I : Inits Δ} (q : D ⊑ Δ) (x : D ∋ A)
  → Only q I
  → Only q (I ⊕ ⊑-∋ q x)
only-⊕ here⊑ x o = tt
only-⊕ {I = b ∷ I} (there⊑ q) x (t , o) = t , only-⊕ q x o

{- the parameters' slots are initialized at the start of a body -}
fill-∈ : ∀ {Δ Γ A} (f : ∀ {B} → Γ ∋ B → Δ ∋ B) (x : Γ ∋ A) → f x ∈ fill Γ f
fill-∈ {Γ = A ∷ Γ} f Z = ∈-⊕ {I = fill Γ (λ y → f (S y))} (f Z)
fill-∈ {Γ = A ∷ Γ} f (S x) =
  ∈-⊕ʳ {I = fill Γ (λ y → f (S y))} (f Z) (f (S x)) (fill-∈ (λ y → f (S y)) x)

only-initial : ∀ {Γ Δ} (p : Γ ⊑ Δ) → Only p (initial p)
only-initial {Γ} p = go Γ (λ x → x)
  where
  go : ∀ Γ' (g : ∀ {B} → Γ' ∋ B → Γ ∋ B) → Only p (fill Γ' (λ x → ⊑-∋ p (g x)))
  go [] g = only-none p
  go (A ∷ Γ') g = only-⊕ p (g Z) (go Γ' (λ x → g (S x)))

{- a suffix is shorter -}
⊑-≤ : ∀ {D Δ : Ctx} → D ⊑ Δ → length D ≤ length Δ
⊑-≤ here⊑ = ≤-refl
⊑-≤ (there⊑ p) = m≤n⇒m≤1+n (⊑-≤ p)

⊑-long : ∀ {Δ : Ctx} {A} → (A ∷ Δ) ⊑ Δ → ⊥
⊑-long p = n≮n _ (⊑-≤ p)

{- Only does not depend on the proof that D is a suffix -}
only-⊑ : ∀ {D Δ} {I : Inits Δ} (p p' : D ⊑ Δ)
  → Only p I
  → Only p' I
only-⊑ here⊑ here⊑ o = o
only-⊑ here⊑ (there⊑ p') o = ⊥-elim (⊑-long p')
only-⊑ (there⊑ p) here⊑ o = ⊥-elim (⊑-long p)
only-⊑ {I = b ∷ I} (there⊑ p) (there⊑ p') (t , o) = t , only-⊑ p p' o

{- the slots initialized in I are among those of a longer suffix -}
only-up : ∀ {D D' Δ} {I : Inits Δ} (p : D ⊑ Δ) (g : D ⊑ D') (q : D' ⊑ Δ)
  → Only p I
  → Only q I
only-up p g q o = only-grow g q (only-⊑ p (⊑-trans g q) o)

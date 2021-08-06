open import Data.Empty using (⊥-elim) renaming (⊥ to False)
open import Data.List using (List ; _∷_ ; []; _++_; length)
open import Data.List.Properties using (++-conicalˡ)
open import Data.List.Membership.Propositional renaming (_∈_ to _⋵_)
open import Data.List.Membership.Propositional.Properties
  using (∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any using (here; there) 
open import Data.Nat using (ℕ; zero; suc; _≟_; _<_; s≤s)
open import Data.Product using (_×_; Σ; Σ-syntax; proj₁; proj₂)
    renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt) renaming (⊤ to True)
open import Level renaming (zero to lzero; suc to lsuc)
open import Relation.Binary.PropositionalEquality
    using (_≡_; _≢_; refl; sym; subst)
open import Relation.Nullary using (¬_; Dec; yes; no)

open import Primitives
open import PValueCBV
open import ScopedTuple hiding (𝒫)
open import SetsAsPredicates
open import Sig
open import Syntax
open import Utilities using (extensionality)

module PValueCBVProperties (Op : Set) (sig : Op → List Sig) where

open import Fold2 Op sig
open Syntax.OpSig Op sig
open import WellScoped Op sig using (WF-plug) 

rel-args : ∀{ℓ}{T : Set ℓ}
   → (∀ b → ArgTy T b → ArgTy T b → Set₁)
   → ∀ bs → Tuple bs (ArgTy T)
   → Tuple bs (ArgTy T) → Set₁
rel-args R [] xs ys = Lift (lsuc lzero) True
rel-args R (b ∷ bs) ⟨ x , xs ⟩ ⟨ y , ys ⟩ = (R b x y) × (rel-args R bs xs ys)

⊆-arg : ∀ b → ArgTy (𝒫 Value) b → ArgTy (𝒫 Value) b → Set₁
⊆-arg ■ x y = Lift (lsuc lzero) (x ⊆ y)
⊆-arg (ν b) f g = ∀ X → ⊆-arg b (f X) (g X)
⊆-arg (∁ b) x y = ⊆-arg b x y

⊆-args = rel-args ⊆-arg

record Semantics : Set₁ where
  field interp-op  : (op : Op) → Tuple (sig op) (ArgTy (𝒫 Value)) → 𝒫 Value
  
  ⟦_⟧_ : ABT → Env → 𝒫 Value
  ⟦ M ⟧ ρ = fold interp-op ∅ ρ M

  ⟦_⟧ₐ_ : ∀{b} → Arg b → Env  → ArgTy (𝒫 Value) b
  ⟦ arg ⟧ₐ ρ = fold-arg interp-op ∅ ρ arg

  ⟦_⟧₊_ : ∀{bs} → Args bs → Env  → Tuple bs (ArgTy (𝒫 Value))
  ⟦ args ⟧₊ ρ = fold-args interp-op ∅ ρ args

  field mono-op : ∀{op}{xs}{ys} → ⊆-args (sig op) xs ys → interp-op op xs ⊆ interp-op op ys
  
open Semantics {{...}}

{- Monotonic ------------------------------------------------------------------}

⟦⟧-mono : ∀{{_ : Semantics}} {ρ ρ′} (M : ABT)
  →  (∀ x → ρ x ⊆ ρ′ x)  →  ⟦ M ⟧ ρ ⊆ ⟦ M ⟧ ρ′
⟦⟧-mono-arg : ∀{{_ : Semantics}} {b}{ρ ρ′} (arg : Arg b)
  →  (∀ x → ρ x ⊆ ρ′ x)  →  ⊆-arg b (⟦ arg ⟧ₐ ρ) (⟦ arg ⟧ₐ ρ′)
⟦⟧-mono-args : ∀{{_ : Semantics}} {bs}{ρ ρ′} (args : Args bs)
  →  (∀ x → ρ x ⊆ ρ′ x)  →  ⊆-args bs (⟦ args ⟧₊ ρ) (⟦ args ⟧₊ ρ′)
  
⟦⟧-mono {ρ}{ρ′} (` x) ρ<ρ′ = ρ<ρ′ x
⟦⟧-mono {ρ}{ρ′} (op ⦅ args ⦆) ρ<ρ′ = mono-op (⟦⟧-mono-args  args ρ<ρ′)

⟦⟧-mono-arg {■} (ast M) ρ<ρ′ = lift (⟦⟧-mono M ρ<ρ′)
⟦⟧-mono-arg {ν b}{ρ}{ρ′} (bind arg) ρ<ρ′ X =
    ⟦⟧-mono-arg {b}{X • ρ}{X • ρ′} arg (env-ext ρ<ρ′)
⟦⟧-mono-arg {∁ b} (clear arg) ρ<ρ′ =
    ⟦⟧-mono-arg {b}{λ x → ∅}{λ x → ∅} arg λ x d z → z

⟦⟧-mono-args {bs = []} nil ρ<ρ′ = lift tt
⟦⟧-mono-args {bs = b ∷ bs} (cons arg args) ρ<ρ′ =
  ⟨ ⟦⟧-mono-arg arg ρ<ρ′ , ⟦⟧-mono-args args ρ<ρ′ ⟩

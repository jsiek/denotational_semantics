{-

  What the typed languages (Language/Typed/) share in the graph model:
  project, and the tables of global definitions.

  * inject is the identity: a value carries its own kind.
  * project t D is D, provided that D has a value that the tag t accepts
    (guardᵖ), and ∅ otherwise: a failed project means ∅, as an error
    does in the graph model. The tag accepts what the X86 test of t reads
    (Compiler/Select.agda): an integer, an injection, component i
    of a tuple of n + 1 (ttup n i), and a function, which is an entry of
    a function's graph (fun₂) up to Clos3ᵀ and a pair from Clos4ᵀ on,
    where a closure is a pair of code and environment (fun₄).
  * A table gives each definition of a program (Σ ∋ n) its meaning. The
    definitions are given meaning newest first, each with the table of
    the older ones (tables, by the level of a reference, as in
    Untyped/Semantics/Graph/Clos5Iswim.agda); a reference to another means ∅.

-}

module Semantics.Graph.Typed.Ops where

open import Framework.Primitives using (Int)
open import Framework.GraphModel.SetsAsPredicates
open import Framework.GraphModel.Domain
open import Framework.GraphModel.TypedGuard using (guardᵖ) public
open import Language.Typed.Type hiding (_≟_)

open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; length)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Nat using (ℕ; _≟_)
open import Data.Product using (Σ-syntax)
open import Data.Sum using (_⊎_)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (yes; no)

fun₂ fun₄ : Value → Set
fun₂ (V ↦ w) = ⊤
fun₂ ν = ⊤
fun₂ _ = ⊥
fun₄ ⦅ u , v ⦆ = ⊤
fun₄ _ = ⊥

accepts : (Value → Set) → Tag → Value → Set
accepts F tfun d = F d
accepts F tsum d = (Σ[ u ∈ Value ] d ≡ left u) ⊎ (Σ[ u ∈ Value ] d ≡ right u)
accepts F tint d = Σ[ k ∈ _ ] d ≡ const {Int} k
accepts F (ttup n i) d = Σ[ u ∈ Value ] d ≡ tup[ i ] u

projectᵍ : (Value → Set) → Tag → 𝒫 Value → 𝒫 Value
projectᵍ F t = guardᵖ (accepts F t)

init : 𝒫 Value
init = ⌈ ω ⌉

Table : List ℕ → Set₁
Table Σ = ∀ {n} → Σ ∋ n → 𝒫 Value

{- the table of the definitions ds (newest first), given the meaning of
   a definition with the table of the older ones -}
tables : ∀ {Σ} {D : ℕ → Set} → (Table Σ → ∀ {n} → D n → 𝒫 Value) → ∀ {ns} → All D ns → Table Σ
tables cd [] f = ∅
tables cd {_ ∷ ns} (d ∷ ds) f with lvl f ≟ length ns
... | yes _ = cd (tables cd ds) d
... | no _ = tables cd ds f

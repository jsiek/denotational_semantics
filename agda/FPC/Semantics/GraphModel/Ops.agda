{-

  What the languages of FPC from GlobalFunμ on share in the graph
  model: the tables of global definitions, as in
  ISWIM/Semantics/Graph/Typed/Ops.agda (which also has project, which
  FPC does not have).

  A table gives each definition of a program (Σ ∋ s) its meaning. The
  definitions are given meaning newest first, each with the table of
  the older ones (tables, by the level of a reference); a reference to
  another means ∅.

  The fixed frame of Impμ, CFGμ and X86μ is an environment (Env Value)
  that gives the slot at each position its meaning. A write to the
  slot at position i updates the frame in place (σ [ i ≔ X ]). A body
  starts in the frame start p X Y, in which every slot holds init
  except the slots of its environment X and its argument Y, which are
  written in that order.

-}

module FPC.Semantics.GraphModel.Ops where

open import Framework.GraphModel.Prelude
open import Framework.Membership using (_⊑_; ⊑-∋)
open import FPC.Language.Type using (Ctx; _∋_; Z; S; lvl; idx)
open import FPC.Language.GlobalFun using (DSig)

open import Data.List using (List; []; _∷_; length)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Nat using (ℕ; _≟_)
open import Relation.Nullary using (yes; no)

init : 𝒫 Value
init = ⌈ ⟨⟩ ⌉

{- the frame σ with X in the slot at position i -}
infixl 6 _[_≔_]
_[_≔_] : Env Value → ℕ → 𝒫 Value → Env Value
(σ [ i ≔ X ]) j with i ≟ j
... | yes _ = X
... | no _ = σ j

{- the frame at the start of a body with parameters A ∷ B ∷ [] (an
   argument and an environment), the environment X written first and
   then the argument Y -}
start : ∀ {Δ : Ctx} {A B} → (A ∷ B ∷ []) ⊑ Δ → 𝒫 Value → 𝒫 Value → Env Value
start p X Y = (λ _ → init) [ idx (⊑-∋ p (S Z)) ≔ X ] [ idx (⊑-∋ p Z) ≔ Y ]

Table : List DSig → Set₁
Table Σ = ∀ {s} → Σ ∋ s → 𝒫 Value

{- the table of the definitions ds (newest first), given the meaning of
   a definition with the table of the older ones -}
tables : ∀ {Σ} {D : DSig → Set} → (Table Σ → ∀ {s} → D s → 𝒫 Value) → ∀ {ss}
  → All D ss → Table Σ
tables cd [] f = ∅
tables cd {_ ∷ ss} (d ∷ ds) f with lvl f ≟ length ss
... | yes _ = cd (tables cd ds) d
... | no _ = tables cd ds f

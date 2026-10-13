module Semantics.Graph.Imp where
{-

 What the two semantics of Imp, the language after the 'lift locals'
 pass (Language/Imp.agda), have in common: stores, slots, atoms and simple
 expressions. They are also used by the semantics of CFG (Semantics/Graph/CFG.agda).

 The two semantics of expressions are

 - continuation-passing (Semantics/Graph/ImpK.agda), used by the main proof: an
   expression is run with a continuation, given its value and the store
   it leaves; and
 - direct (proof/Semantics/Graph/ImpDirect.agda), an alternative: an expression means a
   set of values and the store it leaves.

 A store σ gives each slot of the frame a meaning, a set of values. An
 expression runs in a frame of n slots. Reading a slot beyond the frame
 gives init, the error value, as an out-of-scope variable does in Clos5;
 assigning one goes wrong, so the construct means ∅ (checked), as a
 stuck program does.

 As in Clos5, the meaning depends on a table T of the global definitions.
 A call app f e a applies the meaning of f to those of e and a, as in
 Clos5, and leaves the store as it was: the code of a definition,
 Λ X. Λ Y. …, runs its body in a fresh frame, with X in slot 0, Y in
 slot 1 and 0 in the others (frame). main runs in a frame whose slots
 hold 0 (zeros).

-}

open import Framework.GraphModel.SetsAsPredicates
open import Framework.GraphModel.DOpSig using (Results)
open import Framework.GraphModel.Domain
open import Framework.GraphModel.Ops
open import Semantics.Graph.Prim
open import Semantics.Graph.Clos5Iswim using (Table; init) public
open import Language.Imp renaming (pair to pair′; inl to inl′; inr to inr′)
open import Framework.Primitives using (Int)

open import Data.Integer using (+_)
open import Data.Nat using (ℕ; zero; suc; _≟_; _<?_)
open import Data.List using (List; []; _∷_; length; replicate)
open import Data.Product using () renaming (_,_ to ⟨_,_⟩)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Relation.Nullary using (yes; no)

Store : Set₁
Store = ℕ → 𝒫 Value

{- slot x of a frame of n slots -}
read : ℕ → Store → ℕ → 𝒫 Value
read n σ x with x <? n
... | yes _ = σ x
... | no _ = init

_[_↦_] : Store → ℕ → 𝒫 Value → Store
(σ [ x ↦ D ]) y with y ≟ x
... | yes _ = D
... | no _ = σ y

{- D, if slot x is within a frame of n slots -}
checked : ℕ → ℕ → 𝒫 Value → 𝒫 Value
checked n x D with x <? n
... | yes _ = D
... | no _ = ∅

𝒜 : Table → ℕ → Store → Atm → 𝒫 Value
𝒜 T n σ (var x) = read n σ x
𝒜 T n σ (lit B k) = ℬ B k ptt
𝒜 T n σ (fun-ref k) = T k

𝒜s : Table → ℕ → Store → (as : List Atm) → Results (𝒫 Value) (replicate (length as) ■)
𝒜s T n σ [] = ptt
𝒜s T n σ (a ∷ as) = ⟨ 𝒜 T n σ a , 𝒜s T n σ as ⟩

{- the value of a simple expression in a frame of n slots; it leaves the
   store as it was -}
𝒮 : Table → ℕ → Store → Simple → 𝒫 Value
𝒮 T n σ (atm a) = 𝒜 T n σ a
𝒮 T n σ (app f e a) = ⋆ ⟨ ⋆ ⟨ 𝒜 T n σ f , ⟨ 𝒜 T n σ e , ptt ⟩ ⟩ , ⟨ 𝒜 T n σ a , ptt ⟩ ⟩
𝒮 T n σ (pair′ a b) = pair ⟨ 𝒜 T n σ a , ⟨ 𝒜 T n σ b , ptt ⟩ ⟩
𝒮 T n σ (fst a) = car ⟨ 𝒜 T n σ a , ptt ⟩
𝒮 T n σ (snd a) = cdr ⟨ 𝒜 T n σ a , ptt ⟩
𝒮 T n σ (tuple as) = 𝒯 (length as) (𝒜s T n σ as)
𝒮 T n σ (get i a) = proj i ⟨ 𝒜 T n σ a , ptt ⟩
𝒮 T n σ (inl′ a) = inl ⟨ 𝒜 T n σ a , ptt ⟩
𝒮 T n σ (inr′ a) = inr ⟨ 𝒜 T n σ a , ptt ⟩
𝒮 T n σ (prim p a b) = primD p ⟨ 𝒜 T n σ a , ⟨ 𝒜 T n σ b , ptt ⟩ ⟩

{- the slots of a fresh frame -}
zeros : Store
zeros _ = ℬ Int (+ 0) ptt

frame : 𝒫 Value → 𝒫 Value → Store
frame X Y zero = X
frame X Y (suc zero) = Y
frame X Y (suc (suc y)) = zeros y

{- the table of a list of definitions, newest first, given the code of a
   definition (code in Semantics/Graph/ImpK.agda and proof/Semantics/Graph/ImpDirect.agda) -}
tables : (Table → Body → 𝒫 Value) → List Body → Table
tables code [] k = ∅
tables code (b ∷ bs) k with k ≟ length bs
... | yes _ = code (tables code bs) b
... | no _ = tables code bs k

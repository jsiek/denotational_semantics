module Compiler.Model.Graph.Sem.CFG where
{-

 The semantics of CFG, the language after the explicate-control pass
 (Lang/CFG.agda).

 Stores, slots and simple expressions are as in Imp (Sem/Imp.agda). A
 tail runs in a frame of n slots, given the meanings B of the blocks it
 can see, and given the store as it enters it means a set of values: a
 tail produces a value, not a store. A block means a function from
 stores to sets of values.

 x := s; t is strict in s, like an assignment in Imp: ⋆ ⟨ Λ F , D ⟩,
 where D is the value of s and F X is the value of t with X in slot x.
 case a x l₁ l₂ is 𝒞, its branches running block l₁ or l₂ with the
 payload in slot x. Assigning a slot beyond the frame goes wrong: the
 construct means ∅ (checked), as in Imp. goto l runs block l in the store
 as it is.

 The blocks of a body are given meaning as the global definitions are
 (tables in Sem/Imp.agda): newest first, each with the meanings of the
 blocks older than it, which are all it can jump to, so no fixed point is
 needed. A jump to a label that is not among the visible blocks means ∅,
 as a reference to a missing global definition does.

 Calls are simple expressions, as in Imp: the code of a definition runs
 the start of its body in a fresh frame, with the meanings of all its
 blocks. main runs in a frame whose slots hold 0.

-}

open import Framework.GraphModel.SetsAsPredicates
open import Framework.GraphModel.Domain
open import Framework.GraphModel.Ops
open import Compiler.Model.Graph.Sem.Imp
  using (Table; init; Store; _[_↦_]; checked; 𝒜; 𝒮; zeros; frame) public
open import Compiler.Lang.CFG

open import Data.Nat using (ℕ; _≟_)
open import Data.List using (List; []; _∷_; length)
open import Data.Product using () renaming (_,_ to ⟨_,_⟩)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Relation.Nullary using (yes; no)

{- the meanings of the visible blocks, by label -}
Blocks : Set₁
Blocks = ℕ → Store → 𝒫 Value

{- t in a frame of n slots, with the blocks B -}
⟦_⟧[_] : Tail → Table → ℕ → Blocks → Store → 𝒫 Value
⟦ return s ⟧[ T ] n B σ = 𝒮 T n σ s
⟦ seq x s t ⟧[ T ] n B σ = checked n x
  (⋆ ⟨ Λ ⟨ (λ X → ⟦ t ⟧[ T ] n B (σ [ x ↦ X ])) , ptt ⟩ , ⟨ 𝒮 T n σ s , ptt ⟩ ⟩)
⟦ goto l ⟧[ T ] n B σ = B l σ
⟦ case a x l₁ l₂ ⟧[ T ] n B σ = checked n x
  (𝒞 ⟨ 𝒜 T n σ a , ⟨ (λ X → B l₁ (σ [ x ↦ X ])) , ⟨ (λ X → B l₂ (σ [ x ↦ X ])) , ptt ⟩ ⟩ ⟩)

{- the blocks bs (newest first), each with the meanings of the older ones -}
blocks : Table → ℕ → List Tail → Blocks
blocks T n [] l σ = ∅
blocks T n (t ∷ bs) l with l ≟ length bs
... | yes _ = ⟦ t ⟧[ T ] n (blocks T n bs)
... | no _ = blocks T n bs l

{- the start of a body, in a frame of its size, with its blocks -}
run : Table → Body → Store → 𝒫 Value
run T (body n bs t) = ⟦ t ⟧[ T ] n (blocks T n bs)

{- the function whose body is b, given the table T of the older
   definitions: it takes the tuple of free variables X and then the
   argument Y -}
code : Table → Body → 𝒫 Value
code T b = Λ ⟨ (λ X → Λ ⟨ (λ Y → run T b (frame X Y)) , ptt ⟩) , ptt ⟩

{- the table of a list of definitions, newest first -}
table : List Body → Table
table [] k = ∅
table (b ∷ bs) k with k ≟ length bs
... | yes _ = code (table bs) b
... | no _ = table bs k

{- the meaning of a whole program: the value of main -}
⟦_⟧ₚ : Program → 𝒫 Value
⟦ program ds b ⟧ₚ = run (table ds) b zeros

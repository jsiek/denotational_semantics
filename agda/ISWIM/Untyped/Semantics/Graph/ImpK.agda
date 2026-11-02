module Untyped.Semantics.Graph.ImpK where
{-

 The continuation-passing semantics of Imp (Language/Imp.agda), the one the
 main proof uses; proof/Semantics/Graph/ImpDirect.agda is a direct alternative. Stores,
 slots, atoms and simple expressions are in Semantics/Graph/Imp.agda.

 An expression runs in a frame of n slots, given the store σ as it
 enters and a continuation κ, the meaning of what runs after it: κ D σ'
 is the meaning of the rest of the body, given the value D of the
 expression and the store σ' it leaves. So an expression means a set of
 values, the result of the whole body, and the store need not be
 collected over the runs of an expression, as it is in
 proof/Semantics/Graph/ImpDirect.agda: each run passes its own store to κ.

 x := e₁; e₂ runs e₁ with the continuation that, given its value D and
 store σ', is strict in D like let in Clos5, ⋆ ⟨ Λ F , D ⟩, where F X
 runs e₂ in σ' with X in slot x and then κ. case is 𝒞, each branch
 running with κ. Assigning a slot beyond the frame, by assign or case,
 means ∅ (checked).

 A call app f e a is a simple expression and leaves the caller's store
 as it was: the code of a definition runs its body in a fresh frame with
 the continuation halt, which returns the value. main runs in a frame
 whose slots hold 0, also with halt.

-}

open import Framework.GraphModel.SetsAsPredicates
open import Framework.GraphModel.Domain
open import Framework.GraphModel.Ops
open import Untyped.Semantics.Graph.Imp using (Table; Store; _[_↦_]; checked; 𝒜; 𝒮; zeros; frame; tables) public
open import Untyped.Language.Imp

open import Data.Nat using (ℕ)
open import Data.List using (List)
open import Data.Product using () renaming (_,_ to ⟨_,_⟩)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)

{- what runs after an expression, given its value and the store it leaves -}
Kont : Set₁
Kont = 𝒫 Value → Store → 𝒫 Value

{- e in a frame of n slots, then κ -}
⟦_⟧ᴷ[_] : Exp → Table → ℕ → Store → Kont → 𝒫 Value
⟦ simple s ⟧ᴷ[ T ] n σ κ = κ (𝒮 T n σ s) σ
⟦ case a x e₁ e₂ ⟧ᴷ[ T ] n σ κ = checked n x
  (𝒞 ⟨ 𝒜 T n σ a , ⟨ (λ X → ⟦ e₁ ⟧ᴷ[ T ] n (σ [ x ↦ X ]) κ) , ⟨ (λ X → ⟦ e₂ ⟧ᴷ[ T ] n (σ [ x ↦ X ]) κ) , ptt ⟩ ⟩ ⟩)
⟦ assign x e₁ e₂ ⟧ᴷ[ T ] n σ κ = ⟦ e₁ ⟧ᴷ[ T ] n σ (λ D σ' → checked n x
  (⋆ ⟨ Λ ⟨ (λ X → ⟦ e₂ ⟧ᴷ[ T ] n (σ' [ x ↦ X ]) κ) , ptt ⟩ , ⟨ D , ptt ⟩ ⟩))

{- the end of a body: its value -}
halt : Kont
halt D σ = D

{- the function whose body is b, given the table T of the older
   definitions: it takes the tuple of free variables X and then the
   argument Y -}
code : Table → Body → 𝒫 Value
code T (body n e) = Λ ⟨ (λ X → Λ ⟨ (λ Y → ⟦ e ⟧ᴷ[ T ] n (frame X Y) halt) , ptt ⟩) , ptt ⟩

{- the table of a list of definitions, newest first -}
table : List Body → Table
table = tables code

{- the meaning of a whole program: the value of main -}
⟦_⟧ᴷₚ : Program → 𝒫 Value
⟦ program ds (body n e) ⟧ᴷₚ = ⟦ e ⟧ᴷ[ table ds ] n zeros halt

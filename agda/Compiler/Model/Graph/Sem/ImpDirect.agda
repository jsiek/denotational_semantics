module Compiler.Model.Graph.Sem.ImpDirect where
{-

 The direct semantics of Imp (Lang/Imp.agda), an alternative to the
 continuation-passing one (Sem/ImpK.agda) that the main proof uses.
 Stores, slots, atoms and simple expressions are in Sem/Imp.agda.

 An expression runs in a frame of n slots: given the store as it enters,
 it means a set of values and the store as it leaves, so assignments are
 seen by what runs after them, also after the expression that contains
 them. Assigning a slot beyond the frame, by assign or case, means ∅ and
 leaves the store as it was (checked), and nothing after it runs.

 x := e₁; e₂ is strict in e₁, like let in Clos5: its value and each slot
 of the store it leaves are ⋆ ⟨ Λ F , D₁ ⟩, where D₁ is the value of e₁
 and F X is the value (or the slot) after e₂, run in the store that e₁
 leaves with X in slot x. Likewise case is 𝒞, both for its value and for
 each slot of the store it leaves. A run of e₂ (or of a branch) leaves
 its store only if it has a value: a run that goes wrong or diverges
 leaves no store behind. So the store, like the value, collects the runs
 of an expression; in Sem/ImpK.agda each run passes its own store on.

-}

open import SetsAsPredicates
open import Compiler.Model.Graph.Domain.ISWIM.Domain
open import Compiler.Model.Graph.Domain.ISWIM.Ops
open import Compiler.Model.Graph.Sem.Imp
  using (Table; init; Store; read; _[_↦_]; 𝒜; 𝒜s; 𝒮; zeros; frame; tables) public
open import Compiler.Lang.Imp

open import Data.Nat using (ℕ; _<?_)
open import Data.List using (List)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Relation.Nullary using (yes; no)

{- r, if slot x is within a frame of n slots -}
checked : ℕ → ℕ → Store → 𝒫 Value × Store → 𝒫 Value × Store
checked n x σ r with x <? n
... | yes _ = r
... | no _ = ⟨ ∅ , σ ⟩

{- slot y of the store that r leaves, if r has a value -}
_↓_ : 𝒫 Value × Store → ℕ → 𝒫 Value
(r ↓ y) w = w ∈ proj₂ r y × nonempty (proj₁ r)

{- case on A, the branches E₁ and E₂ given the payload: 𝒞, for the value
   and for each slot of the store -}
caseₛ : 𝒫 Value → (𝒫 Value → 𝒫 Value × Store) → (𝒫 Value → 𝒫 Value × Store) → 𝒫 Value × Store
caseₛ A E₁ E₂ =
  ⟨ 𝒞 ⟨ A , ⟨ (λ X → proj₁ (E₁ X)) , ⟨ (λ X → proj₁ (E₂ X)) , ptt ⟩ ⟩ ⟩
  , (λ y → 𝒞 ⟨ A , ⟨ (λ X → E₁ X ↓ y) , ⟨ (λ X → E₂ X ↓ y) , ptt ⟩ ⟩ ⟩) ⟩

{- E given the value D, strict like let: ⋆ ⟨ Λ … , D ⟩, for the value and
   for each slot of the store -}
letₛ : 𝒫 Value → (𝒫 Value → 𝒫 Value × Store) → 𝒫 Value × Store
letₛ D E =
  ⟨ ⋆ ⟨ Λ ⟨ (λ X → proj₁ (E X)) , ptt ⟩ , ⟨ D , ptt ⟩ ⟩
  , (λ y → ⋆ ⟨ Λ ⟨ (λ X → E X ↓ y) , ptt ⟩ , ⟨ D , ptt ⟩ ⟩) ⟩

{- e in a frame of n slots -}
⟦_⟧[_] : Exp → Table → ℕ → Store → 𝒫 Value × Store
⟦ simple s ⟧[ T ] n σ = ⟨ 𝒮 T n σ s , σ ⟩
⟦ case a x e₁ e₂ ⟧[ T ] n σ = checked n x σ
  (caseₛ (𝒜 T n σ a) (λ X → ⟦ e₁ ⟧[ T ] n (σ [ x ↦ X ])) (λ X → ⟦ e₂ ⟧[ T ] n (σ [ x ↦ X ])))
⟦ assign x e₁ e₂ ⟧[ T ] n σ = checked n x σ
  (letₛ (proj₁ (⟦ e₁ ⟧[ T ] n σ)) (λ X → ⟦ e₂ ⟧[ T ] n (proj₂ (⟦ e₁ ⟧[ T ] n σ) [ x ↦ X ])))

{- the function whose body is b, given the table T of the older
   definitions: it takes the tuple of free variables X and then the
   argument Y -}
code : Table → Body → 𝒫 Value
code T (body n e) = Λ ⟨ (λ X → Λ ⟨ (λ Y → proj₁ (⟦ e ⟧[ T ] n (frame X Y))) , ptt ⟩) , ptt ⟩

{- the table of a list of definitions, newest first -}
table : List Body → Table
table = tables code

{- the meaning of a whole program: the value of main -}
⟦_⟧ₚ : Program → 𝒫 Value
⟦ program ds (body n e) ⟧ₚ = proj₁ (⟦ e ⟧[ table ds ] n zeros)

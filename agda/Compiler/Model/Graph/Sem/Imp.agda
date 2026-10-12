module Compiler.Model.Graph.Sem.Imp where
{-

 The semantics of Imp, the language after the 'lift locals' pass
 (Lang/Imp.agda).

 A store σ gives each slot of the frame a meaning, a set of values. An
 expression runs in a frame of n slots: given the store as it enters, it
 means a set of values and the store as it leaves, so assignments are
 seen by what runs after them, also after the expression that contains
 them. Reading a slot beyond the frame gives init, the error value, as an
 out-of-scope variable does in Clos5; assigning one, by assign or case,
 goes wrong, so the construct means ∅, as a stuck program does (and
 nothing after it runs).

 x := e₁; e₂ is strict in e₁, like let in Clos5: its value and each slot
 of the store it leaves are ⋆ ⟨ Λ F , D₁ ⟩, where D₁ is the value of e₁
 and F X is the value (or the slot) after e₂, run in the store that e₁
 leaves with X in slot x. Likewise case is 𝒞, both for its value and for
 each slot of the store it leaves. A run of e₂ (or of a branch) leaves
 its store only if it has a value: a run that goes wrong or diverges
 leaves no store behind.

 As in Clos5, the meaning depends on a table T of the global definitions.
 A call app f e a applies the meaning of f to those of e and a, as in
 Clos5, and leaves the store as it was: the code of a definition,
 Λ X. Λ Y. …, runs its body in a fresh frame, with X in slot 0, Y in
 slot 1 and 0 in the others. main runs in a frame whose slots hold 0.

-}

open import SetsAsPredicates
open import NewDOpSig using (Results)
open import Compiler.Model.Graph.Domain.ISWIM.Domain
open import Compiler.Model.Graph.Domain.ISWIM.Ops
open import Compiler.Model.Graph.Sem.Clos5Iswim using (Table; init) public
open import Compiler.Lang.Imp renaming (pair to pair′; inl to inl′; inr to inr′)
open import Primitives using (Int)

open import Data.Integer using (+_)
open import Data.Nat using (ℕ; zero; suc; _≟_; _<?_)
open import Data.List using (List; []; _∷_; length; replicate)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
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

{- r, if slot x is within a frame of n slots -}
checked : ℕ → ℕ → Store → 𝒫 Value × Store → 𝒫 Value × Store
checked n x σ r with x <? n
... | yes _ = r
... | no _ = ⟨ ∅ , σ ⟩

𝒜 : Table → ℕ → Store → Atm → 𝒫 Value
𝒜 T n σ (var x) = read n σ x
𝒜 T n σ (lit B k) = ℬ B k ptt
𝒜 T n σ (fun-ref k) = T k

𝒜s : Table → ℕ → Store → (as : List Atm) → Results (𝒫 Value) (replicate (length as) ■)
𝒜s T n σ [] = ptt
𝒜s T n σ (a ∷ as) = ⟨ 𝒜 T n σ a , 𝒜s T n σ as ⟩

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

{- e in a frame of n slots -}
⟦_⟧[_] : Exp → Table → ℕ → Store → 𝒫 Value × Store
⟦ simple s ⟧[ T ] n σ = ⟨ 𝒮 T n σ s , σ ⟩
⟦ case a x e₁ e₂ ⟧[ T ] n σ = checked n x σ
  (caseₛ (𝒜 T n σ a) (λ X → ⟦ e₁ ⟧[ T ] n (σ [ x ↦ X ])) (λ X → ⟦ e₂ ⟧[ T ] n (σ [ x ↦ X ])))
⟦ assign x e₁ e₂ ⟧[ T ] n σ = checked n x σ
  (letₛ (proj₁ (⟦ e₁ ⟧[ T ] n σ)) (λ X → ⟦ e₂ ⟧[ T ] n (proj₂ (⟦ e₁ ⟧[ T ] n σ) [ x ↦ X ])))

{- the slots of a fresh frame -}
zeros : Store
zeros _ = ℬ Int (+ 0) ptt

frame : 𝒫 Value → 𝒫 Value → Store
frame X Y zero = X
frame X Y (suc zero) = Y
frame X Y (suc (suc y)) = zeros y

{- the function whose body is b, given the table T of the older
   definitions: it takes the tuple of free variables X and then the
   argument Y -}
code : Table → Body → 𝒫 Value
code T (body n e) = Λ ⟨ (λ X → Λ ⟨ (λ Y → proj₁ (⟦ e ⟧[ T ] n (frame X Y))) , ptt ⟩) , ptt ⟩

{- the table of a list of definitions, newest first -}
table : List Body → Table
table [] k = ∅
table (b ∷ bs) k with k ≟ length bs
... | yes _ = code (table bs) b
... | no _ = table bs k

{- the meaning of a whole program: the value of main -}
⟦_⟧ₚ : Program → 𝒫 Value
⟦ program ds (body n e) ⟧ₚ = proj₁ (⟦ e ⟧[ table ds ] n zeros)

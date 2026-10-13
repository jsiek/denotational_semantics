module Semantics.Graph.X86 where
{-

 The semantics of X86, the language after the select-instructions pass
 (Language/X86.agda), in continuation-passing style, as Semantics/Graph/CFG.agda and
 Semantics/Graph/ImpK.agda.

 The state of a body is its frame σ (a store, as in Semantics/Graph/Imp.agda), its
 registers ρ (a set of values for each), and the flag φ, a set of values
 left ⟨⟩ (set) and right ⟨⟩ (not set); ∅ is no flag, so that sete and je
 then go wrong. What runs from a point of a body on (Kont) means, given
 the state, a set of values, the result of the body. An instruction
 transforms the state and passes it on to its continuation; a sequence
 of instructions runs one after the other, and a block is its
 instructions followed by its jump: retq produces %rax, jmp l runs block
 l in the state as it is, and je l₁ l₂ is 𝒞 on the flag.

 Every write is strict, so that an instruction whose computation goes
 wrong or diverges (its value is ∅) stops the body: nothing after it
 runs. A slot of the frame is a variable of the body and is bound as in
 CFG: d := D runs the rest with a finite, nonempty, consistent part of D
 in d (⋆ ⟨ Λ F , D ⟩). A register or the flag holds D itself, provided D
 is nonempty (strict D E: E, if D is nonempty). Reading an unset
 register or a clobbered flag gives ∅. Reading a slot beyond the frame
 gives init and assigning one means ∅ (checked), as in CFG.

 (A register is not bound like a slot: a call would then apply the
 callee to finite parts of %rdi and %rsi, which is the same as applying
 it to the whole sets only when they are consistent, and the set of a
 code pointer is not known to be.)

 The values the instructions compute are those of Imp's simple
 expressions: subq and cmpq are primD, sete d puts the flag in d, testinl
 sets the flag by the tag of its operand (isinl), alloc and load are the
 operators of pairs, tuples and injections (load payload takes the
 payload of either injection).

 Calls: callq a applies the code pointer a to %rdi and then to %rsi, as
 Imp's app does, and puts the result in %rax; %rdi, %rsi and the flag
 are clobbered (∅), and the caller's frame is as it was. The code of a
 global definition is Λ X. Λ Y. its start, run in a fresh frame of
 max(2, locals) slots holding 0, with X in %rdi, Y in %rsi and %rax unset
 (its start moves them to slots 0 and 1). The blocks of a body, and the
 global definitions, are given meaning newest first, each with the older
 ones, as in CFG. main runs in a fresh frame of locals slots holding 0,
 with %rax holding 0, %rdi and %rsi unset, and no flag.

-}

open import Framework.GraphModel.SetsAsPredicates
open import Framework.GraphModel.DOpSig using (Results)
open import Framework.GraphModel.Domain
open import Framework.GraphModel.Ops
open import Semantics.Graph.Prim using (primD)
open import Semantics.Graph.Imp
  using (Table; Store; read; _[_↦_]; checked; zeros) public
open import Language.Prim using (sub; eq)
open import Language.X86 renaming (pair to pairₛ; inl to inlₛ; inr to inrₛ)

open import Data.Nat using (ℕ; _≟_; _⊔_)
open import Data.List using (List; []; _∷_; length; replicate)
open import Data.Product using (Σ-syntax; _×_) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (yes; no)

Regs : Set₁
Regs = Reg → 𝒫 Value

_[_≔_] : Regs → Reg → 𝒫 Value → Regs
(ρ [ rax ≔ D ]) rax = D
(ρ [ rdi ≔ D ]) rdi = D
(ρ [ rsi ≔ D ]) rsi = D
(ρ [ g ≔ D ]) g' = ρ g'

{- the registers after a call that returns R: %rdi and %rsi are clobbered -}
called : 𝒫 Value → Regs
called R rax = R
called R _ = ∅

{- the registers at the start of a global definition -}
args : 𝒫 Value → 𝒫 Value → Regs
args X Y rax = ∅
args X Y rdi = X
args X Y rsi = Y

{- what runs from a point of a body on, given the frame, registers and flag -}
Kont : Set₁
Kont = Store → Regs → 𝒫 Value → 𝒫 Value

{- an operand, in a frame of n slots -}
𝒪 : Table → ℕ → Store → Regs → Arg → 𝒫 Value
𝒪 T n σ ρ (loc (var x)) = read n σ x
𝒪 T n σ ρ (loc (reg g)) = ρ g
𝒪 T n σ ρ (imm B k) = ℬ B k ptt
𝒪 T n σ ρ (label k) = T k

𝒪s : Table → ℕ → Store → Regs → (as : List Arg) → Results (𝒫 Value) (replicate (length as) ■)
𝒪s T n σ ρ [] = ptt
𝒪s T n σ ρ (a ∷ as) = ⟨ 𝒪 T n σ ρ a , 𝒪s T n σ ρ as ⟩

{- E, provided that D is nonempty -}
strict : 𝒫 Value → 𝒫 Value → 𝒫 Value
strict D E w = nonempty D × w ∈ E

{- d := D, then κ -}
put : ℕ → Loc → 𝒫 Value → Kont → Kont
put n (var x) D κ σ ρ φ = checked n x (⋆ ⟨ Λ ⟨ (λ X → κ (σ [ x ↦ X ]) ρ φ) , ptt ⟩ , ⟨ D , ptt ⟩ ⟩)
put n (reg g) D κ σ ρ φ = strict D (κ σ (ρ [ g ≔ D ]) φ)

{- the flag that testinl sets -}
isinl : 𝒫 Value → 𝒫 Value
isinl D w = (Σ[ u ∈ Value ] left u ∈ D × w ≡ left ⟨⟩) ⊎ (Σ[ u ∈ Value ] right u ∈ D × w ≡ right ⟨⟩)

{- the payload of an injection -}
payloadD : 𝒫 Value → 𝒫 Value
payloadD D v = left v ∈ D ⊎ right v ∈ D

{- the object that alloc builds; a wrong number of fields goes wrong -}
object : Table → ℕ → Store → Regs → Shape → List Arg → 𝒫 Value
object T n σ ρ pairₛ (a ∷ b ∷ []) = pair ⟨ 𝒪 T n σ ρ a , ⟨ 𝒪 T n σ ρ b , ptt ⟩ ⟩
object T n σ ρ tuple as = 𝒯 (length as) (𝒪s T n σ ρ as)
object T n σ ρ inlₛ (a ∷ []) = inl ⟨ 𝒪 T n σ ρ a , ptt ⟩
object T n σ ρ inrₛ (a ∷ []) = inr ⟨ 𝒪 T n σ ρ a , ptt ⟩
object T n σ ρ _ _ = ∅

{- the field that load takes -}
field′ : Field → 𝒫 Value → 𝒫 Value
field′ fst D = car ⟨ D , ptt ⟩
field′ snd D = cdr ⟨ D , ptt ⟩
field′ (get i) D = proj i ⟨ D , ptt ⟩
field′ payload D = payloadD D

{- flag := F, then κ -}
flag : 𝒫 Value → Kont → Store → Regs → 𝒫 Value
flag F κ σ ρ = strict F (κ σ ρ F)

{- %rax := R after a call, then κ -}
call : 𝒫 Value → Kont → Store → 𝒫 Value
call R κ σ = strict R (κ σ (called R) ∅)

{- an instruction in a frame of n slots, then κ -}
⟦_⟧ⁱ : Instr → Table → ℕ → Kont → Kont
⟦ movq a d ⟧ⁱ T n κ σ ρ φ = put n d (𝒪 T n σ ρ a) κ σ ρ φ
⟦ subq a d ⟧ⁱ T n κ σ ρ φ = put n d (primD sub ⟨ 𝒪 T n σ ρ (loc d) , ⟨ 𝒪 T n σ ρ a , ptt ⟩ ⟩) κ σ ρ φ
⟦ cmpq a₂ a₁ ⟧ⁱ T n κ σ ρ φ = flag (primD eq ⟨ 𝒪 T n σ ρ a₁ , ⟨ 𝒪 T n σ ρ a₂ , ptt ⟩ ⟩) κ σ ρ
⟦ sete d ⟧ⁱ T n κ σ ρ φ = put n d φ κ σ ρ φ
⟦ testinl a ⟧ⁱ T n κ σ ρ φ = flag (isinl (𝒪 T n σ ρ a)) κ σ ρ
⟦ alloc s as d ⟧ⁱ T n κ σ ρ φ = put n d (object T n σ ρ s as) κ σ ρ φ
⟦ load f a d ⟧ⁱ T n κ σ ρ φ = put n d (field′ f (𝒪 T n σ ρ a)) κ σ ρ φ
⟦ callq a ⟧ⁱ T n κ σ ρ φ =
  call (⋆ ⟨ ⋆ ⟨ 𝒪 T n σ ρ a , ⟨ ρ rdi , ptt ⟩ ⟩ , ⟨ ρ rsi , ptt ⟩ ⟩) κ σ

⟦_⟧ˢ : List Instr → Table → ℕ → Kont → Kont
⟦ [] ⟧ˢ T n κ = κ
⟦ i ∷ is ⟧ˢ T n κ = ⟦ i ⟧ⁱ T n (⟦ is ⟧ˢ T n κ)

{- the meanings of the visible blocks, by label -}
Blocks : Set₁
Blocks = ℕ → Kont

⟦_⟧ʲ : Jump → Blocks → Kont
⟦ retq ⟧ʲ B σ ρ φ = ρ rax
⟦ jmp l ⟧ʲ B = B l
⟦ je l₁ l₂ ⟧ʲ B σ ρ φ = 𝒞 ⟨ φ , ⟨ (λ _ → B l₁ σ ρ φ) , ⟨ (λ _ → B l₂ σ ρ φ) , ptt ⟩ ⟩ ⟩

⟦_⟧ᵇ : Block → Table → ℕ → Blocks → Kont
⟦ b ⟧ᵇ T n B = ⟦ Block.instrs b ⟧ˢ T n (⟦ Block.jump b ⟧ʲ B)

{- the blocks bs (newest first), each with the meanings of the older ones -}
blocks : Table → ℕ → List Block → Blocks
blocks T n [] l σ ρ φ = ∅
blocks T n (b ∷ bs) l with l ≟ length bs
... | yes _ = ⟦ b ⟧ᵇ T n (blocks T n bs)
... | no _ = blocks T n bs l

{- the start of a body, in a frame of n slots, with its blocks -}
run : Table → ℕ → Body → Kont
run T n (body _ bs b) = ⟦ b ⟧ᵇ T n (blocks T n bs)

{- the function whose body is b, given the table T of the older definitions -}
code : Table → Body → 𝒫 Value
code T b = Λ ⟨ (λ X → Λ ⟨ (λ Y → run T (2 ⊔ Body.locals b) b zeros (args X Y) ∅) , ptt ⟩) , ptt ⟩

{- the table of a list of definitions, newest first -}
table : List Body → Table
table [] k = ∅
table (b ∷ bs) k with k ≟ length bs
... | yes _ = code (table bs) b
... | no _ = table bs k

{- the meaning of a whole program: the value of main -}
⟦_⟧ₚ : Program → 𝒫 Value
⟦ program ds b ⟧ₚ = run (table ds) (Body.locals b) b zeros (called (zeros 0)) ∅

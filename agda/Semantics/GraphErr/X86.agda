module Semantics.GraphErr.X86 where
{-

 The semantics of X86 (Language/X86.agda) in the graph model with errors:
 that of Semantics/Graph/X86.agda, with the error-propagating operators
 and the checks of the machine (Semantics/CEK/X86.agda).

 An unset register and the absent flag hold init, {ω}, so that reading
 them errs: %rdi and %rsi in main, %rax at the start of a definition,
 %rdi, %rsi and the flag after a call. A write is strict in its value
 (strictᵐ for a register or the flag, letᵐ for a slot): an instruction
 whose value errs stops the body with ω, one whose value diverges with
 ∅. Writing a slot beyond the frame errs (frameᵐ). alloc of the wrong
 number of fields errs; load errs on a value of the wrong kind; testinl
 on a non-injection; callq is the late-check call callᵐ of the code
 pointer, %rdi and %rsi; a jump to a missing block errs.

-}

open import Framework.Primitives
open import Framework.GraphModel.SetsAsPredicates
open import Framework.GraphModel.DOpSig
open import Framework.GraphModel.Domain
open import Framework.GraphModel.OpsBase using (ℬ)
open import Framework.GraphModel.ErrorMonad
open import Semantics.GraphErr.Prim
open import Semantics.GraphErr.Frames using (Table; Store; init; read; _[_↦_]; frameᵐ; zeros; tables) public
open import Language.Prim using (sub; eq)
open import Language.X86 renaming (pair to pairₛ; inl to inlₛ; inr to inrₛ)

open import Data.Integer using (+_)
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

{- the registers after a call that returns R: %rdi and %rsi are unset -}
called : 𝒫 Value → Regs
called R rax = R
called R _ = init

{- the registers at the start of a global definition: %rax is unset -}
args : 𝒫 Value → 𝒫 Value → Regs
args X Y rax = init
args X Y rdi = X
args X Y rsi = Y

Kont : Set₁
Kont = Store → Regs → 𝒫 Value → 𝒫 Value

𝒪 : Table → ℕ → Store → Regs → Arg → 𝒫 Value
𝒪 T n σ ρ (loc (var x)) = read n σ x
𝒪 T n σ ρ (loc (reg g)) = ρ g
𝒪 T n σ ρ (imm B k) = ℬ B k ptt
𝒪 T n σ ρ (label k) = T k

𝒪s : Table → ℕ → Store → Regs → (as : List Arg) → Results (𝒫 Value) (replicate (length as) ■)
𝒪s T n σ ρ [] = ptt
𝒪s T n σ ρ (a ∷ as) = ⟨ 𝒪 T n σ ρ a , 𝒪s T n σ ρ as ⟩

{- d := D, then κ -}
put : ℕ → Loc → 𝒫 Value → Kont → Kont
put n (var x) D κ σ ρ φ = frameᵐ n x D (letᵐ ⟨ D , ⟨ (λ X → κ (σ [ x ↦ X ]) ρ φ) , ptt ⟩ ⟩)
put n (reg g) D κ σ ρ φ = strictᵐ D (κ σ (ρ [ g ≔ D ]) φ)

{- the object that alloc builds; a wrong number of fields errs -}
object : Table → ℕ → Store → Regs → Shape → List Arg → 𝒫 Value
object T n σ ρ pairₛ (a ∷ b ∷ []) = pairᵐ ⟨ 𝒪 T n σ ρ a , ⟨ 𝒪 T n σ ρ b , ptt ⟩ ⟩
object T n σ ρ tuple as = 𝒯ᵐ (length as) (𝒪s T n σ ρ as)
object T n σ ρ inlₛ (a ∷ []) = inlᵐ ⟨ 𝒪 T n σ ρ a , ptt ⟩
object T n σ ρ inrₛ (a ∷ []) = inrᵐ ⟨ 𝒪 T n σ ρ a , ptt ⟩
object T n σ ρ _ _ = init

field′ : Field → 𝒫 Value → 𝒫 Value
field′ fst D = carᵐ ⟨ D , ptt ⟩
field′ snd D = cdrᵐ ⟨ D , ptt ⟩
field′ (get i) D = projᵐ i ⟨ D , ptt ⟩
field′ payload D = payloadᵐ D

{- flag := F, then κ -}
flag : 𝒫 Value → Kont → Store → Regs → 𝒫 Value
flag F κ σ ρ = strictᵐ F (κ σ ρ F)

{- %rax := R after a call, then κ, with %rdi, %rsi and the flag unset -}
call : 𝒫 Value → Kont → Store → 𝒫 Value
call R κ σ = strictᵐ R (κ σ (called R) init)

⟦_⟧ⁱ : Instr → Table → ℕ → Kont → Kont
⟦ movq a d ⟧ⁱ T n κ σ ρ φ = put n d (𝒪 T n σ ρ a) κ σ ρ φ
⟦ subq a d ⟧ⁱ T n κ σ ρ φ = put n d (primᵐ sub ⟨ 𝒪 T n σ ρ (loc d) , ⟨ 𝒪 T n σ ρ a , ptt ⟩ ⟩) κ σ ρ φ
⟦ cmpq a₂ a₁ ⟧ⁱ T n κ σ ρ φ = flag (primᵐ eq ⟨ 𝒪 T n σ ρ a₁ , ⟨ 𝒪 T n σ ρ a₂ , ptt ⟩ ⟩) κ σ ρ
⟦ sete d ⟧ⁱ T n κ σ ρ φ = put n d φ κ σ ρ φ
⟦ testinl a ⟧ⁱ T n κ σ ρ φ = flag (isinlᵐ (𝒪 T n σ ρ a)) κ σ ρ
⟦ alloc s as d ⟧ⁱ T n κ σ ρ φ = put n d (object T n σ ρ s as) κ σ ρ φ
⟦ load f a d ⟧ⁱ T n κ σ ρ φ = put n d (field′ f (𝒪 T n σ ρ a)) κ σ ρ φ
⟦ callq a ⟧ⁱ T n κ σ ρ φ =
  call (callᵐ ⟨ 𝒪 T n σ ρ a , ⟨ ρ rdi , ⟨ ρ rsi , ptt ⟩ ⟩ ⟩) κ σ

⟦_⟧ˢ : List Instr → Table → ℕ → Kont → Kont
⟦ [] ⟧ˢ T n κ = κ
⟦ i ∷ is ⟧ˢ T n κ = ⟦ i ⟧ⁱ T n (⟦ is ⟧ˢ T n κ)

Blocks : Set₁
Blocks = ℕ → Kont

⟦_⟧ʲ : Jump → Blocks → Kont
⟦ retq ⟧ʲ B σ ρ φ = ρ rax
⟦ jmp l ⟧ʲ B = B l
⟦ je l₁ l₂ ⟧ʲ B σ ρ φ = 𝒞ᵐ ⟨ φ , ⟨ (λ _ → B l₁ σ ρ φ) , ⟨ (λ _ → B l₂ σ ρ φ) , ptt ⟩ ⟩ ⟩

⟦_⟧ᵇ : Block → Table → ℕ → Blocks → Kont
⟦ b ⟧ᵇ T n B = ⟦ Block.instrs b ⟧ˢ T n (⟦ Block.jump b ⟧ʲ B)

{- the blocks bs (newest first); a missing block errs -}
blocks : Table → ℕ → List Block → Blocks
blocks T n [] l σ ρ φ = init
blocks T n (b ∷ bs) l with l ≟ length bs
... | yes _ = ⟦ b ⟧ᵇ T n (blocks T n bs)
... | no _ = blocks T n bs l

run : Table → ℕ → Body → Kont
run T n (body _ bs b) = ⟦ b ⟧ᵇ T n (blocks T n bs)

code : Table → Body → 𝒫 Value
code T b = ΛΛᵐ ⟨ (λ X Y → run T (2 ⊔ Body.locals b) b zeros (args X Y) init) , ptt ⟩

table : List Body → Table
table = tables code

{- main: %rax holds 0, %rdi and %rsi are unset, and there is no flag -}
⟦_⟧ₚ : Program → 𝒫 Value
⟦ program ds b ⟧ₚ = run (table ds) (Body.locals b) b zeros (called (ℬ Int (+ 0) ptt)) init

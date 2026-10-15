{-

  The semantics of X86ᵀ (Language/Typed/X86.agda) in the graph model
  with errors: that of untyped X86 (Untyped/Semantics/GraphErr/X86.agda)
  with the typed operators of the typed
  languages (Semantics/GraphErr/Typed/Ops.agda), which check nothing.
  The frame is the environment, as in CFGᵀ (Semantics/GraphErr/Typed/CFG.agda):
  slot x is position idx x, and writing slot k forgets the slots after
  it (drop). A label means its block, under the meanings of the older
  blocks.

  The only check is chk's: the project of the typed languages, a closure
  being a pair (projectᵠ kind₄). Only chk and callq can fail or diverge,
  so only their results are written strictly (a register: strictᵐ); the
  other instructions, on operands of the types they need, always have a
  value, and a register write is a substitution. A slot write binds its
  value (letᵗ), as CFGᵀ's seq does. An unset register and an unset
  flag hold init, {ω}. callq calls the code in %rax with %rdi and %rsi
  (an application, ⋆, as the typed call is); a closure's code and
  environment are car and cdr of its slot. testinl sets the flag to the
  tag of an injection, and je takes a case on it.

-}

module Semantics.GraphErr.Typed.X86 where

open import Framework.GraphModel.ErrorPrelude
open import Framework.GraphModel.Ops using (⋆; car; cdr; payloadD)
open import Semantics.GraphErr.Typed.Ops
open import Semantics.GraphErr.Typed.Clos4 using (kind₄)
open import Semantics.GraphErr.Typed.Clos5 using (tbl)
open import Semantics.GraphErr.Typed.Imp using (Table; 𝒜; letᵗ)
open import Semantics.GraphErr.Typed.CFG using (BEnv; drop)
open import Language.Prim using (sub; eq)
open import Language.Typed.Type hiding (_≟_)
open import Language.Typed.X86

open import Data.List using (List; []; _∷_; replicate)
open import Data.Nat using (ℕ)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Product using () renaming (_,_ to ⟨_,_⟩)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)

RegsD : Set₁
RegsD = Reg → 𝒫 Value

_[_≔_] : RegsD → Reg → 𝒫 Value → RegsD
(R [ rax ≔ D ]) rax = D
(R [ rdi ≔ D ]) rdi = D
(R [ rsi ≔ D ]) rsi = D
(R [ _ ≔ D ]) r = R r

{- the registers after a call that returns C, and at the start of a
   definition of environment X and argument Y -}
called-regs : 𝒫 Value → RegsD
called-regs C rax = C
called-regs C _ = init

args : 𝒫 Value → 𝒫 Value → RegsD
args X Y rax = init
args X Y rdi = X
args X Y rsi = Y

{- what runs next, from a frame, registers and a flag -}
Kont : Set₁
Kont = Env Value → RegsD → 𝒫 Value → 𝒫 Value

module _ {Σ : List ℕ} (T : Table) where

  𝒪 : ∀ {ψ τ} → Arg Σ ψ τ → Env Value → RegsD → 𝒫 Value
  𝒪 (atom a) ρ R = 𝒜 a T ρ
  𝒪 (reg r _) ρ R = R r
  𝒪 (a ↑) ρ R = 𝒪 a ρ R

  𝒪s : ∀ {ψ m} → Vec (Arg Σ ψ (ty Any)) m → Env Value → RegsD → Results (𝒫 Value) (replicate m ■)
  𝒪s [] ρ R = ptt
  𝒪s (a ∷ as) ρ R = ⟨ 𝒪 a ρ R , 𝒪s as ρ R ⟩

  object : ∀ {ψ A} → Obj Σ ψ A → Env Value → RegsD → 𝒫 Value
  object (pair c e) ρ R = pairᵐ ⟨ 𝒪 c ρ R , ⟨ 𝒪 e ρ R , ptt ⟩ ⟩
  object (tuple {m = m} as) ρ R = 𝒯ᵐ m (𝒪s as ρ R)
  object (inl a) ρ R = inlᵐ ⟨ 𝒪 a ρ R , ptt ⟩
  object (inr a) ρ R = inrᵐ ⟨ 𝒪 a ρ R , ptt ⟩

  field′ : ∀ {A B} → Field A B → 𝒫 Value → 𝒫 Value
  field′ (get i) D = getᵗ i D
  field′ payload D = D ≫= λ X → payloadD (X ⇂ ValPayload)

  {- d := D, then κ; strictly, for a result that may fail or diverge -}
  put : ∀ {n ψ τ ψ'} → Dst n ψ τ ψ' → 𝒫 Value → Kont → Kont
  put (reg r) D κ ρ R F = κ ρ (R [ r ≔ D ]) F
  put (slot p _) D κ ρ R F = letᵗ D λ X → κ (X • drop p ρ) R F

  putˢ : ∀ {n ψ τ ψ'} → Dst n ψ τ ψ' → 𝒫 Value → Kont → Kont
  putˢ (reg r) D κ ρ R F = strictᵐ D (κ ρ (R [ r ≔ D ]) F)
  putˢ d@(slot p _) D κ = put d D κ

  ⟦_⟧ⁱ : ∀ {n ψ ψ'} → Instr Σ n ψ ψ' → Kont → Kont
  ⟦ movq a d ⟧ⁱ κ ρ R F = put d (𝒪 a ρ R) κ ρ R F
  ⟦ subq a r _ ⟧ⁱ κ ρ R F = κ ρ (R [ r ≔ primᵗ sub (R r) (𝒪 a ρ R) ]) F
  ⟦ cmpq a₂ a₁ ⟧ⁱ κ ρ R F = κ ρ R (primᵗ eq (𝒪 a₁ ρ R) (𝒪 a₂ ρ R))
  ⟦ sete d ⟧ⁱ κ ρ R F = put d F κ ρ R F
  ⟦ testinl a ⟧ⁱ κ ρ R F = κ ρ R (𝒪 a ρ R ≫= isinlD)
  ⟦ alloc o d ⟧ⁱ κ ρ R F = put d (object o ρ R) κ ρ R F
  ⟦ load f a d ⟧ⁱ κ ρ R F = put d (field′ f (𝒪 a ρ R)) κ ρ R F
  ⟦ loadfst x r ⟧ⁱ κ ρ R F = κ ρ (R [ r ≔ car ⟨ ρ (idx x) , ptt ⟩ ]) F
  ⟦ loadsnd {x = x} r ⟧ⁱ κ ρ R F = κ ρ (R [ r ≔ cdr ⟨ ρ (idx x) , ptt ⟩ ]) F
  ⟦ callq a _ _ ⟧ⁱ κ ρ R F = strictᵐ C (κ ρ (called-regs C) init)
    where C = ⋆ ⟨ ⋆ ⟨ 𝒪 a ρ R , ⟨ R rdi , ptt ⟩ ⟩ , ⟨ R rsi , ptt ⟩ ⟩
  ⟦ chk t x d ⟧ⁱ κ ρ R F = putˢ d (projectᵠ kind₄ t (ρ (idx x))) κ ρ (R [ rax ≔ init ]) init

  ⟦_⟧ˢ : ∀ {n Bs ψ} → Seq Σ n Bs ψ → BEnv Bs → Kont
  ⟦ i ∷ k ⟧ˢ B = ⟦ i ⟧ⁱ (⟦ k ⟧ˢ B)
  ⟦ retq _ ⟧ˢ B ρ R F = R rax
  ⟦ jmp l ⟧ˢ B ρ R F = B l ρ
  ⟦ je l₁ l₂ ⟧ˢ B ρ R F = caseᵗ F (λ _ → B l₁ ρ) (λ _ → B l₂ ρ)

  {- each block, from its frame, with the meanings of the older ones -}
  blocks : ∀ {n Bs} → Blocks Σ n Bs → BEnv Bs
  blocks (bs ▷ k) Z ρ = ⟦ k ⟧ˢ (blocks bs) ρ (λ _ → init) init
  blocks (bs ▷ k) (S l) = blocks bs l

  run : ∀ {ψ} → Body Σ ψ → Kont
  run (body n bs k) = ⟦ k ⟧ˢ (blocks bs)

{- the code of a definition: its body with %rdi and %rsi set -}
codeₜ : ∀ {Σ} → Table → ∀ {m} → Body Σ (called m) → 𝒫 Value
codeₜ T b = ΛΛᵐ ⟨ (λ X Y → run T b (λ _ → init) (args X Y) init) , ptt ⟩

⟦_⟧ₜ : Program → 𝒫 Value
⟦ program {Σ} ds b ⟧ₜ = run (tbl (codeₜ {Σ}) ds) b (λ _ → init) (λ _ → init) init

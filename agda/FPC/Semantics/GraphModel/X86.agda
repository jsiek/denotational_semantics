{-

  The semantics of X86μ (FPC/Language/X86.agda) in the graph model, as
  that of X86ᵀ (ISWIM/Semantics/Graph/Typed/X86.agda), in a fixed frame.
  What runs next (Kont) is given the frame, the registers and the flag.
  The frame is the environment, as in CFGμ: slot x is position idx x,
  and a write to slot x updates that position in place
  (FPC/Semantics/GraphModel/Ops.agda). A label means its block, under
  the meanings of the older blocks; a block starts with its frame, the
  registers unset and no flag.

  * A slot write binds its value as CFGμ's seq does: ⋆ ⟨ Λ F , D ⟩, F X
    running the rest with X written to the slot. A register write is a
    substitution (R [ r ≔ʳ D ]), and so is the flag's (cmpq).
  * Only callq can diverge (∅), so only it writes its result strictly
    (strict, E provided that D is nonempty): it applies the code to
    %rdi and %rsi (⋆, as CFGμ's call) and puts the result in %rax.
  * An unset register, and an unset flag, hold init, {⟨⟩}: typed code
    never reads them. After a call %rdi, %rsi and the flag are unset.
  * fold and unfold (↑, ↓) are the identity; case x y z l₁ l₂ is 𝒞 on
    slot x, as CFGμ's case: a branch writes the payload to slot y or z
    and runs its block.
  * The code of a definition is Λ X. Λ Y. its body, with X in %rdi and Y
    in %rsi, in an empty frame; definitions are given meaning as in
    GlobalFunμ (tables).

-}

module FPC.Semantics.GraphModel.X86 where

open import Framework.GraphModel.Prelude
open import Framework.GraphModel.DOpSig using (Results)
open import Framework.GraphModel.Ops renaming (pair to pairD; inl to inlD; inr
  to inrD)
open import Semantics.Graph.Prim using (primD)
open import FPC.Semantics.GraphModel.Ops
open import FPC.Semantics.GraphModel.Imp using (𝒜)
open import FPC.Semantics.GraphModel.CFG using (Meanings)
open import Language.Prim using (sub; eq)
open import FPC.Language.Type
open import FPC.Language.X86
open import FPC.Framework.AllUtil using (All; []; _∷_; pos)

open import Data.List using (List; length; replicate)
open import Data.Product using () renaming (_,_ to ⟨_,_⟩)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)

RegsD : Set₁
RegsD = Reg → 𝒫 Value

{- the registers R with D in register r -}
_[_≔ʳ_] : RegsD → Reg → 𝒫 Value → RegsD
(R [ rax ≔ʳ D ]) rax = D
(R [ rdi ≔ʳ D ]) rdi = D
(R [ rsi ≔ʳ D ]) rsi = D
(R [ _ ≔ʳ D ]) r = R r

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

module _ {Σ : List DSig} (T : Table Σ) where

  𝒪 : ∀ {Δ} {ψ : St Δ} {τ} → Arg Σ ψ τ → Env Value → RegsD → 𝒫 Value
  𝒪 (atom a) ρ R = 𝒜 a T ρ
  𝒪 (reg r _) ρ R = R r
  𝒪 (a ↑) ρ R = 𝒪 a ρ R
  𝒪 (a ↓) ρ R = 𝒪 a ρ R

  𝒪s : ∀ {Δ} {ψ : St Δ} {Δs} → All (λ A → Arg Σ ψ (ty A)) Δs → Env Value → RegsD
    → Results (𝒫 Value) (replicate (length Δs) ■)
  𝒪s [] ρ R = ptt
  𝒪s (a ∷ as) ρ R = ⟨ 𝒪 a ρ R , 𝒪s as ρ R ⟩

  object : ∀ {Δ} {ψ : St Δ} {A} → Obj Σ ψ A → Env Value → RegsD → 𝒫 Value
  object (pair c e) ρ R = pairD ⟨ 𝒪 c ρ R , ⟨ 𝒪 e ρ R , ptt ⟩ ⟩
  object (tuple {Δs} as) ρ R = 𝒯 (length Δs) (𝒪s as ρ R)
  object (inl a) ρ R = inlD ⟨ 𝒪 a ρ R , ptt ⟩
  object (inr a) ρ R = inrD ⟨ 𝒪 a ρ R , ptt ⟩

  {- d := D, then κ -}
  put : ∀ {Δ} {ψ : St Δ} {τ ψ'} → Dst ψ τ ψ' → 𝒫 Value → Kont → Kont
  put (reg r) D κ ρ R F = κ ρ (R [ r ≔ʳ D ]) F
  put (slot x _) D κ ρ R F =
    ⋆ ⟨ Λ ⟨ (λ X → κ (ρ [ idx x ≔ X ]) R F) , ptt ⟩ , ⟨ D , ptt ⟩ ⟩

  ⟦_⟧ⁱ : ∀ {Δ} {ψ ψ' : St Δ} → Instr Σ ψ ψ' → Kont → Kont
  ⟦ movq a d ⟧ⁱ κ ρ R F = put d (𝒪 a ρ R) κ ρ R F
  ⟦ subq a r _ ⟧ⁱ κ ρ R F =
    κ ρ (R [ r ≔ʳ primD sub ⟨ R r , ⟨ 𝒪 a ρ R , ptt ⟩ ⟩ ]) F
  ⟦ cmpq a₂ a₁ ⟧ⁱ κ ρ R F = κ ρ R (primD eq ⟨ 𝒪 a₁ ρ R , ⟨ 𝒪 a₂ ρ R , ptt ⟩ ⟩)
  ⟦ sete d ⟧ⁱ κ ρ R F = put d F κ ρ R F
  ⟦ alloc o d ⟧ⁱ κ ρ R F = put d (object o ρ R) κ ρ R F
  ⟦ load i a d ⟧ⁱ κ ρ R F = put d (proj (pos i) ⟨ 𝒪 a ρ R , ptt ⟩) κ ρ R F
  ⟦ loadfst x _ r ⟧ⁱ κ ρ R F = κ ρ (R [ r ≔ʳ car ⟨ ρ (idx x) , ptt ⟩ ]) F
  ⟦ loadsnd {x = opened x} r ⟧ⁱ κ ρ R F =
    κ ρ (R [ r ≔ʳ cdr ⟨ ρ (idx x) , ptt ⟩ ]) F
  ⟦ callq a _ _ ⟧ⁱ κ ρ R F = strict C (κ ρ (called-regs C) init)
    where C = ⋆ ⟨ ⋆ ⟨ 𝒪 a ρ R , ⟨ R rdi , ptt ⟩ ⟩ , ⟨ R rsi , ptt ⟩ ⟩

  ⟦_⟧ˢ : ∀ {Δ R' Bs ψ} → Seq Σ Δ R' Bs ψ → Meanings Bs → Kont
  ⟦ i ∷ k ⟧ˢ B = ⟦ i ⟧ⁱ (⟦ k ⟧ˢ B)
  ⟦ retq _ ⟧ˢ B ρ R F = R rax
  ⟦ jmp l ⟧ˢ B ρ R F = B l ρ
  ⟦ case x _ y z l₁ l₂ ⟧ˢ B ρ R F =
    𝒞
      ⟨ ρ (idx x)
        ,
        ⟨ (λ X → B l₁ (ρ [ idx y ≔ X ]))
          , ⟨ (λ X → B l₂ (ρ [ idx z ≔ X ])) , ptt ⟩ ⟩ ⟩

  {- each block, from its frame, with the meanings of the older ones -}
  blocks : ∀ {Δ R' Bs} → Blocks Σ Δ R' Bs → Meanings Bs
  blocks (bs ▷ k) Z ρ = ⟦ k ⟧ˢ (blocks bs) ρ (λ _ → init) init
  blocks (bs ▷ k) (S l) = blocks bs l

  run : ∀ {R' ψ} → Body Σ R' ψ → Kont
  run (body Δ bs k) = ⟦ k ⟧ˢ (blocks bs)

{- the code of a definition: its body with %rdi and %rsi set -}
codeₜ : ∀ {Σ} → Table Σ → ∀ {s} → Body Σ (DSig.cod s) (called s) → 𝒫 Value
codeₜ T b =
  Λ ⟨ (λ X → Λ ⟨ (λ Y → run T b (λ _ → init) (args X Y) init) , ptt ⟩) , ptt ⟩

{- the meaning of a whole program: the value of main -}
⟦_⟧ₜ : ∀ {A} → Program A → 𝒫 Value
⟦ program ds b ⟧ₜ = run (tables codeₜ ds) b (λ _ → init) (λ _ → init) init

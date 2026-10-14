{-

  CFGᵀ with the checks of X86: a semantics of the typed CFGᵀ syntax
  (Language/Typed/CFG.agda) whose operators are the untyped, checking
  ones that the instructions select produces mean
  (Semantics/GraphErr/X86.agda): fst and snd of a closure check a pair,
  a call checks a function, get a tuple, a primitive integers, a case an
  injection, a slot binding is letᵐ, and project t runs the X86 test of
  t (test) before it moves its operand. The code of a definition binds
  its parameters to its first two slots, as the X86 prologue does.

  It is the middle of the proof of select (SelectCorrect.agda): select
  is correct for it exactly (SelectX86), and it is related to the typed
  semantics, which checks nothing but project (SelectBoundary).

-}

module proof.Correctness.GraphErr.SelectCheck where

open import Framework.Primitives using (Int)
open import Framework.GraphModel.SetsAsPredicates
open import Framework.GraphModel.DOpSig
open import Framework.GraphModel.Domain
open import Framework.GraphModel.OpsBase using (ℬ)
open import Framework.GraphModel.ErrorMonad
open import Framework.GraphModel.Env using (Env)
open import Semantics.GraphErr.Prim using (primᵐ)
open import Semantics.GraphErr.Typed.Ops using (init)
open import Semantics.GraphErr.Typed.CFG using (Table; tbl; 𝒜; BEnv; drop)
open import Semantics.GraphErr.Typed.Clos5 using (⟦_⟧s[_])
open import Language.Prim using (sub)
open import Language.Typed.Type hiding (_≟_)
import Language.Typed.Mon as M
open import Language.Typed.CFG
open import Language.Typed.Imp using (Simple; atm; pack; callc; tuple; get; inl; inr; prim; inject; project)

open import Data.Integer using (+_)
open import Data.List using (List; []; _∷_)
open import Data.Product using () renaming (_,_ to ⟨_,_⟩)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)

{- the X86 test of a tag -}
test : Tag → 𝒫 Value → 𝒫 Value
test tint A = primᵐ sub ⟨ A , ⟨ ℬ Int (+ 0) ptt , ptt ⟩ ⟩
test tsum A = isinlᵐ A
test tfun A = carᵐ ⟨ A , ptt ⟩
test (ttup n i) A = projᵐ i ⟨ A , ptt ⟩

𝒮ᶜ : ∀ {Σ Δ A} → Simple Σ Δ A → Table → Env Value → 𝒫 Value
𝒮ᶜ (atm a) T ρ = 𝒜 a T ρ
𝒮ᶜ (pack c e) T ρ = pairᵐ ⟨ 𝒜 c T ρ , ⟨ 𝒜 e T ρ , ptt ⟩ ⟩
𝒮ᶜ (callc f a) T ρ = strictᵐ C (strictᵐ D (strictᵐ (𝒜 a T ρ) (callᵐ ⟨ C , ⟨ D , ⟨ 𝒜 a T ρ , ptt ⟩ ⟩ ⟩)))
  where C = carᵐ ⟨ 𝒜 f T ρ , ptt ⟩
        D = cdrᵐ ⟨ 𝒜 f T ρ , ptt ⟩
𝒮ᶜ (tuple {n = n} as) T ρ = 𝒯ᵐ n (⟦ M.⌜ as ⌝ᵛ ⟧s[ T ] ρ)
𝒮ᶜ (get i a) T ρ = projᵐ i ⟨ 𝒜 a T ρ , ptt ⟩
𝒮ᶜ (inl a) T ρ = inlᵐ ⟨ 𝒜 a T ρ , ptt ⟩
𝒮ᶜ (inr a) T ρ = inrᵐ ⟨ 𝒜 a T ρ , ptt ⟩
𝒮ᶜ (prim p a b) T ρ = primᵐ p ⟨ 𝒜 a T ρ , ⟨ 𝒜 b T ρ , ptt ⟩ ⟩
𝒮ᶜ (inject G a) T ρ = 𝒜 a T ρ
𝒮ᶜ (project t a) T ρ = strictᵐ (test t (𝒜 a T ρ)) (𝒜 a T ρ)

⟦_⟧ᶜᵗ : ∀ {Σ Bs Δ} → Tail Σ Bs Δ → Table → BEnv Bs → Env Value → 𝒫 Value
⟦ return s ⟧ᶜᵗ T B ρ = 𝒮ᶜ s T ρ
⟦ seq p s t ⟧ᶜᵗ T B ρ = letᵐ ⟨ 𝒮ᶜ s T ρ , ⟨ (λ X → ⟦ t ⟧ᶜᵗ T B (X • drop p ρ)) , ptt ⟩ ⟩
⟦ goto l ⟧ᶜᵗ T B ρ = B l ρ
⟦ case a p l₁ l₂ ⟧ᶜᵗ T B ρ = 𝒞ᵐ ⟨ 𝒜 a T ρ , ⟨ (λ X → B l₁ (X • drop p ρ)) , ⟨ (λ X → B l₂ (X • drop p ρ)) , ptt ⟩ ⟩ ⟩

blocksᶜ : ∀ {Σ Bs} → Blocks Σ Bs → Table → BEnv Bs
blocksᶜ (bs ▷ t) T Z = ⟦ t ⟧ᶜᵗ T (blocksᶜ bs T)
blocksᶜ (bs ▷ t) T (S l) = blocksᶜ bs T l

runᶜ : ∀ {Σ Δ} → Body Σ Δ → Table → Env Value → 𝒫 Value
runᶜ (body bs t) T = ⟦ t ⟧ᶜᵗ T (blocksᶜ bs T)

codeᶜʰ : ∀ {Σ} → Table → ∀ {n} → Body Σ (Any ∷ ⟪ tup n ⟫ ∷ []) → 𝒫 Value
codeᶜʰ T b = ΛΛᵐ ⟨ (λ X Y → letᵐ ⟨ X , ⟨ (λ X' → letᵐ ⟨ Y , ⟨ (λ Y' → runᶜ b T (Y' • X' • λ _ → init)) , ptt ⟩ ⟩) , ptt ⟩ ⟩) , ptt ⟩

⟦_⟧ᶜʰ : Program → 𝒫 Value
⟦ program {Σ} ds b ⟧ᶜʰ = runᶜ b (tbl (codeᶜʰ {Σ}) ds) (λ _ → init)

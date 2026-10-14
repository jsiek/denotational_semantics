{-

  A clocked interpreter for CFGᵀ (Language/Typed/CFG.agda), the output
  of typed explicate control. A tail runs in a frame typed by its
  context and returns a value: return s gives the value of s (as in
  Impᵀ, Semantics/Interp/Typed/Imp.agda); seq p s t assigns the value
  of s to the slot after those of Δ' (p : Δ' ⊑ Δ), forgetting the newer
  ones (forget), and runs t; case a p l₁ l₂ does so with the payload
  of a and jumps to l₁ or l₂. A tail runs with the blocks it may jump
  to, and block l with the blocks older than it, so the interpreter is
  structurally recursive on the clock, the blocks and the tail; only
  calls tick the clock.

-}

module Semantics.Interp.Typed.CFG where

open import Language.Typed.Type
open import Framework.Membership using (_⊑_; here⊑; there⊑)
open import Language.Typed.CFG
open import Semantics.Interp.Clock
open import Semantics.Interp.Typed.Clos5 using (module Vals)
open import Semantics.Interp.Typed.Imp using (atom; eval-simple)
open import Framework.Lookup using (_!_; forget)

open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)

module _ {Σ : List ℕ} (ds : All (λ n → Body Σ (Any ∷ ⟪ tup n ⟫ ∷ [])) Σ) where
  open Vals Σ

  tail : ∀ {Bs Δ} → ℕ → Blocks Σ Bs → Env Δ → Tail Σ Bs Δ → Result (Val Any)
  jump : ∀ {Bs Δ} → ℕ → Blocks Σ Bs → Bs ∋ Δ → Env Δ → Result (Val Any)
  run : ∀ {Δ} → ℕ → Body Σ Δ → Env Δ → Result (Val Any)
  call : ℕ → Val ⟪ fun ⟫ → Val Any → Result (Val Any)

  tail ck bs φ (return s) = eval-simple (call ck) φ s
  tail ck bs φ (seq p s t) = do v ← eval-simple (call ck) φ s; tail ck bs (v ∷ forget p φ) t
  tail ck bs φ (goto l) = jump ck bs l φ
  tail ck bs φ (case a p l₁ l₂) =
    either (atom φ a) (λ v → jump ck bs l₁ (v ∷ forget p φ)) (λ v → jump ck bs l₂ (v ∷ forget p φ))

  jump ck (bs ▷ t) Z φ = tail ck bs φ t
  jump ck (bs ▷ t) (S l) φ = jump ck bs l φ

  run ck (body bs t) φ = tail ck bs φ t

  call zero f w = timeout
  call (suc ck) (pack (code f) e) w = run ck (ds ! f) (w ∷ e ∷ [])

sem : Program → Semantics
sem (program {Σ} ds b) = semantics (Val Any) obs (λ ck → run ds ck b [])
  where open Vals Σ

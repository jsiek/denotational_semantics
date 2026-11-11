{-

  A clocked interpreter for CFGμ (FPC/Language/CFG.agda), the output of
  explicate control, as the one for CFGᵀ
  (ISWIM/Semantics/Interp/Typed/CFG.agda). A tail runs in a fixed frame
  that holds a value for each initialized slot, as in Impμ
  (FPC/Semantics/ClockedInterpreters/Imp.agda), and returns a value of the
  body's result type: return s gives the value of s; seq x s p t writes the
  value of s to slot x and runs t, in the frame without the slots that t
  does not start with (restrict p); case a x y l₁ l₂ writes the payload of a
  to slot x or y and jumps to l₁ or l₂. A tail runs with the blocks it may
  jump to, and block l with the blocks older than it, so the interpreter is
  structurally recursive on the clock, the blocks and the tail; only calls
  tick the clock.

-}

module FPC.Semantics.ClockedInterpreters.CFG where

open import FPC.Language.Type
open import FPC.Language.CFG
open import FPC.Framework.AllUtil using (All; []; _∷_; lookup)
open import FPC.Framework.Slots using (write; restrict; empty; params)
open import Semantics.Interp.Clock
open import FPC.Semantics.ClockedInterpreters.GlobalFun using (module Vals)
open import FPC.Semantics.ClockedInterpreters.Imp using (Fr; atom; eval-simple)

open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)

module _ {Σ : List DSig}
  (ds : All (λ s → Body Σ (DSig.cod s) (Args s)) Σ) where
  open Vals Σ

  tail : ∀ {R Δ Bs I} → ℕ → Blocks Σ R Δ Bs → Fr Δ I → Tail Σ R Δ Bs I
    → Result (Val R)
  jump : ∀ {R Δ Bs I} → ℕ → Blocks Σ R Δ Bs → Bs ∋ I → Fr Δ I
    → Result (Val R)
  run : ∀ {Δ A B} → ℕ → Body Σ B (A ∷ tup Δ ∷ []) → Val (tup Δ) → Val A
    → Result (Val B)
  call : ∀ {A B} → ℕ → Val (A ⇒ B) → Val A → Result (Val B)

  tail ck bs φ (return s) = eval-simple (call ck) φ s
  tail ck bs φ (seq x s p t) =
    do v ← eval-simple (call ck) φ s; tail ck bs (restrict p (write φ x v)) t
  tail ck bs φ (goto l) = jump ck bs l φ
  tail ck bs φ (case a x y l₁ l₂) =
    either (atom φ a) (λ v → jump ck bs l₁ (write φ x v))
      (λ v → jump ck bs l₂ (write φ y v))

  jump ck (bs ▷ t) Z φ = tail ck bs φ t
  jump ck (bs ▷ t) (S l) φ = jump ck bs l φ

  run ck (body Δ p bs t) v w = tail ck bs (params p v w) t

  call zero f w = timeout
  call (suc ck) (pack (code f) e) w = run ck (lookup ds f) e w

sem : ∀ {A} → Program A → Semantics
sem {A} (program {Σ} ds (body Δ p bs t)) =
  semantics (Val A) obs (λ ck → tail ds ck bs (empty Δ) t)
  where open Vals Σ

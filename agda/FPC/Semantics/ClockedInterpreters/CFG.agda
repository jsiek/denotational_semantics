{-

  A clocked interpreter for CFGμ (FPC/Language/CFG.agda), the output of
  explicate control, as the one for CFGᵀ (ISWIM/Semantics/Interp/Typed/CFG.agda).
  A tail runs in a frame typed by its context and returns a value of the
  body's result type: return s gives the value of s (as in Impμ,
  FPC/Semantics/ClockedInterpreters/Imp.agda); seq p s t pops the slots after those of
  Δ' (p : Δ' ⊑ Δ), pushes the value of s as the new slot, and
  runs t; case a p l₁ l₂ does so with the payload of a and jumps to l₁
  or l₂. A tail runs with the blocks it may jump to, and block l with
  the blocks older than it, so the interpreter is structurally recursive
  on the clock, the blocks and the tail; only calls tick the clock.

-}

module FPC.Semantics.ClockedInterpreters.CFG where

open import FPC.Language.Type
open import Framework.Lookup using (pop)
open import FPC.Language.CFG
open import FPC.Framework.AllUtil using (All; []; _∷_; lookup)
open import Semantics.Interp.Clock
open import FPC.Semantics.ClockedInterpreters.GlobalFun using (module Vals)
open import FPC.Semantics.ClockedInterpreters.Imp using (atom; eval-simple)

open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)

module _ {Σ : List DSig} (ds : All (λ s → Body Σ (DSig.cod s) (Args s)) Σ) where
  open Vals Σ

  tail : ∀ {R Bs Δ} → ℕ → Blocks Σ R Bs → Env Δ → Tail Σ R Bs Δ → Result (Val R)
  jump : ∀ {R Bs Δ} → ℕ → Blocks Σ R Bs → Bs ∋ Δ → Env Δ → Result (Val R)
  run : ∀ {R Δ} → ℕ → Body Σ R Δ → Env Δ → Result (Val R)
  call : ∀ {A B} → ℕ → Val (A ⇒ B) → Val A → Result (Val B)

  tail ck bs φ (return s) = eval-simple (call ck) φ s
  tail ck bs φ (seq p s t) = do v ← eval-simple (call ck) φ s; tail ck bs (v ∷ pop p φ) t
  tail ck bs φ (goto l) = jump ck bs l φ
  tail ck bs φ (case a p l₁ l₂) =
    either (atom φ a) (λ v → jump ck bs l₁ (v ∷ pop p φ)) (λ v → jump ck bs l₂ (v ∷ pop p φ))

  jump ck (bs ▷ t) Z φ = tail ck bs φ t
  jump ck (bs ▷ t) (S l) φ = jump ck bs l φ

  run ck (body bs t) φ = tail ck bs φ t

  call zero f w = timeout
  call (suc ck) (pack (code f) e) w = run ck (lookup ds f) (w ∷ e ∷ [])

sem : ∀ {A} → Program A → Semantics
sem {A} (program {Σ} ds b) = semantics (Val A) obs (λ ck → run ds ck b [])
  where open Vals Σ

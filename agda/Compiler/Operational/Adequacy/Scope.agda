open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _<_; s≤s; z≤n)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤; tt)
open import abt.Sig using (Sig; ν; ■; ∁)
open import abt.Var using (Var)

{-
  Well-scoped terms, for any signature (as WS in OptimizeSim.agda, for
  Clos2): WS k M when every variable of M is bound in a context of k
  variables, where a cleared argument (∁) is in a context of its own
  binders only. Renaming preserves it.
-}
module Compiler.Operational.Adequacy.Scope (Op : Set) (sig : Op → List Sig) where

open import abt.AbstractBindingTree Op sig using (`_; _⦅_⦆; ast; bind; clear; nil; cons)
  renaming (ABT to AST; Arg to Arg; Args to Args)
open import Compiler.Lang.Rename Op sig using (ext; rename; rename-arg; rename-args; shift)

WS : ℕ → AST → Set
WS-arg : ∀ {b} → ℕ → Arg b → Set
WS-args : ∀ {bs} → ℕ → Args bs → Set

WS k (` x) = x < k
WS k (op ⦅ args ⦆) = WS-args k args

WS-arg k (ast M) = WS k M
WS-arg k (bind a) = WS-arg (suc k) a
WS-arg k (clear a) = WS-arg 0 a

WS-args k nil = ⊤
WS-args k (cons a args) = WS-arg k a × WS-args k args

{- Renaming ----------------------------------------------------------------------}

Fits : ℕ → ℕ → (Var → Var) → Set
Fits k k' r = ∀ x → x < k → r x < k'

fits-ext : ∀ {k k' r} → Fits k k' r → Fits (suc k) (suc k') (ext r)
fits-ext h zero _ = s≤s z≤n
fits-ext h (suc x) (s≤s x<) = s≤s (h x x<)

ws-rename : ∀ {k k'} r M → Fits k k' r → WS k M → WS k' (rename r M)
ws-rename-arg : ∀ {k k' b} r (a : Arg b) → Fits k k' r → WS-arg k a → WS-arg k' (rename-arg r a)
ws-rename-args : ∀ {k k' bs} r (args : Args bs) → Fits k k' r → WS-args k args
  → WS-args k' (rename-args r args)

ws-rename r (` x) h w = h x w
ws-rename r (op ⦅ args ⦆) h w = ws-rename-args r args h w

ws-rename-arg r (ast M) h w = ws-rename r M h w
ws-rename-arg r (bind a) h w = ws-rename-arg (ext r) a (fits-ext h) w
ws-rename-arg r (clear a) h w = w

ws-rename-args r nil h w = tt
ws-rename-args r (cons a args) h (w , ws) = ws-rename-arg r a h w , ws-rename-args r args h ws

ws-shift : ∀ {k} M → WS k M → WS (suc k) (shift M)
ws-shift M = ws-rename suc M (λ x x< → s≤s x<)

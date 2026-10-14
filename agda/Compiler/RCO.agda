{-

  Typed remove complex operands (Clos5ᵀ → Monᵀ), after Essentials of
  Compilation, as the untyped pass (Untyped/Compiler/RCO.agda): every complex
  operand is bound to a fresh variable by a let, left to right, so the
  operands of every operation become atoms.

  atomize M ρ k gives the atom for the operand M to the continuation k:
  M itself if it is an atom, else a fresh variable bound to M by a let,
  in which case k runs under that let. k takes the renaming from the
  variables at the operand to those where the atom is used (the lets of
  later operands put it under more binders), so it is Kripke-style; the
  pass carries the renaming ρ of the source's variables to the target's.
  A case or let is a complex expression: its branches and body are
  translated in place, so nothing is duplicated.

-}

module Compiler.RCO where

open import Language.Typed.Type
open import Language.Typed.Clos5
import Language.Typed.Mon as M
open M using (Atm; Exp; var; lit; ref; atm; ren)

open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_) renaming (map to All-map)
open import Data.Nat using (ℕ)
open import Data.Vec using (Vec; []; _∷_)

Ren : Ctx → Ctx → Set
Ren Γ Δ = ∀ {A} → Γ ∋ A → Δ ∋ A

ext : ∀ {Γ Δ B} → Ren Γ Δ → Ren (B ∷ Γ) (B ∷ Δ)
ext r Z = Z
ext r (S x) = S (r x)

{- a continuation that takes an atom, under more binders -}
K : List ℕ → Ctx → Ty → Ty → Set
K Σ Δ A B = ∀ {Δ'} → Ren Δ Δ' → Atm Σ Δ' A → Exp Σ Δ' B

rco : ∀ {Σ Γ Δ A} → Tm Σ Γ A → Ren Γ Δ → Exp Σ Δ A
atomize : ∀ {Σ Γ Δ A B} → Tm Σ Γ A → Ren Γ Δ → K Σ Δ A B → Exp Σ Δ B
atomizes : ∀ {Σ Γ Δ n B} → Vec (Tm Σ Γ Any) n → Ren Γ Δ
  → (∀ {Δ'} → Ren Δ Δ' → Vec (Atm Σ Δ' Any) n → Exp Σ Δ' B) → Exp Σ Δ B
{- two operands -}
atomize₂ : ∀ {Σ Γ Δ A₁ A₂ B} → Tm Σ Γ A₁ → Tm Σ Γ A₂ → Ren Γ Δ
  → (∀ {Δ'} → Atm Σ Δ' A₁ → Atm Σ Δ' A₂ → Exp Σ Δ' B) → Exp Σ Δ B

rco (` x) ρ = atm (var (ρ x))
rco (fun-ref f) ρ = atm (ref f)
rco (pack L M) ρ = atomize₂ L M ρ M.pack
rco (callc L M) ρ = atomize₂ L M ρ M.callc
rco (lit B c) ρ = atm (lit B c)
rco (tuple Ms) ρ = atomizes Ms ρ λ _ as → M.tuple as
rco (get i N) ρ = atomize N ρ λ _ a → M.get i a
rco (inl N) ρ = atomize N ρ λ _ a → M.inl a
rco (inr N) ρ = atomize N ρ λ _ a → M.inr a
rco (case L N₁ N₂) ρ = atomize L ρ λ r a → M.case a (rco N₁ (ext λ x → r (ρ x))) (rco N₂ (ext λ x → r (ρ x)))
rco (prim p L N) ρ = atomize₂ L N ρ (M.prim p)
rco (let′ N₁ N₂) ρ = M.let′ (rco N₁ ρ) (rco N₂ (ext ρ))
rco (inject G N) ρ = atomize N ρ λ _ a → M.inject G a
rco (project t N) ρ = atomize N ρ λ _ a → M.project t a

atomize (` x) ρ k = k (λ y → y) (var (ρ x))
atomize (fun-ref f) ρ k = k (λ y → y) (ref f)
atomize (lit B c) ρ k = k (λ y → y) (lit B c)
atomize N ρ k = M.let′ (rco N ρ) (k S (var Z))

atomizes [] ρ k = k (λ y → y) []
atomizes (N ∷ Ns) ρ k =
  atomize N ρ λ r a → atomizes Ns (λ x → r (ρ x)) λ r' as → k (λ x → r' (r x)) (ren r' a ∷ as)

atomize₂ L N ρ k = atomize L ρ λ r a → atomize N (λ x → r (ρ x)) λ r' b → k (ren r' a) b

{- the pass, for a whole program -}
rco-program : Program → M.Program
rco-program (program ds N) = M.program (All-map (λ D → rco D (λ x → x)) ds) (rco N λ x → x)

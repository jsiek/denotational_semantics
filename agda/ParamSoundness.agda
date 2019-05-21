open import Data.Nat using (ℕ; zero; suc)
open import LambdaV using (Term; $; _·_; ƛ)
open LambdaV.AST using (Var; Z; S_; `_; extensionality; Subst; exts)

module ParamSoundness
  (Env : ℕ → Set)
  (Value : Set)
  (Sem : ℕ → Set₁)
  (ℰ : ∀{Γ} → Term Γ → Sem Γ)
  (ℰ-var : ∀ {Γ} {γ : Env Γ} {x} → ℰ (` x) γ (γ x))
  (_`,_ : ∀ {Γ} → Env Γ → Value → Env (suc Γ))
  (`ℰ : ∀{Δ Γ} → Subst Γ Δ → Env Δ → Env Γ → Set)
  where
 

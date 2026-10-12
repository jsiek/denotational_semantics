open import Data.List using (List; replicate)
open import Data.Nat using (ℕ; zero; suc; _+_; _<_; s≤s; z≤n)
open import Data.Nat.Properties using (+-suc; ≤-pred)
open import Data.Product using (_,_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (subst; sym)
open import Framework.abt.Sig using (Sig; ■)

{-
  Substitution preserves well-scopedness (WS, Syntax.Scope).
-}
module proof.Framework.Syntax.ScopeSubst (Op : Set) (sig : Op → List Sig) where

open import Framework.abt.AbstractBindingTree Op sig using (`_; _⦅_⦆; ast; bind; clear; nil; cons)
  renaming (ABT to AST; Arg to Arg; Args to Args)
open import proof.Framework.Syntax.ScopeRename Op sig using (WS; WS-arg; WS-args; ws-shift)
open import Framework.Syntax.Subst Op sig using (Subst; sub; sub-arg; sub-args; exts; extend; _•_)

{- σ maps the variables below k to terms well scoped in j -}
SFits : ℕ → ℕ → Subst → Set
SFits k j σ = ∀ x → x < k → WS j (σ x)

sfits-exts : ∀ {k j σ} → SFits k j σ → SFits (suc k) (suc j) (exts σ)
sfits-exts h zero _ = s≤s z≤n
sfits-exts {σ = σ} h (suc x) (s≤s x<) = ws-shift (σ x) (h x x<)

ws-sub : ∀ {k j} σ M → SFits k j σ → WS k M → WS j (sub σ M)
ws-sub-arg : ∀ {k j b} σ (a : Arg b) → SFits k j σ → WS-arg k a → WS-arg j (sub-arg σ a)
ws-sub-args : ∀ {k j bs} σ (as : Args bs) → SFits k j σ → WS-args k as → WS-args j (sub-args σ as)
ws-sub σ (` x) h w = h x w
ws-sub σ (op ⦅ as ⦆) h w = ws-sub-args σ as h w
ws-sub-arg σ (ast M) h w = ws-sub σ M h w
ws-sub-arg σ (bind a) h w = ws-sub-arg (exts σ) a (sfits-exts h) w
ws-sub-arg σ (clear a) h w = w
ws-sub-args σ nil h w = tt
ws-sub-args σ (cons a as) h (w , ws) = ws-sub-arg σ a h w , ws-sub-args σ as h ws

{- σ extended by well-scoped operands -}
sfits-extend : ∀ {n k j σ} (Ms : Args (replicate n ■)) → WS-args j Ms → SFits k j σ
  → SFits (n + k) j (extend Ms σ)
sfits-extend {zero} nil _ h = h
sfits-extend {suc n} {k} {σ = σ} (cons (ast M) Ms) (w , ws) h x x< =
  sfits-extend Ms ws h' x (subst (x <_) (sym (+-suc n k)) x<)
  where h' : SFits (suc k) _ (M • σ)
        h' zero _ = w
        h' (suc y) (s≤s y<) = h y y<

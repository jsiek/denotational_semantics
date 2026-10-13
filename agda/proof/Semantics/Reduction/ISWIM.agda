{-

  The values of the ISWIM reduction semantics (Semantics/Reduction/ISWIM.agda):
  they reduce to val, and substitution keeps them values; and closed
  programs (Closed) are well scoped.

-}

module proof.Semantics.Reduction.ISWIM where

open import Semantics.Reduction.ISWIM public
open import Language.ISWIM
open import Semantics.Reduction.Smallstep using (val)
open import Framework.Syntax.SyntaxUtil using (_,,_; Nil; ⟩_,,_)
open import Framework.Syntax.Subst Op sig using (sub; sub-args)
open import Framework.Syntax.Uses Op sig using (bound; bound-args)
open import Framework.Syntax.Scope Op sig using (WS; WS-args)
open import Compiler.EncloseScope using (Closed)

open import Data.List using (replicate)
open import Data.Nat using (zero; suc; _≤_; _⊔_; _∸_; s≤s; z≤n)
open import Data.Nat.Properties using (m⊔n≤o⇒m≤o; m⊔n≤o⇒n≤o; ≤-trans; m≤n+m∸n)
open import Data.Product using (_,_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

data Value : AST → Set
infixr 5 _∷_
data Values : ∀ {n} → Args (replicate n ■) → Set

data Value where
  lam : ∀ {N} → Value (lam ⦅ ⟩ N ,, Nil ⦆)
  lit : ∀ {B k} → Value (lit B k ⦅ Nil ⦆)
  tuple : ∀ {n as} → Values as → Value (tuple n ⦅ as ⦆)
  inl : ∀ {V} → Value V → Value (inl-op ⦅ V ,, Nil ⦆)
  inr : ∀ {V} → Value V → Value (inr-op ⦅ V ,, Nil ⦆)

data Values where
  [] : Values Nil
  _∷_ : ∀ {n V} {as : Args (replicate n ■)} → Value V → Values as → Values (V ,, as)

value-red : ∀ {V} → Value V → red V ≡ val
values-red : ∀ {n} {as : Args (replicate n ■)} → Values as → red-args as ≡ val
value-red lam = refl
value-red lit = refl
value-red (tuple vs) rewrite values-red vs = refl
value-red (inl v) rewrite value-red v = refl
value-red (inr v) rewrite value-red v = refl
values-red [] = refl
values-red (v ∷ vs) rewrite value-red v | values-red vs = refl

{- a closed program is well scoped -}
private
  l : ∀ m n {o} → m ⊔ n ≤ o → m ≤ o
  l m n = m⊔n≤o⇒m≤o m n
  r : ∀ m n {o} → m ⊔ n ≤ o → n ≤ o
  r m n = m⊔n≤o⇒n≤o m n
  bind≤ : ∀ m {k} → m ∸ 1 ≤ k → m ≤ suc k
  bind≤ m le = ≤-trans (m≤n+m∸n m 1) (s≤s le)

bound-ws : ∀ {k} M → bound M ≤ k → WS k M
bound-ws-args : ∀ {k n} (as : Args (replicate n ■)) → bound-args as ≤ k → WS-args k as
bound-ws (` x) le = le
bound-ws (lam ⦅ ⟩ N ,, Nil ⦆) le = bound-ws N (bind≤ (bound N) (l (bound N ∸ 1) 0 le)) , tt
bound-ws (app ⦅ L ,, M ,, Nil ⦆) le =
  bound-ws L (l (bound L) _ le) , bound-ws M (l (bound M) 0 (r (bound L) (bound M ⊔ 0) le)) , tt
bound-ws (lit B k ⦅ Nil ⦆) le = tt
bound-ws (tuple n ⦅ as ⦆) le = bound-ws-args as le
bound-ws (get i ⦅ M ,, Nil ⦆) le = bound-ws M (l (bound M) 0 le) , tt
bound-ws (inl-op ⦅ M ,, Nil ⦆) le = bound-ws M (l (bound M) 0 le) , tt
bound-ws (inr-op ⦅ M ,, Nil ⦆) le = bound-ws M (l (bound M) 0 le) , tt
bound-ws (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) le =
  bound-ws L (l (bound L) _ le)
  , bound-ws M (bind≤ (bound M) (l (bound M ∸ 1) _ le₁))
  , bound-ws N (bind≤ (bound N) (l (bound N ∸ 1) 0 (r (bound M ∸ 1) _ le₁)))
  , tt
  where le₁ = r (bound L) ((bound M ∸ 1) ⊔ ((bound N ∸ 1) ⊔ 0)) le
bound-ws (prim p ⦅ L ,, M ,, Nil ⦆) le =
  bound-ws L (l (bound L) _ le) , bound-ws M (l (bound M) 0 (r (bound L) (bound M ⊔ 0) le)) , tt
bound-ws-args {n = zero} Nil le = tt
bound-ws-args {n = suc n} (M ,, as) le = bound-ws M (l (bound M) (bound-args as) le) , bound-ws-args as (r (bound M) (bound-args as) le)

closed-ws : ∀ {M} → Closed M → WS 0 M
closed-ws {M} c = bound-ws M (subst (_≤ 0) (sym c) z≤n)

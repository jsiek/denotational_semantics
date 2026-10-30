{-

  capture produces well-scoped Clos2 programs (WS 0,
  Framework/Syntax/Scope.agda) from closed ISWIM programs (Closed,
  Compiler/CaptureScope.agda). The
  simulation and interpreter proofs of prune need well-scoped
  programs; the adequacy proof for Clos5 also uses this.

-}

module Untyped.proof.Compiler.CaptureScope where

open import Compiler.CaptureScope public

open import Framework.Syntax.SyntaxUtil using (_,,_; Nil; ⟩_,,_)
open import Untyped.Language.Clos2 using (AST; Op; sig; ■)
import Language.ISWIM as I
open import Framework.Syntax.Uses I.Op I.sig using (bound; bound-args)
open import Framework.Syntax.Scope Op sig using (WS; WS-arg; WS-args)
open import Untyped.Compiler.Prune using (bind-n-ast)
open import Untyped.Compiler.Capture using (capture; enc-args; fv-vars)

open import Data.List using (replicate)
open import Data.Nat using (zero; suc; _+_; _∸_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties
  using (≤-trans; n≤1+n; +-suc; +-identityʳ; m≤n+m∸n; m⊔n≤o⇒m≤o; m⊔n≤o⇒n≤o)
open import Data.Product using (_,_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; sym; subst)

{- capture of a closed ISWIM program is well scoped -}
module Captured where
  open I using (`_; _⦅_⦆; lam; app; lit; tuple; get; inl-op; inr-op; case-op; prim; let-op)

  bind-n-ws : ∀ m k N → WS (suc (m + k)) N → WS-arg k (bind-n-ast m N)
  bind-n-ws zero k N w = w
  bind-n-ws (suc m) k N w = bind-n-ws m (suc k) N (subst (λ x → WS (suc x) N) (sym (+-suc m k)) w)

  fv-vars-ws : ∀ m {k} → m ≤ k → WS-args k (fv-vars m)
  fv-vars-ws zero _ = tt
  fv-vars-ws (suc m) le = le , fv-vars-ws m (≤-trans (n≤1+n m) le)

  ⊔ˡ = m⊔n≤o⇒m≤o
  ⊔ʳ = m⊔n≤o⇒n≤o

  {- under one binder -}
  ∸1 : ∀ {k} b → b ∸ 1 ≤ k → b ≤ suc k
  ∸1 b le = ≤-trans (m≤n+m∸n b 1) (s≤s le)

  capture-ws : ∀ {k} (M : I.AST) → bound M ≤ k → WS k (capture M)
  enc-args-ws : ∀ {n k} (args : I.Args (replicate n ■)) → bound-args args ≤ k
    → WS-args k (enc-args args)

  capture-ws (` x) b = b
  capture-ws (lam ⦅ ⟩ N ,, Nil ⦆) b =
    bind-n-ws (bound N ∸ 1) 0 (capture N)
      (capture-ws N (subst (λ x → bound N ≤ suc x) (sym (+-identityʳ _)) (m≤n+m∸n (bound N) 1)))
    , fv-vars-ws (bound N ∸ 1) (⊔ˡ _ _ b)
  capture-ws (app ⦅ L ,, M ,, Nil ⦆) b =
    capture-ws L (⊔ˡ _ _ b) , capture-ws M (⊔ˡ _ _ (⊔ʳ (bound L) _ b)) , tt
  capture-ws (lit B k ⦅ Nil ⦆) b = tt
  capture-ws (tuple n ⦅ args ⦆) b = enc-args-ws args b
  capture-ws (get i ⦅ M ,, Nil ⦆) b = capture-ws M (⊔ˡ _ _ b) , tt
  capture-ws (inl-op ⦅ M ,, Nil ⦆) b = capture-ws M (⊔ˡ _ _ b) , tt
  capture-ws (inr-op ⦅ M ,, Nil ⦆) b = capture-ws M (⊔ˡ _ _ b) , tt
  capture-ws (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) b =
    capture-ws L (⊔ˡ _ _ b)
    , capture-ws M (∸1 (bound M) (⊔ˡ _ _ (⊔ʳ (bound L) _ b)))
    , capture-ws N (∸1 (bound N) (⊔ˡ _ _ (⊔ʳ (bound M ∸ 1) _ (⊔ʳ (bound L) _ b))))
    , tt
  capture-ws (prim p ⦅ L ,, M ,, Nil ⦆) b =
    capture-ws L (⊔ˡ _ _ b) , capture-ws M (⊔ˡ _ _ (⊔ʳ (bound L) _ b)) , tt
  capture-ws (let-op ⦅ M ,, ⟩ N ,, Nil ⦆) b =
    capture-ws M (⊔ˡ _ _ b) , capture-ws N (∸1 (bound N) (⊔ˡ _ _ (⊔ʳ (bound M) _ b))) , tt

  enc-args-ws {zero} Nil b = tt
  enc-args-ws {suc n} (M ,, args) b = capture-ws M (⊔ˡ _ _ b) , enc-args-ws args (⊔ʳ (bound M) _ b)

capture-closed : ∀ M → Closed M → WS 0 (capture M)
capture-closed M c = Captured.capture-ws M (subst (_≤ 0) (sym c) z≤n)

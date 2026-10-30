{-

  simplify keeps programs closed (simplify-closed), which the operational
  proofs of the compiler need for capture (Closed) and for the scoping of
  its output (compile-scoped). By induction on the term, simp keeps
  terms well scoped (WS) when what it knows of the variables is (Fits).

-}

module proof.Compiler.SimplifyScope where

open import Language.ISWIM
import Language.Prim
open import Language.Prim using (int; bool)
open import Compiler.Simplify
open import Compiler.CaptureScope using (Closed)
open import proof.Compiler.SimplifyFacts using (comp-inv; branch-inl; branch-inr)
open import Framework.Syntax.Uses Op sig using (bound; bound-args)
open import Data.Nat using (_≤_; _⊔_; _∸_)
open import Data.Nat.Properties using (m⊔n≤o⇒m≤o; m⊔n≤o⇒n≤o; ≤-trans; m≤n+m∸n)
open import Framework.Syntax.SyntaxUtil using (_,,_; Nil; ⟩_,,_)
open import proof.Framework.Syntax.Scope Op sig using (WS; WS-args; ws-bound)
open import proof.Framework.Syntax.ScopeRename Op sig using (ws-shift)
open import Framework.Syntax.Rename Op sig using (shift)
open import Framework.ListUtil using (proj; args→list; has-length)

open import Data.Bool using (true; false)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (replicate)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; zero; suc; _<_; s≤s; z≤n; _≤ᵇ_)
open import Data.Nat.Properties using (n≤0⇒n≡0)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ-syntax)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

{- Closed programs ---------------------------------------------------------------}

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
bound-ws (let-op ⦅ M ,, ⟩ N ,, Nil ⦆) le =
  bound-ws M (l (bound M) _ le) , bound-ws N (bind≤ (bound N) (l (bound N ∸ 1) 0 (r (bound M) _ le))) , tt
bound-ws-args {n = zero} Nil le = tt
bound-ws-args {n = suc n} (M ,, as) le = bound-ws M (l (bound M) (bound-args as) le) , bound-ws-args as (r (bound M) (bound-args as) le)

closed-ws : ∀ {M} → Closed M → WS 0 M
closed-ws {M} c = bound-ws M (subst (_≤ 0) (sym c) z≤n)

{- an Info is well scoped: its term, and what it is known to be -}
record WSI (j : ℕ) (I : Info) : Set
record Fits (k j : ℕ) (E : Facts) : Set
WSK : ℕ → Known → Set

record WSI j I where
  inductive
  pattern
  constructor wsi
  field
    tm : WS j (term I)
    kn : ∀ {K} → known I ≡ just K → WSK j K
open WSI

{- what simp knows of the variables below k is well scoped in j -}
record Fits k j E where
  inductive
  pattern
  constructor fits
  field at : ∀ x → x < k → WSI j (E x)
open Fits

WSK j (val V) = WS j V
WSK j (fun N E) = Σ[ k ∈ ℕ ] WS (suc k) N × Fits k j E

wsi-self : ∀ {j V} → WS j V → WSI j (self V)
wsi-self w = wsi w λ { refl → w }

wsi-info : ∀ {j} M → WS j M → WSI j (info M)
wsi-info M w with value M
... | true = wsi w λ { refl → w }
... | false = wsi w λ ()

wsi-shift : ∀ {j} I → WSI j I → WSI (suc j) (shift-info I)
wsk-shift : ∀ {j} K → WSK j K → WSK (suc j) (shift-known K)
wsi-shift (T ∣ just K) (wsi w k) = wsi (ws-shift T w) λ { refl → wsk-shift K (k refl) }
wsi-shift (T ∣ nothing) (wsi w k) = wsi (ws-shift T w) λ ()
wsk-shift (val V) w = ws-shift V w
wsk-shift (fun N E) (k , wN , fits f) = k , wN , fits (λ x x< → wsi-shift (E x) (f x x<))

fits-under : ∀ {k j E} → Fits k j E → Fits (suc k) (suc j) (under E)
fits-under {E = E} f = fits λ { zero _ → wsi-self (s≤s z≤n) ; (suc x) (s≤s x<) → wsi-shift (E x) (at f x x<) }

fits-known-as : ∀ {k j E I} → Fits k j E → WSI j I → Fits (suc k) (suc j) (known-as I E)
fits-known-as {E = E} {I} f sI =
  fits λ { zero _ → wsi (s≤s z≤n) (kn (wsi-shift I sI)) ; (suc x) (s≤s x<) → wsi-shift (E x) (at f x x<) }

fits-• : ∀ {k j E I} → Fits k j E → WSI j I → Fits (suc k) j (I • E)
fits-• f sI = fits λ { zero _ → sI ; (suc x) (s≤s x<) → at f x x< }

ws-proj : ∀ {j n m} (i : Fin n) (as : Args (replicate m ■)) {V} → WS-args j as → proj i (args→list as) ≡ just V → WS j V
ws-proj {n = suc n} {suc m} zero (K ,, as) (w , _) e with has-length n (args→list as)
ws-proj {n = suc n} {suc m} zero (K ,, as) (w , _) refl | true = w
ws-proj {m = suc m} (suc i) (K ,, as) (_ , ws) e = ws-proj i as ws e

ws-prim-term : ∀ {j} o → WS j (prim-term o)
ws-prim-term (int n) = tt
ws-prim-term (bool true) = tt , tt
ws-prim-term (bool false) = tt , tt

simp-ws : ∀ fl M {k j E} → WS k M → Fits k j E → WSI j (simp fl E M)
simp-ws-args : ∀ {n} fl (as : Args (replicate n ■)) {k j E} → WS-args k as → Fits k j E → WS-args j (simp-args fl E as)
app-ws : ∀ fl L M {k j E I} → WS k L → WSI j I → Fits k j E → WSI j (simp-app fl E L I)
let-ws : ∀ fl N {k j E I} → WS (suc k) N → WSI j I → Fits k j E → WSI j (simp-let fl E N I)
call-ws : ∀ fl J I {j} → WSI j J → WSI j I → WSI j (simp-call fl J I)

simp-ws fl (` x) w f = at f x w
simp-ws fl (lam ⦅ ⟩ N ,, Nil ⦆) {k} (w , _) f = wsi (tm (simp-ws fl N w (fits-under f)) , tt) λ { refl → k , w , f }
simp-ws fl (app ⦅ L ,, M ,, Nil ⦆) (wL , wM , _) f = app-ws fl L M wL (simp-ws fl M wM f) f
simp-ws fl (lit B k ⦅ Nil ⦆) w f = wsi-self tt
simp-ws fl (tuple n ⦅ as ⦆) w f = wsi-info _ (simp-ws-args fl as w f)
simp-ws fl (get i ⦅ L ,, Nil ⦆) {E = E} (w , _) f with simp-ws fl L w f | component i (known (simp fl E L)) in c
... | wL | nothing = wsi (tm wL , tt) λ ()
... | wL | just K with comp-inv i (known (simp fl E L)) c
...   | m , Ks , k , p with small K
...     | true = wsi-self (ws-proj i Ks (kn wL k) p)
...     | false = wsi (tm wL , tt) λ { refl → ws-proj i Ks (kn wL k) p }
simp-ws fl (inl-op ⦅ M ,, Nil ⦆) (w , _) f = wsi-info _ (tm (simp-ws fl M w f) , tt)
simp-ws fl (inr-op ⦅ M ,, Nil ⦆) (w , _) f = wsi-info _ (tm (simp-ws fl M w f) , tt)
simp-ws fl (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) {E = E} (wL , wM , wN , _) f with simp-ws fl L wL f | branch (known (simp fl E L)) in b
... | sL | nothing =
  wsi (tm sL , tm (simp-ws fl M wM (fits-under f)) , tm (simp-ws fl N wN (fits-under f)) , tt) λ ()
... | sL | just (true , K) = simp-ws fl M wM (fits-• f (wsi-self (proj₁ (kn sL (proj₁ (branch-inl (known (simp fl E L)) b))))))
... | sL | just (false , K) = simp-ws fl N wN (fits-• f (wsi-self (proj₁ (kn sL (proj₁ (branch-inr (known (simp fl E L)) b))))))
simp-ws fl (prim p ⦅ L ,, M ,, Nil ⦆) {E = E} (wL , wM , _) f with int-of (known (simp fl E L))
... | nothing = wsi (tm (simp-ws fl L wL f) , tm (simp-ws fl M wM f) , tt) λ ()
... | just n with int-of (known (simp fl E M))
...   | nothing = wsi (tm (simp-ws fl L wL f) , tm (simp-ws fl M wM f) , tt) λ ()
...   | just m = wsi-self (ws-prim-term (Language.Prim.δ p n m))

simp-ws fl (let-op ⦅ M ,, ⟩ N ,, Nil ⦆) (wM , wN , _) f = let-ws fl N wN (simp-ws fl M wM f) f

simp-ws-args {zero} fl Nil w f = tt
simp-ws-args {suc n} fl (M ,, as) (w , ws) f = tm (simp-ws fl M w f) , simp-ws-args fl as ws f

app-ws fl L M wL sI f with lam? L
... | is-lam N = let-ws fl N (proj₁ wL) sI f
... | other = call-ws fl _ _ (simp-ws fl L wL f) sI

let-ws fl N {E = E} {I} wN sI f with small (term I) | value (term I)
... | true | _ = simp-ws fl N wN (fits-• f sI)
... | false | true = wsi (tm sI , tm (simp-ws fl N wN (fits-known-as f sI)) , tt) λ ()
... | false | false = wsi (tm sI , tm (simp-ws fl N wN (fits-under f)) , tt) λ ()

call-ws (suc fl) (T ∣ just (fun N E)) I (wsi wT kn) sI with size (term (simp-let fl E N I)) ≤ᵇ inline-size
... | true = let-ws fl N (proj₁ (proj₂ (kn refl))) sI (proj₂ (proj₂ (kn refl)))
... | false = wsi (wT , tm sI , tt) λ ()
call-ws zero J I sJ sI = wsi (tm sJ , tm sI , tt) λ ()
call-ws (suc fl) (T ∣ nothing) I sJ sI = wsi (tm sJ , tm sI , tt) λ ()
call-ws (suc fl) (T ∣ just (val K)) I sJ sI = wsi (tm sJ , tm sI , tt) λ ()

{- simplify keeps programs closed -}
simplify-closed : ∀ M → Closed M → Closed (simplify M)
simplify-closed M c = n≤0⇒n≡0 (ws-bound (simplify M) (tm (simp-ws inline-fuel M (closed-ws {M} c) (fits (λ x ())))))

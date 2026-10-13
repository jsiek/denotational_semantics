{-

  simplify keeps programs closed (simplify-closed), which the operational
  proofs of the compiler need for enclose (Closed) and for the scoping of
  its output (compile-scoped). By induction on the term, simp keeps
  terms well scoped (WS) when what it knows of the variables is (Fits).

-}

module proof.Compiler.SimplifyScope where

open import Language.ISWIM
import Language.Prim
open import Language.Prim using (int; bool)
open import Compiler.Simplify
open import Compiler.EncloseScope using (Closed)
open import proof.Compiler.SimplifyFacts using (closed-ws; comp-inv; branch-inl; branch-inr)
open import Framework.Syntax.SyntaxUtil using (_,,_; Nil; ⟩_,,_)
open import proof.Framework.Syntax.Scope Op sig using (WS; WS-args; ws-bound)
open import proof.Framework.Syntax.ScopeRename Op sig using (ws-shift)
open import Framework.Syntax.Rename Op sig using (shift)
open import Framework.ListUtil using (proj; args→list; has-length)

open import Data.Bool using (true; false)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (replicate)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; zero; suc; _<_; s≤s; z≤n)
open import Data.Nat.Properties using (n≤0⇒n≡0)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

{- an Info is well scoped: its term, and its known value -}
record WSI (j : ℕ) (I : Info) : Set where
  constructor wsi
  field
    tm : WS j (term I)
    kn : ∀ {K} → known I ≡ just K → WS j K
open WSI

{- what simp knows of the variables below k is well scoped in j -}
record Fits (k j : ℕ) (E : Facts) : Set where
  constructor fits
  field at : ∀ x → x < k → WSI j (E x)
open Fits

wsi-self : ∀ {j V} → WS j V → WSI j (self V)
wsi-self w = wsi w λ { refl → w }

wsi-info : ∀ {j} M → WS j M → WSI j (info M)
wsi-info M w with value M
... | true = wsi w λ { refl → w }
... | false = wsi w λ ()

wsi-shift : ∀ {j} I → WSI j I → WSI (suc j) (shift-info I)
wsi-shift (T ∣ just K) (wsi w k) = wsi (ws-shift T w) λ { refl → ws-shift K (k refl) }
wsi-shift (T ∣ nothing) (wsi w k) = wsi (ws-shift T w) λ ()

fits-under : ∀ {k j E} → Fits k j E → Fits (suc k) (suc j) (under E)
fits-under {E = E} f = fits λ { zero _ → wsi-self (s≤s z≤n) ; (suc x) (s≤s x<) → wsi-shift (E x) (at f x x<) }

fits-self : ∀ {k j E V} → Fits k j E → WS j V → Fits (suc k) j (self V • E)
fits-self f w = fits λ { zero _ → wsi-self w ; (suc x) (s≤s x<) → at f x x< }

ws-proj : ∀ {j n m} (i : Fin n) (as : Args (replicate m ■)) {V} → WS-args j as → proj i (args→list as) ≡ just V → WS j V
ws-proj {n = suc n} {suc m} zero (K ,, as) (w , _) e with has-length n (args→list as)
ws-proj {n = suc n} {suc m} zero (K ,, as) (w , _) refl | true = w
ws-proj {m = suc m} (suc i) (K ,, as) (_ , ws) e = ws-proj i as ws e

ws-prim-term : ∀ {j} o → WS j (prim-term o)
ws-prim-term (int n) = tt
ws-prim-term (bool true) = tt , tt
ws-prim-term (bool false) = tt , tt

simp-ws : ∀ M {k j E} → WS k M → Fits k j E → WSI j (simp E M)
simp-ws-args : ∀ {n} (as : Args (replicate n ■)) {k j E} → WS-args k as → Fits k j E → WS-args j (simp-args E as)
app-ws : ∀ L M {k j E I} → WS k L → WSI j I → Fits k j E → WSI j (simp-app E L I)
app-dflt : ∀ L {k j E I} → WS k L → WSI j I → Fits k j E → WSI j (app ⦅ term (simp E L) ,, term I ,, Nil ⦆ ∣ nothing)
app-dflt L wL sI f = wsi (tm (simp-ws L wL f) , tm sI , tt) λ ()

simp-ws (` x) w f = at f x w
simp-ws (lam ⦅ ⟩ N ,, Nil ⦆) (w , _) f = wsi-self (tm (simp-ws N w (fits-under f)) , tt)
simp-ws (app ⦅ L ,, M ,, Nil ⦆) (wL , wM , _) f = app-ws L M wL (simp-ws M wM f) f
simp-ws (lit B k ⦅ Nil ⦆) w f = wsi-self tt
simp-ws (tuple n ⦅ as ⦆) w f = wsi-info _ (simp-ws-args as w f)
simp-ws (get i ⦅ L ,, Nil ⦆) {E = E} (w , _) f with simp-ws L w f | component i (known (simp E L)) in c
... | wL | nothing = wsi (tm wL , tt) λ ()
... | wL | just K with comp-inv i (known (simp E L)) c
...   | m , Ks , k , p with small K
...     | true = wsi-self (ws-proj i Ks (kn wL k) p)
...     | false = wsi (tm wL , tt) λ { refl → ws-proj i Ks (kn wL k) p }
simp-ws (inl-op ⦅ M ,, Nil ⦆) (w , _) f = wsi-info _ (tm (simp-ws M w f) , tt)
simp-ws (inr-op ⦅ M ,, Nil ⦆) (w , _) f = wsi-info _ (tm (simp-ws M w f) , tt)
simp-ws (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) {E = E} (wL , wM , wN , _) f with simp-ws L wL f | branch (known (simp E L)) in b
... | sL | nothing =
  wsi (tm sL , tm (simp-ws M wM (fits-under f)) , tm (simp-ws N wN (fits-under f)) , tt) λ ()
... | sL | just (true , K) = simp-ws M wM (fits-self f (proj₁ (kn sL (proj₁ (branch-inl (known (simp E L)) b)))))
... | sL | just (false , K) = simp-ws N wN (fits-self f (proj₁ (kn sL (proj₁ (branch-inr (known (simp E L)) b)))))
simp-ws (prim p ⦅ L ,, M ,, Nil ⦆) {E = E} (wL , wM , _) f with int-of (known (simp E L))
... | nothing = wsi (tm (simp-ws L wL f) , tm (simp-ws M wM f) , tt) λ ()
... | just n with int-of (known (simp E M))
...   | nothing = wsi (tm (simp-ws L wL f) , tm (simp-ws M wM f) , tt) λ ()
...   | just m = wsi-self (ws-prim-term (Language.Prim.δ p n m))

simp-ws-args {zero} Nil w f = tt
simp-ws-args {suc n} (M ,, as) (w , ws) f = tm (simp-ws M w f) , simp-ws-args as ws f

app-ws (lam ⦅ ⟩ N ,, Nil ⦆) M {j = j} {E} {I} (wN , _) sI f with small (term I) | value (term I)
... | true | _ = simp-ws N wN (fits-self f (tm sI))
... | false | true = wsi ((tm (simp-ws N wN f') , tt) , tm sI , tt) λ ()
  where
  f' : Fits _ (suc j) (((` 0) ∣ just (shift (term I))) • (λ x → shift-info (E x)))
  f' = fits λ { zero _ → wsi (s≤s z≤n) λ { refl → ws-shift (term I) (tm sI) } ; (suc x) (s≤s x<) → wsi-shift (E x) (at f x x<) }
... | false | false = wsi ((tm (simp-ws N wN (fits-under f)) , tt) , tm sI , tt) λ ()
app-ws L@(` x) M wL sI f = app-dflt L wL sI f
app-ws L@(app ⦅ _ ⦆) M wL sI f = app-dflt L wL sI f
app-ws L@(lit B k ⦅ _ ⦆) M wL sI f = app-dflt L wL sI f
app-ws L@(tuple n ⦅ _ ⦆) M wL sI f = app-dflt L wL sI f
app-ws L@(get i ⦅ _ ⦆) M wL sI f = app-dflt L wL sI f
app-ws L@(inl-op ⦅ _ ⦆) M wL sI f = app-dflt L wL sI f
app-ws L@(inr-op ⦅ _ ⦆) M wL sI f = app-dflt L wL sI f
app-ws L@(case-op ⦅ _ ⦆) M wL sI f = app-dflt L wL sI f
app-ws L@(prim p ⦅ _ ⦆) M wL sI f = app-dflt L wL sI f

{- simplify keeps programs closed -}
simplify-closed : ∀ M → Closed M → Closed (simplify M)
simplify-closed M c = n≤0⇒n≡0 (ws-bound (simplify M) (tm (simp-ws M (closed-ws {M} c) (fits (λ x ())))))

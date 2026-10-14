{-

  Cast insertion (ISWIM → ISWIMᵀ), after Essentials of Compilation, ch. 9:
  every term of ISWIM becomes a term of type Any.

  * A value is injected with its flat type:
      λx. N ⇒ inject fun (lam N'),   (M₁, …, Mₙ) ⇒ inject (tup n) (tuple …).
  * An operation projects its operand to the flat type it needs, at the
    point where the ISWIM machine checks it:
      (L M) ⇒ app (project fun L') M'        (the operator, before M),
      get i L ⇒ get i (project (tup n) L'),  case L … ⇒ case (project sum L') …
  * A primitive checks both operands after it has evaluated them both, so
    they are let-bound first:
      prim p L M ⇒ let x = L' in let y = M' in
                     inject (out-flat p) (prim p (project Int x) (project Int y)).

  The pass is defined on well-scoped terms (WS k M: a closed program is
  WS 0, Compiler/EncloseScope.agda), so every variable becomes a typed
  one. It carries a renaming r of the variables, for the variable that
  the let of a primitive adds around its second operand.

-}

module Compiler.Typed.Cast where

open import Framework.Syntax.SyntaxUtil using (_,,_; Nil; ⟩_,,_)
open import Language.ISWIM
open import Framework.Syntax.Scope Op sig using (WS; WS-args)
open import Language.Typed.Type
import Language.Typed.ISWIM as T

open import Data.Fin using (Fin; zero; suc; fromℕ<)
open import Data.List using (replicate)
open import Data.Nat using (ℕ; suc)
open import Data.Vec using (Vec; []; _∷_)
open import Framework.Primitives using (Int)
open import Data.Product using (_,_)

{- the renaming for the body of a binder -}
ext : ∀ {k k'} → (Fin k → Fin k') → Fin (suc k) → Fin (suc k')
ext r zero = zero
ext r (suc x) = suc (r x)

cast : ∀ {k k'} → (Fin k → Fin k') → (M : AST) → WS k M → T.Tm k' Any
casts : ∀ {k k' n} → (Fin k → Fin k') → (Ms : Args (replicate n ■)) → WS-args k Ms
  → Vec (T.Tm k' Any) n

cast r (` x) x<k = T.` r (fromℕ< x<k)
cast r (lam ⦅ ⟩ N ,, Nil ⦆) (w , _) = T.inject fun (T.lam (cast (ext r) N w))
cast r (app ⦅ L ,, M ,, Nil ⦆) (wL , wM , _) = T.app (T.project fun (cast r L wL)) (cast r M wM)
cast r (lit B k ⦅ Nil ⦆) _ = T.inject (base B) (T.lit B k)
cast r (tuple n ⦅ Ms ⦆) w = T.inject (tup n) (T.tuple (casts r Ms w))
cast r (get {n} i ⦅ M ,, Nil ⦆) (w , _) = T.get i (T.project (tup n) (cast r M w))
cast r (inl-op ⦅ M ,, Nil ⦆) (w , _) = T.inject sum (T.inl (cast r M w))
cast r (inr-op ⦅ M ,, Nil ⦆) (w , _) = T.inject sum (T.inr (cast r M w))
cast r (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) (wL , wM , wN , _) =
  T.case (T.project sum (cast r L wL)) (cast (ext r) M wM) (cast (ext r) N wN)
cast r (prim p ⦅ L ,, M ,, Nil ⦆) (wL , wM , _) =
  T.let′ (cast r L wL) (T.let′ (cast (λ x → suc (r x)) M wM)
    (T.inject (out-flat p) (T.prim p (T.project (base Int) (T.` suc zero))
                                     (T.project (base Int) (T.` zero)))))
cast r (let-op ⦅ M ,, ⟩ N ,, Nil ⦆) (wM , wN , _) = T.let′ (cast r M wM) (cast (ext r) N wN)

casts {n = ℕ.zero} r Nil _ = []
casts {n = suc n} r (M ,, Ms) (w , ws) = cast r M w ∷ casts r Ms ws

{- the pass, for a whole (well-scoped, closed) program -}
cast-program : (M : AST) → WS 0 M → T.Tm 0 Any
cast-program = cast (λ x → x)

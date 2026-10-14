{-

  Cast insertion (ISWIM → ISWIMᵀ), after Essentials of Compilation, ch. 9:
  every term of ISWIM becomes a term of type Any.

  * A value is injected with its flat type:
      λx. N ⇒ inject fun (lam N'),   (M₁, …, Mₙ) ⇒ inject (tup n) (tuple …).
  * An operation projects its operand to the flat type it needs, at the
    point where the ISWIM machine checks it:
      (L M) ⇒ app (project tfun L') M'        (the operator, before M),
      get i L ⇒ get i (project (ttup n i) L'),  case L … ⇒ case (project tsum L') …
  * A primitive checks both operands after it has evaluated them both, so
    they are let-bound first:
      prim p L M ⇒ let x = L' in let y = M' in
                     inject (out-flat p) (prim p (project tint x) (project tint y)).

  The pass is defined on well-scoped terms (WS k M: a closed program is
  WS 0, Compiler/EncloseScope.agda), so every variable becomes a typed
  one. It carries a renaming r of the variables, for the variable that
  the let of a primitive adds around its second operand.

-}

module Compiler.Typed.Cast where

open import Framework.Syntax.SyntaxUtil using (_,,_; Nil; ⟩_,,_)
open import Language.ISWIM
open import Framework.Syntax.Scope Op sig using (WS; WS-args)
open import Framework.Syntax.ScopeDec Op sig using (ws?)
open import Relation.Nullary using (yes; no)
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
cast r (app ⦅ L ,, M ,, Nil ⦆) (wL , wM , _) = T.app (T.project tfun (cast r L wL)) (cast r M wM)
cast r (lit B k ⦅ Nil ⦆) _ = T.inject (base B) (T.lit B k)
cast r (tuple n ⦅ Ms ⦆) w = T.inject (tup n) (T.tuple (casts r Ms w))
cast r (get {suc n} i ⦅ M ,, Nil ⦆) (w , _) = T.get i (T.project (ttup n i) (cast r M w))
cast r (inl-op ⦅ M ,, Nil ⦆) (w , _) = T.inject sum (T.inl (cast r M w))
cast r (inr-op ⦅ M ,, Nil ⦆) (w , _) = T.inject sum (T.inr (cast r M w))
cast r (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) (wL , wM , wN , _) =
  T.case (T.project tsum (cast r L wL)) (cast (ext r) M wM) (cast (ext r) N wN)
cast r (prim p ⦅ L ,, M ,, Nil ⦆) (wL , wM , _) =
  T.let′ (cast r L wL) (T.let′ (cast (λ x → suc (r x)) M wM)
    (T.inject (out-flat p) (T.prim p (T.project tint (T.` suc zero))
                                     (T.project tint (T.` zero)))))
cast r (let-op ⦅ M ,, ⟩ N ,, Nil ⦆) (wM , wN , _) = T.let′ (cast r M wM) (cast (ext r) N wN)

casts {n = ℕ.zero} r Nil _ = []
casts {n = suc n} r (M ,, Ms) (w , ws) = cast r M w ∷ casts r Ms ws

{- the pass, for a whole (well-scoped, closed) program -}
cast-program : (M : AST) → WS 0 M → T.Tm 0 Any
cast-program = cast (λ x → x)

{- the pass on any program: a program that is not closed (that cast
   insertion cannot type) becomes one that stops with an error at once,
   the application of an empty tuple; the theorems are for closed
   programs, for which cast-closed M is cast-program M w for every w
   (proof/Compiler/Typed/CastScope.agda) -}
cast-closed : AST → T.Tm 0 Any
cast-closed M with ws? 0 M
... | yes w = cast-program M w
... | no _ = T.app (T.project tfun unit) unit
  where unit = T.inject (tup 0) (T.tuple [])

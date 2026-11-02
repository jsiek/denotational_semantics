{-

  Cast insertion on closed programs, for the typed compiler
  (Compiler/Pipeline.agda): a closed program, simplified, is well
  scoped (WS 0), and then cast-closed is cast-program at any proof that
  it is (scoping proofs are unique). Every column's composition starts
  from these.

-}

module proof.Compiler.CastScope where

open import Language.ISWIM
open import Framework.Syntax.Scope Op sig using (WS; WS-arg; WS-args)
open import Framework.Syntax.ScopeDec Op sig using (ws?)
open import Compiler.CaptureScope using (Closed)
open import Compiler.Simplify using (simplify)
open import proof.Compiler.SimplifyScope using (simplify-closed; closed-ws)
open import Compiler.Cast using (cast-program; cast-closed)

open import Data.Empty using (⊥-elim)
open import Data.Nat.Properties using (<-irrelevant)
open import Data.Product using (_,_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
open import Relation.Nullary using (yes; no)

{- scoping proofs are unique -}
ws-irr : ∀ {k} M (w w' : WS k M) → w ≡ w'
ws-irr-arg : ∀ {b k} (a : Arg b) (w w' : WS-arg k a) → w ≡ w'
ws-irr-args : ∀ {bs k} (as : Args bs) (w w' : WS-args k as) → w ≡ w'
ws-irr (` x) w w' = <-irrelevant w w'
ws-irr (op ⦅ as ⦆) w w' = ws-irr-args as w w'
ws-irr-arg (ast M) w w' = ws-irr M w w'
ws-irr-arg (bind a) w w' = ws-irr-arg a w w'
ws-irr-arg (clear a) w w' = ws-irr-arg a w w'
ws-irr-args nil tt tt = refl
ws-irr-args (cons a as) (w , ws) (w' , ws') = cong₂ _,_ (ws-irr-arg a w w') (ws-irr-args as ws ws')

cast-closed-≡ : ∀ M (w : WS 0 M) → cast-closed M ≡ cast-program M w
cast-closed-≡ M w with ws? 0 M
... | yes w' = cong (cast-program M) (ws-irr M w' w)
... | no ¬w = ⊥-elim (¬w w)

{- a closed program, simplified, is well scoped -}
simplify-ws : ∀ M → Closed M → WS 0 (simplify M)
simplify-ws M c = closed-ws {simplify M} (simplify-closed M c)

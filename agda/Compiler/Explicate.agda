module Compiler.Explicate where
{-

 The explicate-control pass (Imp → CFG), after Essentials of
 Compilation: the nested assignments and cases of an Imp body become a
 control-flow graph of blocks.

 explicate-tail e translates e in tail position, where its value is the
 body's result; explicate-assign e x k translates x := e followed by
 the tail k, in continuation-passing style (Danvy): a nested assignment
 y := e₁; e₂ becomes y := e₁ followed by x := e₂ followed by k, and a
 case becomes a case whose branches assign x and jump to a new block for
 k, the join point, so that k is not duplicated. The branches of a case
 also become blocks.

 Both thread the list of blocks made so far (newest first); a new block
 gets the next label, its length. A tail made at a point refers only to
 the blocks made before it, so every block jumps only to older ones, as
 CFG requires.

-}

open import Language.Imp as Imp using (Exp; simple; case; assign)
open import Language.CFG

open import Data.List using (List; []; _∷_; length; map)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_)

{- add the block t, and its label -}
add : Tail → List Tail → ℕ × List Tail
add t bs = length bs , t ∷ bs

explicate-assign : Exp → ℕ → Tail → List Tail → Tail × List Tail
explicate-assign (simple s) x k bs = seq x s k , bs
explicate-assign (assign y e₁ e₂) x k bs =
  let (t , bs₁) = explicate-assign e₂ x k bs in
  explicate-assign e₁ y t bs₁
explicate-assign (case a y e₁ e₂) x k bs =
  let (l , bs₁) = add k bs
      (t₁ , bs₂) = explicate-assign e₁ x (goto l) bs₁
      (l₁ , bs₃) = add t₁ bs₂
      (t₂ , bs₄) = explicate-assign e₂ x (goto l) bs₃
      (l₂ , bs₅) = add t₂ bs₄ in
  case a y l₁ l₂ , bs₅

explicate-tail : Exp → List Tail → Tail × List Tail
explicate-tail (simple s) bs = return s , bs
explicate-tail (assign x e₁ e₂) bs =
  let (t , bs₁) = explicate-tail e₂ bs in
  explicate-assign e₁ x t bs₁
explicate-tail (case a x e₁ e₂) bs =
  let (t₁ , bs₁) = explicate-tail e₁ bs
      (l₁ , bs₂) = add t₁ bs₁
      (t₂ , bs₃) = explicate-tail e₂ bs₂
      (l₂ , bs₄) = add t₂ bs₃ in
  case a x l₁ l₂ , bs₄

explicate-body : Imp.Body → Body
explicate-body (Imp.body n e) =
  let (t , bs) = explicate-tail e [] in
  body n bs t

{- the pass, for a whole program -}
explicate : Imp.Program → Program
explicate (Imp.program ds b) = program (map explicate-body ds) (explicate-body b)

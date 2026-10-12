{-

  The compiler produces well-formed Clos5 programs (Clos5WF.agda) from
  closed ISWIM programs: compile-wf.

  Well-scopedness is compile-scoped (Compiler.Compile.PipelineScope). The
  rest is that each definition refers only to older ones, and main to
  existing ones (RB): globalize adds the code of a function as a
  definition after the definitions made from the functions nested in it,
  and the code refers only to those (glob-shape, from GlobalizeCorrect.agda).

-}

module proof.Compiler.Operational.Adequacy.CompileWF where

open import Compiler.Lang.Clos4
import Compiler.Lang.Clos5 as C5
import proof.Compiler.Operational.Adequacy.Clos5WF as F
open import Compiler.Compile.EncloseScope using (Closed)
open import Compiler.Compile.Globalize
open import Compiler.Compile.PipelineScope using (Scoped; compile-scoped)
open import proof.Compiler.Model.Graph.Correctness.GlobalizeCorrect using (RB; glob-shape)
open import Compiler.Compile.Pipeline using (compile; compile₄)

open import Data.List using (List; []; _∷_; length)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)

{- the definitions, newest first, refer only to older ones -}
DefsRB : List C5.AST → Set
DefsRB [] = ⊤
DefsRB (N ∷ Ns) = RB (length Ns) N × DefsRB Ns

glob-rb : ∀ M ds → DefsRB ds → DefsRB (proj₂ (glob M ds))
glob-rb-arg : ∀ {b} (a : Arg b) ds → DefsRB ds → DefsRB (proj₂ (glob-arg a ds))
glob-rb-args : ∀ {bs} (args : Args bs) ds → DefsRB ds → DefsRB (proj₂ (glob-args args ds))

glob-rb (` x) ds d = d
glob-rb (fun-op ⦅ cons (clear (bind (bind (ast N)))) nil ⦆) ds d =
  proj₂ (glob-shape N ds) , glob-rb N ds d
glob-rb (app ⦅ args ⦆) ds d = glob-rb-args args ds d
glob-rb (lit B k ⦅ args ⦆) ds d = glob-rb-args args ds d
glob-rb (pair-op ⦅ args ⦆) ds d = glob-rb-args args ds d
glob-rb (fst-op ⦅ args ⦆) ds d = glob-rb-args args ds d
glob-rb (snd-op ⦅ args ⦆) ds d = glob-rb-args args ds d
glob-rb (tuple n ⦅ args ⦆) ds d = glob-rb-args args ds d
glob-rb (get i ⦅ args ⦆) ds d = glob-rb-args args ds d
glob-rb (inl-op ⦅ args ⦆) ds d = glob-rb-args args ds d
glob-rb (inr-op ⦅ args ⦆) ds d = glob-rb-args args ds d
glob-rb (case-op ⦅ args ⦆) ds d = glob-rb-args args ds d
glob-rb (let-op ⦅ args ⦆) ds d = glob-rb-args args ds d
glob-rb (prim p ⦅ args ⦆) ds d = glob-rb-args args ds d

glob-rb-arg (ast M) ds d = glob-rb M ds d
glob-rb-arg (bind a) ds d = glob-rb-arg a ds d
glob-rb-arg (clear a) ds d = glob-rb-arg a ds d

glob-rb-args nil ds d = d
glob-rb-args (cons a args) ds d = glob-rb-args args (proj₂ (glob-arg a ds)) (glob-rb-arg a ds d)

defs-wf : ∀ ds → DefsRB ds → All (F.WS 2) ds → F.DefsWF ds
defs-wf [] _ _ = tt
defs-wf (N ∷ Ns) (r , rs) (w ∷ ws) = (r , w) , defs-wf Ns rs ws

{- The compiler ----------------------------------------------------------------------}

compile-wf : ∀ M → Closed M → F.WF (compile M)
compile-wf M c =
  defs-wf _ (glob-rb M₄ [] tt) (proj₁ S) , proj₂ (glob-shape M₄ []) , proj₂ S
  where
  M₄ = compile₄ M
  S = compile-scoped M c

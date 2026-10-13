{-

  Well-formed Clos5 programs, the precondition of soundness and adequacy
  for the Clos5 machine (Adequacy/Clos5.agda); globalize produces them
  from closed ISWIM programs (Adequacy/CompileWF.agda).

  * The main expression is closed (WS 0), and the code of each global
    definition uses only its two parameters (WS 2): the machine runs code
    in an environment of exactly two values, and an unbound variable,
    which goes wrong in the machine, denotes init = {ω}.

  * Each reference refers to an existing definition, and the code of a
    definition only to older ones (RB, from GlobalizeCorrect.agda): the
    semantics interprets each definition with the table of the older ones
    only, while the machine looks references up in the whole table.

-}

module proof.Adequacy.Clos5WF where

open import Language.Clos5
open import proof.Correctness.Graph.GlobalizeCorrect using (RB) public
open import proof.Framework.Syntax.ScopeRename Op sig public

open import Data.List using (List; []; _∷_; length)
open import Data.Product using (_×_)
open import Data.Unit using (⊤)

{- the definitions, newest first -}
DefsWF : List AST → Set
DefsWF [] = ⊤
DefsWF (N ∷ Ns) = (RB (length Ns) N × WS 2 N) × DefsWF Ns

WF : Program → Set
WF (program ds M) = DefsWF ds × RB (length ds) M × WS 0 M

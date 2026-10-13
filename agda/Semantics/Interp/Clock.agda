{-

  Functional big-step semantics with a clock, in the style of CakeML
  (Framework/Clocked.agda, language independent; its lemmas are in
  proof/Framework/Clocked.agda, instantiated in
  proof/Semantics/Interp/Clock.agda), instantiated at this
  compiler's observations.

  Design note, for the interpreters of each language and the proof of
  each pass:

  * Each language has an interpreter (Semantics/Interp/*.agda),
      eval : ℕ → Env → AST → Result Val
    a total function, by recursion on the clock and the term. Values and
    environments are those of the CEK machines: a function value is a
    syntactic closure, code plus environment.

  * The clock is decremented only when a function is called, as in
    CakeML; a call with clock 0 times out. Every other construct
    evaluates its subterms with the same clock.

  * An interpreter goes wrong (wrong) exactly when the corresponding
    machine is stuck, and evaluates in the same order: left to right, and
    the operator of an application is checked to be a function before its
    argument is evaluated (in Clos4 and Clos5: when it is called, after
    its operands).

  * A program terminates with o if, for some clock, it returns a value
    observed as o, or goes wrong and o is o-wrong; it diverges if it times
    out for every clock. The end theorem (Equivalent) has the shape of
    the simulation one, over the same observations (Observation.agda).

  * No pass adds or removes function calls, so a pass is proved correct
    clock for clock: for every clock, the program and its compilation
    both time out, both go wrong, or return related values (RelResult).
    That gives both directions of the end theorem at once (clocked),
    with no determinism argument.

-}

module Semantics.Interp.Clock where

open import Semantics.Observation using (Obs; o-wrong)
open import Framework.Clocked Obs o-wrong public

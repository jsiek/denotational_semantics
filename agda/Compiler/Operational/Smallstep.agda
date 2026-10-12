{-

  Transition systems and their behaviors, in the spirit of CompCert's
  Smallstep library (../../Smallstep.agda), instantiated at this
  compiler's observations. (Forward simulations are in Simulation.agda.)

  Design note, for the machines of each language and the simulation proof
  of each pass:

  * Each language has a CEK-style machine (Machine/*.agda) with states
      eval M ρ κ   evaluate term M in environment ρ, then continue with κ
      ret v κ      return value v to continuation κ
    Environments are lists of values (variable x is the x-th element),
    and a function value is a syntactic closure: code plus environment.
    Lists of subterms (tuple components, a closure's free variables) are
    evaluated left to right, collecting values in a continuation frame.

  * A machine is a step function, step : State → Next State, which either
    moves to the next state or stops with an observation (see
    Observation.agda): the observation of the value returned to the empty
    continuation, or o-wrong when the machine is stuck (an unbound
    variable, applying a non-function, projecting from a non-tuple, ...).
    So every state either steps or is final, and machines are
    deterministic, by construction.

  * A program's machine (Machine) starts in the state eval M [] halt. It
    terminates with o if it reaches a final state with observation o, and
    diverges if it can take n steps for every n.

  * A pass is proved correct by a forward simulation (Simulation.agda):
    one source step is matched by one or more target steps, or by no
    target step when a natural-number index of the match decreases. Since
    both machines are deterministic and total, this gives the end theorem
    (Equivalent): the program and its compilation terminate with the same
    observations (including o-wrong), and one diverges iff the other does.
    We never need "terminates or diverges", which is not constructive.
    When no source step is matched by zero target steps (as for enclose),
    plus-simulation builds the forward simulation from one lemma,
      sim : s₁ ~ s₂ → Answers L₂ _~_ (step s₁) s₂
    (the target stops with the same observation, or takes a plus to a
    matching state), proved by cases on the match. When some source
    steps are matched by no target step (as for optimize, where the
    source evaluates free variables that the target drops),
    the forward simulation is given directly: a match indexed by a
    natural number, which such a step must decrease.

  * Layout: ../Observation.agda (shared with the clocked interpreters);
    the framework, language independent, in ../../Smallstep.agda and
    ../../Simulation.agda, instantiated at these observations here and in
    Simulation.agda; Machine/*.agda (one per language);
    Correctness/*Sim.agda (one per pass).

-}

module Compiler.Operational.Smallstep where

open import Compiler.Observation using (Obs)
open import Smallstep Obs public

{-

  Reduction semantics (Framework/Reduction.agda) as transition systems
  (Framework/Smallstep.agda), at this compiler's observations. (Forward
  simulations between them are in proof/Framework/Reduction.agda.)

  Design note, for the reduction semantics of each language and the
  simulation proof of each pass:

  * Each language with binders (ISWIM, Clos2–Clos5) has a reduction
    semantics (Reduction/*.agda): a state is a term, and a step
    substitutes values for bound variables (β, case, let) or computes a
    primitive, inside an evaluation context. The step function red is
    written with congruence rules (step-in), call by value, left to
    right, with the same order of evaluation and the same checks as the
    CEK machines (the operator of an application is checked to be a
    function before its argument is evaluated in ISWIM, Clos2 and Clos3,
    and only at the call in Clos4 and Clos5). Variables are never looked
    up: a variable that is reached is unbound, and goes wrong.

  * Congruence rules rather than evaluation contexts: one function, with
    no decomposition into a context and a redex, no plugging and no
    unique-decomposition lemma; it is deterministic and total by
    construction, as the machines are. Lifting a run through a context
    is one generic lemma (proof/Framework/Reduction.agda).

  * The first-order languages Imp, CFG and X86 have no binders, so a
    reduction semantics for them would be the configuration-stepping
    machines they already have (Operational/Machine/{Imp,CFG,X86}.agda).
    Those machines, and the proofs of explicate control and select
    instructions between them, are shared with the CEK machine +
    simulation proof.

  * A pass is proved correct by a forward simulation, as in the CEK
    proof, now between terms: each source step is matched by one or more
    target steps, and a source term that is a value or is stuck by a
    target run to a value with the same observation or to a stuck term.

-}

module Compiler.Reduction.Smallstep where

open import Compiler.Observation using (Obs; o-wrong)
open import Framework.Smallstep Obs public
open import Framework.Reduction Obs o-wrong public

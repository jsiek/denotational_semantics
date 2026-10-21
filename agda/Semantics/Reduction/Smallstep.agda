{-

  Reduction semantics (Framework/Reduction.agda) as transition systems
  (Framework/Smallstep.agda), at this compiler's observations. (Forward
  simulations between them are in proof/Framework/Reduction.agda.)

  Design note, for the reduction semantics of each language and the
  simulation proof of each pass:

  * Each language with binders (ISWIM, the source of cast insertion,
    and ISWIMᵀ, Clos2ᵀ–Clos5ᵀ) has a reduction semantics
    (Reduction/ISWIM.agda, Reduction/Typed/*.agda): a state is a term,
    and a step substitutes values for bound variables (β, case, let) or
    computes a primitive, inside an evaluation context. The step
    function red is written with congruence rules (step-in), call by
    value, left to right, with the same order of evaluation as the CEK
    machines. ISWIM's makes the same checks as its machine, and a
    variable that is reached is unbound, and errors; the typed ones run
    closed, well-typed terms, so they reach no variable and no operand
    of the wrong kind, and their only error is a failed project. Monᵀ
    runs as its embedding into Clos5ᵀ.

  * Congruence rules rather than evaluation contexts: one function, with
    no decomposition into a context and a redex, no plugging and no
    unique-decomposition lemma; it is deterministic and total by
    construction, as the machines are. Lifting a run through a context
    is one generic lemma (proof/Framework/Reduction.agda).

  * The first-order languages Impᵀ, CFGᵀ and X86ᵀ have no binders, so a
    reduction semantics for them would be the configuration-stepping
    machines they already have (Semantics/CEK/Typed/{Imp,CFG,X86}.agda).
    Those machines, and the proofs of explicate control and select
    instructions between them, are shared with the CEK machine +
    simulation proof; lift locals is proved between the Clos5ᵀ
    reduction semantics and the Impᵀ machine.

  * A pass is proved correct by a forward simulation, as in the CEK
    proof, now between terms: each source step is matched by one or more
    target steps, and a source term that is a value or is stuck by a
    target run to a value with the same observation or to a stuck term.
    Simplify is the exception: the target's steps are matched by the
    source's (a simulation of the target by the source), and
    Equivalent is symmetric.

-}

module Semantics.Reduction.Smallstep where

open import Semantics.Observation using (Obs; o-error)
open import Framework.Smallstep Obs public
open import Framework.Reduction Obs o-error public

# Notes for the Artifact of "Denotational Results and Comparative Semantics"

## Semantics

The semantics definitions are in `agda/FPC/Semantics/`.

### Reduction semantics for FPC (Sec. F.4 of the Appendix)

In this section, we describe the Agda mechanization of the reduction semantics.
The reduction rewrites closed terms using substitution. The reduction is call by
value, left to right.

The reduction semantics is presented as a function: `red` maps an intrinsically
typed term under the empty typing context to a result, which says that the term
is a value, gets stuck, or reduces to another term. This `red` function is
deterministic and total by construction.

The congruence rules are written with one combinator, `step-in f r k`. If the
subterm reduces (with the reduction `r`), then so does the whole term, in the
evaluation context `f`; if it is a value, continue with `k`; if it is stuck, so
is the whole term. Consider the case of `red` for function application:

```
red (app L M) = step-in (λ L' → app L' M) (red L) (step-in (app L) (red M) (β L refl M))
```

The function `λ L' → app L' M` plays the role of the evaluation context `□ M`.
Similarly, `app L` plays the role of `V □`. As a result, we reduce the rator
(`L`) first, then reduce the rand (`M`), and finally take the β step.

(The reduction semantics is described in Sec. F.4 of the Appendix of the paper.)

### CEK machine for FPC (Sec. F.3 of the Appendix)

In this section, we explain how the CEK machine mechanized in Agda is isomorphic
to the one in the "Control Operators, the SECD-Machine, and the λ-Calculus"
paper by Matthias Felleisen, Daniel P. Friedman.

The `State` datatype captures the CEK machine states and is equivalent to a CEK
triple. The `ret v κ` state carries a ret-continuation and mirrors the `⟨ ‡ , ∅
, (κ ret v)⟩` state. (Note that the environment is always empty here, so we
don't need it.) The `eval M ρ κ` state carries a term `M` (the control string),
an environment `ρ`, and a continuation `κ`.

  - A *control string* is an intrinsically typed term (`Tm Γ A`).
  - An *environment* (`Env Γ`) is isomorphic to a list of values. The
    environment inside a closure is stored as a tuple. To be specific, a closure
    is modeled as `pack (code N) (tup ρ)`, which packs the function body `N`
    with the environment `ρ`.
  - A *continuation* is also intrinsically typed, defined in the `Cont`
    datatype. The definition directly corresponds to that in Felleisen and
    Friedman with extension of primitives, let-expressions, tuples, sums, and
    recursive types. For example, `halt` corresponds to the empty continuation
    `stop`; `appL` corresponds to `arg`, and `appR` is `fun` in their paper.

The `step` function captures the CEK machine transitions. It has the type
`step : State → Next State`. The function maps each state either to a next state
or to a final observation. The latter is through `step (ret v halt) = stop (obs
v)`.

(The CEK machine is described in Sec. F.3 of the Appendix of the paper.)

# Notes for the Artifact of "Denotational Results and Comparative Semantics"

## Semantics

The semantics definitions are in `agda/FPC/Semantics/`.

### Reduction semantics for FPC

TBA

### CEK machine for FPC

The `State` datatype captures the CEK machine states. It is isomorphic to the
CEK triple in the "Control Operators, the SECD-Machine, and the λ-Calculus"
paper by Matthias Felleisen, Daniel P. Friedman. The `ret` state carries a
ret-continuation and mirrors the `⟨ ‡ , ∅ , 𝑘 ⟩` state (note the environment is
always empty, so we don't need it). The `eval` state carries a term (the control
string), an environment, and a continuation.

  - A *control string* is an intrinsically typed term (`Tm Γ A`).
  - An *environment* (`Env Γ`) is isomorphic to a list of values. In particular, a
    closure is modeled as `pack (code N) (tup ρ)`, which packs the function body
    `N` with the environment `ρ`.
  - A *continuation* is also intrinsically typed, defined in the `Cont`
    datatype, with `halt` being the empty continuation.

The `step` function captures the CEK machine transitions. It has the type
`step : State → Next State`.

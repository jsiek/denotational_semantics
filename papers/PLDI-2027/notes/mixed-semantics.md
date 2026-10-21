# Mixing semantics: graph model and clocked interpreter

> **Status (2026-10-15).** Design written first (§1–§4, estimates as they stood before building); split (a) then built and measured (§5), (b) and (c) estimated only. In short: split (a) is 1839 lines against the interpreter column's 1653, so mixing does not pay on ISWIMμ; the bridge at ISWIMμ, 395 lines, is also an ISWIMμ adequacy theorem w.r.t. the interpreter, against 464 w.r.t. the CEK machine. Results in §5 and in the section "Mixing semantics" of `../loc.md` (`loc.py --mixed`). Since then (§6) the graph model's adequacy is against the interpreters, and the bridge *is* its ISWIMμ half, moved to `agda/Mu/proof/Adequacy/`.

The question: the four columns of ISWIMμ prove every pass in one style. Each pass has a cheapest style (the bold cells of the main table of `../loc.md`). Is the compiler cheaper to prove if each pass uses the cheaper of the graph-model proof and the interpreter proof, joined by **bridges**? A bridge is an adequacy theorem between a language's graph semantics and its clocked interpreter, at each language where the style changes.

## 1. The end theorem

The same as the four columns' end theorem, stated with the interpreters as the interpreter column states it (`Mu/proof/Correctness/Interp/CompilerFuel.agda`). For `M : Tm [] (base Int)`:

* `Terminates (ISWIMμᵢ.sem M) (o-const Int k) ⇔ Terminates (X86μᵢ.sem (compile-x86 M)) (o-const Int k)`
* `Diverges (ISWIMμᵢ.sem M) ⇔ Diverges (X86μᵢ.sem (compile-x86 M))`

So the program and its compilation stop with the same constant, or both diverge, observed through the interpreters.

## 2. Bridges

A bridge at language L, for closed programs `P` of L:

* `const k ∈ ⟦ P ⟧ ⇔ Terminates (Lᵢ.sem P) (o-const B k)`
* `Diverges (Lᵢ.sem P) ⇔ ¬ nonempty ⟦ P ⟧`

Both are constructive: `¬ nonempty → Diverges` looks at the interpreter's result at each clock. A returned value would denote a nonempty part of `⟦ P ⟧` (soundness). An error cannot happen (the interpreters never err, `Mu/proof/Semantics/Interp/NoError.agda`).

A bridge has two halves:

* **Soundness:** what the interpreter returns at some clock denotes a part of the denotation. This is by induction on the clock and the term. It is like the CEK machine's soundness (`Mu/proof/Adequacy/Soundness.agda`) without the continuations: no `𝒦`, no `𝒦-mono`, no `halts`, and no `step-⊆` over every machine state.
* **Adequacy:** every element of the denotation is related, by a logical relation by recursion on the denotational value (as in `Mu/proof/Adequacy/LogRel.agda`), to the value the interpreter returns. "Returns" is `Stable`: the same result from some clock on (`proof/Framework/Clocked.agda`).
  * `st-bind` composes stable results, so no monotonicity lemma for the interpreter is needed.
  * `stable-unique` gives determinism, which the CEK version gets from `⇓-det`.

**A bridge at ISWIMμ is also an ISWIMμ adequacy theorem w.r.t. the interpreter.** Today's ISWIMμ adequacy is the "ISWIM" row of the adequacy table, 464 lines, and it is w.r.t. the CEK machine.

## 3. Candidate splits

Per-pass sizes (graph / interpreter), with the cheaper one in bold:

| pass | graph | interpreter |
|---|---:|---:|
| simplify | **360** | 633 |
| enclose | 43 | **33** |
| optimize | 83 | **65** |
| concretize | 68 | **42** |
| delay | 524 | **35** |
| globalize | **118** | 183 |
| rco | 125 | **85** |
| lift locals | 44 | **27** |
| explicate | **71** | 75 |
| select | 83 | **48** |

Only three passes are cheaper in the graph model: simplify (saves 273), globalize (saves 65) and explicate (saves 4).

* **(a) Graph for simplify only, interpreter for the rest.** Simplify is ISWIMμ → ISWIMμ, so one bridge, at ISWIMμ, used at both ends of simplify (for `M` and for `simplify M`).
  * Chain: interp(M) ⇔ ⟦M⟧ ⇔ ⟦simplify M⟧ ⇔ interp(simplify M) ⇔ interp(compile-x86 M).
  * Extra semantics: only ISWIMμ's graph semantics and its `Ok` lemmas, and the meaning of the primitives (`Semantics.Graph.Prim`). The interpreter semantics of every language is still needed.
* **(b) (a), plus graph for globalize and/or explicate.**
  * Globalize (Clos4μ → Clos5μ) needs bridges at Clos4μ and Clos5μ to save 65 lines.
    * The Clos4μ bridge is like ISWIMμ's, plus code values.
    * The Clos5μ bridge has the global tables. The CEK-based "Clos5" adequacy row is 307 lines, and that is only the values and tables that X86μ adequacy uses.
  * Explicate (Impμ → CFGμ) needs bridges at Impμ and CFGμ to save 4 lines.
* **(c) The per-pass minimum:** graph for simplify, globalize and explicate. Five bridges: ISWIMμ, Clos4μ, Clos5μ, Impμ, CFGμ.

## 4. Estimates (before building)

The ISWIMμ bridge:

| piece | estimate |
|---|---:|
| soundness, interpreter → graph (CEK: 342 with continuations) | ~180 |
| tuples of sets, reused (`Mu/proof/Adequacy/Tuples.agda`, shared with the CEK adequacy) | ~95 |
| logical relation and fundamental lemma (CEK: 212) | ~190 |
| statements: const iff, diverges iff (CEK: 78) | ~50 |
| **bridge at ISWIMμ** | **~400–500** |

Every other bridge is at least as big. Clos4μ has code values. Clos5μ, Impμ and CFGμ have global tables, and the first-order languages also have blocks.

| split | interpreter-only rows | graph rows | extra graph semantics | bridges | composition | total (est.) |
|---|---:|---:|---:|---:|---:|---:|
| interpreter only (measured) | 1653 | — | — | — | — | 1653 |
| (a) | 1653 − 633 | +360 | ~+80 (ISWIMμ) + 34 (primitives) | ~450 | ~+10 | **~1950** |
| (b) globalize too | (a) − 183 | +118 | + Clos4μ, Clos5μ semantics ~+150 | + ~2 × 450 | | ~2900 |
| (c) | (b) − 75 | +71 | + Imp, CFG ~+160 | + ~2 × 400 | | ~3900 |

So (b) and (c) are dominated: a bridge costs an order of magnitude more than the 65 or 4 lines it would save. Only (a) is worth building. Even (a) is expected to come out *above* the interpreter column's 1653, because the bridge (~450) and ISWIMμ's graph semantics cost more than simplify saves (273).

For fairness, compare each pure column's end theorem:

* The graph column's end theorem (`compile-x86-same`) is about denotations. Reaching running code needs adequacy too: 1958 + 1599 = 3557.
* The interpreter column's end theorem is already about running code.

Split (a) reaches the interpreters with one bridge in place of the graph column's two adequacy theorems (ISWIMμ and X86μ machines).

## 5. Results (built: split (a))

Built in `agda/Mu/proof/Mixed/` (the bridge's three modules are now in `agda/Mu/proof/Adequacy/`, see §6):

* `Soundness.agda` (174): soundness of the interpreter.
* `LogRel.agda` (121): the logical relation and the fundamental lemma.
* `ISWIM.agda` (26): the bridge's statements, `const-iff` and `diverges-iff`.
* `CompilerMixed.agda` (28): the composition, with the end theorems `compile-x86-const` and `compile-x86-diverges`, stated as in `CompilerFuel`.

The per-pass proofs of both columns are unchanged. The bridge reuses the tuples of sets of ISWIMμ's adequacy (`Mu/proof/Adequacy/Tuples.agda`, 74). Counted by `loc.py --mixed` (side `mu-mix`, in no total of the four):

| | estimate | measured |
|---|---:|---:|
| soundness | ~180 | 174 |
| logical relation | ~190 | 121 |
| statements | ~50 | 26 |
| tuples (reused) | ~95 | 74 |
| **bridge at ISWIMμ** | ~400–500 | **395** |
| **split (a), total** | ~1950 | **1839** |

* Against the pure columns: interpreter **1653**, graph model 1958 (3557 with its adequacy), CEK 2258, reduction 3207.
* Split (a) is 186 lines more than the interpreter column. Simplify saves 273. The bridge (395), ISWIMμ's graph semantics (38) and the meaning of the primitives (34) cost 467.
* (b) and (c) are estimated by `loc.py` from the measured rows, each further bridge at the ISWIMμ bridge's 321 lines without the tuples:
  * (b) with globalize: ~2528;
  * (b) with explicate control: ~2595;
  * (c): ~3265.
  * These are optimistic: Clos4μ has code values; Clos5μ, Impμ and CFGμ have tables. They are not built, since even the optimistic numbers are far above (a).
* **ISWIMμ adequacy w.r.t. the interpreter: 395, against 464 w.r.t. the CEK machine.**
  * Soundness: 174 against 239. It needs no continuations, no `𝒦-mono` and no `halts`.
  * The logical relation: 121 against 128. `Stable` and `st-bind` replace runs of the machine, and `stable-unique` replaces `⇓-det`.
  * The result predicate of soundness excludes `error`, so the bridge needs no no-error lemma.
* Infrastructure (in no total): split (a) uses 1571 lines, nearly all the graph model's (1542) plus the clocked framework (249, less what both share). The interpreter column uses 413.

**Recommendation for the paper.** Present mixing as a measured negative result with one positive by-product:

* Per-pass minima do not add up. A bridge costs about as much as a pass's whole proof (here 395 against the largest saving, 273), so mixing pays only for a pass whose saving exceeds the bridges it needs. On ISWIMμ no pass does, and the pure interpreter column stays the cheapest proof of the same end theorem.
* Mixing does give the graph model a much cheaper route to running code: graph model for simplify, interpreters elsewhere, 1839, against 3557 for graph model plus adequacy.
* The interpreter is the cheaper target for adequacy (395 against 464). Its soundness is by induction on the clock and the term, and stable results compose.

A short paragraph and one table (the split table above) suffice. The per-row table belongs in the artifact (`loc.py --mixed`).

## 6. Afterwards: adequacy against the interpreters

The bridge at ISWIMμ was cheaper than ISWIMμ's adequacy w.r.t. the CEK machine, so the graph model's adequacy was redone against the interpreters, for ISWIMμ and X86μ (`agda/Mu/proof/Adequacy/`, stated in `agda/Mu/Theorems/Adequacy.agda`):

* **ISWIMμ:** the bridge itself, moved from `Mu/proof/Mixed/` to `Mu/proof/Adequacy/` (`Soundness`, `LogRel`, `ISWIM`, with `Tuples`): 395, against 464. `CompilerMixed.agda` stays in `Mu/proof/Mixed/` and imports it from there.
* **X86μ:** direct against the X86μ interpreter, with the Clos5μ interpreter's values (`Clos5Values` 231 + `Clos5Common` 70) and the well-formedness of compiled programs (`X86Compiled`, 38), as before: `X86LogRel` 169 (199 for the machine), `X86Soundness` 499 (470), `X86Common` 4 (10), `X86` 40 (18); the X86 row 712 against 697. Unlike ISWIMμ's, X86μ's adequacy does not shrink: without a call stack, soundness must merge the callee's approximations of its start, one per element of the result, where the machine carries one approximation down the stack.
* **End to end:** `compile-x86-same` and the two adequacy theorems give exactly the interpreter column's statements (`compile-x86-const`, `compile-x86-diverges`; 15, against 22), with no no-error lemma: soundness shows that neither interpreter errs, and divergence is the emptiness of the denotations.
* **Totals:** adequacy 1599 → 1532; the graph model to running code 3557 → 3490 (graph column 1958 + adequacy 1532), against interpreter 1653, CEK 2258, reduction 3207, and mixed (a) 1839.
* **The mixing numbers do not change,** and the bridge is not double counted: `loc.py` counts it once in each total that reaches it. Split (a)'s 1839 includes it (in its bridge row) and stands alone; the graph model's 3490 includes it (in adequacy's ISWIM row). No total adds the two.
* The adequacy for the CEK machines is kept as an alternative (`agda/Mu/proof/Adequacy/CEK/`, reachable from `agda/Mu/All.agda`, not stated in `Mu/Theorems/`), reported beside the new one by `loc.py` (side `mu-adeq-cek`, in no total).

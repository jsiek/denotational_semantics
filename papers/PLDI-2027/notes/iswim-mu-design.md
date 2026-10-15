# A typed ISWIM with recursive types: design of the experiment (v2)

> **Status (2026-10-15).** The design as approved, with the pilot P0 built (`agda/Mu/`, `loc.py --mu`, the section "ISWIMμ pilot" of `../loc.md`). Where the pilot showed the design wrong or settled an open point, a note marked **[P0]** says so; the rest is the design as written. In short:
>
> * The measured rows fall inside the estimates: graph-model delay 552 → 524, the other three passes 197 → 194 (graph) and 354 → 331 (CEK), CEK delay 99 → 96.
> * The depth index of ApproxLR stays load-bearing, as argued in §3.2 (now also in the comment of `Mu/proof/Correctness/Graph/DelayRel.agda`).
> * The unification risk did not materialize: `unfold` needs no equation argument (§5).
> * Heterogeneous contexts cost nothing net: optimize got smaller, and the CEK lemmas about tuple lengths disappeared (§3.3).

Revision of `typed-source-design.md` (v1, which had simple types plus `rec`), after the author's response. The goals now are:

* a typed counterpart of ISWIM, with the same constructs and the same CBV semantics;
* divergence in the language itself;
* a design in which the type index **cannot** make the delay relation well founded, so ApproxLR stays load-bearing.

This is design only. The base is `origin/master` 9f0d5c2 (PR #64); counts are from `loc.md`.

## 0. Summary

* **Source: ISWIMμ.** It has ISWIM's constructs, with the types `base B | A ⇒ B | tup Δ | A ⊹ B | μX.A | X`.
  * Recursive types are **iso-recursive**, with `fold`/`unfold`.
  * `fold` and `unfold` mean nothing at run time: they are the identity in the graph model and a move in X86. They play the role that `inject`/`project` play today, without the failure.
  * There is **no `rec`/`fix`**. The CBV Z combinator is typable through μ, so divergence and general recursion come for free.
  * No graph semantics needs a least fixed point, which keeps the property of today's pipeline that v1 would have lost.
* **ApproxLR stays as it is**: defined by recursion on approximant depth (fuel `ApproxLR≤`, `ApproxLR-depth-irrelevant`).
  * A type-indexed definition breaks exactly at μ: `R_{μX.A} = R_{A[μX.A/X]}` is not structurally smaller. With `μX. X ⇒ Int`, `app-obs` asks for the relation at the same type again.
  * Since `fold` is the identity on denotations, the depth does not drop at a fold either. Only the depth of the approximant (its arguments and results in `Calls`) decreases, as today.
  * This is the step-indexing phenomenon for recursive types, and it is the point of the experiment.
* **Errors.** Nothing traps.
  * `unfold` cannot fail, the primitives are total, and terms are typed and closed.
  * X86 gets no `chk`.
  * With a main program of ground type, the plain graph model plus adequacy gives the operational `Equivalent`, so **the graph-with-errors column is unneeded**.
* **The comparison this enables.** Today's pipeline is, in effect, *this* pipeline specialised to the single recursive type `Any ≅ μX. Σ_G G[X]`, with case-on-tag fused into a partial `project`. So the two pipelines have **the same recursion** (a recursive type in both) and **the same closure conversion**. They differ only in the trapped errors and tag checks. The difference in each column is therefore the cost of dynamic typing, with recursion held constant.
* **Pipeline.** A parallel copy of `Language/Typed/*` (proposed: `agda/Mu/`), with three mechanical changes:
  * `Ty` gains type structure and μ, and loses `Any`, `Flat`, `Tag` and `_≟_`;
  * `inject` becomes `fold` and `project t` becomes `unfold` (total);
  * contexts and environments become heterogeneous: existentials hide a `Ctx`, and tables are lists of code types.

  The calling convention is unchanged (two registers): no self parameter is needed.
* **Estimate** (without simplify; today's comparable totals are 1722 / 1881 / 1079 / 2606): graph about **1620–1720**, CEK about **1820–1900**, interpreter about **1040–1100**, reduction about **2540–2660**. Graph delay changes little (552 → about 500–540): its cost is not caused by errors.

## 1. Source: ISWIMμ

### 1.1 Iso- or equi-recursive

| | iso-recursive (`fold`/`unfold`) | equi-recursive (`μX.A = A[μX.A]`) |
|---|---|---|
| Agda, intrinsic syntax | ordinary inductive `Ty n` (de Bruijn type variables); `unfold : Tm Γ (μ A) → Tm Γ (A [ μ A ])` | type equality up to unfolding (coinductive or bisimulation-decided); a conversion rule in every typed language; type-indexed `Val`/`Cont` families no longer match definitionally |
| semantics, every style | `fold`/`unfold` are identities (graph model), or a wrapper and its elimination (machine values), as `inject`/`dyn` are today | nothing to do at run time, but every proof transports along type equalities |
| closeness to ISWIM | erases to ISWIM: `fold`/`unfold` vanish | erases to ISWIM directly |
| **verdict** | **recommended**: it mirrors today's `inject`/`project` slots one for one, and the cost in each column is one congruence per pass | rejected: the type equality would be the biggest piece of new infrastructure in the project |

### 1.2 Grammar

* `Ty n ::= base B | A ⇒ B | tup Δ | A ⊹ B | μ A | var x`, with `μ : Ty (suc n) → Ty n`. Terms are indexed by closed types `Ty 0`.
* The body of μ is **contractive**: it must start with `⇒`, `tup`, `⊹` or `base`, not a variable or another μ. That rules out `μX.X`, has no cost in expressiveness, and keeps unfolding productive.
  * **[P0]** Enforced by a hidden argument of `μ`, `{Contractive A}`, with `Contractive` defined by induction-recursion with `Ty` (⊤ or ⊥ by the head of A), which `--safe` allows. Renaming and substitution carry it (one line per head). `Ty` also has `code Δ A B` (Clos4μ only).
* The terms are ISWIM's, typed: `` ` ``, `lam`, `app`, `lit`, `tuple`, `get (Δ ∋ A)`, `inl`, `inr`, `case`, `prim {sub, eq}`, `let`, plus `fold` and `unfold`.
* Type substitution `A [ B ]` (renaming and substitution on `Ty`) is about 30–40 shared lines. No term-level lemma needs it, because there is no polymorphism and contexts hold closed types.
  * **[P0]** 46 lines, with contractiveness; no lemma about it was needed anywhere.

### 1.3 Divergence and recursion without `rec`

* Ω is typable: `ω = λx. unfold x x : (μX. X ⇒ A) ⇒ A`, and `Ω = ω (fold ω)`.
* The CBV fixed-point combinator is typable:
  * `fix f = (λx. f (λv. unfold x x v)) (fold (λx. f (λv. unfold x x v)))`, with `x : μX. X ⇒ (A ⇒ B)`.
  * It is a definable term, or a front-end macro: no construct, no proof cost.
* **`rec` is not needed.** Adding it as a construct would cost what v1 described:
  * a least fixed point in the semantics of the source, Clos2 and Clos3;
  * consistency, continuity and unfolding lemmas for it (about 120–180 lines of infrastructure);
  * a self parameter (a third register) from delay down;
  * a fixed-point case in both directions of delay.

  If directness matters (one call per iteration instead of Z's extra closure), offer `rec` as sugar for the Z encoding. Do not make it a construct.

### 1.4 Untyped ISWIM as the uni-typed fragment

* For a program P, let `D_P = μX. base Int ⊹ (X ⇒ X) ⊹ (X ⊹ X) ⊹ tup[X,…,X] ⊹ …`, with one tuple arity per arity used in P and the base types P uses. ISWIM's `tuple n` ranges over every n, so a single finite μ-type needs P's arities. Today's `Any` is the infinite version of this sum.
* The embedding injects every value (`fold ∘ inl/inr…`) and **cases on the tag** at every elimination.
* **What a tag mismatch does is the crux.** ISWIM traps there. ISWIMμ has no trap, so the faithful embedding needs one more construct, `error`, in the mismatch branch. With `error` added, ISWIMμ + `error` + `D` is exactly today's cast insertion into `Any`, and the errors (and the errors column) are back.
* **Recommendation:** keep ISWIMμ **without** `error`. State the embedding as a remark: it is faithful for programs that don't go wrong, or it maps errors to Ω. The existing typed pipeline *is* the "with error" point of the design space, already built. That is what makes the comparison clean (§4).

## 2. Pipeline

### 2.1 Can today's typed IRs be reused by reading `Any` as μ?

They already are a μ-typed pipeline with exactly one recursive type. `Any` is `μX. Σ_{G ∈ Flat} G[X]`:

* `inject G` is `fold ∘ in_G`;
* `project t` is `case-on-tag ∘ unfold`, with an error in every other branch.

What prevents reuse is not μ but the fact that this sum is open-ended, and that `Any` fixes the shape of everything else:

* ISWIMᵀ/Clos2ᵀ contexts are `ℕ`;
* `fun` is `Any → Any`;
* `tup n` holds `Any`s;
* `code n`, `⟪tup n⟫`, tables `List ℕ`, and X86ᵀ's `codeα`/`tupα` hide an `ℕ`.

So reusing them as they are reproduces today's experiment.

### 2.2 Minimal change to `Language/Typed/*`

These are the same constructors and the same passes, re-indexed. Where μ appears is marked **μ**.

| module | change |
|---|---|
| `Type` | `Ty n` as in §1.2 (**μ**, type substitution); `code Δ A B`; drop `Any`, `Flat`, `Tag`, `out-flat`'s flat types (eq: `tup [] ⊹ tup []`) and `_≟_` (project needed decidable equality; nothing does now) |
| `ISWIM`, `Clos2` | contexts `ℕ` → `Ctx`; `lam : Tm (A ∷ Γ) B → Tm Γ (A ⇒ B)`; `tuple : All (Tm Γ) Δ`; `get : Δ ∋ A → …`; typed `inl`, `inr`, `case`, `let`; `inject` → `fold`, `project` → `unfold` (**μ**); Clos2: `clos : Tm (A ∷ Δ) B → All (Tm Γ) Δ → Tm Γ (A ⇒ B)` |
| `Clos3` | code over `A ∷ tup Δ ∷ []` |
| `Clos4` | `A ⇒ B` is `∃Δ. code Δ A B × tup Δ` (the witness is a `Ctx`, as in Minamide, Morrisett and Harper); `pack`, `callc` as today |
| `Clos5`, `Mon`, `Imp`, `CFG` | tables `List (Ctx × Ty × Ty)`; `fold`/`unfold` as `Exp`/`Simple` forms (**μ**); definitions start with env, arg (unchanged) |
| `X86` | `RTy`'s `codeα`/`tupα` hide a `Ctx`; no `chk`; `fold`/`unfold` are a `movq` between slots of the two types (**μ**; as `inject` is today a move), or a typing coercion with no instruction |

* **[P0] Optimize** cannot send an unused free variable to the argument, as the typed pass does, since the types differ. Its renaming is defined only on the variables the term uses (`Ren (uses M) Γ'`: a variable and a proof that it is used), and a closure's code is renamed by `squeeze`, defined on the kept variables. `covers` (the code uses only kept variables) moves from the proofs into the pass. No thinnings or strengthening lemmas were needed. The heterogeneous vectors (lookup, flags, `select`, `squeeze`, pointwise relations, `Thin`) are 78 lines of infrastructure (`Mu/Framework/AllUtil.agda`).
* **Where μ shows up:** only in the types of values (environments and frames may hold μ-typed values, and code types and state types may mention μ) and in the two coercions. **No pass looks at μ**: closure conversion, globalize, rco, lift locals, explicate and select are oblivious to it. That orthogonality is a result worth stating.
* **Parallel copy or "alongside"?** One could keep `Any` and add μ to one `Ty`, serving both pipelines from one set of IRs. But the proofs would then include `project`'s failure cases for the typed source too, and the error-free column could not be measured. **Recommend a parallel copy**, `agda/Mu/` with module prefix `Mu.`, and `loc.py --mu`, reusing `Framework/` unchanged. A merge can come later if wanted.

## 3. Per-column impact

### 3.1 Graph model

* **Semantics.** `⟦fold M⟧ = ⟦unfold M⟧ = ⟦M⟧`. `Λ` self-application gives recursion, as in untyped ISWIM. There is **no least fixed point**.
* **Removed:** `projectᵍ`/`guardᵖ`/`accepts`/`fun₂`/`fun₄`, and the per-language `ok` lines for `project` (about −20 to −30 in the semantics row).
  * **[P0]** The four languages' semantics with their lemmas are 123 → 124 lines (a `fold` and an `unfold` line where `inject` and `project` had one each). The saving is `Ops` (36 lines, of which about 17 are `project`; the rest, the tables, serves Clos5ᵀ and later).
* **Equational passes:** `fold`/`unfold` are congruences (1–2 lines each), replacing `project`'s.
* **Delay.**
  * Unchanged in structure: preserve (`v ⊑ D'` by recursion on the source value), reflect (ApproxLR by depth), and `Calls`/`CarEntry`/`collect`.
  * Lost: ApproxLR's `fun-obs` field (which exists only for `project`) and the `project` cases of the fundamental lemmas.
  * The component selectors `Untag`/`tag-obs` stay: `get` and `case` need them, not `project`.
  * Expect 552 → about 500–540. **The finding: the denotational cost of delay is not caused by dynamic typing.**
  * **[P0]** 552 → 524. Gone (33 lines): `fun-obs` (10), `acc-preserve` (7), `acc-reflect` with `untag-ne` (8), and the `project` cases (8). Added (5): the second coercion's case in each lemma and the length of a list of types. `Calls`, `CarEntry`, `collect`, the fuel `ApproxLR≤` with `ApproxLR-depth-irrelevant`, `tag-obs` and the closure case are unchanged.
* **Adequacy:** the logical relation is by recursion on the denotational value d (`proof/Adequacy/LogRel.agda`), unchanged, with `fold`/`unfold` trivial.

### 3.2 Why the type index cannot replace the depth

Try `R_A(D, V')` by recursion on the Clos3 type A:

* `R_{A⇒B}(D, V') := … ∀ Calls V' U W. R_A(E, U) → R_B(D ● E, W)`. This is fine, since A and B are smaller.
* `R_{μX.A}(D, V') := R_{A[μX.A/X]}(D, V')` (`fold` is the identity on denotations). This is **not structurally smaller**.
  * Take `A = μX. X ⇒ Int`. Then `R_A` unfolds to `R_{A ⇒ Int}`, whose `app-obs` needs `R_A` on the arguments: the same type.
  * Agda rejects the definition, and no other order on types repairs it: unfolding grows the type.

What does decrease is the **depth of the finite target approximant**: the arguments U and results W of `Calls V' U W` are shallower than V' (`Bnd-Calls-args`, `Bnd-Calls-apps`). That is exactly today's `ApproxLR≤` fuel, with `ApproxLR-depth-irrelevant` to show the fuel doesn't matter.

* With the depth as the measure, the type index is redundant. Values in the graph model are untyped, and `fold` doesn't change them.
* Indexing *additionally* by type would only rule out impossible cases (a pair at `Int`). That saves a few lines per case but costs a typed environment relation.
* **Recommendation:** keep ApproxLR untyped, as today.
* A variant where `fold` adds a tag in the domain would make `unfold` decrease the depth. It still needs the depth (the type grows), so it buys nothing.

**[P0]** Confirmed in the proof: ApproxLR is the typed pipeline's, minus `fun-obs`, untyped, and recursive on the depth of the approximant. Its `app-obs` is what needs a measure. It quantifies over the arguments `U` and results `W` of `Calls V U W`, which are shallower than `V`, and over every `E` of the source. At `μX. X ⇒ Int` the argument and the function have the same type, so no type-indexed definition of `app-obs` is structurally recursive. It cannot be an inductive datatype instead either, since the relation occurs negatively in `app-obs`.

**For the paper.** The depth index is the denotational counterpart of step indexing (Appel–McAllester; Ahmed). It is needed because of recursive types, whether `Any` or a user-written μ, not because of dynamic typing or errors. So the experiment keeps ApproxLR load-bearing in a statically typed, error-free language, which strengthens the related-work claim ("indexed by finite values, not types") rather than weakening it.

### 3.3 CEK machine + simulation

* Typed values gain `fold v`, as `dyn G v` today, and frames gain `foldK`/`unfoldK`, as `injK`/`projK`. The `projK` step always succeeds.
* Per pass: a `project` failure case (`stops`) goes, and a total `unfold` case comes.
* The value relations stay first-order and inductive, with one `fold` constructor.
* Expect about −3 to −8 per pass and the semantics about −15. The heterogeneous environments cost about +0 to +20, mostly in optimize.
  * **[P0]** Per pass −3 to −13 (enclose 106 → 93, optimize 133 → 127, concretize 115 → 111, delay 99 → 96), the four machines 317 → 303. The heterogeneous environments cost nothing net. The machines collect a tuple's values newest first into `All Val Δ'`, and the tuple's type is `tup (Δ' <>< Δ)` (reverse-append), which needs no rewriting as the values come in. So the length equations of the typed machines and their lemmas (`Common`, 30 lines) go. Their counterpart is 3 lines of infrastructure (`_<><₂_`).

### 3.4 Clocked interpreter

As CEK: `unfold` on `fold v` returns v, and there is no error result. This is the smallest change of any column. Expect it to remain the smallest column.

### 3.5 Reduction semantics

* `unfold (fold V) ⟶ V`, with `fold V` a value. One congruence per construct, as for `inject`/`project` now, minus the stuck/error case.
* The typed substitution kits are unchanged: types are closed.
* Note: today cast insertion costs 300 lines in this column. That cost disappears, but it is outside the like-for-like rows anyway.

### 3.6 Errors, observations, adequacy

* **Does anything trap?** No.
  * `unfold` is total (iso-recursive, typed values).
  * `case`/`get` are typed; `sub`/`eq` are total.
  * There are no free variables (no `{ω}` from ρ₀).
  * X86 has no `chk`. Erased to untyped X86, the code reaches none of X86's traps (the assurance argument, minus `chk`).
* **Observation.** Restrict `main` to ground type (`Int`).
  * **[P0]** Not needed for the pilot's theorems, which hold for a closed program of any type: the CEK machines observe a function as `o-fun`, as today, and the graph-model theorem is about constants and nonemptiness. The restriction matters only for P2's end-to-end `Equivalent` from the graph model.
  * The graph model's "same constants, nonempty together", plus adequacy, plus a lemma per machine that it never stops with `o-error` (a few lines, by inspection of the typed step function), gives `Equivalent`.
  * The four columns state **the same theorem**, which removes the caveat "the theorems differ".
  * **The graph-with-errors column is unneeded**: it has nothing left to observe.
* **Adequacy** (reported separately):
  * ISWIMμ adequacy is about ISWIM's 653, minus its kind-error cases;
  * Clos5 and X86 adequacy lose `chk`/`project` (about −20 to −40);
  * no errors adequacy.
  * About 2100–2200 against 2214.

## 4. What the experiment shows

| # | hypothesis |
|---|---|
| H1 | **The cost of dynamic typing, with recursion held constant**: today's typed pipeline (one recursive type `Any`, a partial `project`, errors) against the μ pipeline (recursive types, total `unfold`, no errors), row by row. The like-for-like rows are the semantics, the passes from enclose to select, and the composition. Cast insertion is reported alongside: it is the front end that dynamic typing needs and the μ source does not |
| H2 | ApproxLR (depth-indexed) is still needed and graph delay barely shrinks. Delay's denotational cost comes from the change of representation plus recursive types, not from errors |
| H3 | Recursion through μ costs no column more than a congruence (no least fixed point, no self parameter), as it costs nothing today |
| H4 | The ranking of styles is unchanged (interpreter < graph ≈ CEK < reduction); report whether graph and CEK swap |
| H5 | With an error-free typed source, the graph model alone (plus adequacy) states the operational theorem: a fifth column is unnecessary |

**Report:**

1. the four-column table (`loc.py --mu`);
2. μ against today's typed pipeline row by row, with today's "total without cast insertion" (and without simplify, unless it is ported);
3. graph delay broken into relation, preserve and reflect, showing what left with `project`;
4. the audit surface.

## 5. Plan and estimate

| phase | content |
|---|---|
| P0 pilot | ISWIMμ → Clos4μ (enclose, optimize, concretize, delay) in **graph + CEK**; confirm that ApproxLR ports unchanged and measure H1/H2 on the CC passes; go/no-go. **[P0] Done**: graph model 908 → 842, CEK 800 → 730 on the rows of these four passes and the four languages' semantics (with `Ops` and `Common`); ApproxLR ported minus `fun-obs` |
| P1 | Clos5μ…X86μ, all four columns, composition |
| P2 | adequacy (ISWIMμ, Clos5μ, X86μ) and the no-error lemmas, giving the end-to-end `Equivalent` from the graph model |
| P3 (optional) | port simplify to ISWIMμ (typed cp0; folding through `unfold (fold V)` is one more known-value rule) |

**Lines** (today = typed pipeline without simplify and cast insertion):

| row | graph | CEK | interpreter | reduction |
|---|---|---|---|---|
| semantics | 450 → 410–440 | 684 → 650–680 | 442 → 420–440 | 1068 → 1030–1070 |
| lemmas shared by the passes | — | 55 → 50–60 | — | — |
| enclose + optimize + concretize | 197 → 190–230 | 354 → 330–380 | 135 → 125–160 | 544 → 530–590 |
| delay | 552 → 500–540 | 99 → 90–100 | 35 → 30–35 | 142 → 135–145 |
| globalize … select | 495 → 470–500 | 642 → 620–650 | 419 → 400–420 | 810 → 790–820 |
| composition, shared | 28 | 47 | 48 | 42 |
| **total** | **1722 → 1620–1720** | **1881 → 1820–1900** | **1079 → 1040–1100** | **2606 → 2540–2660** |
| graph model with errors | 2488 (without cast insertion) → **none** | | | |

* **Shared code** (languages and passes, not counted): about the same as today, with about +40 for type substitution and about −30 for `Tag`/`_≟_`. Infrastructure for heterogeneous vectors and thinnings (optimize's pruning) is about 80–150.
* **No least-fixed-point infrastructure.**
* **New code:** about 6–8k lines, mostly a mechanical copy-and-edit of `agda/` (as the typed port of PRs #55/#56 was).

**Risks:**

* **Green slime.** Matching a term of a concrete type (`Tm Γ (base Int)`) against `unfold`, whose index is `A [ μ A ]`, cannot be unified by Agda. Mitigation: `unfold` takes an equation (`A [ μ A ] ≡ B`), or the relevant functions stay type-generic. Settle this in P0.
  * **[P0] Settled: no equation.** `unfold : Tm Γ (μ A) → Tm Γ (A [ μ A ])` and the machines' `foldK : Cont (μ A) → Cont (A [ μ A ])` keep the plain index. As the pilot confirmed, Agda cannot split such a term or continuation at a concrete type. But no definition or proof does: every one splits terms, continuations and their relations at a generic type. That is the discipline the typed pipeline already follows for `prim`, whose index `out-flat p` has the same property. Where a value is split at `μ A` (`ret (fold v) (unfoldK κ)`, and the same case of each simulation), Agda's coverage checker splits the continuation first, at the generic type.
* **Heterogeneous environments.** **[P0]** Resolved for P0 (see §2.2 and §3.3). The X86 existential over a `Ctx` remains for P1.
* **Heterogeneous environments.** Optimize's pruning over `All (Tm Γ) Δ` needs thinnings, and the X86 existential hides a `Ctx`. This is the largest unknown in the shared code.
* **The predicted small change in graph delay could be wrong** in either direction. That is the point of P0.
* **No simplify in round 1** means totals are comparable only row by row.
* **Maintenance:** a third pipeline.

## 6. Open questions (with recommendations)

1. **Iso- or equi-recursive?** Iso, with `fold`/`unfold` as coercions that vanish at run time (§1.1).
2. **`rec`/`fix` as a construct?** No: Z is typable through μ, so divergence and recursion are in the language. If wanted, offer it as front-end sugar, never as a construct: as a construct it would need a least fixed point in the graph model and a self parameter, which today's pipeline avoids.
3. **An `error` construct, to embed untyped ISWIM faithfully?** No. Today's pipeline is that design point. Leaving it out is what makes H1 a clean comparison.
4. **Contractive μ only?** Yes. It costs nothing and keeps unfolding productive.
5. **Make ApproxLR type-indexed as well?** No. The type index can't carry the recursion (§3.2) and the values are untyped. Report the failed type-indexed definition as the argument, not as code.
6. **Parallel copy, or μ alongside `Any` in one `Ty`?** A parallel copy (`agda/Mu/`). Alongside would mix `project`'s failure cases into the error-free column.
7. **Observation?** `main : Int`, so the four end theorems coincide.
8. **Simplify?** Omit it in round 1. Port it in P3 if the paper needs totals.
9. **Fold in X86: a `movq` or a pure typing coercion?** A `movq`, as `inject` is today. Select stays uniform, and the erasure gives exactly today's instructions.
10. **Paper placement.** A section, "Errors versus recursion", with the row-by-row table of today's typed pipeline against the μ pipeline, and §3.2's argument that recursive types, not errors, need the depth index. No fifth column.

# History of the delay-pass relation (and related relations) in jsiek/denotational_semantics

Sources: `git log --all`, files in `agda/old/` (final states of the 2019–2022 work), deleted files via `git show`, GitHub issue #1 and PRs #2, #12, #15, #17, #18, #19, `notes.txt`, `blog/stuck.md`, `papers/PLDI-2027/loc.md`, and the blog post at
https://siek.blogspot.com/2023/06/help-were-failing-to-prove-correctness.html .
"Record" means a file, commit, issue or PR says it. "Inference" means it is my reading.

Kinds of relation:
- **A (adequacy).** Relates a denotation to an operational semantics.
- **B (two denotations).** Relates the denotations of a compiler pass's source and target. Delay is the main case.

Authors: Jeremy Siek (`jsiek`, also "Jeremy G. Siek") and `madheime`, who made every 2021-11 to 2022-05 commit on delay. The 2026-10 commits carry `Co-Authored-By: Claude`.

---

## 1. Timeline

| # | Kind | Date | Ref | Relation shape | Recursion | Direction | Outcome |
|---|---|---|---|---|---|---|---|
| A1 | A | 2019-04 – 2019-06 | `agda/old/Adequate{1,2}.lagda`, `AdequacyCallByName/CallByValue/ISWIM.agda` (7959762, 8b16460, 061c7fb, b374e88) | one denotational value vs one closure or value (`𝕍 : Value → Clos → Set`) | structural on the value (⊔ split) | denotation ⇒ operational | complete (the 2017-paper / PLFA line) |
| B0 | (B, no relation) | 2019-06-29 – 2020-05 | `agda/old/ClosureConversion.agda` (d3b0f86 "finished closure conversion!") | none: goal is equality `ℳ (𝒞 M) ≃ ℰ M`, closures as curried n-ary functions in the same domain | — | equality | only the transformation is finished; holes `compress-pres`, `apply-curry` |
| A2 | A | 2021-08-04/09 | `agda/PValue.agda` (548cbf5, d23d851) | one value vs one value; a function's argument is a **finite list** `𝕍s V c` | structural on the value | den ⇒ op | complete |
| B1 | B | 2021-07-15 – 07-29 | `agda/old/Delay.agda` (72a2016 … bad7e05), Siek | single value ≅ single value, lifted to **set vs set** both ways: `D₁ ≈ D₂ = D₁ ⪅ D₂ × D₁ ⪆ D₂` (∀∃ both ways) | inductive on values; logical relation on set-functions at binders | both | abandoned; backward lambda, app, tuple holes |
| B2 | B | 2021-08-13/15 | `agda/old/DelayClos.agda` (5e1a8e1, 765679e), Siek | single value ≅ single value, source functions annotated with free variables (`fvs ⊢ V ↦ w`); `to` function | inductive on values | **cut down to forward only** (`≲`) | partial; holes |
| B3 | B | 2021-11-21 – 12-04 | `agda/NewDelayCorrect.agda` → `GraphModel/DelayCorrect.agda`, madheime | function `to : Value → Value` (annotated source values) | structural on one value | forward | **complete** ("delay pass forward direction complete", 88d3be7) |
| B4 | B | 2021-12-03 | same file (bb9636b), `delay-val`/`dv` | inductive value vs value, with ∃ target environment | inductive | forward | all holes; a comment summarizes the obstruction |
| B5 | B | 2021-12-09 – 2022-01-07 | same (28e6b3d, 20d029b, 4e2d805), `fro : Value → Value` | target value ↦ source value | structural on one target value | backward | all cases but **app**: car and cdr membership don't give one pair |
| B6 | B | 2022-01-26 | `GraphModel/DelayCorrectSal.agda` (1a84f1b) | unary `salient` on target values + `fro` | structural | backward | 22 holes; `terminating-has-salience` open |
| B7 | B | 2022-01-26 | `GraphModel/DelayCorrectRel.agda` | `~del` value vs value with a negated premise (`--no-positivity-check`) | inductive | both | backward closure, app, tuple, case holes |
| B8 | B | 2022-01-26 | `GraphModel/DelayCorrectSet.agda` | `_~d_ : 𝒫 Value → 𝒫 Value → Set₁`, **infinite set vs infinite set** | inductive with element witnesses | both | only var, lit, inl, inr |
| B9 | B | 2022-02-02 – 02-15 | `DelayCorrectSingle/Multi/AnnLam.agda` (ac50238, 9985092, b7d0aab) | `~to`/`~tos` pointwise; `fro` + "smash closure" of target denotations | structural | both | Single: the single-value relation was found too weak (a value needs several related values). AnnLam: app goes through via `keylemma'`; `smash-⟦⟧'` unproved |
| B10 | B | 2022-02-18 – 03-29 | Filter model: `Model/Filter/DelayCorrect.agda` → `Correctness/Delay/PreserveAnnFunIswim.agda`, `ReflectIswimIswim{,Fail}.agda` | `to`/`fro` with ⊔ values; a `failure : 𝒫 Value → Value → Set₁` | structural | forward nearly done; backward partial | forward: termination hole at ⊔ inside a closure. Fail variant: app trivial, closure intro breaks |
| B11 | B | 2022-03-29 – 04-13 | `ReflectIswimIswimGood.agda`, `ReflectIswimGood.agda`, `Clos4Good.agda`, `Goodness*.agda`, `TtoG` (7e524c5, dcddd61) | "Good" target semantics (restricted pairs) + `mkGood ctxt d`; `has-good-related-subset` (value vs subset) | structural, context value threaded | backward | reflect into Good done; Good ⊇ target (`TtoG`) all holes |
| B12 | B | 2022-03-09 | `Model/Graph/Correctness/DelayCorrectRel.agda` (fea5cf3) | `~tos`: source list vs target list (each source element related to All target elements) | inductive | forward | closure case holes |
| B13 | B | 2022-04-23 | `DelayIswimIswimReflect.agda` (b89f30e, ff4edb0) | `fro c T Dₜ Dₛ`: **infinite set vs infinite set**, indexed by target **type** and a **step count** c | course-of-values on c, then on the type | backward | var only; ff4edb0: "this works for everything but function elimination" |
| B14 | B | 2022-04-27 – 05-04 | `DelayIswimIswimReflectNew.agda` (f1e4f17 "pointed-set relation", 73bc8eb "element-directed logical relation") | `fro dₜ Dₜ Dₛ`: one **target point** dₜ, with an arbitrary target set Dₜ and an arbitrary source set Dₛ; `froList` over finite lists | structural on the target point | backward | var, lit, inl, inr. Closure-intro `cond` and the app source witness open; 3 postulates. **Last attempt before the 2026 restart** |
| B15 | B (paper) | 2023-06-08/09 | `blog/stuck.md`, blog post, `notes.txt` (85a504b, 397a375) | (i) ∀∃ both ways over sets with an element equivalence `~`; (ii) "bulk" relation `D₁ ≈ D₂` on **infinite sets**, guarded by ▷ | guarded (later ▷) | both | not mechanized; the post asks for help |
| A3 | A | 2024-12-15 | `step-indexed/DTLC.agda` (5e5dc21 …) | unary step-indexed predicate on interpreter values/terms (`Setᵒ`, `▷ᵒ`); a term's denotation must be nonempty | step-indexed logic | op ⇒ den | unfinished (11 holes) |
| B16 | B | 2026-10-09 | **issue #1** (proposal); **PR #2**: 753d58a, ae14b2d | `R k V' D`: **finite list of target observations vs arbitrary source set** (record `Obs`); forward mirror `V ⊵ D'` | fuel k bounding `depth` of the list; `R-irr` | reflect (forward mirror for preserve) | **complete**, both directions, no holes or postulates |
| B17 | B | 2026-10-10 | PR #12 (4abd74d, d76a54c) | same; single `Entry` parameter, `Calls` batches | same | both | refactor |
| A4 | A | 2026-10-11 10:17 | dc1295a `Operational/Adequacy/LogRel.agda` | `𝕍 d v`: one domain element vs one CEK value; function arguments are finite lists `𝕍s V v` | structural on d | den ⇒ op | complete |
| B18 | B | 2026-10-11 12:33 | PR #15 (7426353) | preserve: `v ⊑ D'`, **single source value vs target set**. Reflect keeps the finite-list relation | ⊑ structural on v | preserve | complete; 1358 → 832 lines |
| B19 | B | 2026-10-11 | PR #17 (7a29d9f, e31e23d) | `R V D = R′ (suc (depths V)) V D`, fuel private; `Calls` a predicate | hidden fuel | reflect | complete |
| B20 | B | 2026-10-11 | PR #18 (b77b7f7), 2dce586 | joined pairs ⦅u,v⦆; finite lists still needed | — | reflect | 2dce586: "joined pairs were tried and do not remove Calls or the fuel" |
| A5 | A | 2026-10-11 – 10-14 | Clos5, X86, graph model with errors, X86ᵀ adequacy (4693438, 170f4a3, 9ef11c3, e457fa8, a344d2d) | `𝕍` one element vs one machine value; lists for arguments; a location vs a set (∀ elements) | structural on d | den ⇒ op | complete |
| B21 | B | 2026-10-13/14 | a8f1854 (untyped graph model with errors); b369ec0, 7793a82 → 7e62235 (typed: `agda/proof/Correctness/{Graph,GraphErr}/DelayRel.agda`) | same `Obs`/`R′`/`R`. Errors add `err-obs`, `kind-obs`; typed adds `fun-obs` | fuel = depth | reflect | complete; "cannot be by recursion on types: Any makes the types recursive" |

---

## 2. The attempts in detail

### A1. Adequacy, 2019 (kind A)

Context for the author's "single value" recollection: this is the 2017-paper / PLFA Adequacy line. `agda/old/Adequate2.lagda:644-665`:
```agda
𝕍 (v ↦ v') (clos (ƛ M) γ) =
     (∀{c : Clos} → 𝔼 v c → AboveFun v' → Σ[ c' ∈ Clos ] (γ , c) ⊢ M ⇓ c'  ×  𝕍 v' c')
𝕍 (v₁ ⊔ v₂) (clos (ƛ M) γ) = 𝕍 v₁ (clos (ƛ M) γ) × 𝕍 v₂ (clos (ƛ M) γ)
𝔼 v (clos M γ) = AboveFun v → Σ[ c ∈ Clos ] γ ⊢ M ⇓ c × 𝕍 v c
```
- It relates one value to one closure, by structural recursion on the value. Call-by-value (`AdequacyCallByValue.agda`) and ISWIM (`AdequacyISWIM.agda`) have the same shape.
- In `agda/PValue.agda` (2021-08), where values are lists, the arrow's domain is a finite list: `𝕍 (V ↦ w) (val-clos N γ) = ∀ c → 𝕍s V c → …`, with `𝕍s (v ∷ V) c = 𝕍 v c × 𝕍s V c`. A set relates to a value through all of its elements (`𝔾-ext`: `∀ v → v ∈ D → 𝕍 v c`).

### B0. ClosureConversion.agda, 2019–2020 (kind B, no relation)

- d3b0f86 (2019-06-29) "finished closure conversion!" is only the compiler function: 199 lines, no semantics, no theorem.
- Later versions (to f42acbd, 2020-05) aim at equality of denotations, `𝒞-correct : ℳ (𝒞 M) ≃ ℰ M`. The IR's closures are curried n-ary functions in the *same* domain, so no cross-language relation is needed.
- Holes remain (`compress-pres`, `apply-curry`).
- An external datum from the same period: a 2018 TYPES-list thread in which Siek asked for literature on closure-conversion correctness for the untyped λ-calculus with respect to a denotational semantics (https://lists.seas.upenn.edu/pipermail/types-list/2018/002074.html; seen only in search snippets, since the archive returned 404 when fetched).

### B1–B2. Siek's first delay relations, July–August 2021 (kind B)

`agda/old/Delay.agda`:
```agda
data _≅_ : Value → Value → Set where
   ≅-↦ : ∀{u v w v' w'} → v ≅ v' → w ≅ w'
       → v ↦ w ≅ ((const 0 ↦ (u ↦ (v' ↦ w'))) ⊔ (const 1 ↦ u))
D₁ ⪅ D₂ = ∀ u → D₁ u → Σ[ v ∈ Value ] D₂ v × u ≅ v
D₁ ⪆ D₂ = ∀ v → D₂ v → Σ[ u ∈ Value ] D₁ u × u ≅ v
D₁ ≈ D₂ = D₁ ⪅ D₂ × D₁ ⪆ D₂
≈ₐ-ν : (∀ d₁ d₂ → d₁ ≈ d₂ → _≈ₐ_{b} (D₁ d₁) (D₂ d₂)) → _≈ₐ_{ν b} D₁ D₂
delay-correct : ≈-env ρ ρ′ → (ℐ⟦ M ⟧ ρ) ≈ (𝒞⟦ delay M ⟧ ρ′)
```
- This is a single-value relation lifted symmetrically to arbitrary (infinite) sets, with a logical relation on set-functions at binders.
- The forward half of the lambda case is proved. Backward lambda, app and tuple are holes.
- In `DelayClos.agda` (765679e), source functions are annotated with their free variables, the `to` translation appears, and the theorem is weakened to forward only (`≲`). The symmetric version is commented out.

(Inference.) In August 2021 Siek proved the PValue adequacy (A2) in the days just before writing B1/B2. Both are "single value, structural" relations. Nothing in the record states that one was carried over to the other.

### B3–B12. madheime, November 2021 – April 2022 (kind B)

- **Forward worked early.** B3, `to` by structural recursion on an annotated source value, then `delay-preserve : d ∈ ⟦M⟧ρ → to d ∈ ⟦delay M⟧'(map to ρ)`. Complete at 88d3be7 (2021-12-04). It works because the source closure value carries its free-variable values as a finite annotation.
- **Backward was the obstacle in every variant.** The recurring problem: a target call takes its code from `car` and its environment from `cdr` separately, and membership in each does not yield a single pair. With the split half-pairs `⦅u∣`/`∣v⦆`, this is the "mixing" problem.
  - B5, `fro : Value → Value`, proves every case but app.
  - Other variants move the difficulty elsewhere instead of removing it:
    - B10-Fail makes app trivial but breaks closure introduction.
    - B9-AnnLam pushes it into an unproved "smash-closed" property of target denotations.
    - B11 pushes it into an unproved "every target value has a Good counterpart" lemma (`TtoG`).
  - Technical observations recorded in the files' comments (paraphrased):
    - bb9636b proposes giving up a functional relation and relying on continuity for the existence of finite sets.
    - `DelayCorrectSingle.agda` concludes that relating single values is too weak: one value needs several related values.
    - `Goodness.agda` notes that a function value with a smaller codomain is evaluated in a larger context.
- **Set-against-set relations.** B8 `_~d_ : 𝒫 Value → 𝒫 Value → Set₁` (2022-01-26) and B13.
- **B13, type- and step-indexed (b89f30e, ff4edb0; 2022-04-23):**
```agda
fro-step (suc c) rec (Clos n FVTs) Dₜ Dₛ =
   (∀ j → (j≤c : j ≤′ c) → ∀ TE Eₛ Eₜ → projₙ rec j j≤c TE Eₛ Eₜ
     → Σ[ Tapp ∈ Type' ] projₙ rec j j≤c Tapp (((Car Dₜ) ● (Cdr Dₜ)) ● Eₜ) (Dₛ ● Eₛ))
fro-step zero rec (Clos n FVTs) Dₜ Dₛ = Lift _ False
fro = cRec (λ _ → Type' → 𝒫 Value → 𝒫 Value → Set₁) fro-step
```
  - Infinite set vs infinite set, indexed by target type and a step count. This is the only step-indexed delay relation that was mechanized.
  - Comment (ff4edb0): "this works for everything but function elimination, for which we need more information".

### B14. The "pointed-set" / "element-directed logical relation", April–May 2022 (kind B): the direct predecessor

`agda/old/Compiler/Model/Graph/Correctness/DelayIswimIswimReflectNew.agda` (f1e4f17, 73bc8eb, final state):
```agda
fro : ∀ (dₜ : Value) → (Dₜ : 𝒫 Value) → (Dₛ : 𝒫 Value) → Set₁
froList (v ∷ []) Dₜ Dₛ = fro v Dₜ Dₛ
froList (v ∷ (v' ∷ V)) Dₜ Dₛ = fro v Dₜ Dₛ × froList (v' ∷ V) Dₜ Dₛ
fro (const k) Dₜ Dₛ = Lift (lsuc lzero) (Dₜ ≃ Dₛ)
fro ⦅ (fv ∷ FV) ↦ ((v ∷ V) ↦ w) ∣ Dₜ Dₛ = ∀ Eₜ Eₛ (Eₜ~ : consis Eₜ) (Eₛ~ : consis Eₛ) (v∷V⊆Eₜ : mem (v ∷ V) ⊆ Eₜ)
              → (froE : froList (v ∷ V) Eₜ Eₛ)
             {- the next premise is a bit odd ... how are we handling the case where this fails? -}
             {- ... Is this fine, or is it too strict and we need to go back to 'Type's? -}
              → (fv∷FV⊆CdrDₜ : mem (fv ∷ FV) ⊆ Cdr Dₜ)
              → fro w (((Car Dₜ)  ● (Cdr Dₜ)) ● Eₜ) (Dₛ ● Eₛ)
fro ∣ (v ∷ V) ⦆ Dₜ Dₛ = froList (v ∷ V) (Cdr Dₜ) (Cdr Dₛ)
fro (left dₜ) Dₜ Dₛ = fro dₜ (GetLeft Dₜ) (GetLeft Dₛ)
```
- It is indexed by **one target element** (or a finite list, via `froList`) and structural on it. Both carriers are **arbitrary sets**: the target context Dₜ and the source Dₛ.
- Direction is backward. The theorem also asks for a source witness, `Σ[ d ∈ Value ] d ∈ ⟦ M ⟧ ρ × fro d' …`.
- Status:
  - Proved: var, lit, inl, inr.
  - Postulated: `⟦⟧-consis`, `⟦⟧'-consis`, `fro-cong`.
  - Open: the closure case's `cond` and the source witness in app; 28 live holes.
- Issue #1 diagnoses why the closure hole could not be filled: "the premise relates only the listed elements `V` of the argument, while the body's IH needs the whole argument set `Eₜ` related; the context `Dₜ` is an infinite set, so it can't be shrunk to fit."
- (Inference.) The argument order in `froList V Eₜ Eₛ` in the function clause looks swapped relative to `fro dₜ Dₜ Dₛ` in the first version.

### B15. June 2023: the blog post and the "bulk" relation (kind B, paper only)

- `blog/stuck.md` (85a504b, 2023-06-08) is the text of the post "Help! We're Failing to Prove Correctness of Closure Conversion using Denotational Semantics (Graph Models)" (siek.blogspot.com, 8 June 2023).
- It states the target relation as symmetric ∀∃ over sets with an element equivalence `~`, and gives the junk-entry counterexample `{⟨0,0⟩ ↦ (6 ↦ 6)}` against the source's "plus nine" function. It says "We have tried several approaches … but ran into road blocks with each one of them" without listing them.
- Comments on the post:
  - gasche: relate subterms by a logical relation.
  - Neel Krishnaswami: a logical relation, along the lines of Minamide–Morrisett–Harper; "easier over denotations".
  - Siek asks for resources, mentions Max's suggestion of Pitts' "Relational Properties of Domains", and asks whether a typed target is needed.
  - An anonymous commenter points to Pitts Thm 6.5.
- The next day (397a375, 2023-06-09), `notes.txt` gained a guarded "bulk" relation on whole infinite sets:
```
D₁ ≈ D₂ =
  (IsFun(D₁) and IsInjC(D₂) and
   ∀ D₃ D₄. ▷ (D₃ ≈ D₄) → ▷ ((D₁ ▪ D₃) ≈ (let F = (ProjC D₂) in F[0] ▪ F[1] ▪ D₄)))
  or
  (∃ n. IsTup(D,n) and IsInjT(D₂,n) and ∀ i ∈ 1..n, ▷ (D[i] ≈ ProjT(D₂)[i]))
```
- (Inference from the dates.) It responds to the comments. It was never mechanized. Issue #1 later says that "in an untyped language this definition is mixed-variance, so it needs ▷ … a denotational semantics has no evaluation step to discharge the ▷".

### B16–B21. The finite-list-vs-set relation, October 2026 (kind B)

**First appearance: issue #1**, opened 2026-10-09 20:38Z under the `jsiek` account. The body ends "Generated with Claude Code" and says "The proposal has been checked on paper only".
```
For a finite list V' of target values and a source set D, define V' ⊳ D by recursion on the depth of V':
(a) const k ∈ V' ⇒ const k ∈ D   (b) V' ≢ [] ⇒ D nonempty
(c) for every consistent U' ⊆ args(V') and every source set E with U' ⊳ E: app(V', U') ⊳ (D ⋆ E)
    where app(V', U') = [ w | ⦅ FV ↦ (U₀ ↦ w) ∣ ∈ V', FV ⊆ cdr(V'), U₀ ⊆ U' ]
(d) projections, (e) left/right
```
- Rationale, verbatim from the issue:
  - "the indexed side is a **finite list of observations** from the side being simulated; the other side is an **arbitrary set**. The recursion is then well-founded on depth, with no ▷."
  - "Clause (c) is the only place car and cdr meet, and they meet inside the finite V'."
- It contrasts itself with "every attempt so far (2021–2022) [which] tried to relate denotations either **element by element** or **as whole infinite sets**".
- It explicitly rejects Pitts as "heavy machinery".
- It notes that a finite V' is an intersection type, and that clause (c) resembles opening an existential package.
- The record does not show whether the idea came from Siek or from Claude: the issue is Claude-written under Siek's account.

**First mechanization: 753d58a** (2026-10-09 17:03 -0400, PR #2, merged the same day), "finite-observation logical relation, reflect direction":
```agda
record Obs (R : List Value → 𝒫 Value → Set₁) (V' : List Value) (D : 𝒫 Value) : Set₁ where
  field
    const-obs : ∀ {B} (c : base-rep B) → const c ⋵ V' → const c ∈ D
    ω-obs : ω ⋵ V' → ω ∈ D
    nonempty-obs : V' ≢ [] → nonempty D
    app-obs : ∀ U' E → mem U' ⊆ Args-of V' → consis (mem U') → R U' E
            → ∀ W' → mem W' ⊆ Apps V' U' → R W' (D ● E)
    nth-obs : … ; left-obs : … ; right-obs : …
R : ℕ → List Value → 𝒫 Value → Set₁
R zero V' D = pTrue
R (suc k) V' D = Obs (R k) V' D
```
- ae14b2d added the forward mirror (source list vs target set), made generic in `DelayFiniteRel`, and the end theorem.
- PR #2's report:
  - every case closed in both directions;
  - "`R-irr` needs clause (c) to quantify only over `U ⊆ args(V)` … load-bearing";
  - fuel was chosen over well-founded recursion.

**What it solved over B14 (record plus inference).**
- B14 indexed by a target point but kept the whole infinite target context Dₜ. It formed the call as `(Car Dₜ ● Cdr Dₜ) ● Eₜ` and needed `mem FV ⊆ Cdr Dₜ`.
- B16 drops the target set entirely. The finite list V' *is* the target side: car and cdr meet only inside V' (`Calls`/`app(V',U')`), and the argument side is likewise a finite list U' related to an arbitrary source set E.
- That removes the "Dₜ can't be shrunk" obstruction, and with it B14's open closure case.
- The source witness `Σ d ∈ ⟦M⟧ρ` disappears, because the relation is to the source set itself.
- Recursion on the depth of a finite list replaces B13's type and step index and B15's ▷.

**Later changes**
- PR #12: one `Entry` parameter; `Calls` batches.
- PR #15 (7426353, 2026-10-11): forward replaced by the structural single-value relation:
```agda
_⊑_ : Value → 𝒫 Value → Set₁
(U ↦ w) ⊑ D' = Lift (lsuc lzero) (nonempty D') × (∀ E' → U ⊑* E' → w ⊑ D' ⊙ E')
(tup[ i ] d) ⊑ D' = d ⊑ Nth i D' ; left d ⊑ D' = d ⊑ Lefts D' ; v ⊑ D' = Lift … (v ∈ D')
```
  The commit message says this is "a logical relation v ⊑ D' between single source values and target sets, by structural recursion on v, so no fuel, depth bounds, Calls batches … are needed". Only reflect keeps the finite-list relation.
- PR #17 (7a29d9f): the fuel is hidden. `R V D = R′ (suc (depths V)) V D` is private, with `unfold`/`fold`. The reason given: "Agda does not see the recursion on depth as structural, and sized types and `Acc` are not options under `--safe` without funext."
- PR #18 and 2dce586: joined pairs ⦅u,v⦆ do not remove the need. "A call takes its code from car C and its free variables from cdr C separately … (this would be so even if pairs were single values)."
- a8f1854 (graph model with errors) adds ω and kinds. The typed versions (b369ec0, 7793a82, now `agda/proof/Correctness/{Graph,GraphErr}/DelayRel.agda` on origin/master) keep `Obs` with `fun-obs`/`kind-obs`. GraphErr/DelayRel's header says: "the relation cannot be by recursion on types: Any makes the types recursive". `loc.md` says the same: "The relation cannot be indexed by types."

### A4–A5. Adequacy, October 2026 (kind A)

- `agda/proof/Adequacy/LogRel.agda` (dc1295a, 2026-10-11 10:17), header "A logical relation 𝕍 d v, by recursion on the denotational value d":
```agda
𝕍 (V ↦ w) (clo N γ) = ∀ v → 𝕍s V v → Σ[ v' ∈ Val ] (v ∷ γ) ⊢ N ⇓ v' × 𝕍 w v'
𝔾 P ρ γ = ∀ x → P x → ∀ d → d ∈ ρ x → Σ[ v ∈ Val ] γ ‼ x ≡ just v × 𝕍 d v
```
- Clos5, X86, the graph model with errors and X86ᵀ reuse this shape: one element vs one machine value, with argument lists `𝕍s`, no depth or fuel index.
- **A ↔ B transfer.** No commit message or comment links the delay relations to the adequacy relations; the only mention of delay in the adequacy files is a remark on what closures look like after delay.
- (Inference from timing only.) The delay preserve relation `v ⊑ D'` (B18) has adequacy's shape: single value, structural, function clause quantifying over related arguments given as a list. It was committed about 2h15m after dc1295a.
- The reflect relation (B16) predates the 2026 adequacy relation (09 Oct vs 11 Oct) and has a different shape: a finite list vs a set, with a depth index.
- In 2021, PValue adequacy (A2, single value, list arguments) likewise just preceded Siek's single-value delay relations (B1/B2).

---

## 3. Evaluating the recollection: "single value; infinite sets; not the asymmetric version"

**"Previously defined such relations on a single value."**
- Correct for A: the 2019 adequacy proofs, PValue 2021, and the 2026 adequacy proofs are all single element vs single operational value, structural on the element.
- Also correct for B: Siek's 2021 `≅` (B1/B2) and madheime's `to`/`fro`/`dv`/`~del` (B3–B7, B10) are single-value and structural. The forward direction succeeded with a single-value function `to` in 2021 (B3). The 2026 preserve relation `v ⊑ D'` (B18) is single value vs set, and it is current.
- So "single value" was never abandoned for the forward direction. It failed only for reflection.

**"…and on infinite sets."**
- Correct. Siek's `≈`/`⪅`/`⪆` (2021) are symmetric ∀∃ over arbitrary sets. madheime's `_~d_` (2022-01) and the type- and step-indexed `fro c T Dₜ Dₛ` (2022-04) are set vs set. The 2023 "bulk" ▷-relation (paper only) is also set vs set.
- The ∀∃ form and the bulk relation are symmetric and two-sided.

**"…but not the asymmetric finite-list-vs-arbitrary-set version."**
- Essentially correct, with one near miss to mention. madheime's 2022 "pointed-set" / "element-directed" `fro dₜ Dₜ Dₛ` (f1e4f17, 73bc8eb) is already asymmetric in the right direction: indexed by a target element or finite list (`froList`), against an arbitrary source set, structural on the target element, with a logical-relation function clause. That makes it the direct predecessor.
- It differs from the 2026 relation in four ways:
  - it keeps the whole infinite target set Dₜ as context, and forms calls from `Car Dₜ`/`Cdr Dₜ`;
  - it asks for a source witness element;
  - it recurses structurally on one point, not on the depth of a list;
  - it was never completed: the closure case was open.
- Other asymmetric relations in 2022 (`has-good-related-subset`, `failure D d`, `D ⊢ d ~good d'`) pair one value with a set, but they are not logical relations of this form.
- The relation in which **the finite list itself is the whole target side** (car/cdr meeting only inside the list, recursion on its depth, an arbitrary source set) first appears in issue #1 and commit 753d58a (both 2026-10-09). It has no earlier counterpart in the repository.
- **Suggested wording:** "Earlier attempts related single values (as in our adequacy proofs) or whole sets, and one late attempt related a single target point within an infinite target context to a source set. The relation that indexes by a finite list of target observations alone is new here."

## Provenance (from the author, 2026-10-14)
The 2026-10-09 relation came out of a conversation between the author and Claude (Opus 5.5), informed by the whole repository (including madheime's 2022 near miss) and specifically the June 2023 blog post. Indexing by depth was an idea the author had already considered; putting it together with an asymmetric relation in the style of madheime's `fro` (here: a finite target list against an arbitrary source set) was Claude's.

### Account from the originating session
At the author's request, the Claude session in which the relation arose gave this account of the reasoning (lightly edited):

1. The last attempt, `fro d' Dₜ Dₛ` (B14), indexes by a single target element but carries the whole infinite target set as context. The closure-case hole comes from that: the context cannot be shrunk, and only part of the argument set is related.
2. The "bulk" relation (B15) goes to the other extreme, relating whole infinite sets on both sides. That makes the recursion mixed-variance, so it needs ▷, and a denotational semantics has no evaluation step to discharge it.
3. A first idea was a Pitts-style approximation: index by element depth, like the projections πₙ. That fails directly, because a small output of a function can depend on an arbitrarily deep input.
4. What fixed it was two observations. A simulation only has to be one-sided, so only one side needs to shrink and the other can be any set. And the car/cdr matching has to happen inside the index for junk and mixing to go away, so the index has to be a finite set rather than a single element.

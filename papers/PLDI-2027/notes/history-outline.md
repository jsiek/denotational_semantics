# Outline: presenting the history of the delay relation in the paper

Goal: convey how hard the reflection direction of delay is, while keeping the focus on the technical background and on the insight behind the solution.

## Constraints (double-blind and tone)
- Earlier attempts in this repository may be described in the first person ("we tried…") without saying who "we" are.
- Citations of Siek 2017, PLFA and the 2023 blog post are written in the third person.
- Keep personal detail out: no dates, names, anecdotes or quotes that identify anyone. Paraphrase the technical content only.
- Do not link the repository in the submission; supplementary material is an anonymized copy.

## Structure: a tour of relation shapes, not a chronology
Each step is "a natural idea, and why it fails", so each failure motivates a part of the solution. Phrasing such as "we and others tried" gives enough history.

1. **Relate single values.**
   - This works for the forward (preservation) direction.
   - It breaks for reflection: a target call takes its code from `car` and its environment from `cdr` separately, so one target value cannot be matched with one source value.
   - Example: the junk entry `{⟨0,0⟩ ↦ (6 ↦ 6)}` against the source's "plus nine" function.
2. **Relate whole sets on both sides.**
   - The function case makes the definition recursive in both positive and negative positions, so it needs the later modality ▷.
   - A denotational semantics has no evaluation step to discharge the ▷.
3. **Index by element depth, in the style of Pitts's projections πₙ.**
   - This fails because a small output of a function can depend on an arbitrarily deep input.
4. **Index by one target point within an infinite target context (the near miss).**
   - The context cannot be shrunk, and only part of the argument set is related, so the closure case cannot be closed.
5. **The insight.**
   - A simulation needs only one side to shrink, and the `car`/`cdr` matching must happen inside the index.
   - So the index is a finite set of target values: its depth bounds the recursion, and the source side can be any set.
   - This is the approximant logical relation.

Step 5 is the payoff. It leads into the technical background:
- graph models;
- the finite-element tradition for adequacy (Martin-Löf, Winskel, Abramsky, and in the third person Siek 2017 and PLFA);
- Reynolds 1974's tower θ₀ = ⊤, θₙ₊₁ = B(θₙ) as the structural precedent for relations between two denotations.

## Sources
- Each step's evidence: `delay-relation-history.md`, where step 1 is B1–B12, step 2 is B8 and B15, step 3 is the originating-session account, and step 4 is B14.
- Citations: `related-work.md` (Part III).

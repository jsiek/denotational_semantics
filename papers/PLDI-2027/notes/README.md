# Notes for the related-work section

Research notes, not paper text, compiled on 2026-10-14 for the related-work and history parts of the paper, about the logical relation used for the reflection direction of the delay pass (the finite target list against an arbitrary source set; `agda/proof/Correctness/{Graph,GraphErr}/DelayRel.agda`).

- `related-work-literature.md`: the literature, with BibTeX. Part A covers relations for adequacy (a denotation against syntax or an operational semantics). Part B covers relations between two denotational semantics, which is where this relation belongs. Each claim is marked **[V]** (checked against the primary text) or **[U]** (unverified), and the file ends with the list of claims still to check. It also has a name check for candidate names ("finitary", "approximant").
- `delay-relation-history.md`: how the delay relation evolved in this repository from 2019 to 2026, with commits, issues and PRs, the quoted definitions and outcomes. Each attempt is labelled A (adequacy) or B (between two denotations). It ends with the provenance of the current relation.
- `history-outline.md`: an outline for presenting the history in the paper, as a tour of the relation shapes that were tried and why each fails, leading to the insight. It also lists the double-blind and tone constraints.

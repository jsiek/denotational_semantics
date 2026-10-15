# Related-work literature notes: logical relations over finite elements, recursive domains, and denotation-to-denotation relations

Legend: **[V]** = verified against the primary source text (quote given where possible);
**[U]** = unverified (secondary source or memory). "unverified" for any number not seen.

Our R, as a reminder: R V D relates a FINITE target approximation V (list of finite
graph-model values) to an ARBITRARY source denotation D ∈ 𝒫 Value; function case uses the
source model's own application D ● E; defined as a tower R′ 0 = ⊤, R′ (suc k) = Obs (R′ k),
R V D = R′ (suc (depth V)) V D, with index irrelevance above depth. Purpose: correctness of
the compiler pass delay (Clos3 → Clos4). Category: **B** (denotation-to-denotation).

Classification used throughout:
- **(A)** relation between a denotation (or finite elements/tokens/types of one) and
  syntax / an operational semantics / machine code — adequacy, computability, realizability.
- **(B)** relation between two denotational semantics, or within domains (D×D, D×D′).

---------------------------------------------------------------------------------------------

# Name check (candidate names for our R)

**Method.** I ran web searches (standard and extended) for the exact phrases and close
variants. I queried the arXiv API (abstracts) for `finitary AND logical AND relations`, for
`approximant AND "logical relation"`, and for `approximants AND "logical relations"`. I read the
full text of Jung–Tiuryn 1993 (author PostScript) and the O'Hearn–Riecke 1995 abstract (from
the Syracuse repository page). Semantic Scholar was rate-limited (HTTP 429) and DBLP returned a
bot challenge (HTTP 202), so **no DBLP, ACM DL or Google Scholar full-text search was
completed**. Absence of hits is therefore weak evidence. The author should run one Google
Scholar query for each exact phrase before submission.

## 1. "finitary logical relation(s)"

Exact phrase **not found** anywhere: web search (two variants), arXiv abstracts, Jung–Tiuryn
full text.

Near hits, all in the **same community** (PCF full abstraction and λ-definability) and all
with a **different meaning**:
- **O'Hearn & Riecke**, "Kripke Logical Relations and PCF", *Information and Computation*
  120(1):107–116, 1995, doi:10.1006/inco.1995.1103. Abstract [V, repository page]: "Sieber has
  described a model of PCF consisting of continuous functions that are invariant under certain
  (finitary) logical relations, and shown that it is fully abstract for closed terms of up to
  third-order types. We show that one may achieve full abstraction at all types using a form
  of 'Kripke logical relations' introduced by Jung and Tiuryn to characterize λ definability."
  Here "(finitary)" means **of finite arity** (n-ary relations, Sieber's sequentiality
  relations). Only the abstract was read [V]. Whether the body uses "finitary logical
  relations" as a term is [U].
- **Sieber**, "Reasoning about sequential functions via logical relations", in Fourman,
  Johnstone & Pitts (eds.), *Applications of Categories in Computer Science*, LMS Lecture Note
  Series 177, CUP 1992, pp. 258–269 [U: bib from secondary sources]. These are the relations
  O'Hearn–Riecke call finitary. Whether Sieber himself says "finitary" is [U].
- **Jung & Tiuryn**, "A New Characterization of Lambda Definability", TLCA 1993, LNCS 664,
  pp. 245–257 [V, author bib file]. The full text uses "Kripke logical relations with varying
  arity" and **never** "finitary" [V, grep of the full text, allowing for lost fi-ligatures].
- **"Finitary PCF"** is an established term in the same area: PCF over finite base types
  (Jung & Stoughton, TLCA 1993 [U]; Loader, "Finitary PCF is not decidable", TCS 266, 2001
  [U: title seen in search results; volume from memory]).

What "finitary" commonly means (general knowledge, [U] as to any particular source):
- *Finitary relation*: a relation of finite arity (Wikipedia "Finitary relation"; seen in
  search).
- *Finitary functor or monad*: preserves filtered colimits (Lawvere theories, algebraic
  theories).
- *Finitary projection*: in domain theory, a projection whose image is a (Scott/algebraic)
  domain; this underlies Amadio–Bruce–Longo's "finitary projection model" of polymorphism
  (LICS 1986) [U].
- Mulmuley's 1985 inclusive-predicate theory represents domains as **finitary projections** on
  Scott's universal domain [V, CMU-CS-85-149]. That puts the overload inside the B-relation
  literature itself.
- *Finitary semantics*: finite models (e.g. Grellois–Melliès, "Finitary semantics of linear
  logic and higher-order model-checking", arXiv:1502.05147 [V, title seen]).
- *Finitary vs. infinitary*: λ-calculus, logic.

**Risk.** In the most relevant reader population (logical relations and domain theory),
"finitary logical relations" is most likely to be read as **finite-arity** relations
(Sieber/O'Hearn–Riecke) or associated with **finitary PCF**. Neither matches our meaning
(binary; recursion on a finite approximant). The phrase is not a coined term, so there is no
priority clash, but the overload risk is **moderate to high** for PCF-semantics referees. If
used, define it in the first sentence and contrast it with finite-arity relations in a
footnote.

**Verdict: usable but overloaded.** There is no prior use as a name, and a known parenthetical
use in O'Hearn–Riecke has a different meaning (finite arity).

## 2. "approximant logical relation(s)"

Exact phrase **not found**: web search, and arXiv abstracts for approximant(s) + logical
relation(s). There were no exact hits for "approximant relation" in a semantics sense either.

The word "approximant(s)" already carries established meanings nearby:
- **Wadsworth/Böhm-tree approximants**: approximate normal forms, the "Approximation Theorem"
  for intersection types. Example [V, seen in search]: van Bakel's survey "Strict Intersection
  Types for the Lambda Calculus" defines approximants via λ⊥-normal forms, with the
  Approximation Theorem relating types of a term to types of its approximants.
- **Kleene/fixpoint approximants** f^n(⊥) and **syntactic approximants** fix^n in operational
  reasoning (Pitts-style "approximation lemma") [U].
- **Finite elements** of a domain, as approximants of an element [general usage].

Our sense ("a finite approximant of the target denotation") is close to the fixpoint/Böhm
sense. That is a natural fit rather than a clash, but intersection-type readers may expect
Wadsworth approximants (terms).

**Risk: low to moderate.** No prior name use was found.

**Verdict: safer, no prior use found.** It describes the asymmetric, finite-side indexing
better than "finitary". Its main drawback is a mild collision with Wadsworth "approximants"
(which are terms, not values).

---------------------------------------------------------------------------------------------

# PART A — Relations for adequacy / computability (denotation vs. syntax or operations)

## A1. Winskel 1993, *The Formal Semantics of Programming Languages*, ch. 13

```bibtex
@book{Winskel93,
  author    = {Glynn Winskel},
  title     = {The Formal Semantics of Programming Languages: An Introduction},
  publisher = {MIT Press},
  address   = {Cambridge, MA},
  series    = {Foundations of Computing},
  year      = {1993}}
```

Location **[V]** (read from a scanned copy of the 1993 MIT Press edition; table of contents
and running heads):
- Chapter 13 "Recursive types" (starts p. 251).
- §13.4 "Adequacy of eager semantics", pp. 262–267. **Lemma 13.7** (p. 264) — the claim
  "§13.4, Lemma 13.7" is **correct**. Lemma 13.8 (pp. 264–265) is the entailment/up-closure
  property; Theorem 13.9 (p. 265) is adequacy (t⇓ denotationally ⇒ t⇓ operationally);
  Corollary 13.11.
- §13.9 "Adequacy of lazy semantics" (p. 288): **Lemma 13.30** (pp. 288–289) is the lazy
  analogue, Lemma 13.31 the entailment property. **The lazy proof uses the same method** [V].
- Caveat [U]: a secondary listing (2001 printing, Japanese bibliographic page) shows different
  chapter numbering; cite the 1993 edition explicitly.

What is related **[V]**: tokens of the information system V_τ (finite syntactic objects; for
function types a token is a pair (U, V) of finite token sets) and closed canonical forms C_τ.
Quote (Lemma 13.7, OCR-cleaned):
> "For each closed type τ there is a relation ⊑_τ between tokens of V_τ and canonical forms
> C_τ with the following properties: ∅ ⊑_1 (); (a,b) ⊑_{τ1*τ2} (c1,c2) iff a ⊑_{τ1} c1 &
> b ⊑_{τ2} c2; (U,V) ⊑_{τ1->τ2} λx.t iff ∀c ∈ C_{τ1}. U ≲_{τ1} c ⇒ V ≲_{τ2} t[c/x];
> (1,a) ⊑ inl(c) iff a ⊑ c; (2,b) ⊑ inr(c) iff b ⊑ c; a ⊑_{μX.τ} abs(c) iff
> a ⊑_{τ[μX.τ/X]} c, where we write U ≲_τ s ... iff ∀b ∈ U ∃c ∈ C_τ.(b ⊑_τ c & s → c)."

(The relation symbol is garbled by OCR; it is an ⊑/≲-style symbol. The element-level relation
d ≲_τ t for d ∈ |V_τ⊥| is derived from the token relation.)

Recursion principle **[V]**:
> "We can no longer do this when types can be defined recursively; the definition of
> ≲_{μX.τ} cannot be given straightforwardly in terms of ≲_{τ[μX.τ/X]} as such a definition
> would not be well-founded. Fortunately we can still give a simple definition of the
> relations ≲_τ by taking advantage of the information-systems representation."
> Proof of 13.7: "The relation ⊑ exists by well-founded recursion on the size of tokens and
> canonical forms combined lexicographically", with size(∅)=1, size(X)=1+Σ_{a∈X} size(a),
> size((a,b))=1+size(a)+size(b), etc.
(For the lazy Lemma 13.30: "well-founded recursion on the size of tokens and the structure of
canonical forms ordered lexicographically".)

Model **[V]**: Scott information systems (consistency + entailment), with recursive types
solved inside information systems. Purpose: computational adequacy of eager (and lazy)
denotational semantics w.r.t. big-step evaluation. In ch. 11 (§11.4, "Agreement of eager
semantics", p. 190) — no recursive types — the relation is by structural induction on types
[V, as stated in §13.4].

Credits **[V]** (§13.11 "Further reading", p. 295): "The technique used in proving adequacy
follows closely that in Gordon Plotkin's lecture notes—similar methods of proof have been used
by Per Martin-Löf in his domain interpretation of type theory (1983), and by Samson Abramsky
[1]." ([1] = Abramsky, "The lazy lambda calculus".) Martin-Löf has **no** bibliography entry
in Winskel [V]. Which Plotkin notes are meant is not given in that sentence (candidates in the
bibliography: [80] "The Pisa lecture notes", [83] "Types and partial functions", CSLI 1985)
— unverified which.

Relation to our R: closest *technical* ancestor for "recursion on the size of a finite
function token (U,V)" — Winskel's function token is a finite input/output pair just like an
entry of our finite tables. But it is category **A** (token vs canonical term), symmetric only
in the sense of being finite-vs-syntax, and needs no step tower because the recursion is
well-founded on token size; we instead use a depth-indexed tower because the right-hand side
is an arbitrary (possibly infinite) set, not syntax.

## A2. Martin-Löf 1983, "Lecture notes on the domain interpretation of type theory"

```bibtex
@misc{MartinLof83,
  author       = {Per Martin-L{\"o}f},
  title        = {Lecture Notes on the Domain Interpretation of Type Theory},
  howpublished = {In Programming Methodology Group (ed.), Workshop on the Semantics of
                  Programming Languages, Chalmers University of Technology, G{\"o}teborg},
  year         = {1983},
  note         = {Handwritten notes; scan: archive-pml.github.io, file
                  Notes-on-The-Domain-Interpretation-of-Type-Theory-1983.pdf}}
```
Bibliographic form **[V]** as cited in Abramsky's thesis (arXiv:1112.0347, entry [Mar83]):
"P. Martin-Löf. Lecture notes on the domain interpretation of type theory. In Programming
Methodology Group, editor, Workshop on the Semantics of Programming Languages, Chalmers
University of Technology, Göteborg, Sweden, 1983." The scan (title page "Notes on The Domain
Interpretation of Type Theory by Per Martin-Löf", 11 scanned sheets, handwritten pages
numbered 1–39, followed by a typed "Discussion during Per Martin-Löf's talk") was read
visually **[V]**.

Content **[V]** (from the handwritten scan; section numbers are Martin-Löf's own):
1. "Computation rules" — big-step evaluation c ⇒ e for an untyped language of type-theory
   program forms (λ, ap, pairs/E, inl/inr/D, finite sets m_n, 0/s/R, sup/T, ω, omegarec, fix).
2. "(Formal) neighbourhoods" — syntactic finite elements built by finite intersection,
   λ(∩_{i∈I}[U_i,V_i]) (function neighbourhoods as finite intersections of step-function
   neighbourhoods), (U,V), i(U), j(V), s(U), sup(...). Then:
   > "Definition of the relation Approx(a, U) ≡ a ∈ U which says that a formal neighbourhood
   > U approximates a program a."
   given by inference rules, e.g. "c ⇒ λ(b), b(x) ∈ V_i (x ∈ U_i) / c ∈ λ(∩[U_i,V_i])"
   (hypothetical premise: for x ∈ U_i, b(x) ∈ V_i), "c ⇒ (a,b), a ∈ U, b ∈ V / c ∈ (U,V)".
   With every program a he associates "the operational neighbourhood filter ã = {U | a ∈ U}".
3. Formal inclusion and consistency (decidable) and a theorem that formal inclusion implies
   ∀x(x ∈ U ⊃ x ∈ V).
4. "Denotational semantics" — "a neighbourhood filter" (up-closed, ∩-closed, consistent); "By
   induction on its construction, I associate with a program a its denotation â, which is a
   neighbourhood filter"; an open program b(x1..xn) denotes an (n+1)-ary relation between
   neighbourhoods U1,…,Un b̂ V (i.e. an approximable mapping / graph on finite elements).
5. "First theorem. If a ⇒ b, then â = b̂."
6. "Second theorem. For an arbitrary program a, â ⊆ ã. That is, a denotational neighbourhood
   of a program is always an operational neighbourhood of the same program. U ∈ â → U ∈ ã ≡
   a ∈ U. Proof. By induction on the construction of the program a." Followed by a
   Corollary: ĉ = {Δ} ⟺ c does not terminate.

Classification: **A** (formal neighbourhood = finite element vs. program). Recursion
principle: inductive definition by rules indexed by the syntactic structure of the formal
neighbourhood (the relation for λ(∩[U_i,V_i]) refers to U_i, V_i only), so it is well-founded
even though the language is untyped and the domain is reflexive. Purpose: adequacy (agreement
of denotational and operational semantics) for the program forms of (partial) type theory.
Note **[V]**: there is no size measure in the notes; the well-foundedness comes from the
inductive syntax of neighbourhoods (Winskel later phrases it as recursion on token size).

Relation to our R: the true origin of "define the approximation relation only on finite
elements, by induction on their syntax, then lift to arbitrary elements by the filter/closure
property". Like ours, the λ clause quantifies over all arguments approximated by U_i; unlike
ours, the other side is a program, not a denotation, and his relation is purely inductive
(no index).

## A3. Pitts 1996 §5 (and Pitts 1993 MFPS) — the domain-vs-syntax part
See B1/B2 below for full bibliographic data; the formal-approximation relation of §5 is
category **A**: ◁_σ ⊆ D × Can_σ (domain elements vs canonical forms) **[V]**.

## A4. Abramsky

### A4a. Abramsky, "The Lazy Lambda Calculus" (1990)
```bibtex
@incollection{Abramsky90,
  author    = {Samson Abramsky},
  title     = {The Lazy Lambda Calculus},
  booktitle = {Research Topics in Functional Programming},
  editor    = {David A. Turner},
  publisher = {Addison-Wesley},
  pages     = {65--117},
  year      = {1990}}
```
Pages: 65–117 per Abramsky's Oxford publication page [V]; Pitts 1996's bibliography says
65–116 [V]. Check the physical book before choosing. Text read from the author's re-typeset
PDF (cs.ox.ac.uk/files/293/lazy.pdf, dated 2006), so page numbers there differ from the book.
Result numbers below were checked in that PDF [V].
- §5 "A Domain Logic for Applicative Transition Systems": L ::= t | φ∧ψ | (φ→ψ)⊥.
  **Definition 5.2** (satisfaction, by structural recursion on formulas) [V]: "a ⊨_A (φ → ψ)⊥ ≡
  a⇓f & ∀b ∈ A. b ⊨_A φ ⇒ f(b) ⊨_A ψ". Lemma 5.3 (applicative bisimulation ⊆ ⊑_L) is proved
  "by induction on φ".
- Theorem 5.8 (Soundness of the program logic), Theorem 5.14 (D is L-complete, via DTLF Stone
  duality), Theorem 5.17 (D ≅ Filt L), **Theorem 5.18 (Computational Adequacy)**: "For all M ∈
  Λ, M⇓ ⟺ [[M]]^D ρ⊥ ≠ ⊥" [V]. Abramsky's comment [V]: "The triviality of this proof is
  notable, since analogous results in the literature have required lengthy arguments involving
  recursively defined inclusive predicates (cf. [Plo85])."
- Method: satisfaction of a formula (a syntactic name for a compact element of D = (D→D)⊥)
  by a term in the operational term model, by induction on formulas. Soundness is the
  formula-induction step. Completeness of the logic for D (Stone duality) moves the hard part
  into the logic. Classification **A**. Recursive domain handled by the logic (formulas =
  compact opens) rather than by a recursively specified relation.
- Relation to our R: also a "finite-syntactic-element vs. arbitrary thing" relation by
  structural induction on the finite side, but the arbitrary thing is a term in a transition
  system, not a second denotation.

### A4b. Abramsky & Ong 1993
```bibtex
@article{AbramskyOng93,
  author  = {Samson Abramsky and C.-H. Luke Ong},
  title   = {Full Abstraction in the Lazy Lambda Calculus},
  journal = {Information and Computation},
  volume  = {105},
  number  = {2},
  pages   = {159--267},
  year    = {1993},
  doi     = {10.1006/inco.1993.1044}}
```
Bibliographic data [V] (Crossref; Pitts 1996's bibliography also says 159–267; the Oxford page
says 159–268). Proof method **[V]**, read from `papers/PLDI-2027/related/abramsky-1993.pdf`
(image-only scan, read page by page; journal page numbers as printed). Same method as LLC (A4a),
§5 "A Domain Logic for Applicative Transition Systems", pp. 197–207:
- Domain logic L ::= t | φ∧ψ | (φ→ψ)⊥ with satisfaction over any q-ats by recursion on formulas:
  "a ⊨ (φ → ψ)⊥ ≡ a⇓f & [∀b ∈ A. b ⊨ φ ⇒ f(b) ⊨ ψ]" (Def. 5.2.2, p. 198); λ ≡ (t → t)⊥ and
  "a⇓ ⟺ a ⊨ λ".
- A program logic M, Γ ⊢ φ (intersection-type-like rules), with Theorem 5.3.3 (Soundness of
  Program Logic), "M, Γ ⊢ φ ⇒ M, Γ ⊨ φ" for every lazy λ-model, "proof is again routine" (pp.
  201–202). Theorem 5.4.6: "D is L-complete", via Stone duality (D ≅ Filt(L)) and the
  completeness theorem of DTLF [Abr87c] (p. 204). Proposition 5.4.8: Filt(L) is an lts
  isomorphic to D, and "[[M]]^D_ρ" corresponds to "[[M]]^{Filt L}" (p. 205).
- **Theorem 5.4.9 (Computational Adequacy)**, p. 206: "For all M ∈ Λ°, M⇓ ⟺ D ⊨ M⇓ (i.e.,
  [[M]]^D ≠ ⊥)". Proof: "⇒" "follows immediately from D being a lazy λ-model"; for "⇐",
  [[M]]^D ≠ ⊥ ⇒ [[M]]^{Filt L} ≠ {t} ⇒ M ⊢ λ ⇒ M ⊨ λ (Theorem 5.3.3, in the term model) ⇒ M⇓.
  Comment (p. 206): "The triviality of this proof is notable, since analogous results in the
  literature have required lengthy arguments involving recursively defined predicates (cf.
  (Plo85))."
- What is related to what: formulas (names of compact elements of D) to elements of an
  applicative transition system, here closed terms of the operational model; no relation between
  terms and arbitrary domain elements is defined. Classification **A**; the hard part
  (recursive domain) is moved into the completeness of the logic.
Ong's 1988 Imperial PhD thesis has "§3.2.3 A General Adequacy Result" for continuous lazy
λ-models [V title only, method unseen].

### A4c. Abramsky, "Domain Theory in Logical Form" (1991)
```bibtex
@article{Abramsky91DTLF,
  author  = {Samson Abramsky},
  title   = {Domain Theory in Logical Form},
  journal = {Annals of Pure and Applied Logic},
  volume  = {51},
  number  = {1--2},
  pages   = {1--77},
  year    = {1991},
  doi     = {10.1016/0168-0072(91)90065-T}}
```
Bibliographic data [V]. Content [V] (thesis version arXiv:1112.0347, Chapter 4): Theorem
4.3.1, soundness and completeness of the endogenous logic, "M, Γ ⊢ φ ⟺ M, Γ ⊨ φ" with
"d ⊨ φ ≡ d ∈ [[φ]]". So the DTLF chapter relates **formulas to denotations** (logic vs. model)
and contains no operational adequacy proof. Classification: neither A nor B in our sense: it
is a logic-vs-model duality, and the adequacy use is in the LLC paper. The thesis cites
Martin-Löf [Mar83] for the term-language constructions [V: "following ideas of Martin-Löf
[Mar83] and Plotkin [Plo85]"].

## A5. Intersection types / filter models
Bibliographic data [V] (Crossref):
```bibtex
@article{BCD83,
  author  = {Henk Barendregt and Mario Coppo and Mariangiola Dezani-Ciancaglini},
  title   = {A Filter Lambda Model and the Completeness of Type Assignment},
  journal = {Journal of Symbolic Logic},
  volume  = {48}, number = {4}, pages = {931--940}, year = {1983},
  doi     = {10.2307/2273659}}
@article{CDV81,
  author  = {Mario Coppo and Mariangiola Dezani-Ciancaglini and Betti Venneri},
  title   = {Functional Characters of Solvable Terms},
  journal = {Zeitschrift f{\"u}r mathematische Logik und Grundlagen der Mathematik},
  volume  = {27}, number = {2--6}, pages = {45--58}, year = {1981},
  doi     = {10.1002/malq.19810270205}}
@book{Krivine93,
  author    = {Jean-Louis Krivine},
  title     = {Lambda-Calculus, Types and Models},
  publisher = {Ellis Horwood}, year = {1993},
  note      = {French original: Lambda-calcul, types et mod{\`e}les, Masson, Paris, 1990}}
```
Krivine [V] from the PDF on Krivine's site. The PDF shows "Paris, 1990". English edition [A, Open
Library record OL7174632W]: *Lambda-Calculus, Types and Models*, Ellis Horwood, 1993, ISBN
0-13-062407-1, 192 pp. The translator and the series are not verified. Cleanest citation for "a relation between intersection types and terms,
by induction on types":
- Krivine, ch. 3 "Intersection type systems" [V]: types are interpreted as saturated sets of
  terms "by induction on the length of A: … |Ω| = Λ; if A = B → C, then |A| = |B| → |C|; if
  A = B∧C, then |A| = |B| ∩ |C|".
- **Lemma 3.5 (Adequacy lemma)** [V]: "If t1 ∈ |A1|,…,tk ∈ |Ak| then u[t1/x1,…,tk/xk] ∈ |A|".
  It is used for Theorem 3.7 (typable with a non-trivial type in DΩ ⇒ head reduction finite).
- The link "types = compact elements of the filter model" comes from BCD83, not from Krivine.
  Krivine's predicate is unary realizability for characterisation, not stated as adequacy of a
  filter model.

Classification **A**. Recursion on the type, which is a finite syntactic object, so reflexive
domains cause no trouble. Abramsky (LLC §5) explicitly notes "the striking similarity of our
program logic with type inference, in particular with the intersection type discipline" [V].

Other candidates, all [U]: Barendregt–Dekkers–Statman, *Lambda Calculus with Types* (CUP
2013), Part III; Egidi–Honsell–Ronchi Della Rocca, "Operational, denotational and logical
descriptions: a case study", Fundamenta Informaticae 16(2):149–169, 1992 (ISWIM/SECD vs. a
filter model; method unseen); Ronchi Della Rocca & Paolini, *The Parametric Lambda Calculus*
(Springer 2004).

Relation to our R: the PLFA/Siek "element-indexed" relations are exactly intersection-type
realizability with types replaced by finite graph values. Ours is the denotation-to-denotation
variant.

## A6. Siek 2017, "Revisiting Elementary Denotational Semantics" (arXiv:1707.03762)

```bibtex
@misc{Siek17,
  author        = {Jeremy G. Siek},
  title         = {Revisiting Elementary Denotational Semantics},
  year          = {2017},
  eprint        = {1707.03762},
  archivePrefix = {arXiv},
  primaryClass  = {cs.PL},
  note          = {v4, 21 Oct 2017}}
```
Title **[V]** (v4). Location **[V]**: §5 "Mechanized Correctness of Elementary Semantics",
§5.1 "Sound with respect to operational semantics"; relation G, Lemma 2 (G downward closed),
Lemma 3, Lemma 4 (main lemma), Theorem 2 "(Sound wrt. op. sem.) (aka. Adequacy)". §6 is the
optimizer (inliner) correctness, Lemma 10 "Optimizer Preserves Denotations", Theorem 5.

What is related **[V]**: a *single finite value* d (integer n or finite table t of pairs
(d1,d2)) and a *set* of syntactic values (closures ⟨λx.e, ϱ⟩ of Kahn's big-step semantics):
> "We relate D to sets of syntactic values V of Kahn [38] with the following logical
> relation. Logical relations are usually type-indexed, not element-indexed, but our domain
> elements are isomorphic to types.
>   G : D → P(V)
>   G(n) = {n}
>   G(t) = {⟨λx. e, ϱ⟩ | ∀(d1,d2)∈t. ∀v1. v1∈G(d1) ⟹ ∃v2. ϱ(x:=v1) ⊢ e ⇒ v2 ∧ v2∈G(d2)}"
So: **yes, the phrase "element-indexed" appears** [V]; G is defined by structural recursion on
the finite value d (Lemma 2 "by induction on d"). Model: Siek's own graph-like model
(values are integers or finite graphs/tables; denotation E⟦e⟧ρ is a set of such values), §3.
Purpose: soundness (adequacy) of the elementary semantics w.r.t. Kahn's big-step semantics;
mechanized in Isabelle. The inliner correctness in §6 is proved by denotational equality +
contextual-equivalence soundness, *not* by a relation between two denotations [V].
Category **A**.

Relation to our R: same family of finite values and the same "relation indexed by a finite
value" idea, but A-type (value vs closure) and symmetric-in-kind; no tower needed because the
other side is syntax and recursion is structural on d.

## A7. PLFA, part 3, chapter "Adequacy" (Siek's chapters in Wadler–Kokke–Siek)

```bibtex
@book{PLFA,
  author = {Philip Wadler and Wen Kokke and Jeremy G. Siek},
  title  = {Programming Language Foundations in {A}gda},
  url    = {https://plfa.github.io/},
  year   = {2022},  % cite the version/date actually used
  note   = {Chapters Denotational, Compositional, Soundness, Adequacy}}
```
Source **[V]**: src/plfa/part3/Adequacy.lagda.md (dev branch), module plfa.part3.Adequacy,
title "Adequacy: Adequacy of denotational semantics with respect to operational semantics".
Model **[V]** (Denotational.lagda.md): `data Value : Set where ⊥ : Value; _↦_ : Value →
Value → Value; _⊔_ : Value → Value → Value` with an ordering `_⊑_` (⊑-bot, ⊑-conj-L, …,
including distributivity); `Denotation Γ = (Env Γ → Value → Set)`, `ℰ M = λ γ v → γ ⊢ M ↓ v`
— a filter-model-style semantics for untyped CBN λ-calculus.
Relation **[V]**:
```agda
𝕍 : Value → Clos → Set
𝔼 : Value → Clos → Set
𝕍 v (clos (` x₁) γ) = Bot
𝕍 v (clos (M · M₁) γ) = Bot
𝕍 ⊥ (clos (ƛ M) γ) = ⊤
𝕍 (v ↦ w) (clos (ƛ N) γ) =
    (∀{c : Clos} → 𝔼 v c → above-fun w → Σ[ c' ∈ Clos ]
        (γ ,' c) ⊢ N ⇓ c'  ×  𝕍 w c')
𝕍 (u ⊔ v) (clos (ƛ N) γ) = 𝕍 u (clos (ƛ N) γ) × 𝕍 v (clos (ƛ N) γ)
𝔼 v (clos M γ') = above-fun v → Σ[ c ∈ Clos ] γ' ⊢ M ⇓ c × 𝕍 v c
```
"We define 𝕍 as a function ... and not as a data type because it is mutually recursive with
𝔼 in a negative position ... If the term is a lambda abstraction, we define 𝕍 by recursion
on the value." Environments: 𝔾 γ γ' = ∀x → 𝔼 (γ x) (γ' x). Main lemma `↓→𝔼`
(γ ⊢ M ↓ v and 𝔾 γ γ' ⇒ 𝔼 v (clos M γ')), `sub-𝕍` (down-closure), `↓→⇓`, and `adequacy`
(ℰ M ≃ ℰ (ƛ N) ⇒ M —↠ ƛ N′). Category **A**: finite Value vs closure of a CBN big-step
semantics; recursion on the structure of the Value (Agda structural recursion).

Relation to our R: the immediate Agda predecessor of our approach (same author lineage,
structural recursion on a finite value); our R replaces the closure side by an arbitrary
denotation of a *second* semantics and so cannot recurse purely on the left finite value
when the right-hand side is applied via D ● E — hence the depth-indexed tower.

## A8. Benton & Hur 2009; Benton & Hur 2010; Benton–Kennedy–Varming 2009; Hur & Dreyer 2011

### A8a. Benton & Hur, ICFP 2009
```bibtex
@inproceedings{BentonHur09,
  author    = {Nick Benton and Chung-Kil Hur},
  title     = {Biorthogonality, Step-Indexing and Compiler Correctness},
  booktitle = {Proceedings of the 14th ACM SIGPLAN International Conference on
               Functional Programming (ICFP)},
  pages     = {97--108},
  year      = {2009},
  doi       = {10.1145/1596550.1596567}}
```
[V]: author PDF and Crossref. Abstract [V]: "We define logical relations between the denotational
semantics of a simply typed functional language with recursion and the operational behaviour of
low-level programs in a variant SECD machine. The relations, which are defined using
biorthogonality and step-indexing, capture what it means for a piece of low-level code to
implement a mathematical, domain-theoretic function and are used to prove correctness of a
simple compiler."
- Source [V]: PCFv, call-by-value, with `Fix f x = M`. Types are Int, Bool, × and →, so there
  are **no recursive types**. The semantics is in ω-cpos and is computationally adequate.
- Two **asymmetric** relations [V]:
  1. Low-level approximates denotation. This direction is **step-indexed on the machine side**
     and closed by biorthogonality, by induction on types. The arrow case is
     `E^{t→t'}_i = {(f, df) | ∀k ≤ i, ∀(v,dv) ∈ E^t_k, (([App],[v,f]), λ*:1. df dv) ∈ (I → (E^{t'})⊥)_k}`,
     with `v ◁ d ⇔ ∀i, v E^t_i d`.
  2. Denotation approximates low-level. This direction is **not step-indexed**: "We will not
     use operational step-indexing to define the relation this way around, but an explicit
     admissible closure operation will play a similar rôle", because "{d | v D^t d} is not
     always closed under taking limits of chains".
- Theorems 1 and 2 [V] give compiler correctness, one per direction. For Theorem 1, "In the
  case for recursive functions, there is a nested induction over the step indices".
- Classification **A** (domain element vs. machine code). The step index counts machine steps,
  not the depth of a finite element.
- Relation to our R: this is the closest prior "denotation-side vs. other-side, asymmetric,
  step-indexed" design, but the index sits on the operational side. Ours sits on the finite
  target approximation, and both sides are denotations.

### A8b. Benton & Hur, MSR-TR-2010-62
```bibtex
@techreport{BentonHur10,
  author      = {Nick Benton and Chung-Kil Hur},
  title       = {Realizability and Compositional Compiler Correctness for a Polymorphic
                 Language},
  institution = {Microsoft Research},
  number      = {MSR-TR-2010-62},
  month       = apr,
  year        = {2010}}
```
[V]. **The source semantics is operational, not denotational** [V]: "we work with an
operational, rather than a denotational, semantics for the high-level language".
- Source: Fv, a CBV language with recursion and impredicative ∀ and ∃. It has no recursive
  types; these are listed as future work [V].
- The relations are between SECD components and Fv terms. They are parameterised by an
  abstract approximation relation with axioms that include Unfold (via finite unrollings
  rec^n). The machine side is step-indexed [V].
- Classification **A**.

### A8c. Benton, Kennedy & Varming, TPHOLs 2009
```bibtex
@inproceedings{BKV09,
  author    = {Nick Benton and Andrew Kennedy and Carsten Varming},
  title     = {Some Domain Theory and Denotational Semantics in {C}oq},
  booktitle = {Theorem Proving in Higher Order Logics (TPHOLs 2009)},
  series    = {LNCS}, volume = {5674}, pages = {115--130}, year = {2009},
  doi       = {10.1007/978-3-642-03359-9_10}}
```
[V]. The development goes "up to and including the inverse-limit construction of solutions to
mixed-variance recursive domain equations, and the existence of invariant relations on those
solutions" (abstract).
- Typed language [V]: `relVal τ : SemTy τ → CValue τ → Prop`, by recursion on types.
- Untyped language, D ≅ (nat + (D →c D))⊥ [V]: "now cannot define the relation by induction on
  types. … Following Pitts [23], however, we again use the technique of separating positive and
  negative occurrences … constructed by Knaster-Tarski. … By applying the minimal invariant
  property … we prove that in fact ∆− == ∆+".
- Classification **A** (adequacy only, no compiler). This is a mechanized instance of Pitts's
  minimal-invariant method.
- An extended draft adds Lars Birkedal as an author: Benton, Birkedal, Kennedy & Varming,
  "Formalizing Domains, Ultrametric Spaces and Semantics of Programming Languages". The PDF
  header says it was under consideration for MSCS, received 12 July 2010 [V]. Final
  publication is [U].

### A8d. Hur & Dreyer, POPL 2011
```bibtex
@inproceedings{HurDreyer11,
  author    = {Chung-Kil Hur and Derek Dreyer},
  title     = {A {K}ripke Logical Relation Between {ML} and Assembly},
  booktitle = {Proceedings of the 38th ACM SIGPLAN-SIGACT Symposium on Principles of
               Programming Languages (POPL)},
  pages     = {133--146}, year = {2011},
  doi       = {10.1145/1926385.1926402}}
```
[V]. The relation is fully operational: "a biorthogonal, step-indexed, Kripke logical relation"
between a System-F-like language and assembly. The source has iso-recursive types and
references; recursive types are handled by step levels of worlds.
- Their characterisation of Benton–Hur [V]: "These half-operational, half-denotational
  relations were of necessity asymmetric … step-indexing—but only in defining one direction of
  approximation (in the other direction, they use an admissible closure operation)."
- Not A or B in the denotational sense; it is operational-to-operational. It is useful mainly
  as the authoritative statement of Benton–Hur's asymmetry.

---------------------------------------------------------------------------------------------

# PART B — Relations between two denotational semantics / within domains

## B1. Pitts 1996, "Relational Properties of Domains"

```bibtex
@article{Pitts96,
  author  = {Andrew M. Pitts},
  title   = {Relational Properties of Domains},
  journal = {Information and Computation},
  volume  = {127},
  number  = {2},
  pages   = {66--90},
  year    = {1996},
  note    = {Revised version of Univ. Cambridge Computer Laboratory Tech. Rept. 321 (1993);
             preliminary version: Relational properties of recursively defined domains,
             Proc. 8th LICS 1993, pp. 86--97}}
```
**[V]** volume 127, pp. 66–90, 1996 (article no. 0052) from the PDF header; issue number 2 [V, Crossref
record for doi:10.1006/inco.1996.0052, which also gives June 1996].

Structure **[V]**: §1 Introduction; §2 Overview; §3 "Minimal Solutions of Domain Equations" ( Theorem 3.3 existence
of minimal invariants, Theorem 3.4 Freyd's mixed initiality/finality, Example 3.6 the lazy
λ-calculus domain rec α.(α→α)⊥); §4 relational structures (Example 4.2, Definition 4.3
admissible, Definition 4.8 invariant R-relations, **Theorem 4.16 Existence of Invariant
Relations**); **§5 "Computational Adequacy"** (Proposition 5.1, relations ◁_σ, conditions
(17)–(23)); **§6 "Induction and Co-induction Principles"** (Theorem 6.5 induction, Theorem
6.12 co-induction, Corollary 6.13).

The three methods — **[V]**, §5, p. 81 (the claim "§5 names the Martin-Löf method" is
**correct**; there is no bibliography entry for Martin-Löf, and nothing is cited for him):
> "In the literature, two methods can be found for constructing relations on recursively
> defined domains with such nonmonotonic fixed point properties. One method, due to Milne,
> Plotkin, and Reynolds makes use of Scott's construction of a recursively defined cppo as the
> colimit of a chain of embeddings D0 → D1 → ⋯, where the cppo Dn is obtained by iterating the
> domain constructor n times, starting with the trivial cppo {⊥} ... Then the desired relation
> can be constructed as an intersection of countably many relations defined by induction on n
> at the same time as the Dn are defined; see (Reynolds, 1974). A second method, essentially
> due to Martin-Löf, applies only to Scott domains (precluding the use of constructors like
> the Plotkin powerdomain) since it makes use of their presentation in terms of 'information
> systems' (Scott, 1982). This method hinges upon the fact that each {d | d(◁σ)⊥e} is in fact
> a Scott-closed subset of σ. Hence it suffices to construct the relations ◁σ only for
> compact elements of σ ... Information systems provide a formal language for compact
> elements of (recursively defined) Scott domains, and a(◁σ)⊥e (a compact) can be defined by
> a well-founded induction on the size of (a formal representation of) a; see (Winskel, 1993,
> Section 13.4). Here we show that the existence of relations ◁σ satisfying (17)–(23) follows
> directly from Theorem 4.16 ... This provides a new method of construction that is more
> abstract than the above two, in that it relies upon the 'minimal invariant' property of the
> recursively defined cppo ty rather than upon the techniques for giving concrete
> constructions of recursively defined domains."
Cited for the stage method: Milne 1973 (PhD thesis, Cambridge), Plotkin 1973 ("Lambda
Definability and Logical Relations", Memo SAI-RM-4, Edinburgh), Reynolds 1974 [V, intro and
bibliography]. Note: Pitts calls it a "colimit of a chain of embeddings"/"intersection of
countably many relations defined by induction on n"; the phrase "projection-indexed" is ours.

Which relations are A and which B **[V]**:
- §5, (17)–(23): ◁_σ ⊆ σ⊥ × Can_σ (domain element vs canonical form); clause (23)
  "f ◁_{σ→σ'} λx:σ.e ⟺ ∀d,c (d ◁_σ c ⇒ f(d)(◁_{σ'})⊥ e[c/x])"; R(D) = subsets of D↓×Can
  (Example 4.2(iii) with I = Can). → **A**.
- §6 Theorem 6.5 (induction): unary admissible predicates on D (Example 4.2(i), n=1). →
  within-a-domain, not a relation between two semantics.
- §6 Theorem 6.12 / Corollary 6.13 (co-induction): binary relations R ⊆ D × D on the **same**
  domain ("F-simulation"), concluding d ⊑ d′; includes applicative (bi)simulation. → **B**
  (homogeneous: D vs D, same semantics).
- Example 4.2(ii): n-ary non-strict relations on D × ⋯ × D. → B (homogeneous).
- The paper explicitly names the heterogeneous B case as an application of invariant
  relations but does **not** work it out: invariant relations "lie at the heart of some
  proofs of correspondence between denotational and operational semantics (as in (Plotkin,
  1985), or (Meyer and Cosmadakis, 1988, Appendix), for example), or between two denotational
  semantics (as in (Reynolds, 1974) for example)" (§2 Overview, under "Results — Invariant Relations",
  **p. 68** [V, the author's PDF at cl.cam.ac.uk/~amp12/papers/relpod/relpod.pdf, which carries the
  journal pagination: running head "68 ANDREW M. PITTS"]).

How it copes with recursive domains: minimal-invariant property (Freyd) + admissible actions
on relations; a mixed (negative/positive) separation R⁻/R⁺ and fixed-point induction.
Relation to our R: our R is a heterogeneous B relation (Clos4 finite approximations vs Clos3
denotations) in a graph model with no recursive domain equation at all (𝒫 Value is a
powerset of an inductive datatype); we instead face the same non-monotonicity in the *relation*
and resolve it by an index tower bounded by the finite side's depth — a "stage" method in
which the stages are tied to the finite element, combining the first two of Pitts's methods.

## B2. Pitts 1993/1994 MFPS, "Computational adequacy via 'mixed' inductive definitions"

```bibtex
@inproceedings{Pitts94MFPS,
  author    = {Andrew M. Pitts},
  title     = {Computational Adequacy via `Mixed' Inductive Definitions},
  booktitle = {Mathematical Foundations of Programming Semantics, 9th International
               Conference, New Orleans, LA, USA, April 1993, Proceedings},
  series    = {Lecture Notes in Computer Science},
  volume    = {802},
  pages     = {72--82},
  publisher = {Springer},
  year      = {1994},
  doi       = {10.1007/3-540-58027-1_3}}
```
**[V]** title, LNCS 802, pp. 72–82 (Pitts 1996 bibliography and the author PDF); DOI [U, from
search result].

Content **[V]**: untyped call-by-value functional language; formal-approximation relation
◁ ⊆ D × Prog (Definition 4), constructed by separating negative/positive occurrences,
simultaneous inductive definition of ◁⁻, ◁⁺, and proving them equal by fixed-point induction
using the minimal invariant (Theorem 6 "Existence of ◁"; Theorem 3 Computational Adequacy).
It repeats the three-method comparison (Milne/Plotkin/Reynolds stages; Martin-Löf via
information systems, "See [Winskel], Sect. 13.4"; and the new minimal-invariant method).
Abstract **[V]**: "proofs of correspondence between operational and denotational semantics
(or between two different denotational semantics) often depend upon the existence of
relations specified as the fixed point of non-monotonic operators."
§4 "Further development" **[V]**: "we believe that the recursively specified relation between
two recursively defined domains employed by Reynolds to relate a direct and a continuation
semantics of an untyped functional language in [12] can be constructed by applying our method
to a suitable binary relational structure." (Stated as a belief, not done.) It also notes the
minimal-invariant property amounts to "any element of a recursively defined domain ... can be
expressed as the least upper bound of a chain of projections of the element" [V].
Classification: the worked relation is **A**; the Reynolds remark is **B** (heterogeneous,
two domains), conjectural.

## B3. Reynolds 1974, "On the relation between direct and continuation semantics"
```bibtex
@inproceedings{Reynolds74,
  author    = {John C. Reynolds},
  title     = {On the Relation between Direct and Continuation Semantics},
  booktitle = {Automata, Languages and Programming, 2nd Colloquium (ICALP)},
  editor    = {Jacques Loeckx},
  series    = {Lecture Notes in Computer Science},
  volume    = {14},
  pages     = {141--156},
  publisher = {Springer},
  year      = {1974}}
```
The bibliographic data is **[V]** from Pitts 1996's bibliography. The content is **[V]**, read
from the CMU preprint (16 pages, KiltHub/figshare 6608018). The page numbers below are the
**preprint's own (1–16), not the LNCS pages**. The preprint says a preliminary draft was titled
"A Justification of Continuations".
- **Two different recursive domains [V].** The direct semantics uses "D ≅ P + (D → D)". The
  continuation semantics uses "C = E → O, D' = C → O, E ≅ P + (D' → D')" (pp. 2–3).
- **Relations [V].** η ∈ D ⇸ D' and θ ∈ (D→D) ⇸ (D'→D') (p. 4). θ has the logical clause
  "(∀a∈D, a'∈D') η: a↦a' implies η: f(a)↦f'(a')". The η clauses include "a = ⊥_D and
  (a' = ⊥_{D'}, or a' = λc∈C. error)". Theorem 1 (related environments give related meanings)
  is proved by structural induction.
- Theorem 2 (p. 6) also gives a retraction pair φ, ψ with "M[r](e) = ψ(N[r](φ·e))", "so that the
  semantics provided by M is included in the semantics provided by N" [V].
- **General construction [V]** (p. 14, "Relations between Recursively Defined Domains"): "We
  begin by defining θ_0 to be the universally true relation between the one-point domains D_0
  and D'_0 and θ_{n+1} = B(θ_n)". Then "θ_∞: x ↦ x' iff, for all n, θ_n: [x]_n ↦ [x']_n". This
  is an intersection over the stages via the projections, with uniqueness by induction on n
  (p. 15).
- Admissibility (p. 9) is "directed complete" relations: limits of related directed sequences
  are related.
- **Classification: B, heterogeneous (two different reflexive domains).** The relation's
  direction is D-to-D', but the construction is symmetric in form, since the converse of a
  directed complete relation is again directed complete (Cor. 3(3), p. 9) [V].
- **Indexing: stage-indexed.** Both sides are projected to stage n *in parallel*. Neither side
  is restricted to finite or compact elements.
- Mulmuley's assessment [V, CMU-CS-85-149]: "Though Reynolds' technique is very systematic, it
  can be used only when two domains have similar shapes or when one domain can be
  'transformed' into the other domain."
- **Relation to our R:** the closest *structural* precedent.
  - Same genre: a logical relation between two denotational semantics of a language,
    non-monotone because of the function clause, built as a tower θ_0 = ⊤, θ_{n+1} = B(θ_n).
  - Our tower R′ 0 = ⊤, R′ (suc k) = Obs (R′ k) has exactly the same shape.
  - The differences are three. (i) Reynolds indexes by the inverse-limit stage of *both*
    domains and intersects over all n. We index by the depth of the *finite target value* and
    show index irrelevance above the depth, so no limit or intersection is needed. (ii) We have
    no domain equation: 𝒫 Value is a powerset of an inductive type. (iii) Our relation is
    asymmetric: a finite approximation vs. an arbitrary set.

## B4. Inclusive predicates: Milne & Strachey 1976, Stoy 1977/1981, Mulmuley 1985/1987
- **Milne & Strachey**, *A Theory of Programming Language Semantics*, Chapman & Hall, 1976
  [U]. **Milne**, PhD thesis, Cambridge, 1973 [V, from Pitts's bibliography: "The formal
  semantics of computer languages and their implementations"].
- **Stoy**, *Denotational Semantics: The Scott–Strachey Approach to Programming Language
  Theory*, MIT Press, 1977 [U]. **Stoy**, "The congruence of two programming language
  definitions", TCS 13 (1981) 151–174, doi:10.1016/0304-3975(81)90037-2 [V bib via Crossref].
- **Stoy 1981, content [V, `related/stoy-1981.pdf`, read 2026-10-15].** The PDF is a scan with a
  poor OCR layer; in the quotes below OCR misspellings are corrected, and nothing lost in the OCR is
  filled in. Page numbers are the printed TCS pages.
  - **What is related.** Not standard vs. store semantics (as these notes previously said, from
    secondary sources), but a denotational semantics and an interpreter for a small language PL:
    "one definition gave the denotational semantics, in the style of Scott and Strachey [12], and
    another defined the language using an interpreter, along lines similar to the use of VDL [6]. In
    this paper we present a proof of the congruence of these two definitions." (p. 151). PL is
    "simple enough for its semantics to be given solely in terms of environments" (p. 153).
  - **Two stages.** Stage 1 relates the direct semantics to a new continuation semantics (category
    B, same language); "Our first stage closely resembles this proof [Reynolds 1974], though our
    expression of it is a little different: Reynolds's use of 'directed complete relations'
    corresponds to our use of 'inclusive predicates'." (p. 152). Stage 2 relates the continuation
    semantics to the interpreter (category A: denotation vs. an operational definition), via
    "derepresentation functions, which map representations into the values they represent" (§8,
    p. 159).
  - **Existence (stage 1).** "These predicates have definitions which involve circularity and they
    can be rewritten as a fixed point equation. However, the function of which this set of predicates
    is the fixed point is not monotonic, and so the existence of such a fixed point cannot be inferred
    by the usual appeal to the result of Tarski" (p. 156). The construction: "The construction of
    solutions to these recursive domain equations involves sequences of 'approximation' domains, of
    which the required domains are, in some well-defined sense, the limits. We may define predicates
    on each of these approximation domains: this involves no circularity, but instead uses the
    predicates on earlier domains. Then we may define predicates for some element of the limit domain
    by applying the appropriate predicates to the element's images in all the approximation domains,
    and taking the conjunction of the results." (p. 156). So stage-indexed over both domains, then
    intersected, as in Reynolds.
  - **Asymmetry (stage 2 only).** Exact congruence predicates could not be shown to exist: "we must be
    content with predicates asserting that the denotational value is an approximation of the
    interpretive one" (p. 152); fixed-point induction on the interpreter gives only that "the
    interpreter defines a function which is weaker (in the sense of the partial ordering of the
    appropriate lattice) than that defined by the denotational semantics" (p. 158), so the proof
    goes in both directions and combines them (§11). The reason given: "The present extra
    complications arise in general when one tries to relate an infinitary abstract object, such as
    the function associated with some PL procedure by the denotational definition, with its finitary
    representation, such as the tree which represents the procedure in the interpreter." (p. 159);
    and, for the exact predicates, "Formally, it is the basis of the induction which fails" because
    the first approximation domain has one element "doing duty for all the functions" (§9.2, p. 163).
    Stoy leaves their existence open: "we are not thereby claiming that no such predicates exist (that
    is still an open question), but merely that we do not know how to demonstrate their existence"
    (p. 163).
  - Three inductions: "based on their size, their duration, and the richness of their value domains
    - and there is no correlation whatever between them." (p. 158). Interpreter functions are
    "represented by closures" (p. 167). Paper proof; mechanical aids are named as future relief
    (p. 169).
  - **For C6:** the stage indexing is by approximation domains of the inverse limit (not finite
    elements), and the order-asymmetric ("weaker than") predicates are between a denotation and an
    interpreter (category A), not between two denotations. Stoy's remark about an "infinitary
    abstract object" vs. its "finitary representation" names the same tension our relation handles,
    but on the operational side.
- **Content of the rest [V only via secondary sources]:**
  - Wand & Oliva (LFP 1992) [V]: "Such proofs typically involved complex arguments about
    inclusive predicates that related the domains in the source and target semantics [Milne &
    Strachey; Stoy] … by methods that were essentially denotational (induction on
    approximations to inverse limit domains)".
  - Mulmuley [V] on Stoy's example: an asymmetric predicate "Θ = {(d,e) | ∀(c,f) ∈ Π. dc ⊑
    O(e)f}" ("(d,e) ∈ Θ if d is weaker than e"). The existence proof "is shown using Milne's
    technique. The proof is undeniably complicated." The symmetric "=" version has no solution,
    shown by diagonalization with λx.xx.
- **Mulmuley**, "A Mechanizable Theory for Existence Proofs of Inclusive Predicates", CMU
  tech. rep. CMU-CS-85-149, 1985 [V, read]. Book: *Full Abstraction and Semantic Equivalence*,
  MIT Press (ACM Distinguished Dissertation), 1987 [U, not read]. CADE-7 1984 paper "The
  Mechanization of Existence Proofs of Recursive Predicates" [V as cited in the TR].
  - Setting [V]: two semantics ℰ1: L → D1 and ℰ2: L → D2. When a symmetric predicate does not
    exist, "a weaker predicate Q exists such that (d1,d2) ∈ Q iff d1 is weaker than d2", and
    equivalence is proved as two "weaker-than" directions.
  - Method [V]: work inside Scott's universal domain, representing domains as **finitary
    projections**. "L encapsulates the process of inverse limit construction of the domain D".
    Predicates live in a "predicate cpo".
  - Tool [V]: "IPL (Inclusive Predicate Logic) was implemented on top of LCF which can almost
    automatically prove the existence of most of the inclusive predicates which arise in
    practice."
  - Not indexed by finite elements [V].
- **Classification: B** (heterogeneous, two semantics), with stage/inverse-limit existence; Stoy
  1981's second stage is **A** (denotation vs. interpreter).
  Note the **asymmetric "weaker-than" predicates** (Stoy, Mulmuley): they are asymmetric in
  *order* (d ⊑-approximates e), not in finiteness, and in Stoy 1981 [V] they arise only in the
  denotation-vs-interpreter stage.
- **Polak 1980/81** [V, thesis STAN-CS-80-802 and the LNCS 124 book; see `novelty-literature.md`
  §1.9]: a compiler proof whose code-generation relations ϑ between the LS (source) and LT
  (target) domains are recursive and, Polak notes, not even monotone ("If l increases ϑ_S becomes
  smaller", thesis p. 136, book p. 127). Existence is not proved: "Reynolds [Re74] presents a set
  of easy to check criteria that ensure existence of fixed points. It can be seen that our
  definitions satisfy his criteria; thus we subsequently assume that the above predicates are well
  defined." (§IV.5.3.5, thesis p. 136, book p. 127; identical wording in the book).
  Classification **B** (heterogeneous, compiler source vs target), first-order languages, not
  indexed by finite elements.
- **Relation to our R:** the historical home of "prove two semantics congruent by two one-way
  relations". Our two directions (preservation and reflection) echo this. Note that "finitary
  projection" is a technical term here (see Name check).

## B5. Meyer & Wand 1985; Filinski 1996/2007; Wand–Clinger single-model approach; Stoughton
- **Meyer & Wand**, "Continuation Semantics in Typed Lambda-Calculi (Summary)", *Logics of
  Programs*, LNCS 193, 1985, pp. 219–224 [V metadata via Crossref; V text, `related/meyer-wand-1985.pdf`,
  read 2026-10-15; a six-page summary].
  - Abstract [V, p. 219]: "Previous work on the semantics of continuations has concentrated on
    untyped lambda-calculi and has used primarily the mechanism of inclusive predicates. Such
    predicates are easy to understand on atomic values, but they become obscure on functional
    values. In the case of the typed lambda-calculus, we show that such predicates can be replaced
    by retractions. The main theorem states that the meaning of a closed term is a retraction of
    the meaning of the corresponding continuationised term."
  - On the earlier line [V, p. 219]: Reynolds 74, Stoy 81 and Sethi & Tang 80 "all … discussed
    essentially an untyped lambda calculus with atoms, interpreted in Scott's D∞ model or something
    like it. … The key was the construction of a suitable relation. This was done by the method of
    inclusive predicates, which depended on the details of the models."
  - Method [V, pp. 219–223; page numbers inferred from the running heads, the first page being
    219]: simply typed λ-calculus with an answer type o; the CPS transform M ↦ M̄
    at type (α′ → o) → o, with (α → β)′ = α′ → (β′ → o) → o. Retractions α ◁ β are pairs of
    "lambda-definable maps i: α → β and j: β → α such that j ∘ i is the identity" (§6). Main
    Theorem (§9): for closed M of type α, M = j_α(J_α M̄) (OCR of the formula is damaged; the
    statement is that the direct meaning is recovered from the CPS meaning by a retraction).
    "Rather than have the direct and continuation meanings of a term connected by a relation, we
    show that the direct meaning may be recovered from the continuation meaning by a retraction …
    Hoare's notion of a 'concrete invariant' appears as a crucial part of the proof." (pp. 219–220).
    For open terms a type-indexed predicate P_α on representations (an "acceptable" predicate,
    §10) is needed; existence (§12): "We prove the existence of two acceptable predicates. The
    first uses induction on types; the second depends on the strong normalization theorem."
    "the reasoning in the proof lies entirely in the λ-calculus, and hence the theorem holds in
    any model" (p. 220).
  - Limits [V, §15, p. 223]: "The situation becomes more complicated if we study calculi in which
    strong normalization fails, such as the typed calculus with fixed-point operators. … it is not
    clear as of this writing whether this approach extends to these cases."
  - For C6: type-indexed, no recursion or fixed points, a retraction rather than a relation
    indexed by elements; not finite-element indexed.
  - Filinski's characterization [V, *Controlling Effects*, 1996, §3.4]: "Meyer and Wand's more
    abstract approach [MW85] applied to all models of simply-typed λ-calculi, but did not
    encompass computational effects – not even nontermination."
  - Classification B (term vs. its CPS transform, in models of the typed λ-calculus).
    Typed, so there are no reflexive domains.
- **Filinski**, *Controlling Effects*, PhD thesis, CMU, 1996 (CMU-CS-96-119 [U]). §3.4 [V]:
  "Early investigations [Rey74a, ST80, Sto81] were set in a domain-theoretic framework where
  the main difficulties concerned reflexive domains; as a result, these methods and results
  were closely tied to specific semantic models." Here ST80 = Sethi & Tang, JACM 1980 [U for
  details].
- **Filinski**, "On the relations between monadic semantics", TCS 375(1–3):41–75, 2007,
  doi:10.1016/j.tcs.2006.12.027 [V, full text `related/filinski-2007.pdf`, read 2026-10-15]. The
  paper uses a metalanguage with general recursive types and multiple effects, and a "methodology
  for relating two such interpretations", with Reynolds's direct-vs-continuation example as the
  prototype.
  - **One object language, two semantics.** The goal is "comparing different denotational
    semantics of the same language" (§1, p. 41). The object language (Reynolds's untyped CBN/CBV
    λ-calculus with numerals) is translated once into the metalanguage: "Define a single,
    compositional translation of the sample language … to the metalanguage, in such a way that we
    can recover both the direct and the continuation semantics as particular domain-theoretic
    interpretations of effects in the metalanguage." (§1.5, p. 46). So it is not a compiler-like
    relation between two languages. Target theorem: "Theorem 1 (Agreement of Semantics). For closed
    t, [[t]]^D = Abs([[t]]^C)" (p. 45), where Abs identifies the error answer with divergence.
  - **Construction at recursive types: Pitts-style, by minimal invariance.** "Reynolds's paper goes
    back to the inverse-limit constructions of E^d and E^c, and reinforces them to construct the
    relation ≈ at the same time. In this paper we will use a more abstract method, due to Pitts,
    which establishes the existence (and uniqueness) of ≈ based only on a simple, equational
    characterization of minimality." (§1.4, p. 45). §3.3 "Relations on recursive types",
    Theorem 39 "(Existence of Invariant Relations)" (p. 65): for relational actions F_r^+, F_r^−
    "there exists a unique pair of admissible relations R^+, R^−" satisfying the fixed-point
    equations; existence by Knaster–Tarski on admissible relations ordered by ⊆ (positive) and ⊇
    (negative), uniqueness from minimal invariance ("Unlike Pitts's proof, ours does not exploit
    the fact that the Knaster–Tarski construction actually finds the least (pre)fixed point of the
    operator", p. 65). Example 40 (p. 66) shows uniqueness fails for a non-minimal solution.
  - **Indexing:** type-indexed over the metalanguage's types, including µ-types
    (r⟦µα.τ⟧θr), parameterized by relational actions for the effects (§3.2, §3.5). No
    stages, no step indices, no finite elements; symmetric (both sides are arbitrary elements of
    the two cpos).
  - Conclusion (§4, p. 73): "the naive, circular characterization of the logical relation at
    µ-types is actually uniquely satisfiable." Future work includes "relations … between syntax
    and semantics, as used to show agreement between a denotational semantics and an operational
    one".
  - Classification B, heterogeneous (two cpos), homogeneous in language. Does not affect C6.
- **Filinski & Støvring**, "Inductive reasoning about effectful data types", ICFP 2007 [V
  abstract]: "rigid induction" integrated into logical-relations arguments, used to show that
  success-stream and failure-continuation models of backtracking are equivalent. This is B
  (two models). The body was unread.
- **Wand–Clinger single-model approach** [V via Wand & Oliva 1992]: "Wand [18] showed how to
  avoid the use of inclusive predicates by modelling the target machine in the same semantic
  domains as the source semantics … refined by Clinger [3] to prove the correctness of a
  compiler for Scheme."
  - Wand & Oliva's own relations are on terms: "Since these are relations on terms (not their
    denotations), the existence of the relations is assured" [V].
  - Wand, "Correctness of procedure representations in higher-order assembly language", MFPS
    1991, LNCS 598 [V]. Closure representation is handled inside one λ-theory by a
    conservative-extension theorem (Theorem 3), not by a cross-model relation.
  - Clinger, "The Scheme 311 compiler: an exercise in denotational semantics", LFP 1984 [V,
    `related/clinger-1984.pdf`; details in `vlisp-clinger-wand.md` §2]: target instructions get
    "a continuation semantics for each instruction" (p. 359) in the source's domains, and "Most of
    the correctness proof consists of trivial calculations. This is possible because the meanings
    of target code instructions are expressed in the same language used to express source
    meanings" (p. 356). Single model, so no inclusive predicates; the target keeps closures (a
    `lambda` instruction). Denotational in our sense (meanings are domain elements).
  - Classification: these *avoid* B by putting source and target in one model or theory. Wand
    1991 in particular is **not** a denotational semantics in our sense (author's classification,
    2026-10-15): meanings are λ-terms up to interconvertibility, which is not extensional, and no
    model is used except in the sketched conservativity proof. See `vlisp-clinger-wand.md` §3.
  - Relation to ours: our Clos3/Clos4 graph models are separate but similar. The single-model
    alternative is the obvious "why not just…" a referee may raise.
- **Stoughton** [V via the BRICS PCF bibliography]: Jung & Stoughton TLCA 1993 ("finitary PCF"
  fully abstract model), Stoughton "Mechanizing logical relations" MFPS 1993 (LNCS 802;
  definability in finite models), *Fully Abstract Models of Programming Languages* (Pitman
  1988). **No work relating two semantics over recursive domains was found**; the request may
  have meant Stoy.

## B6. Chlipala 2007 (denotation-to-denotation compiler proof) and closure-conversion proofs

### B6a. Chlipala, PLDI 2007: the closest prior denotation-to-denotation compiler proof
```bibtex
@inproceedings{Chlipala07,
  author    = {Adam Chlipala},
  title     = {A Certified Type-Preserving Compiler from Lambda Calculus to Assembly
               Language},
  booktitle = {Proceedings of the ACM SIGPLAN 2007 Conference on Programming Language
               Design and Implementation (PLDI)},
  pages     = {54--65}, year = {2007},
  doi       = {10.1145/1250734.1250742}}
```
[V]. The source is the simply-typed λ-calculus with naturals and **no recursion**, so it is
total. "We first give each Source type a meaning by a recursive translation into sets" (Coq
types). The pipeline is Source → Linear → CPS → CC → Alloc → Flat → Asm. From Alloc on,
non-termination is modelled with co-inductive traces.
- Each pass is proved by a **logical relation between denotations of the source and target
  ILs, by recursion on types** [V]. On closure conversion [V]: "It relates denotations from the
  CPS and CC languages … f1 ≃_{τ⃗→N} f2 = ∀x1:[[τ⃗]]^P, ∀x2:[[τ⃗]]^C, x1 ≃τ⃗ x2 → f1 x1 ≃ f2 x2.
  This relation is almost identical to the most basic logical relation for simply-typed lambda
  calculus! The secret is that our meta language CIC 'has native support for closures.'"
- Chlipala's related-work claim [V]: "Semantics preservation proofs have been published before
  for individual phases … including closure conversion [MMH95]. All of these proofs that we are
  aware of use operational semantics."
- Classification **B**: heterogeneous (two ILs), symmetric, type-indexed, and total. There are
  no recursive domains, and no finite elements because the semantics is Coq functions.
- Relation to our R: this is the closest prior work in purpose (a closure-conversion-like pass
  proved by relating the denotations of source and target). Our setting differs in four ways:
  an untyped graph model with general recursion; a relation indexed by finite values, not
  types; asymmetric (finite approximation vs. arbitrary set); and reflection is the hard
  direction.

### B6b. Chlipala, POPL 2010: operational
```bibtex
@inproceedings{Chlipala10,
  author    = {Adam Chlipala},
  title     = {A Verified Compiler for an Impure Functional Language},
  booktitle = {Proceedings of the 37th ACM SIGPLAN-SIGACT Symposium on Principles of
               Programming Languages (POPL)},
  pages     = {93--106}, year = {2010},
  doi       = {10.1145/1706299.1706312}}
```
[V]: "total correctness with respect to big-step operational semantics". The source is an
untyped mini-ML with fix, references and exceptions. The proof uses inductive compatibility
relations between source and target values, parameterised by closure heaps. Not
denotation-to-denotation.

### B6c. Closure conversion elsewhere
- Minamide, Morrisett & Harper, "Typed Closure Conversion", POPL 1996, pp. 271–283,
  doi:10.1145/237721.237791 [V]. **Operational**: "a type-indexed family of logical relations
  relating closed source expressions to closed target expressions … defined by induction on
  source types".
- Wand & Steckler, "Selective and Lightweight Closure Conversion", POPL 1994, pp. 435–445,
  doi:10.1145/174675.178044. Journal version: Steckler & Wand, "Lightweight Closure
  Conversion", TOPLAS 19(1):48–86, 1997. Proof method **[U]**, because no primary text was
  readable. Do not characterize it as denotational without checking.

## B7. Graph models (background for our model)
```bibtex
@article{Plotkin93,
  author  = {Gordon D. Plotkin},
  title   = {Set-Theoretical and Other Elementary Models of the $\lambda$-Calculus},
  journal = {Theoretical Computer Science},
  volume  = {121}, number = {1--2}, pages = {351--409}, year = {1993},
  doi     = {10.1016/0304-3975(93)90094-A},
  note    = {Part 1 reprints: A set theoretic definition of application, Memorandum
             MIP-R-95, School of Artificial Intelligence, Univ. Edinburgh, 1972}}
@article{Engeler81,
  author  = {Erwin Engeler},
  title   = {Algebras and Combinators},
  journal = {Algebra Universalis},
  volume  = {13}, number = {1}, pages = {389--392}, year = {1981},
  doi     = {10.1007/BF02483849}}
@article{Scott76,
  author  = {Dana Scott},
  title   = {Data Types as Lattices},
  journal = {SIAM Journal on Computing},
  volume  = {5}, number = {3}, pages = {522--587}, year = {1976},
  doi     = {10.1137/0205037}}
```
All [V] via Crossref. Memo number [V] from the reference list of the Edinburgh preprint.
- Plotkin 1972/1993 [V, preface of the preprint]: "an elementary set-theoretical model of the
  λβ-calculus. Functions are modelled … by their graphs". Application is
  x·y = ⋃{ν | ∃ finite µ ⊆ y. µ→ν ∈ x}.
- Engeler 1981 [U: description via Plotkin and Siek 2017, not Engeler's text]: model P(B_A)
  with B_A = A ∪ (P_f(B_A) × B_A); application x·y = {b | ∃ finite µ ⊆ y. (µ,b) ∈ x}. It was
  used for combinatory logic.
- Scott 1976 [U: description via Plotkin]: the graph model Pω, with x·y = {m | ∃ e_n ⊆ y.
  (n,m) ∈ x}.
- Siek 2017 §2.1 [V] gives P(D_P) with D_P = Z + P_f(D_P) × P_f(D_P) and P(D_E) with
  D_E = Z + P_f(D_E) × D_E, adapted to CBV.

Our model is Engeler/Plotkin style: arbitrary sets of finite values, with no consistency or
entailment closure.


---------------------------------------------------------------------------------------------

# Synthesis
## S1. Lineage of the ideas

**(a) Finite-element / token recursion (category A throughout).**
- Martin-Löf 1983 [V] relates a formal neighbourhood (a syntactic finite element) to a program,
  inductively on the neighbourhood's syntax; the untyped, reflexive setting is no obstacle.
- The method passes through Plotkin's lecture notes [U which ones] and is used by Abramsky's
  domain logic (formulas, LLC 1990 §5) [V].
- Winskel 1993 §13.4, Lemma 13.7 [V] states it for information-system tokens, by well-founded
  recursion on token size.
- Pitts 1993/1996 [V] names it "essentially due to Martin-Löf" and grounds it in the fact that
  {d | d ◁ e} is Scott-closed, so the relation on compact elements determines it.
- Intersection-type realizability (Krivine ch. 3, Lemma 3.5 [V]) is the same idea with types
  as the finite syntax.
- Siek 2017 §5.1 ("element-indexed" G) [V] and PLFA Adequacy (𝕍/𝔼 by recursion on Value) [V]
  are the graph-model versions.
- **All of these relate finite elements to syntax or operations, never to a second
  denotation.**

**(b) Stage / step indexing.**
- Milne 1973, Plotkin 1973 and Reynolds 1974 [V for Reynolds] build relations as towers θ_0 =
  ⊤, θ_{n+1} = B(θ_n) over the inverse-limit stages of *both* domains, then intersect over n.
  Stoy 1981 [V] ("approximation domains … taking the conjunction of the results", p. 156) and,
  per secondary sources, Milne–Strachey and Mulmuley use the same inverse-limit route for
  inclusive predicates.
- Pitts 1993/1996 [V] replaces stages by the minimal-invariant property (mixed fixed points).
  BKV 2009 mechanizes that route [V].
- Operational step-indexing appears in Benton–Hur 2009 [V], on the machine side only, with an
  admissible closure in the other direction, and in Hur–Dreyer 2011 [V] (both sides
  operational).
- Our tower has the same shape as Reynolds's. The index is the depth of the finite target
  value, and index irrelevance above the depth removes the need for limits or intersections.

**(c) Denotation-to-denotation relations (category B).**
- Reynolds 1974 [V]: direct vs. continuation; two different reflexive domains; stage-indexed.
- Milne–Strachey 1976 [U primary, V secondary]: inclusive predicates; inverse-limit induction.
- Stoy 1981 [V]: direct vs. continuation semantics of one language (B, symmetric congruence
  predicates, built on approximation domains and intersected), then continuation semantics vs. an
  interpreter (A, order-asymmetric). Not standard vs. store semantics, as these notes had said.
- Mulmuley 1985/87 [V TR]: a general mechanized existence theory for two semantics (D1, D2),
  via finitary projections in a universal domain; asymmetric "weaker-than" predicates.
- Meyer–Wand 1985 [V]: typed λ-calculus without fixed points; the direct meaning of a closed term
  is recovered from the meaning of its CPS transform by a λ-definable retraction; a type-indexed
  "concrete invariant" for open terms.
- Pitts 1996 §6 [V]: homogeneous binary relations on one domain (simulations / co-induction).
  Pitts 1993 §4 [V] only conjectures that Reynolds's heterogeneous relation fits his method.
- Filinski 2007 [V]: two monadic interpretations of one metalanguage (hence of one object
  language), related by a type-indexed logical relation; at µ-types the relation exists and is
  unique by a Pitts-style argument (Theorem 39, p. 65: Knaster–Tarski plus minimal invariance).
  Symmetric, no stages, no finite elements.
- Chlipala 2007 [V]: pass-by-pass relations between the denotations (Coq sets) of source and
  target ILs, including closure conversion. Type-indexed, total source, no recursive domains.
- Polak 1980 [V]: heterogeneous source/target predicates for a first-order Pascal-subset compiler;
  existence assumed via Reynolds's criteria.
- The Wand–Clinger line [V via Wand–Oliva] avoids B by using one model (Clinger) or one equational
  λ-theory (Wand 1991, not denotational in our sense) for source and target.

**(d) Asymmetry.**
- Finite-vs-arbitrary asymmetry exists only in category A: a finite token, neighbourhood,
  type, formula or Value against a term or closure (Martin-Löf, Winskel, Abramsky,
  Siek/PLFA).
- Benton–Hur 2009 [V] is asymmetric in a different sense: half-denotational, half-operational,
  with step indices on the machine side only.
- Stoy/Mulmuley use order-asymmetric "weaker-than" predicates, but over whole domains. In Stoy
  1981 [V] they relate a denotation to an interpreter (category A), and Stoy explains the need for
  them by the gap between "an infinitary abstract object" and "its finitary representation, such
  as the tree which represents the procedure in the interpreter" (p. 159).

## S2. Answers for Part B specifically
- **Is any prior denotation-to-denotation relation indexed by finite elements?** None that we
  found or verified.
  - Reynolds/Milne/Stoy/Mulmuley index by inverse-limit stages of both domains, which are
    projections of arbitrary elements, not compact elements.
  - Pitts uses the minimal invariant, and so does Filinski 2007 [V] for relations between two
    monadic interpretations.
  - Chlipala, Meyer–Wand [V] and Filinski [V] use types (Filinski's types include µ-types).
  - The finite-element method (Martin-Löf/Winskel) appears in the literature only for adequacy
    (category A). Pitts describes it only in that role, and it is restricted to Scott domains
    via information systems.
  - Caveats: the primary texts of Milne–Strachey and Mulmuley's book are unverified. (Filinski
    2007 and Stoy 1981 are now read; neither indexes by finite elements.)
- **Is any prior B relation asymmetric with a finite element on one side and an arbitrary
  element on the other?** None found.
  - The only asymmetric relations seen between semantics are order-asymmetric (Stoy/Mulmuley
    "weaker-than", Reynolds's η direction), not finiteness-asymmetric; Stoy's [V] are between a
    denotation and an interpreter, so they are not even B.
  - **Safe phrasing for the paper:** "to our knowledge, the first relation between two
    denotational semantics indexed by a finite approximation on one side". Keep "to our
    knowledge" because of the gaps above.
- **Purpose match.** The only prior denotation-to-denotation proof of a closure-conversion-like
  pass that we found is Chlipala 2007, which is typed, total and type-indexed. Wand MFPS 1991
  treats closure representations inside one λ-theory.

## S3. Claims that remain unverified (do not state without checking)
Resolved on 2026-10-15: Pitts 1996's issue number (2) and the page of the §2 Reynolds remark
(p. 68); the Krivine English edition (Ellis Horwood 1993, from Open Library, translator unverified).
Resolved in the third pass (PDFs in `papers/PLDI-2027/related/`): Filinski 2007 (construction:
§3.3, Theorem 39), Meyer–Wand 1985 (content), Clinger 1984 (content), Stoy 1981 (content; it
corrects the earlier "standard vs. store" description), Abramsky & Ong 1993 (image-only scan read
page by page: adequacy via the domain logic, Theorem 5.4.9, p. 206; see A4b). None of the items below
bears on C3; items 5–6 are the remaining caveats on C6.

1. Which "Gordon Plotkin's lecture notes" Winskel means in §13.11 (Pisa notes [80] or CSLI 1985
   [83]).
2. Winskel chapter numbering in later printings (a 2001 listing appears to differ).
3. Whether the DTLF APAL article contains the lazy-λ adequacy material. (Abramsky & Ong 1993's
   adequacy method: resolved, see A4b.)
4. Krivine English edition: translator and series.
5. Milne–Strachey 1976 and Stoy 1977 (the book): chapter and section locations of the
   inclusive-predicate constructions.
6. Mulmuley's 1987 book (only the 1985 TR was read).
7. Wand–Steckler 1994 proof method.
8. Sieber 1992 bib and whether it uses "finitary". Whether the O'Hearn–Riecke body (not just
   the abstract) uses "finitary logical relations".
9. Engeler 1981 and Scott 1976 one-line descriptions (taken from Plotkin and Siek, not the
   originals).
10. The BBKV "Formalizing Domains…" final publication venue.
11. Name check: no Google Scholar, DBLP or ACM full-text search was completed (still blocked on
    2026-10-15: Scholar 429, DBLP bot check, ACM 403). OpenAlex and arXiv abstract searches for
    the novelty claims found no relation between two denotations indexed by finite elements.


Recall that closure conversion lowers lexically-scoped functions into
a flat-closure representation, which pairs a function pointer with a
tuple of values for the function's free variables. The crux of this
pass is a transformation we call "delay" (D) because it postpones the
point at which the function is applied to the above-mentioned tuple,
from the point of definition of the function to the points of
application. Let `⟦-⟧ₛ` be the denotational semantics for the source
language of "delay" and `⟦-⟧ₜ` be the semantics for its target.  (Both
languages are variants of the untyped lambda calculus.)  We tried to
prove something like:

    (∀ x. ρ(x) ≈ ρ'(x)) implies ⟦ M ⟧ₛ ρ ≈ ⟦ D(M) ⟧ₜ ρ'
   
where much of the difficulty was in finding an appropriate definition
for the `≈` relation. In a denotational semantics based on the graph
model, the semantics of a term is an infinite set of finite
descriptions of the term's behavior.  So a straightforward way to
define `≈` is

    S ≈ S' iff     ∀ f. f ∈ S implies ∃f'. f' ∈ S' and f ~ f' (forward)
	           and ∀ f'. f' ∈ S′ implies ∃f. f ∈ S and f ~ f' (backward).

with some suitable definition of equivalence `~` for finite
descriptions.

Consider the following example. The first transformation changes the
lambda abstraction to make explicit the creation of a tuple for the
free variables. The second transformation, the above-mentioned "delay",
does two things, it
(1) replaces the application of `(λ fv ...)` to `⟨ y , z ⟩` with the
creation of another tuple that contains those two items and
(2) replaces the application `add(3)` with the application `add[0](add[1], 3)`.

	let y = 4 in 
	let z = 5 in 
	let add = λ x. x + y + z in
	add(3)
    ===>
	let y = 4 in 
	let z = 5 in 
	let add = (λ fv. λ x. x + fv[0] + fv[1]) ⟨ y , z ⟩ in
	add(3)
    ===> "delay"
	let y = 4 in 
	let z = 5 in 
	let add = ⟨(λ (fv, x). x + fv[0] + fv[1]) , ⟨ y , z ⟩ ⟩ in
	add[0](add[1], 3)

Focusing on the "delay" transformation of the lambda abstractions
and the backward direction of the equivalence, we need to show
that

    ∀f'. f' ∈ ⟦ ⟨(λ fv x. x + fv[0] + fv[1]) , ⟨ y , z ⟩ ⟩ ⟧ₜ(y={4},z={5})
	implies
    ∃f. f ∈ ⟦ (λ fv. λ x. x + fv[0] + fv[1]) ⟨ y , z ⟩ ⟧ₛ(y={4},z={5}) 
	and f ~ f'

Consider

    f' = ⟨ {⟨0,0⟩ ↦ 3 ↦ 3} , ⟨ 4 , 5 ⟩ ⟩

where `{⟨0,0⟩ ↦ 3 ↦ 3}` is one entry in the input-output table for
the lambda abstraction:
    
    {⟨0,0⟩ ↦ (3 ↦ 3)} ∈ ⟦ λ fv. λ x. x + fv[0] + fv[1] ⟧ₜ
	
This entry says that if the pair `⟨0,0⟩` is bound to `fv`, and
`3` is bound to `x`, then the result is `3`.
(Note that there are many other elements of `⟦ λ fv. λ x. ... ⟧ₜ`,
such as `{⟨4,5⟩ ↦ (3 ↦ 12)}`, `{⟨4,5⟩ ↦ (6 ↦ 15)}`,
and `{⟨0,0⟩ ↦ (6 ↦ 6)}`.)

Given this `f'`, we need to find an element `f` of

    ⟦ (λ fv. λ x. x + fv[0] + fv[1]) ⟨ y , z ⟩ ⟧ₛ(y={4},z={5}) 
	
such that `f` corresponds to `f'`, i.e., `f ~ f'`.  However, the elements of
this partially-applied lambda all have y and z fixed at 4 and 5
respectively so this partially-applied lambda is the "plus nine"
function:

    {0 ↦ 9}, {1 ↦ 10}, {2 ↦ 11}, {3 ↦ 12}, {6 ↦ 15}, ...

So there is no `f` in it that corresponds to `{⟨0,0⟩ ↦ (6 ↦ 6)}`,
(the "identity" function).

We have tried several approaches to solving this problem, but ran into
road blocks with each one of them. If you know of a technique for
solving this problem, please let us know!

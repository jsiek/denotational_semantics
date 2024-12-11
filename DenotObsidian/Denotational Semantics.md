Goal: conduct proofs of compiler correctness using denotational semantics. Especially the closure conversion pass.

Need to understand correctness for passes that go from higher-level abstractions to lower-level ones, especially where lower-level abstractions are used for multiple different higher-level ones. For example, in closure conversion, we use tuples to represent closures but also use tuples to represent tuples.

We need a way to capture the invariants from the higher-level language in the lower-level one. One possibility is to define a type system that captures the invariants that arise from a low-level program being in the compilation image of the higher level one.

Let's try this on a simple typed language, without functions, just fractions and pairs.

[[Compiling Fractions]]

Ok, that was pretty easy. The logical relation was straightforward.

brainstorms about next steps:
* use SIL to define semantics?
* use SIL to define the logical relation?
* add recursive types?
* add a dynamic type with inject/project
* add functions
* add general recursion via fix


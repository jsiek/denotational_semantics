
RQ1. Is it possible to prove compiler correctness from a higher-order
source language with general recursion down to a target assembly
language using denotational semantics?

  Answer: Yes, we supply the final missing link, which is the
  reflection direction for the Delay pass of closure conversion.)


RQ2. Does the compositionality and equational reasoning afforded by
denotational semantics yield concise proofs of correctness for some
compiler passes?

  Answer: Yes, most of the passes. For some passes, such as simplify,
  the denotational proof is shorter than correctness proofs using
  operational semantics.


RQ3. Can all the compiler passes from a higher-order and recursive
source language down to a target assembly language be proved by
equational reasoning?

  Answer: Surprisingly no, not for passes that translate program
  values to a lower-level representation, such as the Delay pass.
  

RQ4. How does the denotational approach compare overall to operational
approaches for proving compiler correctness from a higher-order and
recursive source language to a target assembly language?

  Answer: Much to our chagrin, the denotational approach comes in 2nd
  place, behind the clocked interpreter but ahead of abstract machines
  and reduction semantics.


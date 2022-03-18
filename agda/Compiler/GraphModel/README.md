This folder contains partial proofs of correctness of a critical pass in
closure conversion (that we call delay).

Relevant file names/labels include:
- The IRs and passes are, in order, 
   + Clos1 (enclose) exposes free variables; captures free variable values via multiple applications
   + Clos2 (optimize) stops capturing unused free variables
   + Clos2 (concretize) make captured environment a single tuple; single early application
   + Clos3 (delay) delay early applications; place captured envrionment in a closure
   + Clos4
- The first part of names generally indicate what the file contains
   + Clos files are language definitions
   + Compiler contains pass definitions
   + Domain files contain definitions of value sets and their basic properties
   + DOp files contain denotational operators for each domain and proofs of consistency and monotonicity
   + DelayCorrect contains correctness proofs for the delay pass
- The Multi tag indicates that closure pairs contain a list of values in their second component
- The Single tag indicates that closure pairs contain a single value in their second component
- The AnnLam tag indicates that arrow values have annotations
- The AnnPair tag indicates that closure pairs have annotations
- DelayCorrect, the correctness proof for the delay pass has a few different versions
   + AnnLam is the newest version that gets rid of annotated pairs and attempts to use both to and fro functions and a limited form of union on closure environments to do a direct proof in the application case
   + Rel attempts a fro relation instead of function
   + Sal attempts to define "salient" values, which we restrict the correctness result to.
   + Set is an experiment at defining a relation between denotation sets.
   + Single attempts to use pair annotations to sidestep the issues with carrying only single values to represent environments.

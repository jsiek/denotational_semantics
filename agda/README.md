

File Overview

* `Variables`

  Defines de Bruijn indices, Rename, ext, and var≟.

* `Syntax2`

  Abstract binding trees a la Robert Harper,
  substitution, and contexts. 

* `Structures`

  * Generic structures Domain, ValueOrdering, ModelCurry, LambdaModelBasics.
  * Defines auxilliary modules expressed in terms of the
    generic structures: DomainAux, OrderingAux, DenotAux.
    DenotAux includes a proof of compositionality.
  * Denotational semantics of lambda calculus defined
    generically in terms of ●, ℱ, Domain, and ValueOrdering.

* `MultiStep`

  Defines multi-step reduction generically given a reduction
  relation.

* `ValueBCD`

  * Denotational values (⊥, ↦, ⊔) (aka. BCD intersection
    types), the ⊑ ordering, and ℱ. Instances of Domain
    and ValueOrdering.
  * Proves function inversion and stuff
    about AboveFun needed for adequacy of CBN.

* `ValueBCDConst`

  * Adds constants, including primitive operators.

* `Lambda`

  Syntax, reduction, and contextual equivalence for the lambda
  calculus.

* `LambdaCallByValue`

  Call-by-value reduction and contextual equivalence.

* `ISWIM`

  Call-by-value lambda calculus with constants and a δ redution rule.

* `EvalCallByName`

  Call-by-name evaluation as a big-step relation.
  Proves that CBN evaluation implies reduction to WHNF.

* `EvalCallByValue`

  Call-by-value evaluation as a big-step relation.
  Proves that CBV evaluation implies CBV reduction to WHNF.

* `EvalISWIM`

  Same as above, but with constants added.

* `ModelCallByName`

  * ● for CBN and a bunch of lemmas about it.
  * An instance of LambdaModelBasics

* `ModelCallByValue`

  * ● for CBV and a bunch of lemmas about it.
  * An instance of LambdaModelBasics

* `ModelISWIM`

  Same as above for ISWIM. Just instantiates the ModelCallByValue
  module with a different domain.

* `RenamePreserveReflect` (requires LambdaModelBasics)

  Proves that renaming preserves and reflects denotations.

* `Filter` (requires LambdaModelBasics)

  Proves admisibility of subsumption and ⊔ introduction.

* `SubstitutionPreserve` (requires LambdaModelBasics)

  Proves that substitution preserves denotations.

* `SubstitutionReflect`

  Proves that substitution reflects denotations for the models
  of CBN, CBV, and ISWIM.

* `SoundnessCallByName`

  Proves soundness of lambda reduction wrt. CBN denotational model.

* `SoundnessCallByValue`

  Proves soundness of call-by-value reduction wrt. CBV denotational model.

* `SoundnessISWIM`

  Proves soundness of ISWIM reduction wrt. its denotational model.

* `AdequacyCallByName`

  Proves adequacy of CBN model with respect to lambda reduction to WHNF.
  Also proves that denotational equality implies contextual equivalence.

* `AdequacyCallByValue`

  Proves adequacy of CBV model with respect to CBV reduction to WHNF.
  Also proves that denotational equality implies contextual equivalence.

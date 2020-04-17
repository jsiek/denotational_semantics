

File Overview

* `Utilities`

   Miscellaneous small items.

* `Structures`

   Structures ValueStruct, ValueOrdering, ModelCurry, and Consistent.

* `ValueStructAux`  (parameterized on ValueStruct)

   * Environments (type `Env`) and operations on them.
   * Type `Denotation`

* `OrderingAux` (parameterized on ValueStruct and ValueOrdering)

   * Derived rules regarding `⊑`.
   * Equational reasoning for `⊑`.
   * Extending `⊑` to environments.

* `ConsistentAux` (parameterized on Consistent, etc.)

   * denotational equality `≃` and inequality `≲`
	 with notation for equational reasoning.
   * Well-formed environments (`WFEnv`).
   * Consistency for environments.
   * Derived rules regarding `~`.

* `CurryApplyStruct` (parameterized on Consistent, etc.)

   Structures `CurryStruct` and `CurryApplyStruct`.
   
* `CurryApplyAux` (parameterized by CurryApplyStruct)

   Proves congruence rules wrt. ≃ for ℱ and ●. 

* `LambdaDenot` (parameterized on ValueStruct and ValueOrdering)

  Denotational semantics of lambda calculus defined
  generically in terms of ●, ℱ, Domain, and ValueOrdering.

* `ISWIMDenot` (parameterized on ValueStruct and ValueOrdering)

  Denotational semantics of ISWIM defined
  generically in terms of ●, ℱ, Domain, and ValueOrdering.

* `ISWIMDenotAlt`

  An alternative semantic definition of ISWIM that does not use `⊑`
  in the variable case, but only in the meaning of application.
  So it does not satisfy `ℰ-⊑`. Nevertheless, this version is equivalent
  to the above version in the same way that an algorithmic
  type system is equivalent to a declarative one.  

* `Compositionality` (parameterized on CurryApplyStruct)

   Proof of compositionality for the lambda calculus and ISWIM.

* `MultiStep`

  Defines multi-step reduction generically given a reduction
  relation.

* `ValueBCD`

  * Denotational values (⊥, ↦, ⊔) (aka. BCD intersection
    types), the ⊑ ordering, and ℱ. Instances of ValueStruct,
    ValueOrdering, and Consistent.
  * Proves function inversion and stuff about AboveFun needed for
    adequacy of call-by-name.

* `ValueConst`

  * Adds constants, including primitive operators.

* `Consistency`

  * Proof of the consistent subtyping property.
  * Instance of the Consistent structure.

* `Lambda`

  Syntax, reduction, and contextual equivalence for the lambda
  calculus.

* `LambdaCallByValue`

  Call-by-value reduction and contextual equivalence.

* `ISWIM`

  Call-by-value lambda calculus with constants and a δ reduction rule
  for primitive operations.

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
  * An instance of CurryApplyStruct

* `ModelISWIM`

  Same as above for ISWIM. Just instantiates the ModelCallByValue
  module with a different domain.

* `RenamePreserveReflect` (parameterized on CurryApplyStruct)

  Proves that renaming preserves and reflects denotations.

* `Filter` (requires CurryApplyStruct)

  Proves admisibility of subsumption and ⊔ introduction.

* `SubstitutionPreserve` (parameterized on CurryApplyStruct)

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

* `AdequacyISWIM`

  Proves adequacy of ISWIM's model with respect to ISWIM reduction to
  a value (literal or lambda abstraction).  Also proves that
  denotational equality implies contextual equivalence.

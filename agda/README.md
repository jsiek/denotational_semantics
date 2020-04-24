File Overview
=============

* `Utilities`

   Miscellaneous small items.

* `Primitives`

   Mechanism for importing Agda values into a programming language to
   be treated as constants.

* Syntax and Operational Semantics

   * `MultiStep`

     Defines multi-step reduction generically given a reduction
     relation.

   * Lambda Calculus

      * `Lambda`

        Syntax, reduction, and contextual equivalence for the lambda
        calculus.

      * `EvalCallByName`

        Call-by-name evaluation as a big-step relation.
        Proves that CBN evaluation implies reduction to WHNF.

   * CBV Lambda Calculus
   
      * `LambdaCallByValue`

        Call-by-value reduction and contextual equivalence.

      * `EvalCallByValue`

        Call-by-value evaluation as a big-step relation.
        Proves that CBV evaluation implies CBV reduction to WHNF.

   * ISWIM (CBV Lambda Calclulus + constants)

      * `ISWIM`

        Call-by-value lambda calculus with constants and a δ reduction rule
        for primitive operations.

      * `EvalISWIM`

        Call-by-value evaluation as a big-step relation.
        Proves that CBV evaluation implies CBV reduction to WHNF.

* Domain Construction

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

      Structures `CurryStruct` and `CurryApplyStruct`.  These two
      structures capture several properties about the `ℱ` and `●`
      operators, such as being downward closed with respect to `⊑`,
      being closed with respect to `⊔` and `~`, and properties about
      `≲`.

   * `CurryApplyAux` (parameterized by CurryApplyStruct)

      Proves congruence rules wrt. ≃ for ℱ and ●. 

   * `ValueBCD`

      * Denotational values (⊥, ↦, ⊔) (aka. BCD intersection types),
        the ⊑ ordering, and ℱ, for the lambda calculus.
        Instances of ValueStruct, ValueOrdering, and Consistent.

      * Proves function inversion and stuff about AboveFun needed for
        adequacy of call-by-name.

   * `ValueConst`

      * Denotational values (⊥, ↦, ⊔) including constants
        and primitive operators.

      * `CurryConst`

         * Definition of ℱ and ℘.

      * `Consistency`

        * Proof of the consistent subtyping property.
        * Instance of the Consistent structure.

   * `ModelCallByName`

     * Definition of ● for CBN and a bunch of lemmas about it.
     * An instance of LambdaModelBasics

   * `ModelCallByValue` (parameterized on ValueStruct, etc.)

     * Definition ● for CBV and a bunch of lemmas about it.
     * An instance of CurryApplyStruct

   * `ModelISWIM`

     Instantiates the ModelCallByValue with the domain defined
     in ValueConst.


* Denotational Semantics

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

   * `PrimConst`

      Properties of primitive constants for domain in ValueConst.

   * `Compositionality` (parameterized on CurryApplyStruct)

      Proof of compositionality for the lambda calculus and ISWIM.

   * `RenamePreserveReflect` (parameterized on CurryApplyStruct)

      Proves that renaming preserves and reflects denotations.

   * `Filter` (requires CurryApplyStruct)

      Proves admisibility of subsumption and ⊔ introduction
      for the lambda calculus (both CBN and CBV) and for ISWIM.

   * Soundness of reduction with respect to denotational equality

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

   * Adequacy of denotational semantics with respect to reduction

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

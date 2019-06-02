

File Overview

* Variables

  Defines de Bruijn indices, Rename, ext, and var≟.

* Syntax2

  Abstract binding trees a la Robert Harper,
  substitution, and contexts. 

* Structures

  * Generic structures Domain, ValueOrdering, LambdaModelBasics.
  * Defines auxilliary modules expressed in terms of the
    generic structures: DomainAux, OrderingAux, DenotAux.
    DenotAux includes a proof of compositionality.
  * Denotational semantics of lambda calculus defined
    generically in terms of _●_, ℱ, Domain, and ValueOrdering.
  
* ValueBCD

  * Denotational values (⊥, _↦_, _⊔_) (aka. BCD intersection
    types), the ⊑ ordering, and ℱ. Instances of Domain
    and ValueOrdering.
  * Proves function inversion and stuff
    about AboveFun needed for adequacy of CBN.

* Lambda

  Syntax, reduction, and contextual equivalence for the lambda
  calculus.

* LambdaCallByValue

  Call-by-value reduction and contextual equivalence.

* EvalCallByName

  Call-by-name evaluation as a big-step relation.
  Proves that CBN evaluation implies reduction to WHNF.

* EvalCallByValue

  Call-by-value evaluation as a big-step relation.
  Proves that CBV evaluation implies CBV reduction to WHNF.

* ModelCallByName

  * _●_ for CBN and a bunch of lemmas about it.
  * An instance of LambdaModelBasics

* ModelCallByValue

  * _●_ for CBV and a bunch of lemmas about it.
  * An instance of LambdaModelBasics

* RenamePreserveReflect (requires LambdaModelBasics)
  Proves that renaming preserves and reflects denotations.

* SubstitutionPreserve (requires LambdaModelBasics)
  Proves that substitution preserves denotations.

* SubstitutionReflect
  Proves that substitution reflects denotations for both of the
  CBN and CBV models.

* PreserveReflectCallByName
  Proves soundness of lambda reduction wrt. CBN denotational model.

* PreserveReflectCallByValue
  Proves soundness of call-by-value reduction wrt. CBV denotational model.

* AdequacyCallByName
  Proves adequacy of CBN model with respect to lambda reduction to WHNF.
  Also proves that denotational equality implies contextual equivalence.

* AdequacyCallByValue
  Proves adequacy of CBV model with respect to CBV reduction to WHNF.
  Also proves that denotational equality implies contextual equivalence.

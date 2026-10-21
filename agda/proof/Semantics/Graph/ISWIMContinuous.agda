{-

  The ISWIM semantics is continuous (from its operators, in
  proof/Semantics/Graph/ISWIM.agda), and a function body needs only a
  finite part of its argument (body-continuous).

-}

module proof.Semantics.Graph.ISWIMContinuous where

open import proof.Semantics.Graph.ISWIM using (ISWIM-Continuous; body-continuous) public

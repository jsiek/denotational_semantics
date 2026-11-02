{-

  The ISWIM semantics is continuous (from its operators, in
  ISWIM/proof/Semantics/Graph/ISWIM.agda), and a function body needs only a
  finite part of its argument (body-continuous).

-}

module ISWIM.proof.Semantics.Graph.ISWIMContinuous where

open import ISWIM.proof.Semantics.Graph.ISWIM using (ISWIM-Continuous; body-continuous) public

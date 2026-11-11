{-

  This module states the correctness of split (EnvClosμ → PairClosμ) in
  the graph model, as for typed split
  (ISWIM/proof/Correctness/Graph/SplitCorrect.agda). Because split
  changes the representation of closures, the meaning of a program and
  the meaning of its translation differ. Instead of an equation, the
  correctness of split says that it preserves (SplitPreserve.agda) and
  reflects (SplitReflect.agda) the constants that a closed program
  produces, and whether the program produces anything at all.

-}

open import Framework.GraphModel.Prelude
open import Framework.Primitives using (base-rep)
open import FPC.Semantics.GraphModel.Closed using (ρ₀)
open import FPC.Language.EnvClos using (Tm)
open import FPC.Compiler.Split using (split-program)
open import FPC.Semantics.GraphModel.EnvClos using (⟦_⟧)
open import FPC.Semantics.GraphModel.PairClos renaming (⟦_⟧ to ⟦_⟧₄)
open import FPC.proof.Correctness.GraphModel.SplitPreserve using (preserve-const; preserve-nonempty)
open import FPC.proof.Correctness.GraphModel.SplitReflect using (reflect-const; reflect-nonempty)

open import Data.List using ([])
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)

module FPC.proof.Correctness.GraphModel.SplitCorrect where

split-correct-const : ∀ {A} (M : Tm [] A) {B} (c : base-rep B)
  → (  const c ∈ ⟦ M ⟧ ρ₀
     → const c ∈ ⟦ split-program M ⟧₄ ρ₀)
  × (  const c ∈ ⟦ split-program M ⟧₄ ρ₀
     → const c ∈ ⟦ M ⟧ ρ₀)
split-correct-const M c = ⟨ preserve-const M c , reflect-const M c ⟩

split-correct-nonempty : ∀ {A} (M : Tm [] A)
  → (  nonempty (⟦ M ⟧ ρ₀)
     → nonempty (⟦ split-program M ⟧₄ ρ₀))
  × (  nonempty (⟦ split-program M ⟧₄ ρ₀)
     → nonempty (⟦ M ⟧ ρ₀))
split-correct-nonempty M = ⟨ preserve-nonempty M , reflect-nonempty M ⟩

{-

  Correctness of delay (EnvClosμ → FlatClosμ) in Scott domains: a closed
  program and its translation produce the same constants, and one is
  defined exactly when the other is, as in the graph model
  (Mu/proof/Correctness/GraphModel/DelayCorrect.agda). Forward by Pres,
  backward by Refl (DelayTerms.agda): in either relation a defined value
  related to a constant is that constant (Rel-const-is).

-}

open import MLTT.Spartan hiding (inl; inr; cases; _+_)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons

open import Framework.Primitives using (Base; base-rep)
open import Mu.Language.Type
open import Mu.Language.EnvClos
open import Mu.Compiler.Delay using (delay-program)
open import Data.List using ([])

module Mu.proof.Correctness.ScottDomains.DelayCorrect
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : propext 𝓤₀)
       where

open import Framework.Scott.Base pt fe
open import Framework.Scott.Functor pt fe pe using (obj)
open import proof.Framework.Scott.Ops pt fe pe
open import proof.Framework.Scott.Values pt fe pe
open import proof.Framework.Scott.Semantics pt fe pe using (ρ₀)
open import Mu.proof.Correctness.ScottDomains.DelayRel pt fe pe
open import Mu.proof.Correctness.ScottDomains.DelayTerms pt fe pe using (delay-pres; delay-refl)
open import Mu.Semantics.ScottDomains.EnvClos pt fe pe renaming (⟦_⟧ to ⟦_⟧₃)
open import Mu.Semantics.ScottDomains.FlatClos pt fe pe renaming (⟦_⟧ to ⟦_⟧₄)

{- a defined value related to a constant is that constant -}
Rel-const-is : ∀ {δ w} (B : Base) (c : base-rep B) → Rel δ (const B c) w → defined w → w ＝ const B c
Rel-const-is {δ} {w} B c h q = inj-view w q ∙ const-view (view w q) (pr₁ (Rel-view ⋆ h q 0))
 where
  const-view : (u : ⟨ obj Val 𝔻 ⟩) → Same δ (con B c) (pr₁ u) → inj (pr₁ u) · pr₂ u ＝ const B c
  const-view (.(con B c) , ⋆) s-con = refl

delay-correct-defined : ∀ {A} (M : Tm [] A)
  → (defined (⟦ M ⟧₃ · ρ₀) → defined (⟦ delay-program M ⟧₄ · ρ₀))
  × (defined (⟦ delay-program M ⟧₄ · ρ₀) → defined (⟦ M ⟧₃ · ρ₀))
delay-correct-defined M = Rel-defined (delay-pres M) , Rel-defined (delay-refl M)

delay-correct-const : ∀ {A} (M : Tm [] A) (B : Base) (c : base-rep B)
  → (⟦ M ⟧₃ · ρ₀ ＝ const B c → ⟦ delay-program M ⟧₄ · ρ₀ ＝ const B c)
  × (⟦ delay-program M ⟧₄ · ρ₀ ＝ const B c → ⟦ M ⟧₃ · ρ₀ ＝ const B c)
delay-correct-const M B c = same (delay-pres M) , same (delay-refl M)
 where
  same : ∀ {δ a w} → Rel δ a w → a ＝ const B c → w ＝ const B c
  same {δ} {w = w} h refl = Rel-const-is B c h (Rel-defined h (const-defined B c))

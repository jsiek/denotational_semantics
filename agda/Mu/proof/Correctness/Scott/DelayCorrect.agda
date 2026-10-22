{-

  Correctness of delay (Clos3μ → Clos4μ) in Scott domains: a closed
  program and its translation produce the same constants, and one is
  defined exactly when the other is, as in the graph model
  (Mu/proof/Correctness/Graph/DelayCorrect.agda). Forward by Pres
  (DelayPreserveTerms.agda), backward by Refl (DelayReflectTerms.agda):
  a defined value related to a constant is that constant.

-}

open import MLTT.Spartan hiding (inl; inr; cases; _+_)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons

open import Framework.Primitives using (Base; base-rep)
open import Mu.Language.Type
open import Mu.Language.Clos3
open import Mu.Compiler.Delay using (delay-program)
open import Data.List using ([])

module Mu.proof.Correctness.Scott.DelayCorrect
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : propext 𝓤₀)
       where

open import Framework.Scott.Base pt fe
open import Framework.Scott.Functor pt fe pe using (obj)
open import proof.Framework.Scott.Ops pt fe pe
open import proof.Framework.Scott.Values pt fe pe
open import proof.Framework.Scott.Semantics pt fe pe using (ρ₀)
import Mu.proof.Correctness.Scott.DelayPreserve pt fe pe as P
import Mu.proof.Correctness.Scott.DelayReflect pt fe pe as R
import Mu.proof.Correctness.Scott.DelayReflectOps pt fe pe as RO
open import Mu.proof.Correctness.Scott.DelayPreserveTerms pt fe pe using (delay-pres)
open import Mu.proof.Correctness.Scott.DelayReflectTerms pt fe pe using (delay-refl)
open import Mu.Semantics.Scott.Clos3 pt fe pe renaming (⟦_⟧ to ⟦_⟧₃)
open import Mu.Semantics.Scott.Clos4 pt fe pe renaming (⟦_⟧ to ⟦_⟧₄)

private
 {- a defined value whose tag and payload match a constant's is that constant -}
 const-P : (B : Base) (c : base-rep B) (t' : Tag) (y : ⟨ obj (Payload t') 𝔻 ⟩) → P.Match 0 (con B c) t' ⋆ y
   → inj t' · y ＝ const B c
 const-P B c (con .B .c) ⋆ (refl , _) = refl

 const-R : (B : Base) (c : base-rep B) (t : Tag) (x : ⟨ obj (Payload t) 𝔻 ⟩) → R.MatchR 0 t (con B c) x ⋆
   → inj t · x ＝ const B c
 const-R B c (con .B .c) ⋆ (refl , _) = refl

delay-correct-defined : ∀ {A} (M : Tm [] A)
  → (defined (⟦ M ⟧₃ · ρ₀) → defined (⟦ delay-program M ⟧₄ · ρ₀))
  × (defined (⟦ delay-program M ⟧₄ · ρ₀) → defined (⟦ M ⟧₃ · ρ₀))
delay-correct-defined M =
  P.Pres-defined (⟦ M ⟧₃ · ρ₀) (⟦ delay-program M ⟧₄ · ρ₀) (delay-pres M) ,
  RO.Refl-defined (⟦ M ⟧₃ · ρ₀) (⟦ delay-program M ⟧₄ · ρ₀) (delay-refl M)

delay-correct-const : ∀ {A} (M : Tm [] A) (B : Base) (c : base-rep B)
  → (⟦ M ⟧₃ · ρ₀ ＝ const B c → ⟦ delay-program M ⟧₄ · ρ₀ ＝ const B c)
  × (⟦ delay-program M ⟧₄ · ρ₀ ＝ const B c → ⟦ M ⟧₃ · ρ₀ ＝ const B c)
delay-correct-const M B c = forward , backward
 where
  d = ⟦ M ⟧₃ · ρ₀
  d' = ⟦ delay-program M ⟧₄ · ρ₀
  forward : d ＝ const B c → d' ＝ const B c
  forward e = inj-view d' q' ∙ const-P B c (pr₁ (view d' q')) (pr₂ (view d' q'))
                                  (P.Pres-view (con B c) ⋆ d' h q' 0)
   where
    h = transport (λ - → P.Pres - d') e (delay-pres M)
    q' = P.Pres-defined (const B c) d' h (const-defined B c)
  backward : d' ＝ const B c → d ＝ const B c
  backward e = inj-view d q ∙ const-R B c (pr₁ (view d q)) (pr₂ (view d q))
                                 (RO.Refl-view d (con B c) ⋆ h q 0)
   where
    h = transport (λ - → R.Refl d -) e (delay-refl M)
    q = RO.Refl-defined d (const B c) h (const-defined B c)

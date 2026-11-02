{-

  The FPC compiler in Scott domains, observed through the clocked
  interpreters, as the graph model's Mu/proof/Adequacy/EndToEnd.agda:
  for a closed FPC program M,

    FPC interpreter  ⇔  ⟦ M ⟧ ρ₀             (FPC.agda)
                     ⇔  ⟦ compile M ⟧ₜ       (Correctness/ScottDomains/CompilerCorrect.agda)
                     ⇔  X86μ interpreter     (X86.agda)

  for constants, and for divergence through ⊥ (the meanings are ⊥
  exactly when they are not defined, and compiler correctness says that
  ⟦ M ⟧ ρ₀ is defined exactly when ⟦ compile M ⟧ₜ is). So Scott domains
  state, for a main of type Int, the theorem of the interpreter column:
  the two interpreters stop with the same constant, or both diverge.

-}

open import MLTT.Spartan hiding (cases; Type)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons

open import Framework.Primitives using (Int)
open import Mu.Language.Type using (base)
open import Mu.Language.FPC using (Tm)
open import Mu.Compiler.Pipeline using (compile)
open import Semantics.Observation using (o-const; _⇔_)
open import Semantics.Interp.Clock using (Terminates; Diverges)
import Mu.Semantics.ClockedInterpreters.FPC as I
import Mu.Semantics.ClockedInterpreters.X86 as X

open import Data.Integer using (ℤ)
open import Data.List using ([])
import Data.Product as P

module Mu.proof.Adequacy.ScottDomains.EndToEnd
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : propext 𝓤₀)
       where

open import Framework.Scott.Base pt fe hiding (_>>=_)
open import proof.Framework.Scott.Ops pt fe pe using (𝔻; const; ⊥𝔻; defined; ⊥-undefined)
open import proof.Framework.Scott.Values pt fe pe using (undefined-⊥)
open import Mu.Semantics.ScottDomains.FPC pt fe pe using (⟦_⟧)
open import Mu.Semantics.ScottDomains.X86 pt fe pe using (⟦_⟧ₜ)
open import Mu.Semantics.ScottDomains.Closed pt fe pe using (ρ₀)
open import Mu.proof.Correctness.ScottDomains.CompilerCorrect pt fe pe using (compile-same)
import Mu.proof.Adequacy.ScottDomains.FPC pt fe pe as AI
import Mu.proof.Adequacy.ScottDomains.X86 pt fe pe as AX

private
 {- ⊥ exactly when not defined -}
 ⊥-iff : (d : ⟨ 𝔻 ⟩) → (d ＝ ⊥𝔻 → ¬ defined d) × (¬ defined d → d ＝ ⊥𝔻)
 ⊥-iff d = (λ e q → ⊥-undefined (transport defined e q)) , undefined-⊥ d

compile-const : ∀ (M : Tm [] (base Int)) (n : ℤ)
  → Terminates (I.sem M) (o-const Int n) ⇔ Terminates (X.sem (compile M)) (o-const Int n)
compile-const M n =
  (λ t → pr₁ (AX.x86-const-iff M Int n) (pr₁ (pr₁ (compile-same M) Int n) (pr₂ (AI.const-iff M Int n) t)))
  P., (λ t → pr₁ (AI.const-iff M Int n) (pr₂ (pr₁ (compile-same M) Int n) (pr₂ (AX.x86-const-iff M Int n) t)))

compile-diverges : ∀ (M : Tm [] (base Int)) → Diverges (I.sem M) ⇔ Diverges (X.sem (compile M))
compile-diverges M =
  (λ div → pr₂ (AX.x86-diverges-iff M)
             (pr₂ (⊥-iff ⟦ compile M ⟧ₜ) (λ q → pr₁ (⊥-iff (⟦ M ⟧ · ρ₀)) (pr₁ (AI.diverges-iff M) div) (pr₂ D q))))
  P., (λ div → pr₂ (AI.diverges-iff M)
             (pr₂ (⊥-iff (⟦ M ⟧ · ρ₀)) (λ q → pr₁ (⊥-iff ⟦ compile M ⟧ₜ) (pr₁ (AX.x86-diverges-iff M) div) (pr₁ D q))))
 where
  D = pr₂ (compile-same M)

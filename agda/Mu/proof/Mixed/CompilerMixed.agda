{-

  The ISWIMμ compiler proved by mixing semantics: simplify in the graph
  model (Mu/proof/Correctness/GraphModel/SimplifyCorrect.agda), every other
  pass by the clocked interpreters (Mu/proof/Correctness/ClockedInterpreters/, as in
  CompilerFuel.agda), joined at ISWIMμ by the bridge between its graph
  semantics and its interpreter (Mu/proof/Adequacy/ISWIM.agda, the
  graph model's adequacy for the ISWIMμ interpreter), used for
  the program and for its simplification:

    ISWIMμ interpreter, M  ⇔  ⟦ M ⟧ ρ₀              (bridge)
                           ⇔  ⟦ simplify M ⟧ ρ₀     (simplify, graph model)
                           ⇔  ISWIMμ interpreter, simplify M   (bridge)
                           ⇔  X86μ interpreter, compile-x86 M  (the other passes, interpreters)

  for constants, and for divergence through the emptiness of the
  denotations. The end theorem is the interpreter column's
  (Mu/proof/Correctness/ClockedInterpreters/CompilerFuel.agda): for a main of type
  Int, the interpreters of ISWIMμ and X86μ stop with the same constant,
  or both diverge.

-}

module Mu.proof.Mixed.CompilerMixed where

open import Framework.Primitives using (Int)
open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.Domain using () renaming (const to dconst)
open import Mu.Semantics.GraphModel.Closed using (ρ₀)
open import Mu.Language.Type using (base)
open import Mu.Language.ISWIM using (Tm)
open import Mu.Semantics.GraphModel.ISWIM using (⟦_⟧)
open import Mu.Compiler.Simplify using (simplify)
open import Mu.Compiler.Enclose using (enclose)
open import Mu.Compiler.Optimize using (optimize-program)
open import Mu.Compiler.Concretize using (concretize-program)
open import Mu.Compiler.Pipeline using (compile₄; compile; compile-mon; compile-imp; compile-cfg; compile-x86)
open import Semantics.Observation
open import proof.Semantics.Interp.Clock
import Mu.Semantics.ClockedInterpreters.ISWIM as ISWIMμᵢ
import Mu.Semantics.ClockedInterpreters.X86 as X86μᵢ

open import Mu.proof.Correctness.GraphModel.SimplifyCorrect using (simplify-correct)
open import Mu.proof.Correctness.ClockedInterpreters.EncloseFuel using (enclose-correct)
open import Mu.proof.Correctness.ClockedInterpreters.OptimizeFuel using (optimize-correct)
open import Mu.proof.Correctness.ClockedInterpreters.ConcretizeFuel using (concretize-correct)
open import Mu.proof.Correctness.ClockedInterpreters.DelayFuel using (delay-correct)
open import Mu.proof.Correctness.ClockedInterpreters.GlobalizeFuel using (globalize-correct)
open import Mu.proof.Correctness.ClockedInterpreters.RCOFuel using (rco-correct)
open import Mu.proof.Correctness.ClockedInterpreters.LiftLocalsFuel using (lift-locals-correct)
open import Mu.proof.Correctness.ClockedInterpreters.ExplicateFuel using (explicate-correct)
open import Mu.proof.Correctness.ClockedInterpreters.SelectFuel using (select-correct)
open import Mu.proof.Adequacy.ISWIM using (const-iff; diverges-iff)

open import Data.Integer using (ℤ)
open import Data.List using ([])
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Nullary using (¬_)

private
  _∘⇔_ : ∀ {A B C : Set} → A ⇔ B → B ⇔ C → A ⇔ C
  (f , g) ∘⇔ (h , k) = (λ a → h (f a)) , (λ c → g (k c))

  ⇔-sym : ∀ {A B : Set} → A ⇔ B → B ⇔ A
  ⇔-sym (f , g) = g , f

{- the passes after simplify, by the interpreters -}
after-simplify : ∀ {A} (M : Tm [] A) → Equivalent (ISWIMμᵢ.sem (simplify M)) (X86μᵢ.sem (compile-x86 M))
after-simplify M =
  equiv-trans (enclose-correct (simplify M)) (equiv-trans (optimize-correct M₁)
    (equiv-trans (concretize-correct M₂) (equiv-trans (delay-correct (concretize-program M₂))
      (equiv-trans (globalize-correct (compile₄ M)) (equiv-trans (rco-correct (compile M))
        (equiv-trans (lift-locals-correct (compile-mon M)) (equiv-trans (explicate-correct (compile-imp M))
          (select-correct (compile-cfg M)))))))))
  where M₁ = enclose (simplify M)
        M₂ = optimize-program M₁

{- for a main of type Int, as the other columns state it -}

compile-x86-const : ∀ (M : Tm [] (base Int)) (k : ℤ)
  → Terminates (ISWIMμᵢ.sem M) (o-const Int k) ⇔ Terminates (X86μᵢ.sem (compile-x86 M)) (o-const Int k)
compile-x86-const M k =
  ⇔-sym (const-iff M) ∘⇔ ((proj₁ S _ , proj₂ S _) ∘⇔ (const-iff (simplify M)
    ∘⇔ Equivalent.terminates (after-simplify M) (o-const Int k)))
  where S = simplify-correct M

compile-x86-diverges : ∀ (M : Tm [] (base Int)) → Diverges (ISWIMμᵢ.sem M) ⇔ Diverges (X86μᵢ.sem (compile-x86 M))
compile-x86-diverges M =
  diverges-iff M ∘⇔ (empty ∘⇔ (⇔-sym (diverges-iff (simplify M)) ∘⇔ Equivalent.diverges (after-simplify M)))
  where
  S = simplify-correct M
  empty : (¬ nonempty (⟦ M ⟧ ρ₀)) ⇔ (¬ nonempty (⟦ simplify M ⟧ ρ₀))
  empty = (λ ne → λ { (d , d∈) → ne (d , proj₂ S d d∈) }) , (λ ne → λ { (d , d∈) → ne (d , proj₁ S d d∈) })

{-

  The compiler (Compiler/Pipeline.agda), observed through the ISWIM
  machine: adequacy for ISWIM (Adequacy/ISWIM.agda) combined with the
  correctness of the compiler in the graph model (CompilerCorrect.agda),
  so that the constants of the compiled Clos5 program are exactly the
  constants the ISWIM machine computes.

-}

module Untyped.proof.Adequacy.ISWIMCompile where

open import Framework.Primitives using (base-rep)
open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.Domain using () renaming (const to dconst)
open import Untyped.Semantics.Graph.Clos5Iswim using (⟦_⟧ₚ)
open import Untyped.proof.Correctness.Graph.CompilerCorrect
  using (compile; compile-correct-const; compile-correct-nonempty)
open import Semantics.Observation
open import proof.Semantics.CEK.Smallstep using (Terminates)
open import Semantics.CEK.ISWIM using (sem)
open import Compiler.CaptureScope using (Closed)
open import proof.Adequacy.ISWIM using (sound-const; sound-nonempty; adequacy-const; adequacy-converges)

open import Data.Product using (proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)

{- the constants of the compiled program are those the ISWIM machine
   computes, and it produces something exactly when the machine
   terminates with an answer -}
compile-correct-machine-const : ∀ M → Closed M → ∀ {B} (k : base-rep B)
  → Terminates (sem M) (o-const B k) ⇔ (dconst k ∈ ⟦ compile M ⟧ₚ)
compile-correct-machine-const M c k =
  ⟨ (λ t → proj₁ (compile-correct-const M k) (sound-const M t))
  , (λ k∈ → adequacy-const M c (proj₂ (compile-correct-const M k) k∈)) ⟩

compile-correct-machine-converges : ∀ M → Closed M
  → Converges (Terminates (sem M)) ⇔ nonempty ⟦ compile M ⟧ₚ
compile-correct-machine-converges M c =
  ⟨ (λ t → proj₁ (compile-correct-nonempty M) (sound-nonempty M t))
  , (λ ne → adequacy-converges M c (proj₂ (compile-correct-nonempty M) ne)) ⟩

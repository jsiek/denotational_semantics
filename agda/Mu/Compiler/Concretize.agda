{-

  Concretize (Clos2μ → Clos3μ), as typed concretize
  (Compiler/Concretize.agda): each closure stores its free variables in
  one tuple, and inside its code the free variable i becomes get i of
  that tuple (variable S Z of the code).

  The pass maps each Clos2μ variable to where it lives in Clos3μ (Ref):
  a variable, or a component of a tuple held in a variable.

-}

module Mu.Compiler.Concretize where

open import Mu.Language.Type
open import Mu.Language.Clos2
import Mu.Language.Clos3 as T
open import Mu.Framework.AllUtil using (All; []; _∷_)

open import Data.List using ([]; _∷_)

data Ref (Γ : Ctx) (A : Type) : Set where
  var : Γ ∋ A → Ref Γ A
  prj : ∀ {Δ} → Δ ∋ A → Γ ∋ tup Δ → Ref Γ A

Refs : Ctx → Ctx → Set
Refs Γ Γ' = ∀ {A} → Γ ∋ A → Ref Γ' A

ref-tm : ∀ {Γ A} → Ref Γ A → T.Tm Γ A
ref-tm (var x) = T.` x
ref-tm (prj i x) = T.get i (T.` x)

shift-ref : ∀ {Γ A B} → Ref Γ A → Ref (B ∷ Γ) A
shift-ref (var x) = var (S x)
shift-ref (prj i x) = prj i (S x)

{- the map for the body of a binder -}
ext-ref : ∀ {Γ Γ' B} → Refs Γ Γ' → Refs (B ∷ Γ) (B ∷ Γ')
ext-ref φ Z = var Z
ext-ref φ (S x) = shift-ref (φ x)

{- the map for the code of a closure with free variables of types Δ -}
fv-ref : ∀ {Δ A} → Refs (A ∷ Δ) (A ∷ tup Δ ∷ [])
fv-ref Z = var Z
fv-ref (S i) = prj i (S Z)

concretize : ∀ {Γ Γ' A} → Refs Γ Γ' → Tm Γ A → T.Tm Γ' A
concs : ∀ {Γ Γ' Δ} → Refs Γ Γ' → All (Tm Γ) Δ → All (T.Tm Γ') Δ

concretize φ (` x) = ref-tm (φ x)
concretize φ (clos N Ms) = T.clos (concretize fv-ref N) (concs φ Ms)
concretize φ (app L M) = T.app (concretize φ L) (concretize φ M)
concretize φ (lit B c) = T.lit B c
concretize φ (tuple Ms) = T.tuple (concs φ Ms)
concretize φ (get i M) = T.get i (concretize φ M)
concretize φ (inl M) = T.inl (concretize φ M)
concretize φ (inr M) = T.inr (concretize φ M)
concretize φ (case L M N) =
  T.case (concretize φ L) (concretize (ext-ref φ) M) (concretize (ext-ref φ) N)
concretize φ (prim p L M) = T.prim p (concretize φ L) (concretize φ M)
concretize φ (let′ M N) = T.let′ (concretize φ M) (concretize (ext-ref φ) N)
concretize φ (fold M) = T.fold (concretize φ M)
concretize φ (unfold M) = T.unfold (concretize φ M)

concs φ [] = []
concs φ (M ∷ Ms) = concretize φ M ∷ concs φ Ms

{- the pass, for a whole program -}
concretize-program : ∀ {A} → Tm [] A → T.Tm [] A
concretize-program = concretize λ ()

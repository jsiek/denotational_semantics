{-

  Typed concretize (Clos2ᵀ → Clos3ᵀ): each closure stores its free
  variables in one tuple, and inside its code the free variable i
  becomes get i of that tuple (variable 1 of the code).

  The pass maps each Clos2ᵀ variable to where it lives in Clos3ᵀ (Ref):
  a variable, or a component of a tuple held in a variable. Since the
  code of a closure is closed in both languages, there is no variable
  past the free variables to account for.

-}

module Compiler.Typed.Concretize where

open import Language.Typed.Type
open import Language.Typed.Clos2
import Language.Typed.Clos3 as T

open import Data.Fin using (Fin; zero; suc)
open import Data.List using ([]; _∷_)
open import Data.Nat using (ℕ; suc)
open import Data.Vec using (Vec; []; _∷_)

data Ref (Γ : Ctx) : Set where
  var : Γ ∋ Any → Ref Γ
  prj : ∀ {n} → Fin n → Γ ∋ ⟪ tup n ⟫ → Ref Γ

ref-tm : ∀ {Γ} → Ref Γ → T.Tm Γ Any
ref-tm (var x) = T.` x
ref-tm (prj i x) = T.get i (T.` x)

shift-ref : ∀ {Γ A} → Ref Γ → Ref (A ∷ Γ)
shift-ref (var x) = var (S x)
shift-ref (prj i x) = prj i (S x)

{- the map for the body of a binder -}
ext-ref : ∀ {k Γ} → (Fin k → Ref Γ) → Fin (suc k) → Ref (Any ∷ Γ)
ext-ref φ zero = var Z
ext-ref φ (suc x) = shift-ref (φ x)

{- the map for the code of a closure with n free variables -}
fv-ref : ∀ {n} → Fin (suc n) → Ref (Any ∷ ⟪ tup n ⟫ ∷ [])
fv-ref zero = var Z
fv-ref (suc i) = prj i (S Z)

concretize : ∀ {k Γ A} → (Fin k → Ref Γ) → Tm k A → T.Tm Γ A
concs : ∀ {k Γ n} → (Fin k → Ref Γ) → Vec (Tm k Any) n → Vec (T.Tm Γ Any) n

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
concretize φ (inject G M) = T.inject G (concretize φ M)
concretize φ (project G M) = T.project G (concretize φ M)

concs φ [] = []
concs φ (M ∷ Ms) = concretize φ M ∷ concs φ Ms

{- the pass, for a whole program -}
concretize-program : ∀ {A} → Tm 0 A → T.Tm [] A
concretize-program = concretize λ ()

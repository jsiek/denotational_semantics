{-

  Explicate control (Impμ → CFGμ), as typed explicate control
  (ISWIM/Compiler/Explicate.agda): explicate-tail e translates e in tail
  position; explicate-assign e x p k translates "slot x := e, then the
  tail k" in continuation-passing style, so a case becomes a case whose
  branches assign the slot and jump to a new block for k, the join
  point. The frame stays as it is: an assignment nested in the
  expression whose value is assigned writes its own slot first, and
  only the slots that k starts with change (p : J ⊆ I ⊕ x).

  Both thread the blocks made so far (newest first, each typed over the
  older ones); a new block's label is the newest index, and a label made
  earlier is weakened (⊑) as more blocks are added.

-}

module FPC.Compiler.Explicate where

open import FPC.Language.Type
open import Framework.Membership using (_⊑_; here⊑; there⊑; ⊑-∋; ⊑-trans)
import FPC.Language.Imp as I
open I using (⊆-refl; ⊆-⊕⊕)
open import FPC.Language.CFG
open import FPC.Framework.AllUtil using (All; []; _∷_) renaming (map to All-map)

open import Data.List using (List; []; _∷_)

{- a tail over the blocks made so far, and more blocks -}
record Out (Σ : List DSig) (R : Type) (Δ : Ctx) (Bs : List (Inits Δ))
  (I : Inits Δ) : Set where
  constructor out
  field
    {Bs'} : List (Inits Δ)
    grows : Bs ⊑ Bs'
    made : Blocks Σ R Δ Bs'
    tail : Tail Σ R Δ Bs' I

after : ∀ {Σ R Δ Bs Bs₁ I}
  → Bs ⊑ Bs₁
  → Out Σ R Δ Bs₁ I
  → Out Σ R Δ Bs I
after g (out g' bs t) = out (⊑-trans g g') bs t

explicate-assign : ∀ {Σ R Δ Bs A} {I J : Inits Δ} → I.Exp Σ Δ I A
  → (x : Δ ∋ A)
  → .(J ⊆ I ⊕ x)
  → Tail Σ R Δ Bs J → Blocks Σ R Δ Bs
  → Out Σ R Δ Bs I
explicate-assign (I.simple s) x p k bs = out here⊑ bs (seq x s p k)
explicate-assign {I = I} {J} (I.assign y _ e₁ e₂) x p k bs
  with explicate-assign e₂ x (⊆-⊕⊕ {I = I} {J} x y p) k bs
... | out g bs₁ t =
  after g (explicate-assign e₁ y (⊆-refl {I = I ⊕ y}) t bs₁)
explicate-assign {I = I} {J} (I.case a y _ z _ e₁ e₂) x p k bs
  with explicate-assign e₁ x (⊆-⊕⊕ {I = I} {J} x y p) (goto Z) (bs ▷ k)
... | out g₁ bs₁ t₁
  with explicate-assign e₂ x (⊆-⊕⊕ {I = I} {J} x z p)
         (goto (⊑-∋ (there⊑ g₁) Z)) (bs₁ ▷ t₁)
...   | out g₂ bs₂ t₂ =
  out (there⊑ (⊑-trans (there⊑ (⊑-trans (there⊑ here⊑) g₁)) g₂)) (bs₂ ▷ t₂)
      (case a y z (⊑-∋ (there⊑ g₂) Z) Z)

explicate-tail : ∀ {Σ R Δ Bs} {I : Inits Δ} → I.Exp Σ Δ I R → Blocks Σ R Δ Bs
  → Out Σ R Δ Bs I
explicate-tail (I.simple s) bs = out here⊑ bs (return s)
explicate-tail {I = I} (I.assign x _ e₁ e₂) bs with explicate-tail e₂ bs
... | out g bs₁ t =
  after g (explicate-assign e₁ x (⊆-refl {I = I ⊕ x}) t bs₁)
explicate-tail (I.case a x _ y _ e₁ e₂) bs with explicate-tail e₁ bs
... | out g₁ bs₁ t₁ with explicate-tail e₂ (bs₁ ▷ t₁)
...   | out g₂ bs₂ t₂ =
  out (there⊑ (⊑-trans (there⊑ g₁) g₂)) (bs₂ ▷ t₂)
    (case a x y (⊑-∋ (there⊑ g₂) Z) Z)

explicate-body : ∀ {Σ R Γ} → I.Body Σ Γ R → Body Σ R Γ
explicate-body (I.body Δ p e) =
  body Δ p (Out.made (explicate-tail e [])) (Out.tail (explicate-tail e []))

{- the pass, for a whole program -}
explicate : ∀ {A} → I.Program A → Program A
explicate (I.program ds e) =
  program (All-map explicate-body ds) (explicate-body e)

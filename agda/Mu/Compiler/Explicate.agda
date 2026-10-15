{-

  Explicate control (Impμ → CFGμ), as typed explicate control
  (Compiler/Explicate.agda): explicate-tail e translates e in tail
  position; explicate-assign e p k translates "slot k := e, then the
  tail k" in continuation-passing style, so a case becomes a case whose
  branches assign the slot and jump to a new block for k, the join
  point.

  Both thread the blocks made so far (newest first, each typed over the
  older ones); a new block's label is the newest index, and a label made
  earlier is weakened (⊑) as more blocks are added.

-}

module Mu.Compiler.Explicate where

open import Mu.Language.Type
open import Framework.Membership using (_⊑_; here⊑; there⊑; ⊑-∋; ⊑-trans)
import Mu.Language.Imp as I
open import Mu.Language.CFG
open import Mu.Framework.AllUtil using (All; []; _∷_) renaming (map to All-map)

open import Data.List using (List; []; _∷_)

{- a tail over the blocks made so far, and more blocks -}
record Out (Σ : List DSig) (R : Type) (Bs : List Ctx) (Δ : Ctx) : Set where
  constructor out
  field
    {Bs'} : List Ctx
    grows : Bs ⊑ Bs'
    made : Blocks Σ R Bs'
    tail : Tail Σ R Bs' Δ

after : ∀ {Σ R Bs Bs₁ Δ} → Bs ⊑ Bs₁ → Out Σ R Bs₁ Δ → Out Σ R Bs Δ
after g (out g' bs t) = out (⊑-trans g g') bs t

explicate-assign : ∀ {Σ R Bs Δ Δ' A} → I.Exp Σ Δ A → Δ' ⊑ Δ → Tail Σ R Bs (A ∷ Δ') → Blocks Σ R Bs
  → Out Σ R Bs Δ
explicate-assign (I.simple s) p k bs = out here⊑ bs (seq p s k)
explicate-assign (I.assign e₁ e₂) p k bs with explicate-assign e₂ (there⊑ p) k bs
... | out g bs₁ t = after g (explicate-assign e₁ here⊑ t bs₁)
explicate-assign (I.case a e₁ e₂) p k bs with explicate-assign e₁ (there⊑ p) (goto Z) (bs ▷ k)
... | out g₁ bs₁ t₁ with explicate-assign e₂ (there⊑ p) (goto (⊑-∋ (there⊑ g₁) Z)) (bs₁ ▷ t₁)
...   | out g₂ bs₂ t₂ =
  out (there⊑ (⊑-trans (there⊑ (⊑-trans (there⊑ here⊑) g₁)) g₂)) (bs₂ ▷ t₂)
      (case a here⊑ (⊑-∋ (there⊑ g₂) Z) Z)

explicate-tail : ∀ {Σ R Bs Δ} → I.Exp Σ Δ R → Blocks Σ R Bs → Out Σ R Bs Δ
explicate-tail (I.simple s) bs = out here⊑ bs (return s)
explicate-tail (I.assign e₁ e₂) bs with explicate-tail e₂ bs
... | out g bs₁ t = after g (explicate-assign e₁ here⊑ t bs₁)
explicate-tail (I.case a e₁ e₂) bs with explicate-tail e₁ bs
... | out g₁ bs₁ t₁ with explicate-tail e₂ (bs₁ ▷ t₁)
...   | out g₂ bs₂ t₂ =
  out (there⊑ (⊑-trans (there⊑ g₁) g₂)) (bs₂ ▷ t₂) (case a here⊑ (⊑-∋ (there⊑ g₂) Z) Z)

explicate-body : ∀ {Σ R Δ} → I.Exp Σ Δ R → Body Σ R Δ
explicate-body e with explicate-tail e []
... | out _ bs t = body bs t

{- the pass, for a whole program -}
explicate : ∀ {A} → I.Program A → Program A
explicate (I.program ds e) = program (All-map explicate-body ds) (explicate-body e)

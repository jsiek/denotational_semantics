{-

  Scott domains: comparing strictness guards (for the proofs of
  prune and concretize, Mu/proof/Correctness/ScottDomains/). guard n ds e
  and seq d e are ⊥ unless their guards are defined, so they are below
  any value that e is below when the guards are defined (guard-below).
  Hence two guards whose conditions hold together are equal when their
  bodies are equal under the conditions (guard-iff); in particular a
  guard on n values is a seq on their tuple (guard-seq).

-}

open import MLTT.Spartan hiding (inl; inr; cases)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons

open import Data.Fin using (Fin; zero; suc)

module Mu.proof.Semantics.ScottDomains.PruneLemmas
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : propext 𝓤₀)
       where

open import Framework.Scott.Base pt fe
open import proof.Framework.Scott.Ops pt fe pe

All-defined : (n : ℕ) → (Fin n → ⟨ 𝔻 ⟩) → 𝓤₀ ̇
All-defined n ds = (i : Fin n) → defined (ds i)

seq-below : (d e u : ⟨ 𝔻 ⟩) → (defined d → e ⊑⟨ 𝔻 ⟩ u) → seq · d · e ⊑⟨ 𝔻 ⟩ u
seq-below d e u h = ∐ˢˢ-is-lowerbound-of-upperbounds 𝔻⊥ (λ _ → e) (defined-is-prop d) u h

guard-below : (n : ℕ) (ds : Fin n → ⟨ 𝔻 ⟩) (e u : ⟨ 𝔻 ⟩) → (All-defined n ds → e ⊑⟨ 𝔻 ⟩ u)
  → guard n · ds · e ⊑⟨ 𝔻 ⟩ u
guard-below zero ds e u h = h (λ ())
guard-below (succ n) ds e u h =
 seq-below (ds zero) (guard n · (λ i → ds (suc i)) · e) u
   (λ p → guard-below n (λ i → ds (suc i)) e u (λ hs → h (λ { zero → p ; (suc i) → hs i })))

private
 ＝⊑ : (x y : ⟨ 𝔻 ⟩) → x ＝ y → x ⊑⟨ 𝔻 ⟩ y
 ＝⊑ x y q = transport (λ - → x ⊑⟨ 𝔻 ⟩ -) q (reflexivity 𝔻 x)

{- two guards whose conditions hold together -}
guard-iff : (n m : ℕ) (ds : Fin n → ⟨ 𝔻 ⟩) (es : Fin m → ⟨ 𝔻 ⟩) (e e' : ⟨ 𝔻 ⟩)
  → (All-defined n ds → All-defined m es) → (All-defined m es → All-defined n ds)
  → (All-defined n ds → e ＝ e') → guard n · ds · e ＝ guard m · es · e'
guard-iff n m ds es e e' f g h =
 antisymmetry 𝔻 (guard n · ds · e) (guard m · es · e')
   (guard-below n ds e (guard m · es · e')
      (λ p → ＝⊑ e (guard m · es · e') (h p ∙ guard-defined m es (f p) e' ⁻¹)))
   (guard-below m es e' (guard n · ds · e)
      (λ q → ＝⊑ e' (guard n · ds · e) (h (g q) ⁻¹ ∙ guard-defined n ds (g q) e ⁻¹)))

{- a guard on n values is a seq on their tuple -}
guard-seq : (n : ℕ) (ds : Fin n → ⟨ 𝔻 ⟩) (e e' : ⟨ 𝔻 ⟩)
  → (All-defined n ds → e ＝ e') → guard n · ds · e ＝ seq · (tuple n · ds) · e'
guard-seq n ds e e' h =
 antisymmetry 𝔻 (guard n · ds · e) (seq · t · e')
   (guard-below n ds e (seq · t · e')
      (λ p → ＝⊑ e (seq · t · e') (h p ∙ seq-defined t e' (tuple-defined n ds p) ⁻¹)))
   (seq-below t e' (guard n · ds · e)
      (λ q → ＝⊑ e' (guard n · ds · e)
               (h (tuple-defined← n ds q) ⁻¹ ∙ guard-defined n ds (tuple-defined← n ds q) e ⁻¹)))
 where
  t = tuple n · ds

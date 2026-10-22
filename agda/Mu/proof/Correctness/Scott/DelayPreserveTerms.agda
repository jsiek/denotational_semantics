{-

  Correctness of delay (Clos3μ → Clos4μ) in Scott domains, the forward
  half on terms: the meaning of a term and of its translation are
  related by Pres (Mu/proof/Correctness/Scott/DelayPreserve.agda) when
  their environments are, by induction on the term. Each construct is
  one lemma of DelayPreserve.agda: a closure is Pres-clos, an
  application Pres-call, and the others are the same operator on both
  sides.

-}

open import MLTT.Spartan hiding (inl; inr; cases; _+_)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons
open import UF.Base using (transport₂)

open import Mu.Language.Type
open import Mu.Language.Clos3
import Mu.Language.Clos4 as T
open import Mu.Compiler.Delay
open import Mu.Framework.AllUtil using (All; []; _∷_; pos)
open import Framework.abt.GSubst using (_•_)
open import Data.List using (List; []; _∷_; length)
open import Data.Fin using (Fin; zero; suc)

module Mu.proof.Correctness.Scott.DelayPreserveTerms
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : propext 𝓤₀)
       where

open import Framework.Scott.Base pt fe
open import proof.Framework.Scott.Ops pt fe pe
  hiding (ext) renaming (app to appᵈ; inl to inlᵈ; inr to inrᵈ; tuple to tupleᵈ; pair to pairᵈ)
open import proof.Framework.Scott.Semantics pt fe pe
open import Semantics.Scott.Prim pt fe pe using (primD)
open import Mu.proof.Correctness.Scott.DelayPreserve pt fe pe
  using (Pres; Pres-clos; Pres-call; Pres-const; Pres-tuple; Pres-proj; Pres-inl; Pres-inr; Pres-case; Pres-prim; Pres-seq)
open import Mu.Semantics.Scott.Clos3 pt fe pe renaming (⟦_⟧ to ⟦_⟧₃; ⟦_⟧s to ⟦_⟧s₃)
open import Mu.Semantics.Scott.Clos4 pt fe pe renaming (⟦_⟧ to ⟦_⟧₄; ⟦_⟧s to ⟦_⟧s₄)

{- the environments are related through the renaming -}
PresEnv : ∀ {Γ Δ} → Ren Γ Δ → ⟨ Env ⟩ → ⟨ Env ⟩ → 𝓤₁ ̇
PresEnv {Γ} r ρ ρ' = ∀ {C} (x : Γ ∋ C) → Pres (ρ (idx x)) (ρ' (idx (r x)))

ext-env : ∀ {Γ Δ B} (r : Ren Γ Δ) {ρ ρ' : ⟨ Env ⟩} (a a' : ⟨ 𝔻 ⟩) → Pres a a' → PresEnv r ρ ρ'
  → PresEnv (ext {B = B} r) (a • ρ) (a' • ρ')
ext-env r a a' ha h Z = ha
ext-env r a a' ha h (S x) = h x

code-env : ∀ {Δ A} (X X' Y Y' : ⟨ 𝔻 ⟩) → Pres X X' → Pres Y Y'
  → PresEnv {A ∷ tup Δ ∷ []} (λ x → x) (env₂ X Y) (env₂ X' Y')
code-env X X' Y Y' hX hY Z = hY
code-env X X' Y Y' hX hY (S Z) = hX

pres : ∀ {Γ Δ A} (M : Tm Γ A) (r : Ren Γ Δ) {ρ ρ' : ⟨ Env ⟩} → PresEnv r ρ ρ'
  → Pres (⟦ M ⟧₃ · ρ) (⟦ delay r M ⟧₄ · ρ')
pres-s : ∀ {Γ Δ Δ'} (Ms : All (Tm Γ) Δ') (r : Ren Γ Δ) {ρ ρ' : ⟨ Env ⟩} → PresEnv r ρ ρ'
  → (i : Fin (length Δ')) → Pres ((⟦ Ms ⟧s₃ · ρ) i) ((⟦ delays r Ms ⟧s₄ · ρ') i)

pres (` x) r h = h x
pres (clos {Δ} N Ms) r {ρ} {ρ'} h =
  Pres-clos ⟦ N ⟧₃ ⟦ delay (λ x → x) N ⟧₄ (tupleᵈ (length Δ) · (⟦ Ms ⟧s₃ · ρ)) (tupleᵈ (length Δ) · (⟦ delays r Ms ⟧s₄ · ρ'))
    (Pres-tuple (length Δ) (⟦ Ms ⟧s₃ · ρ) (⟦ delays r Ms ⟧s₄ · ρ') (pres-s Ms r h))
    (λ X X' Y Y' hX hY → pres N (λ x → x) (code-env X X' Y Y' hX hY))
pres (app L M) r {ρ} {ρ'} h =
  Pres-call (⟦ L ⟧₃ · ρ) (⟦ delay r L ⟧₄ · ρ') (⟦ M ⟧₃ · ρ) (⟦ delay r M ⟧₄ · ρ') (pres L r h) (pres M r h)
pres (lit B c) r h = Pres-const B c
pres (tuple {Δ} Ms) r {ρ} {ρ'} h = Pres-tuple (length Δ) (⟦ Ms ⟧s₃ · ρ) (⟦ delays r Ms ⟧s₄ · ρ') (pres-s Ms r h)
pres (get i M) r {ρ} {ρ'} h = Pres-proj (pos i) (⟦ M ⟧₃ · ρ) (⟦ delay r M ⟧₄ · ρ') (pres M r h)
pres (inl M) r {ρ} {ρ'} h = Pres-inl (⟦ M ⟧₃ · ρ) (⟦ delay r M ⟧₄ · ρ') (pres M r h)
pres (inr M) r {ρ} {ρ'} h = Pres-inr (⟦ M ⟧₃ · ρ) (⟦ delay r M ⟧₄ · ρ') (pres M r h)
pres (case L M N) r {ρ} {ρ'} h =
  Pres-case (⟦ L ⟧₃ · ρ) (⟦ delay r L ⟧₄ · ρ')
    (abs ⟦ M ⟧₃ · ρ) (abs ⟦ N ⟧₃ · ρ) (abs ⟦ delay (ext r) M ⟧₄ · ρ') (abs ⟦ delay (ext r) N ⟧₄ · ρ')
    (pres L r h)
    (λ a a' ha → pres M (ext r) (ext-env r a a' ha h))
    (λ a a' ha → pres N (ext r) (ext-env r a a' ha h))
pres (prim p L M) r {ρ} {ρ'} h =
  Pres-prim p (⟦ L ⟧₃ · ρ) (⟦ delay r L ⟧₄ · ρ') (⟦ M ⟧₃ · ρ) (⟦ delay r M ⟧₄ · ρ') (pres L r h) (pres M r h)
pres (let′ M N) r {ρ} {ρ'} h =
  transport₂ Pres (letᶜ-β ⟦ M ⟧₃ ⟦ N ⟧₃ ρ ⁻¹) (letᶜ-β ⟦ delay r M ⟧₄ ⟦ delay (ext r) N ⟧₄ ρ' ⁻¹)
    (Pres-seq (⟦ M ⟧₃ · ρ) (⟦ delay r M ⟧₄ · ρ') (⟦ N ⟧₃ · ((⟦ M ⟧₃ · ρ) • ρ)) (⟦ delay (ext r) N ⟧₄ · ((⟦ delay r M ⟧₄ · ρ') • ρ'))
       (pres M r h) (pres N (ext r) (ext-env r (⟦ M ⟧₃ · ρ) (⟦ delay r M ⟧₄ · ρ') (pres M r h) h)))
pres (fold M) r h = pres M r h
pres (unfold M) r h = pres M r h

pres-s (M ∷ Ms) r h zero = pres M r h
pres-s (M ∷ Ms) r h (suc i) = pres-s Ms r h i

{- the meaning of a program and of its translation are related -}
delay-pres : ∀ {A} (M : Tm [] A) → Pres (⟦ M ⟧₃ · ρ₀) (⟦ delay-program M ⟧₄ · ρ₀)
delay-pres M = pres M (λ ()) (λ ())

{-

  Correctness of delay (Clos3μ → Clos4μ) in Scott domains, the backward
  half on terms: the meaning of a term and of its translation are
  related by Refl (Mu/proof/Correctness/Scott/DelayReflect.agda) when
  their environments are, by induction on the term, as for the forward
  half (DelayPreserveTerms.agda): each construct is one lemma of
  DelayReflect.agda.

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

module Mu.proof.Correctness.Scott.DelayReflectTerms
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : propext 𝓤₀)
       where

open import Framework.Scott.Base pt fe
open import proof.Framework.Scott.Ops pt fe pe
  hiding (ext) renaming (app to appᵈ; inl to inlᵈ; inr to inrᵈ; tuple to tupleᵈ; pair to pairᵈ)
open import proof.Framework.Scott.Semantics pt fe pe
open import Semantics.Scott.Prim pt fe pe using (primD)
open import Mu.proof.Correctness.Scott.DelayReflect pt fe pe using (Refl)
open import Mu.proof.Correctness.Scott.DelayReflectOps pt fe pe
  using (Refl-clos; Refl-call; Refl-const; Refl-tuple; Refl-proj; Refl-inl; Refl-inr; Refl-case; Refl-prim; Refl-seq)
open import Mu.Semantics.Scott.Clos3 pt fe pe renaming (⟦_⟧ to ⟦_⟧₃; ⟦_⟧s to ⟦_⟧s₃)
open import Mu.Semantics.Scott.Clos4 pt fe pe renaming (⟦_⟧ to ⟦_⟧₄; ⟦_⟧s to ⟦_⟧s₄)

{- the environments are related through the renaming -}
ReflEnv : ∀ {Γ Δ} → Ren Γ Δ → ⟨ Env ⟩ → ⟨ Env ⟩ → 𝓤₁ ̇
ReflEnv {Γ} r ρ ρ' = ∀ {C} (x : Γ ∋ C) → Refl (ρ (idx x)) (ρ' (idx (r x)))

ext-env : ∀ {Γ Δ B} (r : Ren Γ Δ) {ρ ρ' : ⟨ Env ⟩} (a a' : ⟨ 𝔻 ⟩) → Refl a a' → ReflEnv r ρ ρ'
  → ReflEnv (ext {B = B} r) (a • ρ) (a' • ρ')
ext-env r a a' ha h Z = ha
ext-env r a a' ha h (S x) = h x

code-env : ∀ {Δ A} (X X' Y Y' : ⟨ 𝔻 ⟩) → Refl X X' → Refl Y Y'
  → ReflEnv {A ∷ tup Δ ∷ []} (λ x → x) (env₂ X Y) (env₂ X' Y')
code-env X X' Y Y' hX hY Z = hY
code-env X X' Y Y' hX hY (S Z) = hX

refl-ok : ∀ {Γ Δ A} (M : Tm Γ A) (r : Ren Γ Δ) {ρ ρ' : ⟨ Env ⟩} → ReflEnv r ρ ρ'
  → Refl (⟦ M ⟧₃ · ρ) (⟦ delay r M ⟧₄ · ρ')
refl-ok-s : ∀ {Γ Δ Δ'} (Ms : All (Tm Γ) Δ') (r : Ren Γ Δ) {ρ ρ' : ⟨ Env ⟩} → ReflEnv r ρ ρ'
  → (i : Fin (length Δ')) → Refl ((⟦ Ms ⟧s₃ · ρ) i) ((⟦ delays r Ms ⟧s₄ · ρ') i)

refl-ok (` x) r h = h x
refl-ok (clos {Δ} N Ms) r {ρ} {ρ'} h =
  Refl-clos ⟦ N ⟧₃ ⟦ delay (λ x → x) N ⟧₄ (tupleᵈ (length Δ) · (⟦ Ms ⟧s₃ · ρ)) (tupleᵈ (length Δ) · (⟦ delays r Ms ⟧s₄ · ρ'))
    (Refl-tuple (length Δ) (⟦ Ms ⟧s₃ · ρ) (⟦ delays r Ms ⟧s₄ · ρ') (refl-ok-s Ms r h))
    (λ X X' Y Y' hX hY → refl-ok N (λ x → x) (code-env X X' Y Y' hX hY))
refl-ok (app L M) r {ρ} {ρ'} h =
  Refl-call (⟦ L ⟧₃ · ρ) (⟦ delay r L ⟧₄ · ρ') (⟦ M ⟧₃ · ρ) (⟦ delay r M ⟧₄ · ρ') (refl-ok L r h) (refl-ok M r h)
refl-ok (lit B c) r h = Refl-const B c
refl-ok (tuple {Δ} Ms) r {ρ} {ρ'} h = Refl-tuple (length Δ) (⟦ Ms ⟧s₃ · ρ) (⟦ delays r Ms ⟧s₄ · ρ') (refl-ok-s Ms r h)
refl-ok (get i M) r {ρ} {ρ'} h = Refl-proj (pos i) (⟦ M ⟧₃ · ρ) (⟦ delay r M ⟧₄ · ρ') (refl-ok M r h)
refl-ok (inl M) r {ρ} {ρ'} h = Refl-inl (⟦ M ⟧₃ · ρ) (⟦ delay r M ⟧₄ · ρ') (refl-ok M r h)
refl-ok (inr M) r {ρ} {ρ'} h = Refl-inr (⟦ M ⟧₃ · ρ) (⟦ delay r M ⟧₄ · ρ') (refl-ok M r h)
refl-ok (case L M N) r {ρ} {ρ'} h =
  Refl-case (⟦ L ⟧₃ · ρ) (⟦ delay r L ⟧₄ · ρ')
    (abs ⟦ M ⟧₃ · ρ) (abs ⟦ N ⟧₃ · ρ) (abs ⟦ delay (ext r) M ⟧₄ · ρ') (abs ⟦ delay (ext r) N ⟧₄ · ρ')
    (refl-ok L r h)
    (λ a a' ha → refl-ok M (ext r) (ext-env r a a' ha h))
    (λ a a' ha → refl-ok N (ext r) (ext-env r a a' ha h))
refl-ok (prim p L M) r {ρ} {ρ'} h =
  Refl-prim p (⟦ L ⟧₃ · ρ) (⟦ delay r L ⟧₄ · ρ') (⟦ M ⟧₃ · ρ) (⟦ delay r M ⟧₄ · ρ') (refl-ok L r h) (refl-ok M r h)
refl-ok (let′ M N) r {ρ} {ρ'} h =
  transport₂ Refl (letᶜ-β ⟦ M ⟧₃ ⟦ N ⟧₃ ρ ⁻¹) (letᶜ-β ⟦ delay r M ⟧₄ ⟦ delay (ext r) N ⟧₄ ρ' ⁻¹)
    (Refl-seq (⟦ M ⟧₃ · ρ) (⟦ delay r M ⟧₄ · ρ') (⟦ N ⟧₃ · ((⟦ M ⟧₃ · ρ) • ρ)) (⟦ delay (ext r) N ⟧₄ · ((⟦ delay r M ⟧₄ · ρ') • ρ'))
       (refl-ok M r h) (refl-ok N (ext r) (ext-env r (⟦ M ⟧₃ · ρ) (⟦ delay r M ⟧₄ · ρ') (refl-ok M r h) h)))
refl-ok (fold M) r h = refl-ok M r h
refl-ok (unfold M) r h = refl-ok M r h

refl-ok-s (M ∷ Ms) r h zero = refl-ok M r h
refl-ok-s (M ∷ Ms) r h (suc i) = refl-ok-s Ms r h i

{- the meaning of a program and of its translation are related -}
delay-refl : ∀ {A} (M : Tm [] A) → Refl (⟦ M ⟧₃ · ρ₀) (⟦ delay-program M ⟧₄ · ρ₀)
delay-refl M = refl-ok M (λ ()) (λ ())

{-

  Correctness of delay (Clos3μ → Clos4μ) in Scott domains: the
  fundamental lemma of each half, by induction on terms. The two are
  the same induction, over a relation S between source and target
  values that the operators preserve (module Terms); it is instantiated
  with Pres (DelayPreserve.agda) and Refl (DelayReflect.agda).

-}

open import MLTT.Spartan hiding (inl; inr; cases; _+_)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons
open import UF.Base using (transport₂)

open import Framework.Primitives using (Base; base-rep)
open import Language.Prim using (Prim)
open import Mu.Language.Type
open import Mu.Language.Clos3
open import Mu.Compiler.Delay
open import Mu.Framework.AllUtil using (All; []; _∷_; pos)
open import Framework.abt.GSubst using (_•_)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_; length)

module Mu.proof.Correctness.Scott.DelayTerms
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : propext 𝓤₀)
       where

open import Framework.Scott.Base pt fe
open import proof.Framework.Scott.Ops pt fe pe
  hiding (ext) renaming (app to appᵈ; inl to inlᵈ; inr to inrᵈ; tuple to tupleᵈ; pair to pairᵈ)
open import proof.Framework.Scott.Semantics pt fe pe
open import Semantics.Scott.Prim pt fe pe using (primD)
open import Mu.Semantics.Scott.Clos3 pt fe pe renaming (⟦_⟧ to ⟦_⟧₃; ⟦_⟧s to ⟦_⟧s₃)
open import Mu.Semantics.Scott.Clos4 pt fe pe renaming (⟦_⟧ to ⟦_⟧₄; ⟦_⟧s to ⟦_⟧s₄)
open import Mu.proof.Correctness.Scott.DelayRel pt fe pe
open import Mu.proof.Correctness.Scott.DelayPreserve pt fe pe using (Pres; Pres-clos; Pres-call)
open import Mu.proof.Correctness.Scott.DelayReflect pt fe pe using (Refl; Refl-clos; Refl-call)

module Terms (_∼_ : ⟨ 𝔻 ⟩ → ⟨ 𝔻 ⟩ → 𝓤₁ ̇)
  (S-clos : (B B' : Den Env) {t t' : ⟨ 𝔻 ⟩} → t ∼ t' → (∀ {X X' Y Y'} → X ∼ X' → Y ∼ Y' → B · env₂ X Y ∼ B' · env₂ X' Y')
    → appᵈ · codeᶜ B · t ∼ pairᵈ · codeᶜ B' · t')
  (S-call : ∀ {l l' a a'} → l ∼ l' → a ∼ a' → appᵈ · l · a ∼ (appᵈ · (appᵈ · (car · l') · (cdr · l')) · a'))
  (S-const : (B : Base) (c : base-rep B) → const B c ∼ const B c)
  (S-tuple : (k : ℕ) {ds ds' : Fin k → ⟨ 𝔻 ⟩} → ((i : Fin k) → ds i ∼ ds' i) → tupleᵈ k · ds ∼ tupleᵈ k · ds')
  (S-proj : ∀ {k} (i : Fin k) {d d'} → d ∼ d' → proj i · d ∼ proj i · d')
  (S-inl : ∀ {d d'} → d ∼ d' → inlᵈ · d ∼ inlᵈ · d')
  (S-inr : ∀ {d d'} → d ∼ d' → inrᵈ · d ∼ inrᵈ · d')
  (S-case : ∀ {d d'} (f g f' g' : DCPO[ 𝔻 , 𝔻 ]) → d ∼ d' → (∀ {a a'} → a ∼ a' → f · a ∼ f' · a')
    → (∀ {a a'} → a ∼ a' → g · a ∼ g' · a') → (cases · d · (strict · f , strict · g)) ∼ (cases · d' · (strict · f' , strict · g')))
  (S-prim : (p : Prim) {d d' e e' : ⟨ 𝔻 ⟩} → d ∼ d' → e ∼ e' → primD p · d · e ∼ primD p · d' · e')
  (S-seq : ∀ {d d' e e'} → d ∼ d' → e ∼ e' → seq · d · e ∼ seq · d' · e')
  where

  {- the environments are related through the renaming -}
  SEnv : ∀ {Γ Δ} → Ren Γ Δ → ⟨ Env ⟩ → ⟨ Env ⟩ → 𝓤₁ ̇
  SEnv {Γ} r ρ ρ' = ∀ {C} (x : Γ ∋ C) → (ρ (idx x)) ∼ (ρ' (idx (r x)))

  ext-env : ∀ {Γ Δ B} (r : Ren Γ Δ) {ρ ρ' : ⟨ Env ⟩} {a a' : ⟨ 𝔻 ⟩} → a ∼ a' → SEnv r ρ ρ' → SEnv (ext {B = B} r) (a • ρ) (a' • ρ')
  ext-env r ha h Z = ha
  ext-env r ha h (S x) = h x

  ok : ∀ {Γ Δ A} (M : Tm Γ A) (r : Ren Γ Δ) {ρ ρ' : ⟨ Env ⟩} → SEnv r ρ ρ' → ⟦ M ⟧₃ · ρ ∼ ⟦ delay r M ⟧₄ · ρ'
  oks : ∀ {Γ Δ Δ'} (Ms : All (Tm Γ) Δ') (r : Ren Γ Δ) {ρ ρ' : ⟨ Env ⟩} → SEnv r ρ ρ'
    → (i : Fin (length Δ')) → ((⟦ Ms ⟧s₃ · ρ) i) ∼ ((⟦ delays r Ms ⟧s₄ · ρ') i)

  ok (` x) r h = h x
  ok (clos {Δ} N Ms) r h =
    S-clos ⟦ N ⟧₃ ⟦ delay (λ x → x) N ⟧₄ (S-tuple (length Δ) (oks Ms r h)) λ hX hY → ok N (λ x → x) λ { Z → hY ; (S Z) → hX }
  ok (app L M) r h = S-call (ok L r h) (ok M r h)
  ok (lit B c) r h = S-const B c
  ok (tuple {Δ} Ms) r h = S-tuple (length Δ) (oks Ms r h)
  ok (get i M) r h = S-proj (pos i) (ok M r h)
  ok (inl M) r h = S-inl (ok M r h)
  ok (inr M) r h = S-inr (ok M r h)
  ok (case L M N) r {ρ} {ρ'} h =
    S-case (abs ⟦ M ⟧₃ · ρ) (abs ⟦ N ⟧₃ · ρ) (abs ⟦ delay (ext r) M ⟧₄ · ρ') (abs ⟦ delay (ext r) N ⟧₄ · ρ')
      (ok L r h) (λ ha → ok M (ext r) (ext-env r ha h)) (λ ha → ok N (ext r) (ext-env r ha h))
  ok (prim p L M) r h = S-prim p (ok L r h) (ok M r h)
  ok (let′ M N) r {ρ} {ρ'} h =
    transport₂ _∼_ (letᶜ-β ⟦ M ⟧₃ ⟦ N ⟧₃ ρ ⁻¹) (letᶜ-β ⟦ delay r M ⟧₄ ⟦ delay (ext r) N ⟧₄ ρ' ⁻¹)
      (S-seq (ok M r h) (ok N (ext r) (ext-env r (ok M r h) h)))
  ok (fold M) r h = ok M r h
  ok (unfold M) r h = ok M r h

  oks (M ∷ Ms) r h zero = ok M r h
  oks (M ∷ Ms) r h (suc i) = oks Ms r h i

  {- the meaning of a program and of its translation are related -}
  delay-ok : ∀ {A} (M : Tm [] A) → ⟦ M ⟧₃ · ρ₀ ∼ ⟦ delay-program M ⟧₄ · ρ₀
  delay-ok M = ok M (λ ()) (λ ())

open Terms Pres Pres-clos Pres-call Rel-const Rel-tuple Rel-proj Rel-inl Rel-inr Rel-case Rel-prim Rel-seq
  using () renaming (delay-ok to delay-pres) public
open Terms Refl Refl-clos Refl-call Rel-const (λ k h → Rel-tuple k h) (λ i h → Rel-proj i h) (λ h → Rel-inl h) (λ h → Rel-inr h)
  (λ f g f' g' h hf hg → Rel-case f' g' f g h (λ {a} {a'} r → hf {a'} {a} r) (λ {a} {a'} r → hg {a'} {a} r))
  (λ p h h' → Rel-prim p h h') (λ h h' → Rel-seq h h')
  using () renaming (delay-ok to delay-refl) public

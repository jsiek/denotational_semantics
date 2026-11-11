{-

  This module proves the fundamental lemma for the split closure pass
  (EnvClosμ to PairClosμ) in Scott domains. The lemma says that if the
  source and target environments are related, then the meaning of a
  term and the meaning of its translation are related. The proof is by
  induction on the term.

  The correctness proof of split has two halves, and each half needs
  the fundamental lemma for its own relation. The forward half
  (preservation) uses the relation Pres of SplitPreserve.agda, and the
  backward half (reflection) uses the relation Refl of
  SplitReflect.agda. The two inductions are the same except for the
  relation. So the module Terms below does the induction once, for an
  arbitrary relation, and the end of this file instantiates it twice.
  The two instances give split-pres and split-refl, which
  SplitCorrect.agda uses to prove that split is correct.

-}

open import MLTT.Spartan hiding (inl; inr; cases; _+_)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons
open import UF.Base using (transport₂)

open import Framework.Primitives using (Base; base-rep)
open import Language.Prim using (Prim)
open import FPC.Language.Type
open import FPC.Language.EnvClos
open import FPC.Compiler.Split
open import FPC.Framework.AllUtil using (All; []; _∷_; pos)
open import Framework.abt.GSubst using (_•_)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_; length)

module FPC.proof.Correctness.ScottDomains.SplitTerms
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : propext 𝓤₀)
       where

open import Framework.Scott.Base pt fe
open import proof.Framework.Scott.Ops pt fe pe hiding (ext) renaming (app to
  appᵈ; inl to inlᵈ; inr to inrᵈ; tuple to tupleᵈ; pair to pairᵈ)
open import proof.Framework.Scott.Semantics pt fe pe
open import Semantics.Scott.Prim pt fe pe using (primD)
open import FPC.Semantics.ScottDomains.EnvClos pt fe pe renaming (⟦_⟧ to ⟦_⟧₃;
  ⟦_⟧s to ⟦_⟧s₃)
open import FPC.Semantics.ScottDomains.PairClos pt fe pe renaming (⟦_⟧ to ⟦_⟧₄;
  ⟦_⟧s to ⟦_⟧s₄)
open import FPC.proof.Correctness.ScottDomains.SplitRel pt fe pe
open import FPC.proof.Correctness.ScottDomains.SplitPreserve pt fe pe using
  (Pres; Pres-clos; Pres-call)
open import FPC.proof.Correctness.ScottDomains.SplitReflect pt fe pe using
  (Refl; Refl-clos; Refl-call)

{- Terms is a parameterized module so that one induction on terms can
   serve both halves of the correctness proof. The forward half needs
   the fundamental lemma for Pres, and the backward half needs it for
   Refl. The induction is the same for both relations, because it
   relies only on the fact that each operator takes related arguments
   to related results. So Terms abstracts over the relation _∼_ and
   over exactly those facts, and the end of this file instantiates it
   once with Pres and once with Refl.

   The facts are one hypothesis for each construct of EnvClosμ other
   than variables, fold, and unfold. The case of a variable uses the
   hypothesis that the environments are related, and fold and unfold
   mean the identity in both languages, so these three constructs need
   no hypothesis. Only two hypotheses, S-clos and S-call, are about
   constructs that split changes, and these are proved separately for
   each relation (SplitPreserve.agda and SplitReflect.agda). The other
   eight are about constructs whose source and target operators are the
   same: constants, tuples, projections, the two injections, case,
   primitives, and seq, which let uses. For both relations, the lemmas
   Rel-const, ..., Rel-seq of SplitRel.agda prove them. The backward
   instance adapts these lemmas, because Pres s t is Rel preserve s t,
   with the source value first, while Refl s t is Rel reflect t s, with
   the target value first. -}

module Terms (_∼_ : ⟨ 𝔻 ⟩ → ⟨ 𝔻 ⟩ → 𝓤₁ ̇)
  (S-clos : (B B' : Den Env) {t t' : ⟨ 𝔻 ⟩} → t ∼ t'
      → (∀ {X X' Y Y'} → X ∼ X' → Y ∼ Y' → B · env₂ X Y ∼ B' · env₂ X' Y')
    → appᵈ · codeᶜ B · t ∼ pairᵈ · codeᶜ B' · t')
  (S-call : ∀ {l l' a a'} → l ∼ l' → a ∼ a'
      → appᵈ · l · a ∼ (appᵈ · (appᵈ · (car · l') · (cdr · l')) · a'))
  (S-const : (B : Base) (c : base-rep B) → const B c ∼ const B c)
  (S-tuple : (k : ℕ) {ds ds' : Fin k → ⟨ 𝔻 ⟩} → ((i : Fin k) → ds i ∼ ds' i)
      → tupleᵈ k · ds ∼ tupleᵈ k · ds')
  (S-proj : ∀ {k} (i : Fin k) {d d'} → d ∼ d' → proj i · d ∼ proj i · d')
  (S-inl : ∀ {d d'} → d ∼ d' → inlᵈ · d ∼ inlᵈ · d')
  (S-inr : ∀ {d d'} → d ∼ d' → inrᵈ · d ∼ inrᵈ · d')
  (S-case : ∀ {d d'} (f g f' g' : DCPO[ 𝔻 , 𝔻 ]) → d ∼ d'
      → (∀ {a a'} → a ∼ a' → f · a ∼ f' · a')
    → (∀ {a a'} → a ∼ a' → g · a ∼ g' · a')
      → (cases · d · (strict · f , strict · g))
      ∼ (cases · d' · (strict · f' , strict · g')))
  (S-prim : (p : Prim) {d d' e e' : ⟨ 𝔻 ⟩} → d ∼ d' → e ∼ e'
      → primD p · d · e ∼ primD p · d' · e')
  (S-seq : ∀ {d d' e e'} → d ∼ d' → e ∼ e' → seq · d · e ∼ seq · d' · e')
  where

  {- SEnv ρ ρ' says that the source environment ρ and the target
     environment ρ' are related at every variable of Γ. -}
  SEnv : ∀ {Γ : Ctx} → ⟨ Env ⟩ → ⟨ Env ⟩ → 𝓤₁ ̇
  SEnv {Γ} ρ ρ' = ∀ {C} (x : Γ ∋ C) → (ρ (idx x)) ∼ (ρ' (idx x))

  ext-env : ∀ {Γ B} {ρ ρ' : ⟨ Env ⟩} {a a' : ⟨ 𝔻 ⟩}
    → a ∼ a'
    → SEnv {Γ} ρ ρ'
    → SEnv {B ∷ Γ} (a • ρ) (a' • ρ')
  ext-env ha h Z = ha
  ext-env ha h (S x) = h x

  {- The fundamental lemma. If the environments are related, then the
     meaning of M and the meaning of its translation are related. -}
  ok : ∀ {Γ A} (M : Tm Γ A) {ρ ρ' : ⟨ Env ⟩}
    → SEnv {Γ} ρ ρ'
    → ⟦ M ⟧₃ · ρ ∼ ⟦ split M ⟧₄ · ρ'
  oks : ∀ {Γ Δ} (Ms : All (Tm Γ) Δ) {ρ ρ' : ⟨ Env ⟩}
    → SEnv {Γ} ρ ρ'
    → (i : Fin (length Δ))
    → ((⟦ Ms ⟧s₃ · ρ) i) ∼ ((⟦ splits Ms ⟧s₄ · ρ') i)

  ok (` x) h = h x
  ok (clos {Δ} N Ms) h =
    S-clos ⟦ N ⟧₃ ⟦ split N ⟧₄ (S-tuple (length Δ) (oks Ms h)) λ hX hY →
      ok N λ { Z → hY ; (S Z) → hX }
  ok (app L M) h = S-call (ok L h) (ok M h)
  ok (lit B c) h = S-const B c
  ok (tuple {Δ} Ms) h = S-tuple (length Δ) (oks Ms h)
  ok (get i M) h = S-proj (pos i) (ok M h)
  ok (inl M) h = S-inl (ok M h)
  ok (inr M) h = S-inr (ok M h)
  ok (case L M N) {ρ} {ρ'} h =
    S-case (abs ⟦ M ⟧₃ · ρ) (abs ⟦ N ⟧₃ · ρ) (abs ⟦ split M ⟧₄ · ρ')
      (abs ⟦ split N ⟧₄ · ρ')
      (ok L h) (λ ha → ok M (ext-env ha h)) (λ ha → ok N (ext-env ha h))
  ok (prim p L M) h = S-prim p (ok L h) (ok M h)
  ok (let′ M N) {ρ} {ρ'} h =
    transport₂ _∼_ (letᶜ-β ⟦ M ⟧₃ ⟦ N ⟧₃ ρ ⁻¹)
      (letᶜ-β ⟦ split M ⟧₄ ⟦ split N ⟧₄ ρ' ⁻¹)
      (S-seq (ok M h) (ok N (ext-env (ok M h) h)))
  ok (fold M) h = ok M h
  ok (unfold M) h = ok M h

  oks (M ∷ Ms) h zero = ok M h
  oks (M ∷ Ms) h (suc i) = oks Ms h i

  {- The meanings of a closed program and of its translation are
     related. -}
  split-ok : ∀ {A} (M : Tm [] A) → ⟦ M ⟧₃ · ρ₀ ∼ ⟦ split-program M ⟧₄ · ρ₀
  split-ok M = ok M (λ ())

{- The two instances of Terms. The forward one uses Pres and gives
   split-pres. The backward one uses Refl and gives split-refl. Because
   Refl d d' is Rel reflect d' d, the backward instance passes the
   source and target arguments of Rel-case and of its premises in
   swapped order. -}

open Terms Pres Pres-clos Pres-call
  Rel-const Rel-tuple Rel-proj Rel-inl Rel-inr Rel-case Rel-prim Rel-seq
  using () renaming (split-ok to split-pres) public

open Terms Refl Refl-clos Refl-call
  Rel-const
  (λ k h → Rel-tuple k h)
  (λ i h → Rel-proj i h)
  (λ h → Rel-inl h)
  (λ h → Rel-inr h)
  (λ f g f' g' h hf hg →
     Rel-case f' g' f g h
       (λ {a} {a'} r → hf {a'} {a} r)
       (λ {a} {a'} r → hg {a'} {a} r))
  (λ p h h' → Rel-prim p h h')
  (λ h h' → Rel-seq h h')
  using () renaming (split-ok to split-refl) public

{-

  Soundness and adequacy of the graph model (Sem/ISWIM.agda) with respect
  to the ISWIM machine (Operational/Machine/ISWIM.agda), for closed
  programs M (bound M ≡ 0), started in the environment ρ₀ of a closed
  program on the denotational side and in the empty environment on the
  machine side.

    soundness : if the machine terminates with an answer o (anything but
      o-wrong), then ⟦ M ⟧ ρ₀ has an element of the shape of o (ShapeOf,
      in Adequacy/Common.agda); for o-const B k, the constant itself.
    adequacy : if d ∈ ⟦ M ⟧ ρ₀, then the machine terminates with an
      answer o, and d has the shape of o.

  so that ⟦ M ⟧ ρ₀ contains const k exactly when the machine terminates
  with o-const B k, and is nonempty exactly when the machine terminates
  with an answer (and so is empty when it goes wrong or diverges).
  Combined with the correctness of the compiler in the graph model
  (CompilerCorrect.agda), the constants of the compiled Clos5 program
  are exactly the constants the ISWIM machine computes.

  The approach (no big-step semantics in between):

  * Soundness (Adequacy/Soundness.agda): every machine state denotes a
    set of values, through denotations of machine values, environments
    and continuations, and each step can only shrink it. The β steps
    (application, case) use the continuity of the ISWIM semantics
    (Sem/ISWIMContinuous.agda) and that every value denotes a nonempty
    set.

  * Adequacy (Adequacy/LogRel.agda): a logical relation between
    denotational values and machine values, by recursion on the
    denotational value (as in the classic adequacy proofs for graph
    models), and the fundamental lemma by induction on the term. The
    machine's determinism lets one argument value serve all the (finitely
    many) argument entries of a function entry V ↦ w.

-}

module Compiler.Operational.Adequacy.ISWIM where

open import Primitives using (Base; base-rep)
open import SetsAsPredicates
open import GraphModel.Domain using (Value) renaming (const to dconst)
open import Compiler.Model.Graph.Correctness.DelayFiniteCommon using (ρ₀)
open import Compiler.Lang.ISWIM
open import Compiler.Model.Graph.Sem.ISWIM using (⟦_⟧)
open import Compiler.Model.Graph.Sem.Clos5Iswim using (⟦_⟧ₚ)
open import Compiler.Model.Graph.Correctness.CompilerCorrect
  using (compile; compile-correct-const; compile-correct-nonempty)
open import Compiler.Observation
open import Compiler.Operational.Smallstep
  using (Terminates; Diverges; diverges-not-terminates; next; stop)
open import Compiler.Operational.Machine.ISWIM
open import Compiler.Compile.EncloseScope using (Closed)
open import Syntax.Uses Op sig using (uses-bound)
open import Compiler.Operational.Adequacy.Common
open import Compiler.Operational.Adequacy.Soundness using (soundness) public
open import Compiler.Operational.Adequacy.LogRel

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([])
open import Data.Nat using (_<_)
open import Data.Nat.Properties using (n≮0)
open import Data.Product using (_×_; Σ-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)
open import Relation.Nullary using (¬_)

{- Soundness -------------------------------------------------------------------}

sound-const : ∀ M {B} {k : base-rep B} → Terminates (sem M) (o-const B k) → dconst k ∈ ⟦ M ⟧ ρ₀
sound-const M t with soundness M t (λ ())
... | ⟨ d , ⟨ d∈ , refl ⟩ ⟩ = d∈

sound-nonempty : ∀ M → Converges (Terminates (sem M)) → nonempty (⟦ M ⟧ ρ₀)
sound-nonempty M ⟨ o , ⟨ ans , t ⟩ ⟩ with soundness M t ans
... | ⟨ d , ⟨ d∈ , _ ⟩ ⟩ = ⟨ d , d∈ ⟩

{- Adequacy --------------------------------------------------------------------}

closed-𝔾 : ∀ M → Closed M → 𝔾 (UsesP M) ρ₀ []
closed-𝔾 M c x u = ⊥-elim (n≮0 (subst (x <_) c (uses-bound x M u)))

adequacy : ∀ M → Closed M → ∀ {d} → d ∈ ⟦ M ⟧ ρ₀
  → Σ[ o ∈ Obs ] Terminates (sem M) o × ShapeOf o d
adequacy M c {d} d∈ with adequate M (closed-𝔾 M c) d∈
... | ⟨ v , ⟨ e , r ⟩ ⟩ =
  ⟨ obs v , ⟨ ⟨ ret v halt , ⟨ ↠→star (e halt) , refl ⟩ ⟩
            , 𝕍-shape d v r ⟩ ⟩

adequacy-const : ∀ M → Closed M → ∀ {B} {k : base-rep B}
  → dconst k ∈ ⟦ M ⟧ ρ₀ → Terminates (sem M) (o-const B k)
adequacy-const M c k∈ with adequacy M c k∈
... | ⟨ o , ⟨ t , sh ⟩ ⟩ = subst (Terminates (sem M)) (shape-const sh) t

adequacy-converges : ∀ M → Closed M → nonempty (⟦ M ⟧ ρ₀) → Converges (Terminates (sem M))
adequacy-converges M c ⟨ d , d∈ ⟩ with adequacy M c d∈
... | ⟨ o , ⟨ t , sh ⟩ ⟩ = ⟨ o , ⟨ shape-answer sh , t ⟩ ⟩

{- The machine terminates with at most one observation ----------------------}

terminates-det : ∀ M {o₁ o₂} → Terminates (sem M) o₁ → Terminates (sem M) o₂ → o₁ ≡ o₂
terminates-det M ⟨ t₁ , ⟨ σ₁ , f₁ ⟩ ⟩ ⟨ t₂ , ⟨ σ₂ , f₂ ⟩ ⟩
    with ↠-final-det (star→↠ σ₁) (star→↠ σ₂) f₁ f₂
... | refl with trans (sym f₁) f₂
... | refl = refl

{- Characterizations ------------------------------------------------------------}

const-iff : ∀ M → Closed M → ∀ {B} {k : base-rep B}
  → (dconst k ∈ ⟦ M ⟧ ρ₀) ⇔ Terminates (sem M) (o-const B k)
const-iff M c = ⟨ adequacy-const M c , sound-const M ⟩

nonempty-iff : ∀ M → Closed M → nonempty (⟦ M ⟧ ρ₀) ⇔ Converges (Terminates (sem M))
nonempty-iff M c = ⟨ adequacy-converges M c , sound-nonempty M ⟩

{- a program that goes wrong, or diverges, denotes the empty set -}
wrong-empty : ∀ M → Closed M → Terminates (sem M) o-wrong → ∀ d → ¬ (d ∈ ⟦ M ⟧ ρ₀)
wrong-empty M c w d d∈ with adequacy M c d∈
... | ⟨ o , ⟨ t , sh ⟩ ⟩ = shape-answer sh (terminates-det M t w)

diverges-empty : ∀ M → Closed M → Diverges (sem M) → ∀ d → ¬ (d ∈ ⟦ M ⟧ ρ₀)
diverges-empty M c div d d∈ with adequacy M c d∈
... | ⟨ o , ⟨ t , _ ⟩ ⟩ = diverges-not-terminates div t

{- The compiler, observed through the ISWIM machine ---------------------------}

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

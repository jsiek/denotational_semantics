{-

  Soundness and adequacy of the Scott-domain semantics of FPC
  (Mu/Semantics/ScottDomains/FPC.agda) with respect to its clocked
  interpreter (Mu/Semantics/ClockedInterpreters/FPC.agda), for closed
  programs of any type, as Mu/proof/Adequacy/FPC.agda is for the graph
  model:

    soundness (Soundness.agda): what the interpreter returns at some
      clock means ⟦ M ⟧ ρ₀, and it never errs;
    adequacy (LogRel.agda): if ⟦ M ⟧ ρ₀ is defined, the interpreter
      returns a value from some clock on.

  So ⟦ M ⟧ ρ₀ is the constant c() exactly when the interpreter
  terminates with c (const-iff), and ⟦ M ⟧ ρ₀ is ⊥ exactly when the
  interpreter diverges (diverges-iff). Adequacy gives a clock only
  under a propositional truncation; since whether the interpreter
  returns at a given clock is decidable, the least such clock is found
  (TypeTopology's exit-truncation).

-}

open import MLTT.Spartan hiding (cases; Type)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons

open import Framework.Primitives using (Base; base-rep)
open import Mu.Language.FPC using (Tm)
open import Mu.Semantics.ClockedInterpreters.FPC using (eval; sem; obs) renaming (Val to Value)
open import Semantics.Interp.Clock using (Result; timeout; error; ret; outcome; Terminates; Diverges)
open import Semantics.Observation using (o-const)
open import Naturals.ExitTruncation using (module exit-truncations)

open import Data.List using ([])
open import Mu.Framework.AllUtil using ([])
open import Data.Maybe using (just)
open import Data.Nat.Properties using (≤-refl)
open import Relation.Binary.PropositionalEquality using (_≡_) renaming (refl to ≡-refl; trans to ≡-trans; sym to ≡-sym; cong to ≡-cong)
import Data.Product as P

module Mu.proof.Adequacy.ScottDomains.FPC
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : propext 𝓤₀)
       where

open import Framework.Scott.Base pt fe hiding (_>>=_)
open import proof.Framework.Scott.Ops pt fe pe using (const; ⊥𝔻; defined; const-defined; ⊥-undefined)
open import proof.Framework.Scott.Values pt fe pe using (undefined-⊥)
open import Mu.Semantics.ScottDomains.FPC pt fe pe using (⟦_⟧)
open import Mu.Semantics.ScottDomains.Closed pt fe pe using (ρ₀)
open import Mu.proof.Adequacy.ScottDomains.Soundness pt fe pe using (𝒱; 𝒱-defined; 𝒱-const; const-𝒱; Holds; timeout; ret; sound)
open import Mu.proof.Adequacy.ScottDomains.LogRel pt fe pe using (adequate; run)
open exit-truncations pt using (exit-truncation)

private
 just-inj : ∀ {X : 𝓤₀ ̇ } {a b : X} → just a ≡ just b → a ≡ b
 just-inj ≡-refl = ≡-refl

 {- the interpreter returns at clock ck -}
 Returns : ∀ {A} → Tm [] A → ℕ → 𝓤₀ ̇
 Returns {A} M ck = Σ w ꞉ Value A , eval ck [] M ≡ ret w

 returns? : ∀ {A} (r : Result (Value A)) → is-decidable (Σ w ꞉ Value A , r ≡ ret w)
 returns? timeout = inr (λ { (w , ()) })
 returns? error = inr (λ { (w , ()) })
 returns? (ret w) = inl (w , ≡-refl)

{- a closed program whose meaning is defined returns at some clock -}
terminates : ∀ {A} (M : Tm [] A) → defined (⟦ M ⟧ · ρ₀) → Σ ck ꞉ ℕ , Returns M ck
terminates M q =
  exit-truncation (Returns M) (λ ck → returns? (eval ck [] M))
    (∥∥-functor (λ e → P.proj₁ (run e) , _ , P.proj₂ (run e) (P.proj₁ (run e)) ≤-refl) (pr₂ (adequate M q)))

{- what the interpreter returns means ⟦ M ⟧ ρ₀ -}
sound-ret : ∀ {A} (M : Tm [] A) {ck} {w : Value A} → eval ck [] M ≡ ret w → 𝒱 w ＝ ⟦ M ⟧ · ρ₀
sound-ret M {ck} e = go (eval ck [] M) (sound ck [] M) e
 where
  go : ∀ {A} {w : Value A} {d} (r : Result (Value A)) → Holds (λ v → 𝒱 v ＝ d) r → r ≡ ret w → 𝒱 w ＝ d
  go timeout timeout ()
  go error () e
  go (ret _) (ret s) ≡-refl = s

{- Soundness and adequacy -----------------------------------------------------------}

{- for a closed FPC term M (of any type), and every constant c:
   ⟦ M ⟧ ρ₀ = c() if and only if the interpreter terminates with c -}
const-iff : ∀ {A} (M : Tm [] A) (B : Base) (k : base-rep B)
  → (⟦ M ⟧ · ρ₀ ＝ const B k → Terminates (sem M) (o-const B k))
  × (Terminates (sem M) (o-const B k) → ⟦ M ⟧ · ρ₀ ＝ const B k)
const-iff M B k = to , from
 where
  to : ⟦ M ⟧ · ρ₀ ＝ const B k → Terminates (sem M) (o-const B k)
  to e = ck P., ≡-trans (≡-cong (outcome obs) ev) (≡-cong just (𝒱-const w (sound-ret M ev ∙ e)))
   where
    T = terminates M (transport defined (e ⁻¹) (const-defined B k))
    ck = pr₁ T
    w = pr₁ (pr₂ T)
    ev = pr₂ (pr₂ T)
  from : Terminates (sem M) (o-const B k) → ⟦ M ⟧ · ρ₀ ＝ const B k
  from t = go (eval (P.proj₁ t) [] M) (sound (P.proj₁ t) [] M) (P.proj₂ t)
   where
    go : (r : Result (Value _)) → Holds (λ v → 𝒱 v ＝ ⟦ M ⟧ · ρ₀) r → outcome obs r ≡ just (o-const B k)
       → ⟦ M ⟧ · ρ₀ ＝ const B k
    go timeout timeout ()
    go error () e
    go (ret w) (ret s) e = s ⁻¹ ∙ const-𝒱 w (just-inj e)

{- and ⟦ M ⟧ ρ₀ is ⊥ if and only if the interpreter diverges on M -}
diverges-iff : ∀ {A} (M : Tm [] A)
  → (Diverges (sem M) → ⟦ M ⟧ · ρ₀ ＝ ⊥𝔻) × (⟦ M ⟧ · ρ₀ ＝ ⊥𝔻 → Diverges (sem M))
diverges-iff M = to , from
 where
  ret≢timeout : ∀ {A} {w : Value A} → ¬ (_≡_ {A = Result (Value A)} (ret w) timeout)
  ret≢timeout ()
  to : Diverges (sem M) → ⟦ M ⟧ · ρ₀ ＝ ⊥𝔻
  to div = undefined-⊥ (⟦ M ⟧ · ρ₀) (λ q →
    let T = terminates M q in ret≢timeout (≡-trans (≡-sym (pr₂ (pr₂ T))) (div (pr₁ T))))
  from : ⟦ M ⟧ · ρ₀ ＝ ⊥𝔻 → Diverges (sem M)
  from e ck = go (eval ck [] M) (sound ck [] M)
   where
    go : (r : Result (Value _)) → Holds (λ v → 𝒱 v ＝ ⟦ M ⟧ · ρ₀) r → r ≡ timeout
    go timeout timeout = ≡-refl
    go error ()
    go (ret w) (ret s) = 𝟘-elim (⊥-undefined (transport defined (s ∙ e) (𝒱-defined w)))

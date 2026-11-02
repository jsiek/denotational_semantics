{-

  Soundness and adequacy of the Scott-domain semantics of X86μ
  (FPC/Semantics/ScottDomains/X86.agda, ⟦_⟧ₜ) with respect to the X86μ
  clocked interpreter (FPC/Semantics/ClockedInterpreters/X86.agda), as
  FPC.agda is for FPC and FPC/proof/Adequacy/X86.agda for the graph
  model:

    adequacy (X86LogRel.agda), for every program: if ⟦ P ⟧ₜ is defined,
      the interpreter returns a value from some clock on;
    soundness (X86Soundness.agda), for a program whose table contains
      the code of each definition interpreted with the whole table: what
      the interpreter returns at some clock means ⟦ P ⟧ₜ, and it never
      errs.

  So ⟦ P ⟧ₜ is the constant c() exactly when the interpreter terminates
  with c (const-iff), and it is ⊥ exactly when the interpreter diverges
  (diverges-iff); the programs that the compiler produces have such a
  table (X86Compiled.agda), so this holds of them, at any type, with no
  other precondition.

-}

open import MLTT.Spartan hiding (cases; Type)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons

open import Framework.Primitives using (Base; base-rep)
open import FPC.Language.Type using (Type; _∋_)
open import FPC.Language.X86 using (DSig; Body; called; entry; Program; program; body)
open import FPC.Language.FPC using (Tm)
open import FPC.Compiler.Pipeline using (compile)
open import FPC.Framework.AllUtil using (All; []; lookup)
open import FPC.Semantics.ClockedInterpreters.GlobalFun using (module Vals)
open import FPC.Semantics.ClockedInterpreters.X86 using (rv; run; sem) renaming (⟨_,_,_,_⟩ to mach)
open import Semantics.Interp.Clock using (Result; timeout; error; ret; outcome; Terminates; Diverges)
open import Semantics.Observation using (o-const)
open import Naturals.ExitTruncation using (module exit-truncations)

open import Data.List using (List; [])
open import Data.Maybe using (just)
open import Data.Nat.Properties using (≤-refl)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_) renaming (refl to ≡-refl; trans to ≡-trans; sym to ≡-sym; cong to ≡-cong)
import Data.Product as P

module FPC.proof.Adequacy.ScottDomains.X86
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : propext 𝓤₀)
       where

open import Framework.Scott.Base pt fe hiding (_>>=_)
open import proof.Framework.Scott.Ops pt fe pe using (const; ⊥𝔻; defined; const-defined; ⊥-undefined)
open import proof.Framework.Scott.Values pt fe pe using (undefined-⊥)
open import FPC.Semantics.ScottDomains.X86 pt fe pe using (⟦_⟧ₜ; codeₜ)
open import FPC.Semantics.ScottDomains.Ops pt fe pe using (tables)
open import FPC.proof.Adequacy.ScottDomains.Soundness pt fe pe using (Holds; timeout; ret)
import FPC.proof.Adequacy.ScottDomains.X86Soundness pt fe pe as S
import FPC.proof.Adequacy.ScottDomains.X86LogRel pt fe pe as LR
open import FPC.proof.Adequacy.ScottDomains.X86Compiled pt fe pe using (compiled)
open exit-truncations pt using (exit-truncation)

private
 just-inj : ∀ {X : 𝓤₀ ̇ } {a b : X} → just a ≡ just b → a ≡ b
 just-inj ≡-refl = ≡-refl

module _ {Σ : List DSig} (ds : All (λ s → Body Σ (DSig.cod s) (called s)) Σ)
  (closed : ∀ {s} (f : Σ ∋ s) → tables codeₜ ds f ＝ codeₜ (tables codeₜ ds) (lookup ds f)) where

  open Vals Σ using (Val; obs)

  private
   {- main, run with clock ck -}
   main : ∀ {A} → Body Σ A (entry []) → ℕ → Result (Val A)
   main b ck = run ds ck (Body.blocks b) [] (mach (rv tt tt tt) [] tt tt) (Body.start b)

   returns? : ∀ {A} (r : Result (Val A)) → is-decidable (Σ w ꞉ Val A , r ≡ ret w)
   returns? timeout = inr (λ { (w , ()) })
   returns? error = inr (λ { (w , ()) })
   returns? (ret w) = inl (w , ≡-refl)

   {- a program whose meaning is defined returns at some clock -}
   terminates : ∀ {A} (b : Body Σ A (entry [])) → defined ⟦ program ds b ⟧ₜ → Σ ck ꞉ ℕ , Σ w ꞉ Val A , main b ck ≡ ret w
   terminates b q =
     exit-truncation (λ ck → Σ w ꞉ Val _ , main b ck ≡ ret w) (λ ck → returns? (main b ck))
       (∥∥-functor (λ e → P.proj₁ (LR.run⇓ e) , _ , P.proj₂ (LR.run⇓ e) (P.proj₁ (LR.run⇓ e)) ≤-refl)
          (pr₁ (pr₂ (LR.adequacy ds b q))))

   sound-at : ∀ {A} (b : Body Σ A (entry [])) ck → Holds (λ v → S.𝒱 ds v ＝ ⟦ program ds b ⟧ₜ) (main b ck)
   sound-at b ck = S.soundness ds closed b ck

  const-iff : ∀ {A} (b : Body Σ A (entry [])) (B : Base) (k : base-rep B)
    → (⟦ program ds b ⟧ₜ ＝ const B k → Terminates (sem (program ds b)) (o-const B k))
    × (Terminates (sem (program ds b)) (o-const B k) → ⟦ program ds b ⟧ₜ ＝ const B k)
  const-iff b B k = to , from
   where
    to : ⟦ program ds b ⟧ₜ ＝ const B k → Terminates (sem (program ds b)) (o-const B k)
    to e = ck P., ≡-trans (≡-cong (outcome obs) ev) (≡-cong just (S.𝒱-const ds closed w (go (main b ck) (sound-at b ck) ev ∙ e)))
     where
      T' = terminates b (transport defined (e ⁻¹) (const-defined B k))
      ck = pr₁ T'
      w = pr₁ (pr₂ T')
      ev = pr₂ (pr₂ T')
      go : (r : Result (Val _)) → Holds (λ v → S.𝒱 ds v ＝ ⟦ program ds b ⟧ₜ) r → r ≡ ret w → S.𝒱 ds w ＝ ⟦ program ds b ⟧ₜ
      go timeout timeout ()
      go error () e'
      go (ret _) (ret s) ≡-refl = s
    from : Terminates (sem (program ds b)) (o-const B k) → ⟦ program ds b ⟧ₜ ＝ const B k
    from t = go (main b (P.proj₁ t)) (sound-at b (P.proj₁ t)) (P.proj₂ t)
     where
      go : (r : Result (Val _)) → Holds (λ v → S.𝒱 ds v ＝ ⟦ program ds b ⟧ₜ) r → outcome obs r ≡ just (o-const B k)
         → ⟦ program ds b ⟧ₜ ＝ const B k
      go timeout timeout ()
      go error () e
      go (ret w) (ret s) e = s ⁻¹ ∙ S.const-𝒱 ds closed w (just-inj e)

  diverges-iff : ∀ {A} (b : Body Σ A (entry []))
    → (Diverges (sem (program ds b)) → ⟦ program ds b ⟧ₜ ＝ ⊥𝔻) × (⟦ program ds b ⟧ₜ ＝ ⊥𝔻 → Diverges (sem (program ds b)))
  diverges-iff b = to , from
   where
    ret≢timeout : ∀ {A} {w : Val A} → ¬ (_≡_ {A = Result (Val A)} (ret w) timeout)
    ret≢timeout ()
    to : Diverges (sem (program ds b)) → ⟦ program ds b ⟧ₜ ＝ ⊥𝔻
    to div = undefined-⊥ ⟦ program ds b ⟧ₜ (λ q →
      let T' = terminates b q in ret≢timeout (≡-trans (≡-sym (pr₂ (pr₂ T'))) (div (pr₁ T'))))
    from : ⟦ program ds b ⟧ₜ ＝ ⊥𝔻 → Diverges (sem (program ds b))
    from e ck = go (main b ck) (sound-at b ck)
     where
      go : (r : Result (Val _)) → Holds (λ v → S.𝒱 ds v ＝ ⟦ program ds b ⟧ₜ) r → r ≡ timeout
      go timeout timeout = ≡-refl
      go error ()
      go (ret w) (ret s) = 𝟘-elim (⊥-undefined (transport defined (s ∙ e) (S.𝒱-defined ds closed w)))

{- the programs that the compiler produces -}
x86-const-iff : ∀ {A} (M : Tm [] A) (B : Base) (k : base-rep B)
  → (⟦ compile M ⟧ₜ ＝ const B k → Terminates (sem (compile M)) (o-const B k))
  × (Terminates (sem (compile M)) (o-const B k) → ⟦ compile M ⟧ₜ ＝ const B k)
x86-const-iff M = const-iff (Program.defs (compile M)) (compiled M) (Program.main (compile M))

x86-diverges-iff : ∀ {A} (M : Tm [] A)
  → (Diverges (sem (compile M)) → ⟦ compile M ⟧ₜ ＝ ⊥𝔻) × (⟦ compile M ⟧ₜ ＝ ⊥𝔻 → Diverges (sem (compile M)))
x86-diverges-iff M = diverges-iff (Program.defs (compile M)) (compiled M) (Program.main (compile M))

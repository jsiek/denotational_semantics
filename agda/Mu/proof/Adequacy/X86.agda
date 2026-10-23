{-

  Soundness and adequacy of the graph model of X86μ
  (Mu/Semantics/GraphModel/X86.agda, ⟦_⟧ₜ) with respect to the X86μ clocked
  interpreter (Mu/Semantics/ClockedInterpreters/X86.agda), direct, as
  Mu/proof/Adequacy/ISWIM.agda is for ISWIMμ (and
  Mu/proof/Adequacy/AbstractMachines/X86.agda for the X86μ machine):

    adequacy (X86LogRel.agda), for every program: every d ∈ ⟦ P ⟧ₜ is
      related to the value that the interpreter returns from some clock
      on;
    soundness (X86Soundness.agda), for a program whose table is
      consistent and contains the code of each definition interpreted
      with the whole table: what the interpreter returns at some clock
      denotes a part of ⟦ P ⟧ₜ, and it never errs.

  So ⟦ P ⟧ₜ holds const k exactly when the interpreter terminates with
  o-const B k (const-iff), and it is empty exactly when the interpreter
  diverges (diverges-iff); the programs that the compiler produces have
  such a table (X86Compiled.agda), so this holds of them, at any type,
  with no other precondition.

-}

module Mu.proof.Adequacy.X86 where

open import Framework.Primitives using (base-rep)
open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.Domain using () renaming (const to dconst)
open import Mu.proof.Semantics.GraphModel.Ops using (ConT; tables)
open import Mu.Language.Type using (Type)
open import Mu.Language.X86 using (DSig; Body; called; entry; Program; program; body)
open import Mu.Language.ISWIM using (Tm)
open import Mu.Compiler.Pipeline using (compile)
open import Mu.Semantics.GraphModel.X86 using (⟦_⟧ₜ; codeₜ)
open import Semantics.Observation using (o-const; _⇔_)
open import proof.Semantics.Interp.Clock using (Result; timeout; ret; outcome; Terminates; Diverges)
open import Mu.Semantics.ClockedInterpreters.GlobalFun using (module Vals)
open import Mu.Semantics.ClockedInterpreters.X86 using (sem)
open import Mu.Framework.AllUtil using (All)
open import Mu.proof.Adequacy.X86Compiled using (Contains; compiled)
open import Mu.proof.Adequacy.Soundness using (Holds; timeout; ret)
import Mu.proof.Adequacy.X86LogRel as LR
import Mu.proof.Adequacy.X86Soundness as S

open import Data.Empty using (⊥-elim)
open import Data.List using (List; [])
open import Data.Maybe using (just)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_×_; Σ-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Relation.Nullary using (¬_)

private
  just-inj : ∀ {X : Set} {a b : X} → just a ≡ just b → a ≡ b
  just-inj refl = refl

  ret≢timeout : ∀ {X : Set} {v : X} → ¬ (Result.ret v ≡ Result.timeout)
  ret≢timeout ()

module _ {Σ : List DSig} (ds : All (λ s → Body Σ (DSig.cod s) (called s)) Σ)
  (cT : ConT (tables codeₜ ds)) (cl : Contains codeₜ ds) where

  open Vals Σ using (Val; obs)
  open S ds cT cl using (𝒱; 𝒱-const; 𝒱-ne)

  private
    {- a sound result observed as a constant: the constant is in D -}
    const-in : ∀ {A} {r : Result (Val A)} {D B} {k : base-rep B} → Holds (λ v → 𝒱 v ⊆ D) r
      → outcome obs r ≡ just (o-const B k) → dconst k ∈ D
    const-in (ret {v} v⊆) e = v⊆ _ (𝒱-const v (just-inj e))

    {- a sound result in an empty D times out -}
    empty-timeout : ∀ {A} {r : Result (Val A)} {D} → Holds (λ v → 𝒱 v ⊆ D) r → ¬ nonempty D → r ≡ timeout
    empty-timeout timeout ne = refl
    empty-timeout (ret {v} v⊆) ne with 𝒱-ne v
    ... | ⟨ d , d∈ ⟩ = ⊥-elim (ne ⟨ d , v⊆ d d∈ ⟩)

  const-iff : ∀ {A} (b : Body Σ A (entry [])) {B} {k : base-rep B}
    → (dconst k ∈ ⟦ program ds b ⟧ₜ) ⇔ Terminates (sem (program ds b)) (o-const B k)
  const-iff (body n bs s) =
    ⟨ (λ k∈ → let ⟨ v , ⟨ ⟨ c , e ⟩ , r ⟩ ⟩ = LR.adequacy ds (body n bs s) k∈ in
         ⟨ c , trans (cong (outcome obs) (e c ≤-refl)) (cong just (LR.𝕍-const ds v r)) ⟩)
    , (λ { ⟨ ck , e ⟩ → const-in (S.soundness ds cT cl (body n bs s) ck) e }) ⟩

  diverges-iff : ∀ {A} (b : Body Σ A (entry [])) → Diverges (sem (program ds b)) ⇔ (¬ nonempty ⟦ program ds b ⟧ₜ)
  diverges-iff (body n bs s) =
    ⟨ (λ { div ⟨ d , d∈ ⟩ → let ⟨ v , ⟨ ⟨ c , e ⟩ , _ ⟩ ⟩ = LR.adequacy ds (body n bs s) d∈ in
             ret≢timeout (trans (sym (e c ≤-refl)) (div c)) })
    , (λ ne ck → empty-timeout (S.soundness ds cT cl (body n bs s) ck) ne) ⟩

{- a program whose table is consistent and contains the code of each definition -}
program-const-iff : ∀ {A} (P : Program A) → ConT (tables codeₜ (Program.defs P)) → Contains codeₜ (Program.defs P)
  → ∀ {B} {k : base-rep B} → (dconst k ∈ ⟦ P ⟧ₜ) ⇔ Terminates (sem P) (o-const B k)
program-const-iff (program ds b) cT cl = const-iff ds cT cl b

program-diverges-iff : ∀ {A} (P : Program A) → ConT (tables codeₜ (Program.defs P)) → Contains codeₜ (Program.defs P)
  → Diverges (sem P) ⇔ (¬ nonempty ⟦ P ⟧ₜ)
program-diverges-iff (program ds b) cT cl = diverges-iff ds cT cl b

{- the programs that the compiler produces -}
x86-const-iff : ∀ {A} (M : Tm [] A) {B} {k : base-rep B}
  → (dconst k ∈ ⟦ compile M ⟧ₜ) ⇔ Terminates (sem (compile M)) (o-const B k)
x86-const-iff M = program-const-iff (compile M) (proj₁ (compiled M)) (proj₂ (compiled M))

x86-diverges-iff : ∀ {A} (M : Tm [] A) → Diverges (sem (compile M)) ⇔ (¬ nonempty ⟦ compile M ⟧ₜ)
x86-diverges-iff M = program-diverges-iff (compile M) (proj₁ (compiled M)) (proj₂ (compiled M))

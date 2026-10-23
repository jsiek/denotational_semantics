{-

  The table of the X86μ program that the compiler produces satisfies the
  premises of soundness (X86Soundness.agda), as for X86ᵀ
  (proof/Adequacy/X86Compiled.agda): it is consistent, and it contains
  the code of each definition interpreted with the whole table
  (Contains), not only with the table of the older ones, as the
  semantics interprets it.

  Both hold of the GlobalFunμ program that globalize produces, whose
  definitions refer only to older ones
  (Mu/proof/Compiler/GlobalizeOlder.agda), and pass to X86μ through the
  lemmas of the denotational proofs of remove complex operands, lift
  locals, explicate control and select instructions: the tables of the
  two programs agree, and so does the code of each definition,
  interpreted with tables that agree.

-}

module Mu.proof.Adequacy.X86Compiled where

open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.Domain using (Value; ⟨⟩; Con-⊆; Con-•; Con-⌈⌉; ≈⇒Con; _•_)
open import proof.Framework.GraphModel.Ops using (Λ-≃; ΛΛ-≃; ΛΛ-mono)
open import proof.Framework.GraphModel.Env using (extend-nonempty-env; •-~)
open import Mu.proof.Semantics.GraphModel.Ops using (Table; ConT; tables; tables-con; init)
open import Mu.proof.Semantics.GraphModel.GlobalFun using (ok; code-con; table-con)
open import Mu.Semantics.GraphModel.GlobalFun using (code′; table)
open import Mu.Semantics.GraphModel.Imp using () renaming (code′ to codeᵢ)
open import Mu.Semantics.GraphModel.X86 using (codeₜ)
open import Mu.Language.Type
open import Mu.Language.GlobalFun using (DSig; Code; program)
import Mu.Language.GlobalFun as GlobalFun
open import Mu.Language.X86 using (Program)
open import Mu.Language.ISWIM using (Tm)
open import Mu.Language.Mon using (⌜_⌝)
open import Mu.Framework.AllUtil using (All; lookup) renaming (map to All-map)
open import Mu.proof.Framework.AllProp using (lookup-map)
open import Mu.Compiler.Pipeline using (compile; compile₄; compile-x86)
open import Mu.Compiler.RCO using (rco)
open import Mu.Compiler.LiftLocals using () renaming (lift to liftₗ)
open import Mu.Compiler.Explicate using (explicate-body)
open import Mu.Compiler.Select using (def-body)
open import Mu.proof.Compiler.GlobalizeOlder using (OlderDefs; globalize-older)
open import Mu.proof.Adequacy.GlobalFunCommon using (table-at; agree; tbl-mono; olderAt)
open import Mu.proof.Correctness.GraphModel.RCOCorrect using (code-rco; table-rco)
open import Mu.proof.Correctness.GraphModel.LiftLocalsCorrect using (code-lift; table-lift)
open import Mu.proof.Correctness.GraphModel.ExplicateCorrect using (body-≃; table-explicate)
open import Mu.proof.Correctness.GraphModel.SelectCorrect using (code-≃; table-≃)

open import Data.List using (List; []; _∷_)
open import Data.Maybe using (nothing)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Level using (lift; lower)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

{- the table contains the code of each definition, with the whole table -}
Contains : ∀ {Σ} {D : DSig → Set} → (Table Σ → ∀ {s} → D s → 𝒫 Value) → All D Σ → Set
Contains cd ds = ∀ {s} (f : _ ∋ s) → cd (tables cd ds) (lookup ds f) ⊆ tables cd ds f

clos5-closed : ∀ {Σ} (ds : All (Code Σ) Σ) → OlderDefs ds → Contains code′ ds
clos5-closed ds od f d d∈ =
  subst (d ∈_) (sym (table-at code′ ds f))
    (lower (ΛΛ-mono _ _ ⟨ (λ X X' X⊆ Y Y' Y⊆ → lift λ w w∈ →
      tbl-mono (lookup ds f) (table-con ds) (olderAt od f) (λ g g< x x∈ → subst (x ∈_) (agree code′ ds f g g<) x∈) _ w
        (proj₁ (ok (table-con ds) (lookup ds f)) (•-~ _⊆_ (•-~ _⊆_ (λ _ _ z → z) X⊆) Y⊆) w w∈)) , ptt ⟩) d d∈)

{- the X86μ program that the compiler produces, from its GlobalFunμ one -}
compiled : ∀ {A} (M : Tm [] A) → let ds = Program.defs (compile-x86 M) in ConT (tables codeₜ ds) × Contains codeₜ ds
compiled M = ⟨ (λ f → Con-⊆ (table-con ds₅ f) (proj₂ (TT f))) , closed ⟩
  where
  ds₅ = GlobalFun.Program.defs (compile M)
  dsₘ = All-map (λ D → rco D (λ x → x)) ds₅
  dsᵢ = All-map liftₗ dsₘ
  ds꜀ = All-map explicate-body dsᵢ
  cTₘ = tables-con code-con (All-map ⌜_⌝ dsₘ)
  TT : ∀ {s} (f : _ ∋ s) → table ds₅ f ≃ tables codeₜ (All-map def-body ds꜀) f
  TT f = ≃-trans (table-rco ds₅ f) (≃-trans (table-lift dsₘ f) (≃-trans (table-explicate dsᵢ f) (table-≃ ds꜀ f)))
  closed : Contains codeₜ (All-map def-body ds꜀)
  closed f d d∈ = proj₁ (TT f) d (clos5-closed ds₅ (globalize-older (compile₄ M)) f d (proj₂ code≃ d (subst (λ b → d ∈ codeₜ (tables codeₜ (All-map def-body ds꜀)) b) eq d∈)))
    where
    eq : lookup (All-map def-body ds꜀) f ≡ def-body (explicate-body (liftₗ (rco (lookup ds₅ f) (λ x → x))))
    eq = trans (lookup-map def-body ds꜀ f) (cong def-body (trans (lookup-map explicate-body dsᵢ f)
           (cong explicate-body (trans (lookup-map liftₗ dsₘ f) (cong liftₗ (lookup-map (λ D → rco D (λ x → x)) ds₅ f))))))
    dₘ = rco (lookup ds₅ f) (λ x → x)
    Tₘ = tables code′ (All-map ⌜_⌝ dsₘ)
    code≃ : code′ (table ds₅) (lookup ds₅ f) ≃ codeₜ (tables codeₜ (All-map def-body ds꜀)) (def-body (explicate-body (liftₗ dₘ)))
    code≃ = ≃-trans rco≃ (≃-trans lift≃
      (≃-trans (ΛΛ-≃ λ X Y → body-≃ (table-explicate dsᵢ) (liftₗ dₘ) _) (code-≃ (table-≃ ds꜀) (explicate-body (liftₗ dₘ)))))
      where
      lift≃ : code′ Tₘ ⌜ dₘ ⌝ ≃ codeᵢ (tables codeᵢ dsᵢ) (liftₗ dₘ)
      lift≃ = code-lift cTₘ (table-lift dsₘ) dₘ
      rco≃ : code′ (table ds₅) (lookup ds₅ f) ≃ code′ Tₘ ⌜ dₘ ⌝
      rco≃ = code-rco cTₘ (table-rco ds₅) (lookup ds₅ f)

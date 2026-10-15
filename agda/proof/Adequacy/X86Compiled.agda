{-

  The table of the X86ᵀ program that the compiler produces satisfies the
  premises of soundness (X86Soundness.agda): it is consistent, and it
  contains the code of each definition interpreted with the whole table
  (Contains), not only with the table of the older ones, as the semantics
  interprets it.

  Both hold of the Clos5ᵀ program that globalize produces, whose
  definitions refer only to older ones (globalize-older, as in Clos5ᵀ
  adequacy), and pass to X86ᵀ through the lemmas of the denotational
  proofs of remove complex operands, lift locals, explicate control and
  select instructions: the tables of the two programs agree, and so does
  the code of each definition, interpreted with tables that agree.

-}

module proof.Adequacy.X86Compiled where

open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.Domain using (Value; ω; Con-⊆; Con-•; Con-⌈⌉; ≈⇒Con; _•_)
open import proof.Framework.GraphModel.Ops using (Λ-≃; ΛΛ-≃; ΛΛ-mono)
open import proof.Framework.GraphModel.Env using (extend-nonempty-env; •-~)
open import proof.Framework.Lookup using (map-!)
open import proof.Semantics.Graph.Typed.Ops using (Table; ConT; tables; tables-con; init)
open import proof.Semantics.Graph.Typed.Clos5 using (ok; code-con; table-con)
open import Semantics.Graph.Typed.Clos5 using (code′; table)
open import Semantics.Graph.Typed.Imp using () renaming (code′ to codeᵢ)
open import Semantics.Graph.Typed.X86 using (codeₜ)
open import Language.Typed.Type hiding (_≟_)
open import Language.Typed.Clos5 using (Code; program)
open import Language.Typed.X86 using (Program)
open import Language.ISWIM using (AST)
open import Framework.Lookup using (_!_)
open import Compiler.Pipeline using (compile; compile₄; compile-x86)
open import Compiler.RCO using (rco)
open import Compiler.LiftLocals using () renaming (lift to liftₗ)
open import Compiler.Explicate using (explicate-body)
open import Compiler.Select using (def-body)
open import proof.Compiler.GlobalizeOlder using (OlderDefs; globalize-older)
import proof.Adequacy.Clos5Common as C5
import proof.Adequacy.Clos5Soundness as S5
open import proof.Correctness.Graph.RCOCorrect using (rco-sem; table-rco)
open import proof.Correctness.Graph.LiftLocalsCorrect using (lift-sem; table-lift)
open import proof.Correctness.Graph.ExplicateCorrect using (body-≃; table-explicate)
open import proof.Correctness.Graph.SelectCorrect using (code-≃; table-≃)

open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All) renaming (map to All-map)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Level using (lift; lower)
open import Language.Typed.Mon using (⌜_⌝)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

{- the table contains the code of each definition, with the whole table -}
Contains : ∀ {Σ} {D : ℕ → Set} → (Table Σ → ∀ {n} → D n → 𝒫 Value) → All D Σ → Set
Contains cd ds = ∀ {n} (f : _ ∋ n) → cd (tables cd ds) (ds ! f) ⊆ tables cd ds f

clos5-closed : ∀ {Σ} (ds : All (Code Σ) Σ) → OlderDefs ds → Contains code′ ds
clos5-closed ds od f d d∈ =
  subst (d ∈_) (sym (table-at code′ ds f))
    (lower (ΛΛ-mono _ _ ⟨ (λ X X' X⊆ Y Y' Y⊆ → lift λ w w∈ →
      tbl-mono (ds ! f) (table-con ds) (olderAt od f) (λ g g< x x∈ → subst (x ∈_) (agree code′ ds f g g<) x∈) _ w
        (proj₁ (ok (table-con ds) (ds ! f)) (•-~ _⊆_ (•-~ _⊆_ (λ _ _ z → z) X⊆) Y⊆) w w∈)) , ptt ⟩) d d∈)
  where
  open C5 ds using (table-at; agree)
  open S5 ds od using (tbl-mono; olderAt)

{- the X86ᵀ program that the compiler produces, from its Clos5ᵀ one -}
compiled : ∀ (M : AST) → let ds = Program.defs (compile-x86 M) in ConT (tables codeₜ ds) × Contains codeₜ ds
compiled M = ⟨ (λ f → Con-⊆ (table-con ds₅ f) (proj₂ (TT f))) , closed ⟩
  where
  ds₅ = Language.Typed.Clos5.Program.defs (compile M)
  dsₘ = All-map (λ D → rco D (λ x → x)) ds₅
  dsᵢ = All-map liftₗ dsₘ
  ds꜀ = All-map explicate-body dsᵢ
  cTₘ = tables-con code-con (All-map ⌜_⌝ dsₘ)
  TT : ∀ {n} (f : _ ∋ n) → table ds₅ f ≃ tables codeₜ (All-map def-body ds꜀) f
  TT f = ≃-trans (table-rco ds₅ f) (≃-trans (table-lift dsₘ f) (≃-trans (table-explicate dsᵢ f) (table-≃ ds꜀ f)))
  closed : Contains codeₜ (All-map def-body ds꜀)
  closed f d d∈ = proj₁ (TT f) d (clos5-closed ds₅ (globalize-older (compile₄ M)) f d (proj₂ code≃ d (subst (λ b → d ∈ codeₜ (tables codeₜ (All-map def-body ds꜀)) b) eq d∈)))
    where
    eq : All-map def-body ds꜀ ! f ≡ def-body (explicate-body (liftₗ (rco (ds₅ ! f) (λ x → x))))
    eq = trans (map-! def-body ds꜀ f) (cong def-body (trans (map-! explicate-body dsᵢ f)
           (cong explicate-body (trans (map-! liftₗ dsₘ f) (cong liftₗ (map-! (λ D → rco D (λ x → x)) ds₅ f))))))
    dₘ = rco (ds₅ ! f) (λ x → x)
    Tₘ = tables code′ (All-map ⌜_⌝ dsₘ)
    code≃ : code′ (table ds₅) (ds₅ ! f) ≃ codeₜ (tables codeₜ (All-map def-body ds꜀)) (def-body (explicate-body (liftₗ dₘ)))
    code≃ = ≃-trans rco≃ (≃-trans lift≃
      (≃-trans (ΛΛ-≃ λ X Y → body-≃ (table-explicate dsᵢ) (liftₗ dₘ) _) (code-≃ (table-≃ ds꜀) (explicate-body (liftₗ dₘ)))))
      where
      lift≃ : code′ Tₘ ⌜ dₘ ⌝ ≃ codeᵢ (tables codeᵢ dsᵢ) (liftₗ dₘ)
      lift≃ = Λ-≃ λ V _ cV → Λ-≃ λ U _ cU → lift-sem cTₘ (table-lift dsₘ) dₘ _ nothing
                (Con-• (≈⇒Con cU) (Con-• (≈⇒Con cV) (λ _ → Con-⌈⌉ ω)))
      rco≃ : code′ (table ds₅) (ds₅ ! f) ≃ code′ Tₘ ⌜ dₘ ⌝
      rco≃ = Λ-≃ λ V neV cV → Λ-≃ λ U neU cU → rco-sem cTₘ (table-rco ds₅) (ds₅ ! f) (λ x → x) _ _
        (extend-nonempty-env (extend-nonempty-env (λ _ → ⟨ ω , refl ⟩) (E≢[]⇒nonempty-mem neV)) (E≢[]⇒nonempty-mem neU))
        (Con-• (≈⇒Con cU) (Con-• (≈⇒Con cV) (λ _ → Con-⌈⌉ ω))) (λ x → ≃-refl)

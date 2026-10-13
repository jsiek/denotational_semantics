module proof.Semantics.GraphErr.Clos2 where

open import Framework.Syntax.SigUtil
open import proof.Framework.GraphModel.DOpSig
open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.DenotProperties
open import proof.Framework.GraphModel.Domain
open import proof.Framework.GraphModel.OpsBase
open import proof.Framework.GraphModel.ErrorOps
open import proof.Semantics.GraphErr.Prim
open import Language.Clos2
open import Semantics.GraphErr.Clos2 public hiding (⟦_⟧; init)

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; replicate)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Level using (lift; lower)
open import proof.Framework.GraphModel.Env using (_~ₑ[_]_)

{- The semantics of Semantics/GraphErr/Clos2.agda as an instance of the
   generic Semantics record (proof/Framework/GraphModel/Semantics.agda),
   whose ⟦_⟧ is by definition the ⟦_⟧ there, with the monotonicity and
   consistency of its operators. (Its continuity is in
   proof/Semantics/GraphErr/Clos2Continuous.agda.) -}

apply-n-pres : ∀ (R : 𝒫 Value → 𝒫 Value → Set) n {b} (F F' : Result (𝒫 Value) (ν-n n b)) Ds Ds'
  → result-rel-pres R (ν-n n b) F F' → results-rel-pres R (replicate n ■) Ds Ds'
  → result-rel-pres R b (apply-n n F Ds) (apply-n n F' Ds')
apply-n-pres R zero F F' _ _ F~ _ = F~
apply-n-pres R (suc n) F F' ⟨ D , Ds ⟩ ⟨ D' , Ds' ⟩ F~ ⟨ lift D~ , Ds~ ⟩ =
  apply-n-pres R n (F D) (F' D') Ds Ds' (F~ D D' D~) Ds~

𝕆-Clos2ᵉ-mono : 𝕆-monotone sig 𝕆-Clos2ᵉ
𝕆-Clos2ᵉ-mono (clos-op n) ⟨ F , Ds ⟩ ⟨ F' , Ds' ⟩ ⟨ F⊆ , Ds⊆ ⟩ =
  lift (guardᵉ-n-mono n Ds⊆
         (lower (Λᵉ-mono ⟨ apply-n n F Ds , ptt ⟩ ⟨ apply-n n F' Ds' , ptt ⟩
                         ⟨ apply-n-pres _⊆_ n F F' Ds Ds' F⊆ Ds⊆ , ptt ⟩)))
𝕆-Clos2ᵉ-mono app = ⋆ᵉ-mono
𝕆-Clos2ᵉ-mono (lit B k) = ℬ-mono B k
𝕆-Clos2ᵉ-mono (tuple n) = 𝒯ᵉ-mono n
𝕆-Clos2ᵉ-mono (get i) = projᵉ-mono i
𝕆-Clos2ᵉ-mono inl-op = inlᵉ-mono
𝕆-Clos2ᵉ-mono inr-op = inrᵉ-mono
𝕆-Clos2ᵉ-mono case-op = 𝒞ᵉ-mono
𝕆-Clos2ᵉ-mono (prim p) = primᵉ-mono p
𝕆-Clos2ᵉ-mono let-op = letᵉ-mono

𝕆-Clos2ᵉ-consis : 𝕆-consistent _~_ sig 𝕆-Clos2ᵉ
𝕆-Clos2ᵉ-consis (clos-op n) ⟨ F , Ds ⟩ ⟨ F' , Ds' ⟩ ⟨ F~ , Ds~ ⟩ =
  lift (guardᵉ-n-consis n Ds~
         (lower (Λᵉ-consis ⟨ apply-n n F Ds , ptt ⟩ ⟨ apply-n n F' Ds' , ptt ⟩
                           ⟨ apply-n-pres (Every _~_) n F F' Ds Ds' F~ Ds~ , ptt ⟩))
         Λᵉ-clean Λᵉ-clean)
𝕆-Clos2ᵉ-consis app = ⋆ᵉ-consis
𝕆-Clos2ᵉ-consis (lit B k) = ℬ-consis B k
𝕆-Clos2ᵉ-consis (tuple n) = 𝒯ᵉ-consis n
𝕆-Clos2ᵉ-consis (get i) = projᵉ-consis i
𝕆-Clos2ᵉ-consis inl-op = inlᵉ-consis
𝕆-Clos2ᵉ-consis inr-op = inrᵉ-consis
𝕆-Clos2ᵉ-consis case-op = 𝒞ᵉ-consis
𝕆-Clos2ᵉ-consis (prim p) = primᵉ-consis p
𝕆-Clos2ᵉ-consis let-op = letᵉ-consis

open import proof.Framework.GraphModel.Semantics Op sig public

instance
  Clos2ᵉ-Semantics : Semantics
  Clos2ᵉ-Semantics = record { interp-op = 𝕆-Clos2ᵉ ; mono-op = 𝕆-Clos2ᵉ-mono ; error = ω }
open Semantics {{...}} public

{- consistent environments give consistent denotations -}
Clos2ᵉ-con-env : ∀ M {ρ ρ'} → ρ ~ₑ[ Every _~_ ] ρ' → Every _~_ (⟦ M ⟧ ρ) (⟦ M ⟧ ρ')
Clos2ᵉ-con-env M = ⟦⟧-pres (Every _~_) 𝕆-Clos2ᵉ-consis (Con-⌈⌉ ω) M

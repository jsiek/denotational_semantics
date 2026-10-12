module proof.Compiler.Model.Graph.Sem.Clos2Iswim where

open import Framework.Syntax.SigUtil
open import proof.Framework.GraphModel.DOpSig
open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.DenotProperties
open import proof.Framework.GraphModel.Domain
open import proof.Framework.GraphModel.Ops
open import proof.Compiler.Model.Graph.Prim
open import Compiler.Lang.Clos2
open import Compiler.Model.Graph.Sem.Clos2Iswim public hiding (⟦_⟧; init)

open import Data.Nat using (ℕ; zero; suc; _+_; _<_)
open import Data.List using (List; []; _∷_; replicate)
open import Data.Product
   using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Unit.Polymorphic using () renaming (tt to ptt; ⊤ to pTrue)
open import Level renaming (zero to lzero; suc to lsuc)

{- The semantics of Compiler/Model/Graph/Sem/Clos2Iswim.agda as an instance of
   the generic Semantics record (proof/Framework/GraphModel/Semantics.agda),
   whose ⟦_⟧ is by definition the ⟦_⟧ there, with the monotonicity and
   consistency of its operators. -}

apply-n-mono : ∀ n {b} (F F' : Result (𝒫 Value) (ν-n n b)) Ds Ds'
  → result-rel-pres _⊆_ (ν-n n b) F F' → results-rel-pres _⊆_ (replicate n ■) Ds Ds'
  → result-rel-pres _⊆_ b (apply-n n F Ds) (apply-n n F' Ds')
apply-n-mono zero F F' _ _ F~ _ = F~
apply-n-mono (suc n) F F' ⟨ D , Ds ⟩ ⟨ D' , Ds' ⟩ F~ ⟨ lift D⊆ , Ds~ ⟩ =
  apply-n-mono n (F D) (F' D') Ds Ds' (F~ D D' D⊆) Ds~

𝕆-Clos2-mono : 𝕆-monotone sig 𝕆-Clos2
𝕆-Clos2-mono (clos-op n) ⟨ F , Ds ⟩ ⟨ F' , Ds' ⟩ ⟨ F~ , Ds~ ⟩ = lift G
  where
  Λ⊆ = lower (Λ-mono ⟨ apply-n n F Ds , ptt ⟩ ⟨ apply-n n F' Ds' , ptt ⟩
                     ⟨ apply-n-mono n F F' Ds Ds' F~ Ds~ , ptt ⟩)
  G : guard-n n Ds (Λ ⟨ apply-n n F Ds , ptt ⟩) ⊆ guard-n n Ds' (Λ ⟨ apply-n n F' Ds' , ptt ⟩)
  G w ⟨ ne , w∈ ⟩ =
    ⟨ (λ i → ⟨ proj₁ (ne i) , nthD-mono Ds Ds' Ds~ i _ (proj₂ (ne i)) ⟩) , Λ⊆ w w∈ ⟩
𝕆-Clos2-mono app = ⋆-mono
𝕆-Clos2-mono (lit B k) _ _ _ = lift (λ d z → z)
𝕆-Clos2-mono (tuple x) = 𝒯-mono x
𝕆-Clos2-mono (get x) = proj-mono x
𝕆-Clos2-mono inl-op = inl-mono
𝕆-Clos2-mono inr-op = inr-mono
𝕆-Clos2-mono case-op = 𝒞-mono
𝕆-Clos2-mono (prim p) = primD-mono p

open import proof.Framework.GraphModel.Semantics Op sig public

instance
  Clos2-Semantics : Semantics
  Clos2-Semantics = record { interp-op = 𝕆-Clos2 ;
                             mono-op = 𝕆-Clos2-mono ;
                             error = ω }
open Semantics {{...}} public

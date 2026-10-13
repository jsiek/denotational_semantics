module proof.Semantics.GraphErrM.Clos2 where

open import Framework.Syntax.SigUtil
open import proof.Framework.GraphModel.DOpSig
open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.DenotProperties
open import proof.Framework.GraphModel.Domain
open import proof.Framework.GraphModel.OpsBase
open import proof.Framework.GraphModel.ErrorMonad
open import proof.Framework.GraphModel.ContinuityBase using (mono; consis)
open import proof.Semantics.GraphErrM.Prim
open import Language.Clos2
open import Semantics.GraphErrM.Clos2 public hiding (⟦_⟧; init)

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open import Data.List using (List; []; _∷_; replicate)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Unit using (⊤; tt)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Level using (lift; lower)
open import proof.Framework.GraphModel.Env using (Env; _~ₑ[_]_)

{- The semantics of Semantics/GraphErrM/Clos2.agda as an instance of the
   generic Semantics record, with the monotonicity and consistency of its
   operators. -}

apply-n-pres : ∀ (R : 𝒫 Value → 𝒫 Value → Set) n {b} (F F' : Result (𝒫 Value) (ν-n n b)) Ds Ds'
  → result-rel-pres R (ν-n n b) F F' → results-rel-pres R (replicate n ■) Ds Ds'
  → result-rel-pres R b (apply-n n F Ds) (apply-n n F' Ds')
apply-n-pres R zero F F' _ _ F~ _ = F~
apply-n-pres R (suc n) F F' ⟨ D , Ds ⟩ ⟨ D' , Ds' ⟩ F~ ⟨ lift D~ , Ds~ ⟩ =
  apply-n-pres R n (F D) (F' D') Ds Ds' (F~ D D' D~) Ds~

𝕆-Clos2ᵐ-mono : 𝕆-monotone sig 𝕆-Clos2ᵐ
𝕆-Clos2ᵐ-mono (clos-op n) ⟨ F , Ds ⟩ ⟨ F' , Ds' ⟩ ⟨ F⊆ , Ds⊆ ⟩ =
  lift (binds-mono n {K = λ Xs → Λᵐ ⟨ apply-n n F Xs , ptt ⟩} {λ Xs → Λᵐ ⟨ apply-n n F' Xs , ptt ⟩} Ds⊆ (λ {Xs} {Ys} Xs⊆ → lower (mono (Λᵐ-good {⊤}) ⟨ apply-n n F Xs , ptt ⟩ ⟨ apply-n n F' Ys , ptt ⟩
                                              ⟨ apply-n-pres _⊆_ n F F' Xs Ys F⊆ Xs⊆ , ptt ⟩)))
𝕆-Clos2ᵐ-mono app = mono (⋆ᵐ-good {⊤})
𝕆-Clos2ᵐ-mono (lit B k) = ℬ-mono B k
𝕆-Clos2ᵐ-mono (tuple n) = mono (𝒯ᵐ-good {⊤} n)
𝕆-Clos2ᵐ-mono (get i) = mono (projᵐ-good {⊤} i)
𝕆-Clos2ᵐ-mono inl-op = mono (inlᵐ-good {⊤})
𝕆-Clos2ᵐ-mono inr-op = mono (inrᵐ-good {⊤})
𝕆-Clos2ᵐ-mono case-op = mono (𝒞ᵐ-good {⊤})
𝕆-Clos2ᵐ-mono (prim p) = mono (primᵐ-good {⊤} p)
𝕆-Clos2ᵐ-mono let-op = mono (letᵐ-good {⊤})

𝕆-Clos2ᵐ-consis : 𝕆-consistent _~_ sig 𝕆-Clos2ᵐ
𝕆-Clos2ᵐ-consis (clos-op n) ⟨ F , Ds ⟩ ⟨ F' , Ds' ⟩ ⟨ F~ , Ds~ ⟩ =
  lift (binds-consis n {K = λ Xs → Λᵐ ⟨ apply-n n F Xs , ptt ⟩} {λ Xs → Λᵐ ⟨ apply-n n F' Xs , ptt ⟩} Ds~ (λ {Xs} {Ys} Xs~ → lower (consis (Λᵐ-good {⊤}) tt ⟨ apply-n n F Xs , ptt ⟩ ⟨ apply-n n F' Ys , ptt ⟩
                                                   ⟨ apply-n-pres (Every _~_) n F F' Xs Ys F~ Xs~ , ptt ⟩)))
𝕆-Clos2ᵐ-consis app = consis (⋆ᵐ-good {⊤}) tt
𝕆-Clos2ᵐ-consis (lit B k) = ℬ-consis B k
𝕆-Clos2ᵐ-consis (tuple n) = consis (𝒯ᵐ-good {⊤} n) tt
𝕆-Clos2ᵐ-consis (get i) = consis (projᵐ-good {⊤} i) tt
𝕆-Clos2ᵐ-consis inl-op = consis (inlᵐ-good {⊤}) tt
𝕆-Clos2ᵐ-consis inr-op = consis (inrᵐ-good {⊤}) tt
𝕆-Clos2ᵐ-consis case-op = consis (𝒞ᵐ-good {⊤}) tt
𝕆-Clos2ᵐ-consis (prim p) = consis (primᵐ-good {⊤} p) tt
𝕆-Clos2ᵐ-consis let-op = consis (letᵐ-good {⊤}) tt

open import proof.Framework.GraphModel.Semantics Op sig public

instance
  Clos2ᵐ-Semantics : Semantics
  Clos2ᵐ-Semantics = record { interp-op = 𝕆-Clos2ᵐ ; mono-op = 𝕆-Clos2ᵐ-mono ; error = ω }
open Semantics {{...}} public

{- bind the free variables one at a time, the last one ending up first -}
push : ∀ {n} → Results (𝒫 Value) (replicate n ■) → Env Value → Env Value
push {zero} _ ρ = ρ
push {suc n} ⟨ D , Ds ⟩ ρ = push Ds (D • ρ)

{- a closure's body, applied to its free variables and argument -}
apply-push : ∀ k (a : Arg (ν-n k (ν ■))) (ρ : Env Value) Ds (Y : 𝒫 Value)
  → apply-n k (⟦ a ⟧ₐ ρ) Ds Y ≡ ⟦ unbind-n k a ⟧ (Y • push Ds ρ)
apply-push zero (bind (ast N)) ρ _ Y = refl
apply-push (suc k) (bind a) ρ ⟨ D , Ds ⟩ Y = apply-push k a (D • ρ) Ds Y

push-plus : ∀ n (Ds : Results (𝒫 Value) (replicate n ■)) ρ j → push Ds ρ (n + j) ≡ ρ j
push-plus zero _ ρ j = refl
push-plus (suc n) ⟨ D , Ds ⟩ ρ j rewrite sym (+-suc n j) = push-plus n Ds (D • ρ) (suc j)

Clos2ᵐ-con-env : ∀ M {ρ ρ'} → ρ ~ₑ[ Every _~_ ] ρ' → Every _~_ (⟦ M ⟧ ρ) (⟦ M ⟧ ρ')
Clos2ᵐ-con-env M = ⟦⟧-pres (Every _~_) 𝕆-Clos2ᵐ-consis (Con-⌈⌉ ω) M

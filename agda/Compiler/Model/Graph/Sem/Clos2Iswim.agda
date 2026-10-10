module Compiler.Model.Graph.Sem.Clos2Iswim where
{-

 In this intermediate semantics a closure binds its free variables like a
   nested let: its body is applied directly to the denotations of the free
   variable expressions, and the result is a function of the argument.
   Like tuples, closures are strict: a closure has no values unless each
   of its free variables has one.
 This semantics is after the 'enclose' pass,
   and before the 'concretize' pass.

-}

open import Utilities using (_iff_)
open import Primitives
open import ScopedTuple hiding (𝒫)
open import NewSigUtil
open import NewDOpSig
open import Utilities using (extensionality)
open import SetsAsPredicates
open import NewDenotProperties
open import Compiler.Model.Graph.Domain.ISWIM.Domain
open import Compiler.Model.Graph.Domain.ISWIM.Ops
open import Compiler.Lang.Clos2

open import Data.Empty renaming (⊥ to Bot)
open import Data.Nat using (ℕ; zero; suc; _+_; _<_)
open import Data.Nat.Properties using (+-suc)
open import Data.List using (List; []; _∷_; replicate)
open import Data.Product
   using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Unit using (⊤; tt)
open import Data.Unit.Polymorphic using () renaming (tt to ptt; ⊤ to pTrue)
open import Level renaming (zero to lzero; suc to lsuc)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; sym; cong; cong₂; cong-app)
open Eq.≡-Reasoning

{- apply a curried function of n sets to the denotations of the free variables -}
apply-n : ∀ n {b} → Result (𝒫 Value) (ν-n n b) → Results (𝒫 Value) (replicate n ■)
  → Result (𝒫 Value) b
apply-n zero F _ = F
apply-n (suc n) F ⟨ D , Ds ⟩ = apply-n n (F D) Ds

apply-n-mono : ∀ n {b} (F F' : Result (𝒫 Value) (ν-n n b)) Ds Ds'
  → result-rel-pres _⊆_ (ν-n n b) F F' → results-rel-pres _⊆_ (replicate n ■) Ds Ds'
  → result-rel-pres _⊆_ b (apply-n n F Ds) (apply-n n F' Ds')
apply-n-mono zero F F' _ _ F~ _ = F~
apply-n-mono (suc n) F F' ⟨ D , Ds ⟩ ⟨ D' , Ds' ⟩ F~ ⟨ lift D⊆ , Ds~ ⟩ =
  apply-n-mono n (F D) (F' D') Ds Ds' (F~ D D' D⊆) Ds~

𝕆-Clos2 : DOpSig (𝒫 Value) sig
𝕆-Clos2 (clos-op n) ⟨ F , Ds ⟩ = guard-n n Ds (Λ ⟨ apply-n n F Ds , ptt ⟩)
𝕆-Clos2 app = ⋆
𝕆-Clos2 (lit B k) = ℬ B k
𝕆-Clos2 (tuple n) = 𝒯 n
𝕆-Clos2 (get i) = proj i
𝕆-Clos2 inl-op = ℒ
𝕆-Clos2 inr-op = ℛ
𝕆-Clos2 case-op = 𝒞

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
𝕆-Clos2-mono inl-op = ℒ-mono
𝕆-Clos2-mono inr-op = ℛ-mono
𝕆-Clos2-mono case-op = 𝒞-mono

open import Fold2 Op sig
open import NewSemantics Op sig public

instance
  Clos2-Semantics : Semantics
  Clos2-Semantics = record { interp-op = 𝕆-Clos2 ;
                             mono-op = 𝕆-Clos2-mono ;
                             error = ω }
open Semantics {{...}} public

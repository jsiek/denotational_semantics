{-

  The delay pass translates an application with a let:

    let f = L' in app (fst f , snd f , shift N')

  so that the closure L' is computed once. This means the same as
  applying the code of L' to its environment and to N' directly,

    (car L' ⋆ cdr L') ⋆ N',

  because each result of the latter uses only finitely many elements of
  L' (one code entry, and the environment entries that cover its free
  variables), and a let can bind any finite part of L'.

-}

open import NewSigUtil
open import NewSyntaxUtil
open import SetsAsPredicates
open import NewDOpSig
open import Compiler.Model.Graph.Domain.ISWIM.Domain
open import Compiler.Model.Graph.Domain.ISWIM.Ops
open import Compiler.Lang.Clos4
open import Compiler.Lang.Rename Op sig using (shift)
open import Compiler.Model.Graph.Sem.Clos4Iswim
open import Compiler.Model.Graph.Sem.RenameSem Op sig using (shift-≃)
open import Compiler.Model.Graph.Correctness.DelayFiniteCommon using (Env; _●_; Car; Cdr; _⊙_)

open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Membership.Propositional renaming (_∈_ to _⋵_)
open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Relation.Binary.PropositionalEquality using (refl)

module Compiler.Model.Graph.Correctness.DelayApp where

{- the application, with the closure bound by a let -}
let-app : AST → AST → AST
let-app L' N' =
  let-op ⦅ L' ,, ⟩ (app ⦅ (fst-op ⦅ (` 0) ,, Nil ⦆) ,, (snd-op ⦅ (` 0) ,, Nil ⦆) ,,
                          shift N' ,, Nil ⦆) ,, Nil ⦆

{- finitely many environment entries of L that cover the variables FV -}
cover-cdrs : ∀ (L : 𝒫 Value) FV → mem FV ⊆ Cdr L
  → Σ[ C ∈ List Value ] mem C ⊆ L × (∀ fv → fv ⋵ FV → Σ[ FVs ∈ List Value ] ∣ FVs ⦆ ⋵ C × fv ⋵ FVs)
cover-cdrs L [] _ = ⟨ [] , ⟨ (λ _ ()) , (λ _ ()) ⟩ ⟩
cover-cdrs L (fv ∷ FV) FV⊆ with FV⊆ fv (here refl) | cover-cdrs L FV (λ d d∈ → FV⊆ d (there d∈))
... | ⟨ FVs , ⟨ e∈ , fv∈ ⟩ ⟩ | ⟨ C , ⟨ C⊆ , cov ⟩ ⟩ = ⟨ ∣ FVs ⦆ ∷ C , ⟨ G , H ⟩ ⟩
  where
  G : mem (∣ FVs ⦆ ∷ C) ⊆ L
  G _ (here refl) = e∈
  G d (there d∈) = C⊆ d d∈
  H : ∀ d → d ⋵ (fv ∷ FV) → Σ[ FVs' ∈ List Value ] ∣ FVs' ⦆ ⋵ (∣ FVs ⦆ ∷ C) × d ⋵ FVs'
  H _ (here refl) = ⟨ FVs , ⟨ here refl , fv∈ ⟩ ⟩
  H d (there d∈) with cov d d∈
  ... | ⟨ FVs' , ⟨ e∈' , d∈' ⟩ ⟩ = ⟨ FVs' , ⟨ there e∈' , d∈' ⟩ ⟩

let-app-≃ : ∀ (L' N' : AST) (ρ : Env) → ⟦ let-app L' N' ⟧ ρ ≃ (⟦ L' ⟧ ρ ⊙ ⟦ N' ⟧ ρ)
let-app-≃ L' N' ρ = ⟨ G , H ⟩
  where
  L = ⟦ L' ⟧ ρ
  N = ⟦ N' ⟧ ρ

  G : ⟦ let-app L' N' ⟧ ρ ⊆ (L ⊙ N)
  G w ⟨ V , ⟨ ⟨ ⟨ U₀ , ⟨ ⟨ FV , ⟨ e∈ , ⟨ FV⊆ , neFV ⟩ ⟩ ⟩ , ⟨ U₀⊆ , neU₀ ⟩ ⟩ ⟩ , _ ⟩ , ⟨ V⊆L , _ ⟩ ⟩ ⟩ =
    ⟨ U₀ , ⟨ ⟨ FV , ⟨ V⊆L _ e∈
                    , ⟨ (λ d d∈ → cdr⊆ d (FV⊆ d d∈)) , neFV ⟩ ⟩ ⟩
           , ⟨ (λ d d∈ → proj₁ (shift-≃ N' (mem V) ρ) d (U₀⊆ d d∈)) , neU₀ ⟩ ⟩ ⟩
    where
    cdr⊆ : Cdr (mem V) ⊆ Cdr L
    cdr⊆ d ⟨ FVs , ⟨ e∈' , d∈ ⟩ ⟩ = ⟨ FVs , ⟨ V⊆L _ e∈' , d∈ ⟩ ⟩

  H : (L ⊙ N) ⊆ ⟦ let-app L' N' ⟧ ρ
  H w ⟨ U₀ , ⟨ ⟨ FV , ⟨ e∈ , ⟨ FV⊆ , neFV ⟩ ⟩ ⟩ , ⟨ U₀⊆ , neU₀ ⟩ ⟩ ⟩
      with cover-cdrs L FV FV⊆
  ... | ⟨ C , ⟨ C⊆ , cov ⟩ ⟩ =
    ⟨ V , ⟨ ⟨ ⟨ U₀ , ⟨ ⟨ FV , ⟨ here refl , ⟨ cdrV , neFV ⟩ ⟩ ⟩
                    , ⟨ (λ d d∈ → proj₂ (shift-≃ N' (mem V) ρ) d (U₀⊆ d d∈)) , neU₀ ⟩ ⟩ ⟩
            , (λ ()) ⟩
          , ⟨ V⊆L , (λ ()) ⟩ ⟩ ⟩
    where
    V = ⦅ FV ↦ (U₀ ↦ w) ∣ ∷ C
    V⊆L : mem V ⊆ L
    V⊆L _ (here refl) = e∈
    V⊆L d (there d∈) = C⊆ d d∈
    cdrV : mem FV ⊆ Cdr (mem V)
    cdrV fv fv∈ with cov fv fv∈
    ... | ⟨ FVs , ⟨ e∈' , fv∈' ⟩ ⟩ = ⟨ FVs , ⟨ there e∈' , fv∈' ⟩ ⟩

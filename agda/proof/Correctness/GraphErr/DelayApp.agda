{-

  The delay pass translates an application with a let,

    let f = L' in app (fst f , snd f , shift N'),

  which, in the graph model with errors, means the same as applying the
  code of L' to its environment and to N' directly, L' ⊙ N', when L' is
  consistent: an error of L' is passed on by the let and by fst alike, and
  otherwise each result needs only a finite part of L', which the let can
  bind.

-}

open import Framework.Syntax.SyntaxUtil
open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.Domain
open import proof.Framework.GraphModel.ErrorOps
open import Language.Clos4
open import proof.Framework.Syntax.Rename Op sig using (shift)
open import proof.Semantics.GraphErr.Clos4
open import proof.Framework.GraphModel.RenameSem Op sig using (shift-≃)
open import proof.Framework.GraphModel.Env using (Env; nonempty-env)
open import proof.Correctness.GraphErr.DelayRel using (_⊙_; is-ω?)

open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Data.Unit using (tt)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open import Relation.Nullary using (Dec; yes; no)

module proof.Correctness.GraphErr.DelayApp where

let-app : AST → AST → AST
let-app L' N' =
  let-op ⦅ L' ,, ⟩ (app ⦅ (fst-op ⦅ (` 0) ,, Nil ⦆) ,, (snd-op ⦅ (` 0) ,, Nil ⦆) ,,
                          shift N' ,, Nil ⦆) ,, Nil ⦆

{- a finite set has no ω, or has it -}
ω-in? : ∀ V → NoErr V ⊎ ω ∈ mem V
ω-in? [] = inj₁ (λ ())
ω-in? (v ∷ V) with is-ω? v | ω-in? V
... | yes refl | _ = inj₂ (here refl)
... | no _ | inj₂ i = inj₂ (there i)
... | no v≢ | inj₁ n = inj₁ (λ { (here eq) → v≢ (sym eq) ; (there i) → n i })

{- a call whose code and environment come from L has some element of L -}
call-ne : ∀ {L N w} → w ∈ (L ⊙ N) → nonempty L
call-ne (inj₁ ⟨ _ , ⟨ _ , ⟨ inj₁ ⟨ t , e∈ ⟩ , _ ⟩ ⟩ ⟩) = ⟨ _ , e∈ ⟩
call-ne (inj₁ ⟨ _ , ⟨ _ , ⟨ inj₂ ⟨ () , _ ⟩ , _ ⟩ ⟩ ⟩)
call-ne (inj₂ ⟨ _ , inj₁ (inj₁ (inj₁ ⟨ t , e∈ ⟩)) ⟩) = ⟨ _ , e∈ ⟩
call-ne (inj₂ ⟨ _ , inj₁ (inj₁ (inj₂ ⟨ _ , inj₁ ω∈ ⟩)) ⟩) = ⟨ ω , ω∈ ⟩
call-ne (inj₂ ⟨ _ , inj₁ (inj₁ (inj₂ ⟨ _ , inj₂ ⟨ d , ⟨ d∈ , _ ⟩ ⟩ ⟩)) ⟩) = ⟨ d , d∈ ⟩
call-ne (inj₂ ⟨ _ , inj₁ (inj₂ ⟨ ⟨ d , ⟨ inj₁ ⟨ t , e∈ ⟩ , _ ⟩ ⟩ , _ ⟩) ⟩) = ⟨ _ , e∈ ⟩
call-ne (inj₂ ⟨ _ , inj₁ (inj₂ ⟨ ⟨ d , ⟨ inj₂ ⟨ refl , _ ⟩ , d≢ ⟩ ⟩ , _ ⟩) ⟩) = ⊥-elim (d≢ refl)
call-ne (inj₂ ⟨ _ , inj₂ ⟨ ⟨ d , ⟨ inj₁ ⟨ t , e∈ ⟩ , _ ⟩ ⟩ , _ ⟩ ⟩) = ⟨ _ , e∈ ⟩
call-ne (inj₂ ⟨ _ , inj₂ ⟨ ⟨ d , ⟨ inj₂ ⟨ refl , _ ⟩ , ⟨ d≢ , _ ⟩ ⟩ ⟩ , _ ⟩ ⟩) = ⊥-elim (d≢ refl)

{- a call whose code and environment come from a set that holds ω is ω -}
call-ω : ∀ {L N w} → Con L → ω ∈ L → w ∈ (L ⊙ N) → w ≡ ω
call-ω cL ω∈ (inj₁ ⟨ _ , ⟨ _ , ⟨ inj₁ ⟨ t , e∈ ⟩ , _ ⟩ ⟩ ⟩) with cL _ _ ω∈ e∈
... | ()
call-ω cL ω∈ (inj₂ ⟨ refl , _ ⟩) = refl

let-app-≃ : ∀ (L' N' : AST) (ρ : Env Value) → nonempty-env ρ → Con (⟦ L' ⟧ ρ)
  → ⟦ let-app L' N' ⟧ ρ ≃ (⟦ L' ⟧ ρ ⊙ ⟦ N' ⟧ ρ)
let-app-≃ L' N' ρ NE cL = ⟨ G , H ⟩
  where
  L = ⟦ L' ⟧ ρ
  N = ⟦ N' ⟧ ρ
  B = app ⦅ (fst-op ⦅ (` 0) ,, Nil ⦆) ,, (snd-op ⦅ (` 0) ,, Nil ⦆) ,, shift N' ,, Nil ⦆
  F = λ X → ⟦ B ⟧ (X • ρ)

  F≃ : ∀ X → F X ≃ (X ⊙ N)
  F≃ X = callᵉ-≃ ≃-refl ≃-refl (shift-≃ N' X ρ)

  G : ⟦ let-app L' N' ⟧ ρ ⊆ (L ⊙ N)
  G w (inj₁ ⟨ V , ⟨ ⟨ w∈ , _ ⟩ , ⟨ V⊆L , _ ⟩ ⟩ ⟩) = proj₁ (F≃ L) w (body-mono B ρ V⊆L w w∈)
  G w (inj₂ ⟨ refl , inj₁ () ⟩)
  G w (inj₂ ⟨ refl , inj₂ (inj₁ ⟨ d , ⟨ d∈ , ⟨ _ , nf ⟩ ⟩ ⟩) ⟩) = ⊥-elim (nf (Λᵉ-fun d d∈))
  G w (inj₂ ⟨ refl , inj₂ (inj₂ ⟨ _ , ω∈ ⟩) ⟩) = inj₂ ⟨ refl , inj₁ (inj₁ (inj₂ ⟨ refl , inj₁ ω∈ ⟩)) ⟩

  H : (L ⊙ N) ⊆ ⟦ let-app L' N' ⟧ ρ
  H w w∈ with body-continuous B ρ NE L (call-ne w∈) w (proj₂ (F≃ L) w w∈)
  ... | ⟨ V , ⟨ ne , ⟨ V⊆ , w∈′ ⟩ ⟩ ⟩ with ω-in? V
  ...   | inj₁ n = inj₁ ⟨ V , ⟨ ⟨ w∈′ , ⟨ ne , ⟨ Con⇒≈ V cL V⊆ , n ⟩ ⟩ ⟩ , ⟨ V⊆ , ⟨ ne , n ⟩ ⟩ ⟩ ⟩
  ...   | inj₂ i with call-ω cL (V⊆ ω i) w∈
  ...     | refl = inj₂ ⟨ refl , inj₂ (inj₂ ⟨ ⟨ ν , ⟨ tt , tt ⟩ ⟩ , V⊆ ω i ⟩) ⟩

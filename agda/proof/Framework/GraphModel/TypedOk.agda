{-

  Monotone, continuous and consistent denotations (Ok), for semantics of
  intrinsically typed syntax in the graph model with errors, defined by
  direct recursion on the terms (Semantics/GraphErr/Typed/): the
  analogue of GoodSemantics (SemanticsCore.agda) without an ABT, so a
  language proves Ok of each term by structural induction, one line per
  constructor, from the facts of this module:

  * an operator that is Good (ContinuityBase.agda) preserves Ok
    (ok-op), also on the operands of a vector of terms (ok-vec, through
    split, the bodies of a function to Results); variables and
    constants are Ok, and so is a bind into a body (let-ok); the check
    of a kind, seen through a map φ on kinds, is Good (check-kind-good);
  * a body under one or two binders uses only finite parts of the sets
    it is given (fin₁, fin₂, fin-code).

-}

module proof.Framework.GraphModel.TypedOk where

open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.DOpSig
open import proof.Framework.GraphModel.DenotProperties using (Every)
open import proof.Framework.GraphModel.Domain
open import proof.Framework.GraphModel.OpsBase using (Finitary)
open import proof.Framework.GraphModel.ContinuityBase
open import proof.Framework.GraphModel.ErrorMonad
open import proof.Framework.GraphModel.Env
  using (Env; nonempty-env; _~ₑ[_]_; _⊆ₑ_; •-~; extend-nonempty-env; single-env; single-fin; single-⊆; v∈single[xv]x)
open import Framework.abt.Sig using (∁)
open import Framework.GraphModel.TypedCheck using (checkedᵠ)

open import Data.List using (List; []; _∷_; replicate)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Sum using (inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Data.Product using (_×_; proj₁; proj₂; Σ-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Unit using (⊤; tt)
open import Data.Unit.Polymorphic using () renaming (tt to ptt; ⊤ to ⊤′)
open import Level using (lift; lower)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; trans; sym)

open import proof.Framework.GraphModel.TypedOkBase public

{- a bind into a body -}
let-ok : ∀ {E N} → Ok E → Ok N → Ok (λ ρ → E ρ ≫= λ X → N (X • ρ))
let-ok {E} {N} ⟨ mE , ⟨ kE , cE ⟩ ⟩ ⟨ mN , ⟨ kN , cN ⟩ ⟩ =
  ⟨ (λ ρ⊆ → ≫=-mono (mE ρ⊆) (λ X⊆ → mN (•-~ _⊆_ ρ⊆ X⊆)))
  , ⟨ (λ NE → ≫=-cont′ mE (kE NE) (λ ρ⊆ X⊆ → mN (•-~ _⊆_ ρ⊆ X⊆)) (body NE))
    , (λ ρ~ → ≫=-consis (cE ρ~) (λ X~ → cN (•-~ (Every _~_) ρ~ X~))) ⟩ ⟩
  where
  body : ∀ {ρ} → nonempty-env ρ → Conv (E ρ) → Cont (λ ρ → N (⌊ E ρ ⌋ • ρ)) ρ
  body NE cv w w∈ with kN (extend-nonempty-env NE cv) w w∈
  ... | ⟨ ρ′ , ⟨ f , ⟨ s , w∈′ ⟩ ⟩ ⟩
      with many (λ ρ → ⌊ E ρ ⌋) NE (λ ρ⊆ → ⌊⌋-mono (mE ρ⊆)) (⌊⌋-cont (kE NE)) (proj₁ (f 0))
             (λ d d∈ → s 0 d (proj₂ (proj₁ (proj₂ (f 0))) d d∈))
  ... | ⟨ a , V⊆ ⟩ = done (λ ρ → N (⌊ E ρ ⌋ • ρ)) (approx-join a b) w (mN env⊆ w w∈′)
    where
    b = approx (λ x → ρ′ (suc x)) (λ x → f (suc x)) (λ x → s (suc x))
    env⊆ : ρ′ ⊆ₑ (⌊ E (env (approx-join a b)) ⌋ • env (approx-join a b))
    env⊆ zero d d∈ = ⌊⌋-mono (mE (join-l a b)) d (V⊆ d (proj₁ (proj₁ (proj₂ (f 0))) d d∈))
    env⊆ (suc x) d d∈ = join-r a b x d d∈

{- the check that keeps the elements of kind k, their kinds seen through φ
   (the kernel of a project) -}
check-kind-good : ∀ φ k → Good ⊤ (■ ∷ []) (λ Ds → checkedᵠ φ k (proj₁ Ds) (proj₁ Ds ⇂ λ d → φ (kind d) ≡ k))
check-kind-good φ k = mk-good
  (λ { _ _ ⟨ lift X⊆ , _ ⟩ → lift λ { w (inj₁ ⟨ refl , ⟨ d , ⟨ d∈ , dk ⟩ ⟩ ⟩) → inj₁ ⟨ refl , ⟨ d , ⟨ X⊆ d d∈ , dk ⟩ ⟩ ⟩
                                   ; w (inj₂ w∈) → inj₂ (⇂-mono {P = λ d → φ (kind d) ≡ k} X⊆ w w∈) } })
  (λ { _ _ ⟨ lift X~ , _ ⟩ → lift (con X~) })
  (λ { _ NE ⟨ ⟨ _ , c ⟩ , _ ⟩ → cnt c })
  where
  con : ∀ {X X'} → Every _~_ X X'
    → Every _~_ (checkedᵠ φ k X (X ⇂ λ d → φ (kind d) ≡ k)) (checkedᵠ φ k X' (X' ⇂ λ d → φ (kind d) ≡ k))
  con X~ u w (inj₁ ⟨ refl , _ ⟩) (inj₁ ⟨ refl , _ ⟩) = tt
  con X~ u w (inj₁ ⟨ refl , ⟨ e , ⟨ e∈ , ek ⟩ ⟩ ⟩) (inj₂ ⟨ w∈ , wk ⟩) = ⊥-elim (ek (trans (cong φ (~-kind e w (X~ e w e∈ w∈))) wk))
  con X~ u w (inj₂ ⟨ u∈ , uk ⟩) (inj₁ ⟨ refl , ⟨ e , ⟨ e∈ , ek ⟩ ⟩ ⟩) = ⊥-elim (ek (trans (cong φ (sym (~-kind u e (X~ u e u∈ e∈)))) uk))
  con X~ u w (inj₂ ⟨ u∈ , _ ⟩) (inj₂ ⟨ w∈ , _ ⟩) = X~ u w u∈ w∈
  cnt : ∀ {X : VEnv → 𝒫 Value} {ρ} → Cont X ρ → Cont (λ ρ → checkedᵠ φ k (X ρ) (X ρ ⇂ λ d → φ (kind d) ≡ k)) ρ
  cnt {X} c w (inj₁ ⟨ refl , ⟨ e , ⟨ e∈ , ek ⟩ ⟩ ⟩) with one X c e∈
  ... | ⟨ a , e∈′ ⟩ = done (λ ρ → checkedᵠ φ k (X ρ) (X ρ ⇂ λ d → φ (kind d) ≡ k)) a ω (inj₁ ⟨ refl , ⟨ e , ⟨ e∈′ , ek ⟩ ⟩ ⟩)
  cnt {X} c w (inj₂ w∈) with ⇂-cont {X} {λ d → φ (kind d) ≡ k} c w w∈
  ... | ⟨ ρ′ , ⟨ f , ⟨ s , w∈′ ⟩ ⟩ ⟩ = ⟨ ρ′ , ⟨ f , ⟨ s , inj₂ w∈′ ⟩ ⟩ ⟩


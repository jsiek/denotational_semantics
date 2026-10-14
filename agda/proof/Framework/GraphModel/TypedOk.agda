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
open import Data.List.Relation.Unary.Any using (here)
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

{- the check that keeps the elements of kind k, their kinds seen through φ,
   when the set passes a further test H that is monotone and needs only a
   finite part of the set (the kernel of a project) -}
module _ (H : 𝒫 Value → Set) (H-mono : ∀ {X X'} → X ⊆ X' → H X → H X')
  (H-fin : ∀ {X : VEnv → 𝒫 Value} {ρ} → nonempty-env ρ → Cont X ρ → H (X ρ) → Σ[ a ∈ Approx ρ ] H (X (env a))) where

  Keep : (Kind → Kind) → Kind → 𝒫 Value → 𝒫 Value
  Keep φ k X = X ⇂ λ d → H X × φ (kind d) ≡ k

  check-kind-good : ∀ φ k → Good ⊤ (■ ∷ []) (λ Ds → checkedᵠ φ k (proj₁ Ds) (Keep φ k (proj₁ Ds)))
  check-kind-good φ k = mk-good
    (λ { _ _ ⟨ lift X⊆ , _ ⟩ → lift λ { w (inj₁ ⟨ refl , ⟨ d , ⟨ d∈ , dk ⟩ ⟩ ⟩) → inj₁ ⟨ refl , ⟨ d , ⟨ X⊆ d d∈ , dk ⟩ ⟩ ⟩
                                     ; w (inj₂ ⟨ w∈ , ⟨ h , wk ⟩ ⟩) → inj₂ ⟨ X⊆ w w∈ , ⟨ H-mono X⊆ h , wk ⟩ ⟩ } })
    (λ { _ _ ⟨ lift X~ , _ ⟩ → lift (con X~) })
    (λ { _ NE ⟨ ⟨ m , c ⟩ , _ ⟩ → cnt NE m c })
    where
    con : ∀ {X X'} → Every _~_ X X' → Every _~_ (checkedᵠ φ k X (Keep φ k X)) (checkedᵠ φ k X' (Keep φ k X'))
    con X~ u w (inj₁ ⟨ refl , _ ⟩) (inj₁ ⟨ refl , _ ⟩) = tt
    con X~ u w (inj₁ ⟨ refl , ⟨ e , ⟨ e∈ , ek ⟩ ⟩ ⟩) (inj₂ ⟨ w∈ , ⟨ _ , wk ⟩ ⟩) = ⊥-elim (ek (trans (cong φ (~-kind e w (X~ e w e∈ w∈))) wk))
    con X~ u w (inj₂ ⟨ u∈ , ⟨ _ , uk ⟩ ⟩) (inj₁ ⟨ refl , ⟨ e , ⟨ e∈ , ek ⟩ ⟩ ⟩) = ⊥-elim (ek (trans (cong φ (sym (~-kind u e (X~ u e u∈ e∈)))) uk))
    con X~ u w (inj₂ ⟨ u∈ , _ ⟩) (inj₂ ⟨ w∈ , _ ⟩) = X~ u w u∈ w∈
    cnt : ∀ {X : VEnv → 𝒫 Value} {ρ} → nonempty-env ρ → Mono X → Cont X ρ → Cont (λ ρ → checkedᵠ φ k (X ρ) (Keep φ k (X ρ))) ρ
    cnt {X} NE m c w (inj₁ ⟨ refl , ⟨ e , ⟨ e∈ , ek ⟩ ⟩ ⟩) with one X c e∈
    ... | ⟨ a , e∈′ ⟩ = done (λ ρ → checkedᵠ φ k (X ρ) (Keep φ k (X ρ))) a ω (inj₁ ⟨ refl , ⟨ e , ⟨ e∈′ , ek ⟩ ⟩ ⟩)
    cnt {X} NE m c w (inj₂ ⟨ w∈ , ⟨ h , wk ⟩ ⟩) with one X c w∈ | H-fin NE c h
    ... | ⟨ a , w∈′ ⟩ | ⟨ b , h′ ⟩ = done (λ ρ → checkedᵠ φ k (X ρ) (Keep φ k (X ρ))) (approx-join a b) w
      (inj₂ ⟨ m (join-l a b) w w∈′ , ⟨ H-mono (m (join-r a b)) h′ , wk ⟩ ⟩)

{- Environments reindexed: the head kept, the next position dropped (skip),
   or none (η) -}

Ok-η : ∀ {E} → Ok E → Ok (λ ρ → E (ρ 0 • λ i → ρ (suc i)))
Ok-η {E} o = Ok-≃ (λ ρ → ⟨ proj₁ o (λ { zero _ z → z ; (suc i) _ z → z }) , proj₁ o (λ { zero _ z → z ; (suc i) _ z → z }) ⟩) o

Ok-skip : ∀ {E} → Ok E → Ok (λ ρ → E (ρ 0 • λ i → ρ (suc (suc i))))
Ok-skip ⟨ m , ⟨ k , c ⟩ ⟩ =
  ⟨ (λ ρ⊆ → m λ { zero → ρ⊆ 0 ; (suc i) → ρ⊆ (suc (suc i)) })
  , ⟨ cnt , (λ ρ~ → c λ { zero → ρ~ 0 ; (suc i) → ρ~ (suc (suc i)) }) ⟩ ⟩
  where
  cnt : ∀ {ρ} → nonempty-env ρ → Cont (λ ρ → _) ρ
  cnt {ρ} NE w w∈ with k (λ { zero → NE 0 ; (suc i) → NE (suc (suc i)) }) w w∈
  ... | ⟨ ρ′ , ⟨ f , ⟨ s , w∈′ ⟩ ⟩ ⟩ =
    ⟨ ρ″ , ⟨ (λ { zero → f 0 ; (suc zero) → fin1 ; (suc (suc i)) → f (suc i) })
    , ⟨ (λ { zero → s 0 ; (suc zero) → λ { _ refl → proj₂ (NE 1) } ; (suc (suc i)) → s (suc i) })
    , m (λ { zero _ z → z ; (suc i) _ z → z }) w w∈′ ⟩ ⟩ ⟩
    where
    ρ″ = ρ′ 0 • ⌈ proj₁ (NE 1) ⌉ • λ i → ρ′ (suc i)
    fin1 = ⟨ proj₁ (NE 1) ∷ [] , ⟨ ⟨ (λ { _ refl → here refl }) , (λ { _ (here refl) → refl }) ⟩ , (λ ()) ⟩ ⟩


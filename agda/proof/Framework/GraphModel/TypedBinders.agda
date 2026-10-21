{-

  The binders of the semantics of intrinsically typed syntax in the
  graph model with errors (Semantics/GraphErr/Typed/), for any language:

  * n binds of sets of values, or of equal operands (binds-val-≃,
    binds-≃₂);
  * code, a closed function of two arguments (ΛΛᵐ) whose body is Ok
    (code-ok), and its β laws: applied to an environment T it is the
    function of the body on T (ΛΛᵐ-⋆), and applied to T and E it
    contains the body on them (ΛΛᵐ-call);
  * the call of a closure, a set of pairs P: its code (car) applied to
    its environment (cdr) and an argument (callcᵈ, callc-good).

-}

module proof.Framework.GraphModel.TypedBinders where

open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.DOpSig
open import proof.Framework.GraphModel.DenotProperties using (Every)
open import proof.Framework.GraphModel.Domain
open import proof.Framework.GraphModel.Ops using (⋆; car; cdr; ΛΛ-β; nthD; ⋆₂; ⋆₂-mono; ⋆₂-consis; car-mono; car-consis; cdr-mono; cdr-consis)
open import proof.Framework.GraphModel.Continuity using (⋆₂-cont; car-cont′; cdr-cont′)
open import proof.Framework.GraphModel.ContinuityBase
open import proof.Framework.GraphModel.ErrorMonad
open import proof.Framework.GraphModel.Env using (•-~)
open import proof.Framework.GraphModel.TypedOk using (Ok; const-ok)
open import proof.Framework.GraphModel.TypedOkBase using (callcᵈ; callc-good) public

open import Data.Fin using (zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; proj₁; proj₂; Σ-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Unit using (tt)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Relation.Binary.PropositionalEquality using (_≢_; refl; sym)
open import Level using (lift; lower)

{- n binds ------------------------------------------------------------------------}

⌊⌋-≃ : ∀ {D D'} → D ≃ D' → ⌊ D ⌋ ≃ ⌊ D' ⌋
⌊⌋-≃ D≃ = ⟨ ⌊⌋-mono (proj₁ D≃) , ⌊⌋-mono (proj₂ D≃) ⟩

{- of sets of values: the continuation, on sets equal to them -}
binds-val-≃ : ∀ n {Ds K A} → AllVal n Ds → (∀ {Xs} → (∀ i → nthD Xs i ≃ nthD Ds i) → K Xs ≃ A) → binds n Ds K ≃ A
binds-val-≃ zero _ h = h (λ ())
binds-val-≃ (suc n) {⟨ D , Ds ⟩} {K} vs h =
  ≃-trans (≫=-val-β {F = λ X → binds n Ds (λ Xs → K ⟨ X , Xs ⟩)} (vs zero))
    (binds-val-≃ n (λ i → vs (suc i)) λ r → h λ { zero → ⟨ ⌊⌋-⊆ , ⌊⌋-clean (proj₁ (vs zero)) ⟩ ; (suc i) → r i })

{- of equal operands, into continuations equal on equal values -}
binds-≃₂ : ∀ n {Ds Es K K'} → (∀ i → nthD Ds i ≃ nthD Es i)
  → (∀ {Xs Ys} → (∀ i → nthD Xs i ≃ nthD Ys i × Val (nthD Ys i) × nthD Ys i ⊆ nthD Es i) → K Xs ≃ K' Ys)
  → binds n Ds K ≃ binds n Es K'
binds-≃₂ zero _ h = h (λ ())
binds-≃₂ (suc n) {⟨ D , Ds ⟩} {⟨ E , Es ⟩} {K} {K'} eq h =
  ≫=-≃ {F = λ X → binds n Ds (λ Xs → K ⟨ X , Xs ⟩)} {λ X → binds n Es (λ Xs → K' ⟨ X , Xs ⟩)} (eq zero) λ _ c → binds-≃₂ n (λ i → eq (suc i))
    λ r → h λ { zero → ⟨ ⌊⌋-≃ (eq zero) , ⟨ ⌊⌋-val c , ⌊⌋-⊆ ⟩ ⟩ ; (suc i) → r i }

{- Code -------------------------------------------------------------------------}

code-ok : ∀ {E} → Ok E → Ok (λ _ → ΛΛᵐ ⟨ (λ X Y → E (Y • X • λ _ → ⌈ ω ⌉)) , ptt ⟩)
code-ok o = const-ok (ΛΛᵐ-con λ X X' Y Y' X~ Y~ → proj₂ (proj₂ o) (•-~ (Every _~_) (•-~ (Every _~_) (λ _ → Con-⌈⌉ ω) X~) Y~))

{- code applied to its environment T, when the body uses a finite part of T -}
ΛΛᵐ-⋆ : ∀ {F T} → Con T → Val T → (∀ {X X' Y} → X ⊆ X' → F X Y ⊆ F X' Y)
  → (∀ U w → U ≢ [] → w ∈ F T (mem U) → Σ[ V ∈ List Value ] V ≢ [] × mem V ⊆ T × w ∈ F (mem V) (mem U))
  → ⋆ ⟨ ΛΛᵐ ⟨ F , ptt ⟩ , ⟨ T , ptt ⟩ ⟩ ≃ Λᵐ ⟨ F T , ptt ⟩
ΛΛᵐ-⋆ {F} {T} cT ⟨ clT , ⟨ t , t∈ ⟩ ⟩ m fin = ⟨ H , G ⟩
  where
  G : Λᵐ ⟨ F T , ptt ⟩ ⊆ ⋆ ⟨ ΛΛᵐ ⟨ F , ptt ⟩ , ⟨ T , ptt ⟩ ⟩
  G ν _ = ⟨ t ∷ [] , ⟨ ⟨ ⟨ tt , ⟨ (λ ()) , ≈-single ⟩ ⟩ , ⟨ (λ { (here eq) → clT t t∈ (sym eq) }) , tt ⟩ ⟩
          , ⟨ (λ { _ (here refl) → t∈ }) , (λ ()) ⟩ ⟩ ⟩
  G (U ↦ x) ⟨ ⟨ x∈ , ⟨ neU , cU ⟩ ⟩ , nU ⟩ with fin U x neU x∈
  ... | ⟨ V , ⟨ neV , ⟨ V⊆ , x∈′ ⟩ ⟩ ⟩ =
    ⟨ V , ⟨ ⟨ ⟨ ⟨ x∈′ , ⟨ neU , cU ⟩ ⟩ , ⟨ neV , Con⇒≈ V cT V⊆ ⟩ ⟩ , ⟨ (λ ω∈ → clT ω (V⊆ ω ω∈) refl) , nU ⟩ ⟩
          , ⟨ V⊆ , neV ⟩ ⟩ ⟩
  H : ⋆ ⟨ ΛΛᵐ ⟨ F , ptt ⟩ , ⟨ T , ptt ⟩ ⟩ ⊆ Λᵐ ⟨ F T , ptt ⟩
  H ν _ = ⟨ tt , tt ⟩
  H (U ↦ x) ⟨ V , ⟨ ⟨ ⟨ ⟨ x∈ , r ⟩ , _ ⟩ , ⟨ _ , nU ⟩ ⟩ , ⟨ V⊆T , _ ⟩ ⟩ ⟩ = ⟨ ⟨ m V⊆T x x∈ , r ⟩ , nU ⟩

{- code, applied to sets of values T and E, contains its body on them -}
ΛΛᵐ-call : ∀ {F T E} → Con T → Con E → Clean T → Clean E
  → (∀ w → w ∈ F T E → Σ[ V ∈ List Value ] Σ[ U ∈ List Value ]
       V ≢ [] × U ≢ [] × mem V ⊆ T × mem U ⊆ E × w ∈ F (mem V) (mem U))
  → F T E ⊆ ⋆ ⟨ ⋆ ⟨ ΛΛᵐ ⟨ F , ptt ⟩ , ⟨ T , ptt ⟩ ⟩ , ⟨ E , ptt ⟩ ⟩
ΛΛᵐ-call {F} cT cE clT clE fin w w∈ with ΛΛ-β {F} cT cE fin w w∈
... | ⟨ U , ⟨ ⟨ V , ⟨ e∈ , ⟨ V⊆ , neV ⟩ ⟩ ⟩ , ⟨ U⊆ , neU ⟩ ⟩ ⟩ =
  ⟨ U , ⟨ ⟨ V , ⟨ ⟨ e∈ , ⟨ (λ ω∈ → clT ω (V⊆ ω ω∈) refl) , (λ ω∈ → clE ω (U⊆ ω ω∈) refl) ⟩ ⟩ , ⟨ V⊆ , neV ⟩ ⟩ ⟩ , ⟨ U⊆ , neU ⟩ ⟩ ⟩


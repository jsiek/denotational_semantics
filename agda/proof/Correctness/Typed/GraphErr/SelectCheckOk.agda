{-

  CFGᵀ with the X86 checks (SelectCheck.agda) is monotone, continuous
  and consistent (Ok), under a consistent table: its operators are the
  checking operators of the error monad, all Good.

-}

module proof.Correctness.Typed.GraphErr.SelectCheckOk where

open import Framework.Primitives using (Int)
open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.DenotProperties using (Every)
open import proof.Framework.GraphModel.Domain
open import proof.Framework.GraphModel.ContinuityBase using (Good; mk-good; consis; ℬ-good)
open import proof.Framework.GraphModel.ErrorMonad
open import proof.Framework.GraphModel.Env using (•-~)
open import proof.Framework.GraphModel.TypedOk using (Ok; ok-op; Ok-≃)
open import proof.Semantics.GraphErr.Prim using (primᵐ-good)
open import proof.Semantics.GraphErr.Typed.Clos5 using (ok)
open import proof.Semantics.GraphErr.Typed.CFG using (drop-ok)
open import Semantics.GraphErr.Typed.CFG using (Table; 𝒜; BEnv)
open import Semantics.GraphErr.Typed.Ops using (init)
open import proof.Correctness.Typed.GraphErr.SelectCheck
open import Language.Prim using (sub)
open import Language.Typed.Type hiding (_≟_)
import Language.Typed.Mon as M
open import Language.Typed.Imp using (Simple; atm; pack; callc; tuple; get; inl; inr; prim; inject; project)
open import Language.Typed.CFG using (Tail; return; seq; goto; case; Blocks; _▷_; Body; body)

open import Data.Empty using (⊥-elim)
open import Data.Integer using (+_)
open import Data.List using (List; []; _∷_)
open import Data.Product using (proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Level using (lift; lower)
open import Relation.Binary.PropositionalEquality using (refl)

{- the second operand -}
snd-good : ∀ {P} → Good P (■ ∷ ■ ∷ []) (λ Ds → proj₁ (proj₂ Ds))
snd-good = mk-good (λ { _ _ ⟨ _ , ⟨ r , _ ⟩ ⟩ → r }) (λ { _ _ ⟨ _ , ⟨ r , _ ⟩ ⟩ → r }) (λ { _ NE ⟨ _ , ⟨ ⟨ _ , c ⟩ , _ ⟩ ⟩ → c })

strict-ok : ∀ {D E} → Ok D → Ok E → Ok (λ ρ → strictᵐ (D ρ) (E ρ))
strict-ok oD oE = ok-op (strict-good snd-good) ⟨ oD , ⟨ oE , ptt ⟩ ⟩

{- the test of an injection -}
isinl-good : ∀ {P} → Good P (■ ∷ []) (λ Ds → isinlD (proj₁ Ds))
isinl-good = mk-good
  (λ { _ _ ⟨ lift X⊆ , _ ⟩ → lift λ { w (inj₁ ⟨ u , ⟨ u∈ , e ⟩ ⟩) → inj₁ ⟨ u , ⟨ X⊆ _ u∈ , e ⟩ ⟩
                                   ; w (inj₂ ⟨ u , ⟨ u∈ , e ⟩ ⟩) → inj₂ ⟨ u , ⟨ X⊆ _ u∈ , e ⟩ ⟩ } })
  (λ { _ _ ⟨ lift X~ , _ ⟩ → lift λ { _ _ (inj₁ ⟨ _ , ⟨ _ , refl ⟩ ⟩) (inj₁ ⟨ _ , ⟨ _ , refl ⟩ ⟩) → tt
                                   ; _ _ (inj₁ ⟨ _ , ⟨ u∈ , refl ⟩ ⟩) (inj₂ ⟨ _ , ⟨ v∈ , refl ⟩ ⟩) → ⊥-elim (X~ _ _ u∈ v∈)
                                   ; _ _ (inj₂ ⟨ _ , ⟨ u∈ , refl ⟩ ⟩) (inj₁ ⟨ _ , ⟨ v∈ , refl ⟩ ⟩) → ⊥-elim (X~ _ _ u∈ v∈)
                                   ; _ _ (inj₂ ⟨ _ , ⟨ _ , refl ⟩ ⟩) (inj₂ ⟨ _ , ⟨ _ , refl ⟩ ⟩) → tt } })
  (λ { ⟨ E , _ ⟩ NE ⟨ ⟨ _ , c ⟩ , _ ⟩ w (inj₁ ⟨ u , ⟨ u∈ , e ⟩ ⟩) →
         let ⟨ ρ′ , ⟨ f , ⟨ s , u∈′ ⟩ ⟩ ⟩ = c _ u∈ in ⟨ ρ′ , ⟨ f , ⟨ s , inj₁ ⟨ u , ⟨ u∈′ , e ⟩ ⟩ ⟩ ⟩ ⟩
     ; ⟨ E , _ ⟩ NE ⟨ ⟨ _ , c ⟩ , _ ⟩ w (inj₂ ⟨ u , ⟨ u∈ , e ⟩ ⟩) →
         let ⟨ ρ′ , ⟨ f , ⟨ s , u∈′ ⟩ ⟩ ⟩ = c _ u∈ in ⟨ ρ′ , ⟨ f , ⟨ s , inj₂ ⟨ u , ⟨ u∈′ , e ⟩ ⟩ ⟩ ⟩ ⟩ })

isinlᵐ-good : ∀ {P} → Good P (■ ∷ []) (λ Ds → isinlᵐ (proj₁ Ds))
isinlᵐ-good = strict-good (checkₒ-good isinl-good
  (λ { w (inj₁ ⟨ u , ⟨ u∈ , _ ⟩ ⟩) → inj₂ ⟨ left u , ⟨ u∈ , refl ⟩ ⟩ ; w (inj₂ ⟨ u , ⟨ u∈ , _ ⟩ ⟩) → inj₂ ⟨ right u , ⟨ u∈ , refl ⟩ ⟩ }))

module _ {T : Table} (TC : ∀ k → Con (T k)) where

  okᵃ : ∀ {Σ Δ A} (a : M.Atm Σ Δ A) → Ok (𝒜 a T)
  okᵃ a = ok TC M.⌜ a ⌝ᵃ

  test-ok : ∀ {Σ Δ} t (a : M.Atm Σ Δ Any) → Ok (λ ρ → test t (𝒜 a T ρ))
  test-ok tint a = ok-op (primᵐ-good sub) ⟨ okᵃ a , ⟨ ok-op (ℬ-good Int (+ 0)) ptt , ptt ⟩ ⟩
  test-ok tsum a = ok-op isinlᵐ-good ⟨ okᵃ a , ptt ⟩
  test-ok tfun a = ok-op carᵐ-good ⟨ okᵃ a , ptt ⟩
  test-ok (ttup n i) a = ok-op (projᵐ-good i) ⟨ okᵃ a , ptt ⟩

  simple-ok : ∀ {Σ Δ A} (s : Simple Σ Δ A) → Ok (𝒮ᶜ s T)
  simple-ok (atm a) = okᵃ a
  simple-ok (pack c e) = ok TC M.⌜ M.pack c e ⌝
  simple-ok (callc f a) = strict-ok Cok (strict-ok Dok (strict-ok (okᵃ a) (ok-op callᵐ-good ⟨ Cok , ⟨ Dok , ⟨ okᵃ a , ptt ⟩ ⟩ ⟩)))
    where Cok = ok-op carᵐ-good ⟨ okᵃ f , ptt ⟩
          Dok = ok-op cdrᵐ-good ⟨ okᵃ f , ptt ⟩
  simple-ok (tuple as) = ok TC M.⌜ M.tuple as ⌝
  simple-ok (get i a) = ok-op (projᵐ-good i) ⟨ okᵃ a , ptt ⟩
  simple-ok (inl a) = ok TC M.⌜ M.inl a ⌝
  simple-ok (inr a) = ok TC M.⌜ M.inr a ⌝
  simple-ok (prim p a b) = ok-op (primᵐ-good p) ⟨ okᵃ a , ⟨ okᵃ b , ptt ⟩ ⟩
  simple-ok (inject G a) = okᵃ a
  simple-ok (project t a) = strict-ok (test-ok t a) (okᵃ a)

  tail-okᶜ : ∀ {Σ Bs Δ} (t : Tail Σ Bs Δ) {B : BEnv Bs} → (∀ {Δ'} (l : Bs ∋ Δ') → Ok (B l)) → Ok (⟦ t ⟧ᶜᵗ T B)
  tail-okᶜ (return s) oB = simple-ok s
  tail-okᶜ (seq p s t) oB = ok-op letᵐ-good ⟨ simple-ok s , ⟨ drop-ok p (tail-okᶜ t oB) , ptt ⟩ ⟩
  tail-okᶜ (goto l) oB = oB l
  tail-okᶜ (case a p l₁ l₂) oB = ok-op 𝒞ᵐ-good ⟨ okᵃ a , ⟨ drop-ok p (oB l₁) , ⟨ drop-ok p (oB l₂) , ptt ⟩ ⟩ ⟩

  blocks-okᶜ : ∀ {Σ Bs} (bs : Blocks Σ Bs) {Δ} (l : Bs ∋ Δ) → Ok (blocksᶜ bs T l)
  blocks-okᶜ (bs ▷ t) Z = tail-okᶜ t (blocks-okᶜ bs)
  blocks-okᶜ (bs ▷ t) (S l) = blocks-okᶜ bs l

  run-okᶜ : ∀ {Σ Δ} (b : Body Σ Δ) → Ok (runᶜ b T)
  run-okᶜ (body bs t) = tail-okᶜ t (blocks-okᶜ bs)

  codeᶜʰ-con : ∀ {Σ n} (b : Body Σ (Any ∷ ⟪ tup n ⟫ ∷ [])) → Con (codeᶜʰ T b)
  codeᶜʰ-con b = ΛΛᵐ-con λ X X' Y Y' X~ Y~ →
    lower (consis letᵐ-good tt _ _ ⟨ lift X~ , ⟨ (λ Z Z' Z~ → lift (lower (consis letᵐ-good tt _ _
      ⟨ lift Y~ , ⟨ (λ W W' W~ → lift (proj₂ (proj₂ (run-okᶜ b))
        (•-~ (Every _~_) (•-~ (Every _~_) (λ _ → Con-⌈⌉ ω) Z~) W~))) , ptt ⟩ ⟩))) , ptt ⟩ ⟩)

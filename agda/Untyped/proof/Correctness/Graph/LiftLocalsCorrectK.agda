{-

  Correctness of lift locals (monadic Clos5 → Imp,
  Compiler/LiftLocals.agda) against the continuation-passing semantics of
  Imp (Semantics/Graph/ImpK.agda), the main proof (LiftLocalsCorrect.agda is an
  alternative, against the direct semantics): the meaning of the Imp
  program is that of the Clos5 program.

    lift-program-correct : ⟦ lift-program P mp ⟧ᴷₚ ≃ ⟦ P ⟧ₚ

  The invariant at depth d is that of LiftLocalsCommon.agda: the store
  agrees with the environment, slot d ∸ (x + 1) meaning variable x for
  x < d (Agree), and the variables from d on are out of scope (Scope).
  Running lift n d m
  with a continuation κ that means K D, given the value D and any store
  that agrees with the environment, means K applied to the meaning of m
  (lift-sem). So the store that m leaves is not described: κ is only
  ever given stores that agree.

  K is what the enclosing lets make of the value: nothing at the end of
  a body (K D = D), and ⋆ ⟨ Λ G , D ⟩ for the right-hand side of a let
  whose body and continuation mean G. The commuting conversion is now on
  the Clos5 side: K commutes with let and with case (let-law,
  case-law). Each needs the bound sets to be consistent, so that the
  finitely many runs that ⋆ ⟨ Λ G , - ⟩ uses can be joined into one
  (join): the meaning of the right-hand side of a let, and the
  scrutinee of a case, which has only left or only right elements.

-}

open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.Domain
open import proof.Framework.GraphModel.Ops
open import proof.Semantics.Graph.Prim
open import Untyped.Language.Clos5 using (program)
open import Untyped.Language.Mon
open import Untyped.Compiler.LiftLocals using (lift; height; lift-defs; lift-program)
open import Untyped.Semantics.Graph.Clos5Iswim using (Table; ⟦_⟧[_]; ⟦_⟧₊[_]; table; ⟦_⟧ₚ)
open import Untyped.proof.Semantics.Graph.Clos5IswimContinuous using (⟦⟧[]-monotone; Clos5-con; table-con)
open import Untyped.Semantics.Graph.ImpK
  using (_[_↦_]; checked; Kont; ⟦_⟧ᴷ[_]; ⟦_⟧ᴷₚ)
  renaming (table to tableᴷ)
open import Untyped.proof.Correctness.Graph.LiftLocalsCommon

open import Data.Nat using (zero; suc; _+_; _⊔_; _<_; _≤_; _≟_; _<?_; s≤s)
open import Data.Nat.Properties using (≤-refl)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Product using (_×_; Σ-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Level using () renaming (lift to up)
open import Relation.Binary.PropositionalEquality using (_≢_; refl; sym; trans)
open import Relation.Nullary using (yes; no)

module Untyped.proof.Correctness.Graph.LiftLocalsCorrectK where

open import proof.Framework.GraphModel.Laws

{- Slots ----------------------------------------------------------------------------}

checked-at : ∀ {n x D} → x < n → checked n x D ≃ D
checked-at {n} {x} x<n with x <? n
... | yes _ = ≃-refl
... | no x≮n = ⊥-elim (x≮n x<n)

{- The pass preserves meanings ----------------------------------------------------}

module _ {T T' : Table} (TT : ∀ k → T k ≃ T' k) (TC : ∀ k → Con (T' k)) where

  open AtomsSame TT

  mono-• : ∀ {ρ} M → MonoF (λ X → ⟦ M ⟧[ T' ] (X • ρ))
  mono-• M X⊆ = ⟦⟧[]-monotone T' M λ { zero → X⊆ ; (suc x) → λ _ w∈ → w∈ }

  {- lift at depth d, then a continuation that means K, given a store
     that agrees with ρ -}
  lift-sem : ∀ {M} (m : Mon M) {n d σ ρ} k {κ : Kont} → d + height m ≤ n → Scope d ρ → Agree d σ ρ → Con-env ρ
    → (∀ D σ' → Agree d σ' ρ → κ D σ' ≃ K⟨ k ⟩ D)
    → ⟦ lift n d m ⟧ᴷ[ T ] n σ κ ≃ K⟨ k ⟩ (⟦ M ⟧[ T' ] ρ)
  lift-sem (atom a) k H O A cρ κ≃ = ≃-trans (κ≃ _ _ A) (K-≃ k (atom-≃ a H O A))
  lift-sem (app (a ∷ b ∷ c ∷ [])) k H O A cρ κ≃ = ≃-trans (κ≃ _ _ A) (K-≃ k
    (mono-≃ ⋆₂-mono ⟨ up (atom-≃ a H O A) , ⟨ up (atom-≃ b H O A) , ⟨ up (atom-≃ c H O A) , ptt ⟩ ⟩ ⟩))
  lift-sem (pair (a ∷ b ∷ [])) k H O A cρ κ≃ = ≃-trans (κ≃ _ _ A) (K-≃ k
    (mono-≃ pair-mono ⟨ up (atom-≃ a H O A) , ⟨ up (atom-≃ b H O A) , ptt ⟩ ⟩))
  lift-sem (fst (a ∷ [])) k H O A cρ κ≃ = ≃-trans (κ≃ _ _ A) (K-≃ k (mono-≃ car-mono ⟨ up (atom-≃ a H O A) , ptt ⟩))
  lift-sem (snd (a ∷ [])) k H O A cρ κ≃ = ≃-trans (κ≃ _ _ A) (K-≃ k (mono-≃ cdr-mono ⟨ up (atom-≃ a H O A) , ptt ⟩))
  lift-sem (tuple {k'} {Ms} as) {ρ = ρ} k H O A cρ κ≃ = ≃-trans (κ≃ _ _ A) (K-≃ k
    (atoms-≃ as H O A (λ m Ds → 𝒯 m Ds ≃ 𝒯 k' (⟦ Ms ⟧₊[ T' ] ρ))
                 (λ {m} eq q → ≃-trans (𝒯-≃ m (nthD-≃ _ _ eq)) q) ≃-refl))
  lift-sem (get {i = i} (a ∷ [])) k H O A cρ κ≃ = ≃-trans (κ≃ _ _ A) (K-≃ k (proj-≃ i (atom-≃ a H O A)))
  lift-sem (inl (a ∷ [])) k H O A cρ κ≃ = ≃-trans (κ≃ _ _ A) (K-≃ k (inl-≃ (atom-≃ a H O A)))
  lift-sem (inr (a ∷ [])) k H O A cρ κ≃ = ≃-trans (κ≃ _ _ A) (K-≃ k (inr-≃ (atom-≃ a H O A)))
  lift-sem (prim {p} (a ∷ b ∷ [])) k H O A cρ κ≃ = ≃-trans (κ≃ _ _ A) (K-≃ k
    (mono-≃ (primD-mono p) ⟨ up (atom-≃ a H O A) , ⟨ up (atom-≃ b H O A) , ptt ⟩ ⟩))
  lift-sem (case {L} {M₁} {M₂} a m₁ m₂) {n} {d} {σ} {ρ} k {κ} H O A cρ κ≃ =
    ≃-trans (checked-at (fits-< _ (fits {d} _ H)))
    (≃-trans (𝒞-≃ {F = λ X → ⟦ lift n (suc d) m₁ ⟧ᴷ[ T ] n (σ [ d ↦ X ]) κ} {λ X → K⟨ k ⟩ (⟦ M₁ ⟧[ T' ] (X • ρ))}
                   {λ X → ⟦ lift n (suc d) m₂ ⟧ᴷ[ T ] n (σ [ d ↦ X ]) κ} {λ X → K⟨ k ⟩ (⟦ M₂ ⟧[ T' ] (X • ρ))}
                   (atom-≃ a H O A)
                   (λ v V cV → lift-sem m₁ k (⊔ˡ (height m₁) _ H') (scope-ext O) (agree-ext A)
                                 (Con-• (≈⇒Con cV) cρ) (λ D σ' A' → κ≃ D σ' (weak A')))
                   (λ v V cV → lift-sem m₂ k (⊔ʳ _ (height m₂) H') (scope-ext O) (agree-ext A)
                                 (Con-• (≈⇒Con cV) cρ) (λ D σ' A' → κ≃ D σ' (weak A'))))
             (≃-sym (case-law k {F₁ = λ X → ⟦ M₁ ⟧[ T' ] (X • ρ)} {λ X → ⟦ M₂ ⟧[ T' ] (X • ρ)}
                       (Clos5-con T' TC L cρ) (mono-• M₁) (mono-• M₂))))
    where H' = fits {d} (height m₁ ⊔ height m₂) H
  lift-sem (let′ {M₁} {M₂} m₁ m₂) {n} {d} {σ} {ρ} k {κ} H O A cρ κ≃ =
    ≃-trans (lift-sem m₁ (just G) (⊔ˡ {d} (height m₁) _ H) O A cρ κ₁≃)
            (≃-sym (let-law k {F = λ X → ⟦ M₂ ⟧[ T' ] (X • ρ)} (Clos5-con T' TC M₁ cρ) (mono-• M₂)))
    where
    H₂ = fits {d} _ (⊔ʳ (height m₁) _ H)
    G = λ X → K⟨ k ⟩ (⟦ M₂ ⟧[ T' ] (X • ρ))
    κ₁≃ : ∀ D σ' → Agree d σ' ρ
      → checked n d (⋆ ⟨ Λ ⟨ (λ X → ⟦ lift n (suc d) m₂ ⟧ᴷ[ T ] n (σ' [ d ↦ X ]) κ) , ptt ⟩ , ⟨ D , ptt ⟩ ⟩)
        ≃ K⟨ just G ⟩ D
    κ₁≃ D σ' A' = ≃-trans (checked-at (fits-< _ H₂))
      (⋆-≃ (Λ-≃ {λ X → ⟦ lift n (suc d) m₂ ⟧ᴷ[ T ] n (σ' [ d ↦ X ]) κ} {G} λ V _ cV → lift-sem m₂ k H₂ (scope-ext O) (agree-ext A') (Con-• (≈⇒Con cV) cρ)
                              (λ D' σ'' A'' → κ≃ D' σ'' (weak A''))) ≃-refl)

{- Programs ---------------------------------------------------------------------}

table-lift : ∀ {ds} (ms : All Mon ds) k → tableᴷ (lift-defs ms) k ≃ table ds k
table-lift [] k = ≃-refl
table-lift {N ∷ Ns} (m ∷ ms) k with k ≟ length (lift-defs ms) | k ≟ length Ns
... | yes _ | yes _ =
  Λ-≃ λ X _ cX → Λ-≃ λ Y _ cY → lift-sem (table-lift ms) (table-con Ns) m nothing ≤-refl
    (scope-frame (mem X) (mem Y)) (agree-frame (mem X) (mem Y))
    (Con-• (≈⇒Con cY) (Con-• (≈⇒Con cX) (λ _ → Con-⌈⌉ ω))) (λ _ _ _ → ≃-refl)
... | no _ | no _ = table-lift ms k
... | yes k≡ | no k≢ = ⊥-elim (k≢ (trans k≡ (length-lift-defs ms)))
... | no k≢ | yes k≡ = ⊥-elim (k≢ (trans k≡ (sym (length-lift-defs ms))))

lift-program-correct : ∀ P (mp : MonProgram P) → ⟦ lift-program P mp ⟧ᴷₚ ≃ ⟦ P ⟧ₚ
lift-program-correct (program ds M) ⟨ ms , m ⟩ =
  lift-sem (table-lift ms) (table-con ds) m nothing ≤-refl (λ x _ → ≃-refl) (agree λ x ())
    (λ _ → Con-⌈⌉ ω) (λ _ _ _ → ≃-refl)

{- the whole compiler, into Imp -}
open Into ⟦_⟧ᴷₚ lift-program-correct public

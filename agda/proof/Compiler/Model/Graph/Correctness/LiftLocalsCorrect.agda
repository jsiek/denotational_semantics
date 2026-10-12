{-

  Correctness of lift locals (monadic Clos5 → Imp,
  Compile/LiftLocals.agda) against the direct semantics of Imp
  (Sem/ImpDirect.agda), an alternative to the main proof against the
  continuation-passing semantics (LiftLocalsCorrectK.agda): the meaning
  of the Imp program is that of the Clos5 program.

    lift-program-correct : ⟦ lift-program P mp ⟧ₚ ≃ ⟦ P ⟧ₚ

  The invariant, at depth d, is that of LiftLocalsCommon.agda: the store
  agrees with the environment (Agree) and the variables from d on are
  out of scope (Scope). Running lift n d m then

  - gives the meaning of m (lift-sem), and
  - leaves a store that still agrees with the environment at depth d,
    when m has a value (Out). As in the operational proofs, this is
    stated relative to the environment, not to the store m started
    with, so coming back from under a binder only forgets the top slot
    (weak): whatever the body wrote at depth d + 1 or deeper is no
    longer looked at. The condition that m has a value is inherent: the
    slots after a case are empty when the scrutinee is not an
    injection, and those after a let when its right-hand side has no
    value; and the store of a let or case collects the slots from the
    runs of its body that have a value (Sem/ImpDirect.agda).

  No continuity is needed: the operators of let and case on
  both sides are related by congruence.

-}

open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.Domain
open import proof.Framework.GraphModel.Ops
open import proof.Compiler.Model.Graph.Prim
open import Compiler.Lang.Clos5 using (program)
open import Compiler.Lang.Mon
open import Compiler.Compile.LiftLocals using (lift-atom; lift; height; lift-defs; lift-program)
open import Compiler.Model.Graph.Sem.Clos5Iswim using (Table; ⟦_⟧[_]; ⟦_⟧₊[_]; table; ⟦_⟧ₚ)
open import proof.Compiler.Model.Graph.Sem.ImpDirect
  using (Store; _[_↦_]; 𝒜; caseₛ; letₛ)
  renaming (⟦_⟧[_] to ℐ⟦_⟧[_]; table to tableᵢ; ⟦_⟧ₚ to ℐ⟦_⟧ₚ)
open import proof.Compiler.Model.Graph.Correctness.GlobalizeCorrect
  using (nthD-≃; app-≃; pair-≃; car-≃; cdr-≃; prim-≃; ΛΛ-≃)
open import proof.Compiler.Model.Graph.Correctness.ConcretizeCorrect
  using (⋆-≃; 𝒯-≃; proj-≃; inl-≃; inr-≃; 𝒞-≃)
open import proof.Compiler.Model.Graph.Correctness.RCOCorrect using (strict-≃; Λ-≃; ne-mem)
open import proof.Compiler.Model.Graph.Correctness.LiftLocalsCommon
open import proof.Framework.GraphModel.Env using (Env)

open import Data.Nat using (ℕ; suc; _+_; _⊔_; _≤_; _≟_; _<?_)
open import Data.Nat.Properties using (≤-refl)
open import Data.List using (_∷_; length)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Function using (case_of_)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Level using () renaming (lift to up)
open import Relation.Binary.PropositionalEquality using (sym; trans)
open import Relation.Nullary using (yes; no)

module proof.Compiler.Model.Graph.Correctness.LiftLocalsCorrect where

{- The invariant ---------------------------------------------------------------------}

{- the store that r leaves agrees with ρ, if r has a value -}
Out : ℕ → Env Value → 𝒫 Value × Store → Set
Out d ρ r = nonempty (proj₁ r) → Agree d (proj₂ r) ρ

out-case : ∀ {d ρ A E₁ E₂} → (∀ X → Out d ρ (E₁ X)) → (∀ X → Out d ρ (E₂ X))
  → Out d ρ (caseₛ A E₁ E₂)
out-case R₁ R₂ ne = agree λ x x<d → ⟨
    (λ { u (inj₁ ⟨ _ , ⟨ _ , ⟨ _ , ⟨ ⟨ u∈ , ne' ⟩ , _ ⟩ ⟩ ⟩ ⟩) → proj₁ (at (R₁ _ ne') x x<d) u u∈
          ; u (inj₂ ⟨ _ , ⟨ _ , ⟨ _ , ⟨ ⟨ u∈ , ne' ⟩ , _ ⟩ ⟩ ⟩ ⟩) → proj₁ (at (R₂ _ ne') x x<d) u u∈ })
  , (case ne of λ { ⟨ w , inj₁ ⟨ v , ⟨ V , ⟨ l∈ , ⟨ w∈ , c ⟩ ⟩ ⟩ ⟩ ⟩ u u∈ →
            inj₁ ⟨ v , ⟨ V , ⟨ l∈ , ⟨ ⟨ proj₂ (at (R₁ _ ⟨ w , w∈ ⟩) x x<d) u u∈ , ⟨ w , w∈ ⟩ ⟩ , c ⟩ ⟩ ⟩ ⟩
          ; ⟨ w , inj₂ ⟨ v , ⟨ V , ⟨ r∈ , ⟨ w∈ , c ⟩ ⟩ ⟩ ⟩ ⟩ u u∈ →
            inj₂ ⟨ v , ⟨ V , ⟨ r∈ , ⟨ ⟨ proj₂ (at (R₂ _ ⟨ w , w∈ ⟩) x x<d) u u∈ , ⟨ w , w∈ ⟩ ⟩ , c ⟩ ⟩ ⟩ ⟩ }) ⟩

out-let : ∀ {d ρ D E} → (nonempty D → ∀ X → Out d ρ (E X)) → Out d ρ (letₛ D E)
out-let R ⟨ w , ⟨ V , ⟨ ⟨ w∈ , V≢ ⟩ , ⟨ V⊆ , ne ⟩ ⟩ ⟩ ⟩ = agree λ x x<d →
  ⟨ (λ { u ⟨ U , ⟨ ⟨ ⟨ u∈ , ne' ⟩ , _ ⟩ , ⟨ U⊆ , neU ⟩ ⟩ ⟩ →
         proj₁ (at (R (ne-mem neU U⊆) (mem U) ne') x x<d) u u∈ })
  , (λ u u∈ → ⟨ V , ⟨ ⟨ ⟨ proj₂ (at (R (ne-mem ne V⊆) (mem V) ⟨ w , w∈ ⟩) x x<d) u u∈ , ⟨ w , w∈ ⟩ ⟩ , V≢ ⟩
                    , ⟨ V⊆ , ne ⟩ ⟩ ⟩) ⟩

{- ⋆ ⟨ F , D ⟩ has a value only if D does -}
⋆-strict : ∀ {F D E} → D ⊆ E → ∀ w → w ∈ ⋆ ⟨ F , ⟨ D , ptt ⟩ ⟩ → nonempty E
⋆-strict D⊆ w ⟨ V , ⟨ _ , ⟨ V⊆ , ne ⟩ ⟩ ⟩ = ne-mem ne (λ u u∈ → D⊆ u (V⊆ u u∈))

{- The pass preserves meanings ----------------------------------------------------}

module _ {T T' : Table} (TT : ∀ k → T k ≃ T' k) where

  open AtomsSame TT

  {- lift at depth d: the meaning, and a store that still agrees with ρ -}
  lift-sem : ∀ {M} (m : Mon M) {n d σ ρ} → d + height m ≤ n → Scope d ρ → Agree d σ ρ
    → proj₁ (ℐ⟦ lift n d m ⟧[ T ] n σ) ≃ ⟦ M ⟧[ T' ] ρ × Out d ρ (ℐ⟦ lift n d m ⟧[ T ] n σ)
  lift-sem (atom a) H O A = ⟨ atom-≃ a H O A , (λ _ → A) ⟩
  lift-sem (app (a ∷ b ∷ c ∷ [])) H O A =
    ⟨ app-≃ ⟨ up (atom-≃ a H O A) , ⟨ up (atom-≃ b H O A) , ⟨ up (atom-≃ c H O A) , ptt ⟩ ⟩ ⟩ , (λ _ → A) ⟩
  lift-sem (pair (a ∷ b ∷ [])) H O A =
    ⟨ pair-≃ ⟨ up (atom-≃ a H O A) , ⟨ up (atom-≃ b H O A) , ptt ⟩ ⟩ , (λ _ → A) ⟩
  lift-sem (fst (a ∷ [])) H O A = ⟨ car-≃ ⟨ up (atom-≃ a H O A) , ptt ⟩ , (λ _ → A) ⟩
  lift-sem (snd (a ∷ [])) H O A = ⟨ cdr-≃ ⟨ up (atom-≃ a H O A) , ptt ⟩ , (λ _ → A) ⟩
  lift-sem (tuple {k} {Ms} as) {ρ = ρ} H O A =
    ⟨ atoms-≃ as H O A (λ m Ds → 𝒯 m Ds ≃ 𝒯 k (⟦ Ms ⟧₊[ T' ] ρ))
                 (λ {m} eq q → ≃-trans (𝒯-≃ m (nthD-≃ _ _ eq)) q) ≃-refl
    , (λ _ → A) ⟩
  lift-sem (get {i = i} (a ∷ [])) H O A = ⟨ proj-≃ i (atom-≃ a H O A) , (λ _ → A) ⟩
  lift-sem (inl (a ∷ [])) H O A = ⟨ inl-≃ (atom-≃ a H O A) , (λ _ → A) ⟩
  lift-sem (inr (a ∷ [])) H O A = ⟨ inr-≃ (atom-≃ a H O A) , (λ _ → A) ⟩
  lift-sem (prim {p} (a ∷ b ∷ [])) H O A =
    ⟨ prim-≃ p ⟨ up (atom-≃ a H O A) , ⟨ up (atom-≃ b H O A) , ptt ⟩ ⟩ , (λ _ → A) ⟩
  lift-sem (case {M = M₁} {M₂} a m₁ m₂) {n} {d} {σ} {ρ} H O A with d <? n
  ... | no d≮n = ⊥-elim (d≮n (fits-< _ (fits {d} _ H)))
  ... | yes d<n =
    ⟨ 𝒞-≃ {F = B m₁} {λ X → ⟦ M₁ ⟧[ T' ] (X • ρ)} {B m₂} {λ X → ⟦ M₂ ⟧[ T' ] (X • ρ)}
          (atom-≃ a H O A) (λ v V _ → proj₁ (IH₁ (mem (v ∷ V)))) (λ v V _ → proj₁ (IH₂ (mem (v ∷ V))))
    , out-case {A = 𝒜 T n σ (lift-atom n d a)}
               (λ X ne → weak (proj₂ (IH₁ X) ne)) (λ X ne → weak (proj₂ (IH₂ X) ne)) ⟩
    where
    B = λ {N} (m : Mon N) X → proj₁ (ℐ⟦ lift n (suc d) m ⟧[ T ] n (σ [ d ↦ X ]))
    H' = fits {d} (height m₁ ⊔ height m₂) H
    IH₁ = λ X → lift-sem m₁ (⊔ˡ (height m₁) _ H') (scope-ext O) (agree-ext {X = X} A)
    IH₂ = λ X → lift-sem m₂ (⊔ʳ _ (height m₂) H') (scope-ext O) (agree-ext {X = X} A)
  lift-sem (let′ {M₁} {M₂} m₁ m₂) {n} {d} {σ} {ρ} H O A with d <? n
  ... | no d≮n = ⊥-elim (d≮n (fits-< _ (fits {d} (height m₂) (⊔ʳ (height m₁) _ H))))
  ... | yes d<n =
    ⟨ strict-≃ (⋆-strict {Λ ⟨ F , ptt ⟩} (λ _ w∈ → w∈))
               (⋆-strict {Λ ⟨ F' , ptt ⟩} (proj₂ (proj₁ IH₁)))
        (λ ne → ⋆-≃ (Λ-≃ {F} {F'} λ V _ _ → proj₁ (IH₂ ne (mem V))) (proj₁ IH₁))
    , out-let (λ ne X ne' → weak (proj₂ (IH₂ ne X) ne')) ⟩
    where
    IH₁ = lift-sem m₁ (⊔ˡ {d} (height m₁) _ H) O A
    σ₁ = proj₂ (ℐ⟦ lift n d m₁ ⟧[ T ] n σ)
    F = λ X → proj₁ (ℐ⟦ lift n (suc d) m₂ ⟧[ T ] n (σ₁ [ d ↦ X ]))
    F' = λ X → ⟦ M₂ ⟧[ T' ] (X • ρ)
    IH₂ = λ ne X → lift-sem m₂ (fits {d} _ (⊔ʳ (height m₁) _ H)) (scope-ext O)
      (agree-ext {X = X} (proj₂ IH₁ ne))

{- Programs ---------------------------------------------------------------------}

table-lift : ∀ {ds} (ms : All Mon ds) k → tableᵢ (lift-defs ms) k ≃ table ds k
table-lift [] k = ≃-refl
table-lift {N ∷ Ns} (m ∷ ms) k with k ≟ length (lift-defs ms) | k ≟ length Ns
... | yes _ | yes _ =
  ΛΛ-≃ λ X Y → proj₁ (lift-sem (table-lift ms) m ≤-refl (scope-frame X Y) (agree-frame X Y))
... | no _ | no _ = table-lift ms k
... | yes k≡ | no k≢ = ⊥-elim (k≢ (trans k≡ (length-lift-defs ms)))
... | no k≢ | yes k≡ = ⊥-elim (k≢ (trans k≡ (sym (length-lift-defs ms))))

lift-program-correct : ∀ P (mp : MonProgram P) → ℐ⟦ lift-program P mp ⟧ₚ ≃ ⟦ P ⟧ₚ
lift-program-correct (program ds M) ⟨ ms , m ⟩ =
  proj₁ (lift-sem (table-lift ms) m ≤-refl (λ x _ → ≃-refl) (agree λ x ()))

{- the whole compiler, into Imp -}
open Into ℐ⟦_⟧ₚ lift-program-correct public

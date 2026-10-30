{-

  Correctness of typed hoist (Clos4ᵀ → Clos5ᵀ, Compiler/Hoist.agda)
  in the graph model with errors: the pass moves the code of each
  function into the table, so it preserves meanings exactly.

  The definitions made so far (Made) have a table (madeT), each seeing
  the older ones, as the table of the program does; a term the pass
  makes means the source under any table T that agrees with it below
  the length of the table (Agr). The pass only adds definitions (ext),
  and a term made earlier is weakened, which keeps the levels of its
  references (lvl-⊑), so it means the same (wk-≃). At the end, the table
  of the program, made of the definitions weakened to the whole table,
  is madeT (close-tbl).

-}

module proof.Correctness.GraphErr.HoistCorrect where

open import proof.Framework.GraphModel.ErrorPrelude hiding (_▷_)
open import proof.Framework.GraphModel.OpsBase using (nthD)
open import proof.Framework.GraphModel.Env using (Env; _~ₑ[_]_; •-~)
open import proof.Framework.Lookup using (lvl-⊑; ⊑-len)
open import Framework.Membership using (_⊑_; here⊑; there⊑; ⊑-∋; ⊑-trans)
open import Language.Typed.Type hiding (_≟_)
import Language.Typed.Clos4 as S
open import Language.Typed.Clos5
open import Compiler.Hoist
open import Semantics.GraphErr.Typed.Ops using (getᵗ; primᵗ; projectᵠ)
open import Semantics.GraphErr.Typed.Clos4 using (kind₄) renaming (⟦_⟧ to ⟦_⟧₄; ⟦_⟧s to ⟦_⟧s₄)
open import proof.Semantics.GraphErr.Typed.Clos5
open import proof.Semantics.GraphErr.Typed.Clos2 using (getᵗ-≃; caseᵗ-≃; primᵗ-≃; projectᵗ-≃; ⌊⌋-≃)

open import Data.Empty using (⊥-elim)
open import Data.Fin using (zero; suc)
open import Data.List using (List; []; _∷_; length; replicate)
open import Data.Nat using (ℕ; _<_; _≟_)
open import Data.Nat.Properties using (n<1+n; <-≤-trans; <-irrefl; <-trans)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym)
open import Relation.Nullary using (yes; no)

EnvR : Env Value → Env Value → Set
EnvR ρ ρ' = ρ ~ₑ[ _≃_ ] ρ'

{- The table of the definitions made -------------------------------------------}

madeT : ∀ {Σ} → Made Σ → Table
madeT [] k = errcode
madeT (_▷_ {Σ} D N) k with k ≟ length Σ
... | yes _ = code₅ (madeT D) N
... | no _ = madeT D k

madeT-top : ∀ {Σ n} (D : Made Σ) (N : Code Σ n) → madeT (D ▷ N) (length Σ) ≃ code₅ (madeT D) N
madeT-top {Σ} D N with length Σ ≟ length Σ
... | yes _ = ≃-refl
... | no ne = ⊥-elim (ne refl)

madeT-old : ∀ {Σ n} (D : Made Σ) (N : Code Σ n) k → k < length Σ → madeT (D ▷ N) k ≃ madeT D k
madeT-old {Σ} D N k k< with k ≟ length Σ
... | yes refl = ⊥-elim (<-irrefl refl k<)
... | no _ = ≃-refl

{- T agrees with the table of D below its length -}
record Agr {Σ} (T : Table) (D : Made Σ) : Set where
  constructor agr
  field at : ∀ k → k < length Σ → T k ≃ madeT D k

{- the definitions of D' extend those of D -}
record Ext {Σ Σ'} (D : Made Σ) (D' : Made Σ') : Set where
  constructor ext
  field at : ∀ k → k < length Σ → madeT D' k ≃ madeT D k

agr-ext : ∀ {Σ Σ' T} {D : Made Σ} {D' : Made Σ'} → Σ ⊑ Σ' → Ext D D' → Agr T D' → Agr T D
agr-ext s e a = agr λ k k< → ≃-trans (Agr.at a k (<-≤-trans k< (⊑-len s))) (Ext.at e k k<)

ext-trans : ∀ {Σ₁ Σ₂ Σ₃} {D₁ : Made Σ₁} {D₂ : Made Σ₂} {D₃ : Made Σ₃} → Σ₁ ⊑ Σ₂ → Ext D₁ D₂ → Ext D₂ D₃ → Ext D₁ D₃
ext-trans s e₁ e₂ = ext λ k k< → ≃-trans (Ext.at e₂ k (<-≤-trans k< (⊑-len s))) (Ext.at e₁ k k<)

{- a weakened term means the same -}
wk-same : ∀ {Σ Σ' Γ A} (s : Σ ⊑ Σ') (M : Tm Σ Γ A) {T ρ} → ⟦ wk (⊑-∋ s) M ⟧[ T ] ρ ≃ ⟦ M ⟧[ T ] ρ
wk-same s M {T} = wk-≃ (⊑-∋ s) (λ f → ≃-reflexive (cong T (lvl-⊑ s f))) M (λ _ → ≃-refl)

{- The pass ------------------------------------------------------------------------}

GL : ∀ {Σ Γ A} → S.Tm Γ A → Made Σ → Set₁
GL M D = let o = glob M D in
  Ext D (Out.made o) × (∀ T → Agr T (Out.made o) → ∀ {ρ ρ'} → EnvR ρ ρ' → ⟦ M ⟧₄ ρ ≃ ⟦ Out.res o ⟧[ T ] ρ')

Sem = Env Value → 𝒫 Value

Cong₁ : (Sem → Sem) → Set₁
Cong₁ F = ∀ {E E'} → (∀ {ρ ρ'} → EnvR ρ ρ' → E ρ ≃ E' ρ') → ∀ {ρ ρ'} → EnvR ρ ρ' → F E ρ ≃ F E' ρ'

Cong₂ : (Sem → Sem → Sem) → Set₁
Cong₂ F = ∀ {E₁ E₁' E₂ E₂'} → (∀ {ρ ρ'} → EnvR ρ ρ' → E₁ ρ ≃ E₁' ρ') → (∀ {ρ ρ'} → EnvR ρ ρ' → E₂ ρ ≃ E₂' ρ')
  → ∀ {ρ ρ'} → EnvR ρ ρ' → F E₁ E₂ ρ ≃ F E₁' E₂' ρ'

gl : ∀ {Σ Γ A} (M : S.Tm Γ A) (D : Made Σ) → GL M D
gls : ∀ {Σ Γ n} (Ms : Vec (S.Tm Γ Any) n) (D : Made Σ) → let o = globs Ms D in
  Ext D (Out.made o) × (∀ T → Agr T (Out.made o) → ∀ {ρ ρ'} → EnvR ρ ρ'
    → ∀ i → nthD (⟦ Ms ⟧s₄ ρ) i ≃ nthD (⟦ Out.res o ⟧s[ T ] ρ') i)

gl₁ : ∀ {Σ Γ Γ₁ A B} (f : ∀ {Σ'} → Tm Σ' Γ₁ A → Tm Σ' Γ B) (F : Sem → Sem) → Cong₁ F
  → (∀ {Σ'} (L : Tm Σ' Γ₁ A) {T ρ} → ⟦ f L ⟧[ T ] ρ ≡ F ⟦ L ⟧[ T ] ρ)
  → (L : S.Tm Γ₁ A) (D : Made Σ) → let o = glob₁ f L D in
  Ext D (Out.made o) × (∀ T → Agr T (Out.made o) → ∀ {ρ ρ'} → EnvR ρ ρ' → F ⟦ L ⟧₄ ρ ≃ ⟦ Out.res o ⟧[ T ] ρ')
gl₁ f F cF hf L D with glob L D | gl L D
... | out s D' L' | ⟨ e , h ⟩ = ⟨ e , (λ T a ρ~ → ≃-trans (cF (h T a) ρ~) (≃-reflexive (sym (hf L')))) ⟩

gl₂ : ∀ {Σ Γ Γ₁ Γ₂ A B C} (f : ∀ {Σ'} → Tm Σ' Γ₁ A → Tm Σ' Γ₂ B → Tm Σ' Γ C) (F : Sem → Sem → Sem) → Cong₂ F
  → (∀ {Σ'} (L : Tm Σ' Γ₁ A) (M : Tm Σ' Γ₂ B) {T ρ} → ⟦ f L M ⟧[ T ] ρ ≡ F ⟦ L ⟧[ T ] ⟦ M ⟧[ T ] ρ)
  → (L : S.Tm Γ₁ A) (M : S.Tm Γ₂ B) (D : Made Σ) → let o = glob₂ f L M D in
  Ext D (Out.made o) × (∀ T → Agr T (Out.made o) → ∀ {ρ ρ'} → EnvR ρ ρ' → F ⟦ L ⟧₄ ⟦ M ⟧₄ ρ ≃ ⟦ Out.res o ⟧[ T ] ρ')
gl₂ f F cF hf L M D with glob L D | gl L D
... | out s₁ D₁ L' | ⟨ e₁ , h₁ ⟩ with glob M D₁ | gl M D₁
...   | out s₂ D₂ M' | ⟨ e₂ , h₂ ⟩ =
  ⟨ ext-trans s₁ e₁ e₂
  , (λ T a ρ~ → ≃-trans (cF (λ ρ~ → ≃-trans (h₁ T (agr-ext s₂ e₂ a) ρ~) (≃-sym (wk-same s₂ L'))) (h₂ T a) ρ~)
                        (≃-reflexive (sym (hf (wk (⊑-∋ s₂) L') M')))) ⟩

gl (S.` x) D = ⟨ ext (λ _ _ → ≃-refl) , (λ T a ρ~ → ρ~ (idx x)) ⟩
gl {Σ} (S.code N) D with glob N D | gl N D
... | out {Σ'} s D' N' | ⟨ e , h ⟩ =
  ⟨ ext (λ k k< → ≃-trans (madeT-old D' N' k (<-≤-trans k< (⊑-len s))) (Ext.at e k k<))
  , (λ T a ρ~ → ≃-sym (≃-trans (Agr.at a (length Σ') (n<1+n _)) (≃-trans (madeT-top D' N')
       (ΛΛᵐ-≃ λ X Y → ≃-sym (h (madeT D') (agr λ _ _ → ≃-refl) (λ _ → ≃-refl)))))) ⟩
gl (S.pack L M) D = gl₂ pack (λ E₁ E₂ ρ → pairᵐ ⟨ E₁ ρ , ⟨ E₂ ρ , ptt ⟩ ⟩) (λ h₁ h₂ ρ~ → pairᵐ-≃ (h₁ ρ~) (h₂ ρ~)) (λ _ _ → refl) L M D
gl (S.callc L M) D = gl₂ callc (λ E₁ E₂ ρ → binds 2 ⟨ E₁ ρ , ⟨ E₂ ρ , ptt ⟩ ⟩ callcᵈ) (λ h₁ h₂ ρ~ → callc-≃ (h₁ ρ~) (h₂ ρ~)) (λ _ _ → refl) L M D
  where open import proof.Framework.GraphModel.TypedBinders using (callcᵈ)
gl (S.lit B c) D = ⟨ ext (λ _ _ → ≃-refl) , (λ _ _ _ → ≃-refl) ⟩
gl (S.tuple {n = n} Ms) D with globs Ms D | gls Ms D
... | out s D' Ms' | ⟨ e , h ⟩ = ⟨ e , (λ T a ρ~ → 𝒯ᵐ-≃ n (h T a ρ~)) ⟩
gl (S.get i M) D = gl₁ (get i) (λ E ρ → getᵗ i (E ρ)) (λ h ρ~ → getᵗ-≃ i (h ρ~)) (λ _ → refl) M D
gl (S.inl M) D = gl₁ inl (λ E ρ → inlᵐ ⟨ E ρ , ptt ⟩) (λ h ρ~ → inlᵐ-≃ (h ρ~)) (λ _ → refl) M D
gl (S.inr M) D = gl₁ inr (λ E ρ → inrᵐ ⟨ E ρ , ptt ⟩) (λ h ρ~ → inrᵐ-≃ (h ρ~)) (λ _ → refl) M D
gl (S.case L M N) D with glob L D | gl L D
... | out s₁ D₁ L' | ⟨ e₁ , h₁ ⟩ with glob M D₁ | gl M D₁
...   | out s₂ D₂ M' | ⟨ e₂ , h₂ ⟩ with glob N D₂ | gl N D₂
...     | out s₃ D₃ N' | ⟨ e₃ , h₃ ⟩ =
  ⟨ ext-trans s₁ e₁ (ext-trans s₂ e₂ e₃)
  , (λ T a {ρ} {ρ'} ρ~ → caseᵗ-≃ {F = λ X → ⟦ M ⟧₄ (X • ρ)} {λ X → ⟦ wk (⊑-∋ s₃) M' ⟧[ T ] (X • ρ')}
       {λ X → ⟦ N ⟧₄ (X • ρ)} {λ X → ⟦ N' ⟧[ T ] (X • ρ')}
       (≃-trans (h₁ T (agr-ext s₂ e₂ (agr-ext s₃ e₃ a)) ρ~) (≃-sym (wk-same (⊑-trans s₂ s₃) L')))
       (λ _ _ _ _ → ≃-trans (h₂ T (agr-ext s₃ e₃ a) (•-~ _≃_ ρ~ ≃-refl)) (≃-sym (wk-same s₃ M')))
       (λ _ _ _ _ → h₃ T a (•-~ _≃_ ρ~ ≃-refl))) ⟩
gl (S.prim p L M) D = gl₂ (prim p) (λ E₁ E₂ ρ → primᵗ p (E₁ ρ) (E₂ ρ)) (λ h₁ h₂ ρ~ → primᵗ-≃ p (h₁ ρ~) (h₂ ρ~)) (λ _ _ → refl) L M D
gl (S.let′ M N) D = gl₂ let′ (λ E₁ E₂ ρ → E₁ ρ ≫= λ X → E₂ (X • ρ))
  (λ {E₁} {E₁'} {E₂} {E₂'} h₁ h₂ {ρ} {ρ'} ρ~ → ≫=-≃ {F = λ X → E₂ (X • ρ)} {λ X → E₂' (X • ρ')} (h₁ ρ~)
     λ _ _ → h₂ (•-~ _≃_ ρ~ (⌊⌋-≃ (h₁ ρ~)))) (λ _ _ → refl) M N D
gl (S.inject G M) D = gl₁ (inject G) (λ E → E) (λ h → h) (λ _ → refl) M D
gl (S.project t M) D = gl₁ (project t) (λ E ρ → projectᵠ kind₄ t (E ρ)) (λ h ρ~ → projectᵗ-≃ kind₄ t (h ρ~)) (λ _ → refl) M D

gls [] D = ⟨ ext (λ _ _ → ≃-refl) , (λ _ _ _ ()) ⟩
gls (M ∷ Ms) D with glob M D | gl M D
... | out s₁ D₁ M' | ⟨ e₁ , h₁ ⟩ with globs Ms D₁ | gls Ms D₁
...   | out s₂ D₂ Ms' | ⟨ e₂ , h₂ ⟩ =
  ⟨ ext-trans s₁ e₁ e₂
  , (λ { T a ρ~ zero → ≃-trans (h₁ T (agr-ext s₂ e₂ a) ρ~) (≃-sym (wk-same s₂ M'))
       ; T a ρ~ (suc i) → h₂ T a ρ~ i }) ⟩

{- The program ----------------------------------------------------------------------}

close-tbl : ∀ {Σ Σ'} (D : Made Σ') (s : Σ' ⊑ Σ) k → tbl code₅ (close D s) k ≃ madeT D k
close-tbl [] s k = ≃-refl
close-tbl (_▷_ {Σ'} D N) s k with k ≟ length Σ'
... | yes _ = ΛΛᵐ-≃ λ X Y → wk-≃ (⊑-∋ s') (λ f → ≃-trans (≃-reflexive (cong (tbl code₅ (close D s')) (lvl-⊑ s' f)))
                                                           (close-tbl D s' (lvl f))) N (λ _ → ≃-refl)
  where s' = ⊑-trans (there⊑ here⊑) s
... | no _ = close-tbl D (⊑-trans (there⊑ here⊑) s) k

hoist-correct : ∀ (M : S.Tm [] Any) → ⟦ M ⟧₄ ρ₀ ≃ ⟦ hoist M ⟧₅
hoist-correct M with glob M [] | gl M []
... | out s D M' | ⟨ _ , h ⟩ = h (tbl code₅ (close D here⊑)) (agr λ k _ → close-tbl D here⊑ k) (λ _ → ≃-refl)

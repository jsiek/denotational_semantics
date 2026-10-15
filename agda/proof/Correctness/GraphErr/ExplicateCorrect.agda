{-

  Correctness of typed explicate control (Impᵀ → CFGᵀ, Compiler/Explicate.agda)
  in the graph model with errors, against the continuation-passing
  semantics of Impᵀ (Semantics/GraphErr/Typed/{Imp,CFG}.agda):

    explicate-correct : ⟦ P ⟧ᵢ ≃ ⟦ explicate P ⟧ᶜ

  As in Untyped/proof/Correctness/GraphErr/ExplicateCorrect.agda:
  explicate-assign e p k means e run with the continuation that binds
  the next slot and runs k (cps), and explicate-tail e means e run with
  the identity (tail); each case is a congruence. The pass only adds
  blocks (Ext), and a label made earlier, weakened, finds the same block
  (blocks-ext), so a jump to a join point means its block. Labels are
  typed, so a jump never misses; a slot is the environment's, so there
  are no frame checks.

-}

module proof.Correctness.GraphErr.ExplicateCorrect where

open import proof.Framework.GraphModel.ErrorPrelude hiding (_▷_)
open import Framework.Membership using (_⊑_; here⊑; there⊑; ⊑-∋; ⊑-trans)
open import proof.Semantics.GraphErr.Typed.Clos2 using (caseᵗ-≃)
open import proof.Semantics.GraphErr.Typed.Clos5 using (tm-≃; tbl-map; map-id)
open import proof.Semantics.GraphErr.Typed.Imp using (letᵗ-≃)
open import Semantics.GraphErr.Typed.Imp using (⟦_⟧ᴷ; codeᵢ; ⟦_⟧ᵢ; 𝒮; 𝒜; Table; tbl)
open import Semantics.GraphErr.Typed.CFG using (⟦_⟧ᵗ; blocks; drop; run; codeᶜ; ⟦_⟧ᶜ; letᵗ)
open import Semantics.GraphErr.Typed.Ops using (init)
open import Language.Typed.Type hiding (_≟_)
import Language.Typed.Mon as M
import Language.Typed.Imp as I
open import Language.Typed.CFG
open import Compiler.Explicate

open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_) renaming (map to All-map)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym)
open import Function using (_$_)

{- Blocks only grow ------------------------------------------------------------------}

data Ext {Σ} : ∀ {Bs Bs'} → Bs ⊑ Bs' → Blocks Σ Bs → Blocks Σ Bs' → Set where
  ext-here : ∀ {Bs} {bs : Blocks Σ Bs} → Ext here⊑ bs bs
  ext-there : ∀ {Bs Bs' Δ} {g : Bs ⊑ Bs'} {bs bs'} {t : Tail Σ Bs' Δ} → Ext g bs bs' → Ext (there⊑ g) bs (bs' ▷ t)

ext-trans : ∀ {Σ B₁ B₂ B₃} {g : B₁ ⊑ B₂} {g' : B₂ ⊑ B₃} {b₁ : Blocks Σ B₁} {b₂ b₃} → Ext g b₁ b₂ → Ext g' b₂ b₃ → Ext (⊑-trans g g') b₁ b₃
ext-trans e ext-here = e
ext-trans e (ext-there e') = ext-there (ext-trans e e')

blocks-ext : ∀ {Σ Bs Bs'} {g : Bs ⊑ Bs'} {bs : Blocks Σ Bs} {bs'} → Ext g bs bs' → ∀ {Δ} (l : Bs ∋ Δ) T ρ
  → blocks bs' T (⊑-∋ g l) ρ ≡ blocks bs T l ρ
blocks-ext ext-here l T ρ = refl
blocks-ext (ext-there e) l T ρ = blocks-ext e l T ρ

{- The pass --------------------------------------------------------------------------}

module _ {T T' : Table} (TT : ∀ k → T k ≃ T' k) where

  𝒮-≃ : ∀ {Σ Δ A} (s : I.Simple Σ Δ A) ρ → 𝒮 s T ρ ≃ 𝒮 s T' ρ
  𝒮-≃ s ρ = tm-≃ TT M.⌜ Semantics.GraphErr.Typed.Imp.⌞ s ⌟ ⌝ (λ _ → ≃-refl)

  𝒜-≃ : ∀ {Σ Δ A} (a : I.Atm Σ Δ A) ρ → 𝒜 a T ρ ≃ 𝒜 a T' ρ
  𝒜-≃ a ρ = tm-≃ TT M.⌜ a ⌝ᵃ (λ _ → ≃-refl)

  {- explicate-assign e p k: e, then bind the next slot and run k -}
  CPS : ∀ {Σ Bs Δ Δ' A} → I.Exp Σ Δ A → Δ' ⊑ Δ → Tail Σ Bs (A ∷ Δ') → Blocks Σ Bs → Set₁
  CPS e p k bs = let o = explicate-assign e p k bs in
    Ext (Out.grows o) bs (Out.made o) × (∀ ρ κ → (∀ D → κ D ≃ letᵗ D (λ X → ⟦ k ⟧ᵗ T' (blocks bs T') (X • drop p ρ)))
      → ⟦ e ⟧ᴷ T ρ κ ≃ ⟦ Out.tail o ⟧ᵗ T' (blocks (Out.made o) T') ρ)

  {- explicate-tail e: e, then return -}
  TAIL : ∀ {Σ Bs Δ} → I.Exp Σ Δ Any → Blocks Σ Bs → Set₁
  TAIL e bs = let o = explicate-tail e bs in
    Ext (Out.grows o) bs (Out.made o) × (∀ ρ → ⟦ e ⟧ᴷ T ρ (λ D → D) ≃ ⟦ Out.tail o ⟧ᵗ T' (blocks (Out.made o) T') ρ)

  cps : ∀ {Σ Bs Δ Δ' A} (e : I.Exp Σ Δ A) (p : Δ' ⊑ Δ) (k : Tail Σ Bs (A ∷ Δ')) bs → CPS e p k bs
  cps (I.simple s) p k bs = ⟨ ext-here , (λ ρ κ h → ≃-trans (h _) (letᵗ-≃ {F = λ X → ⟦ k ⟧ᵗ T' (blocks bs T') (X • drop p ρ)} {λ X → ⟦ k ⟧ᵗ T' (blocks bs T') (X • drop p ρ)}
                                              (𝒮-≃ s ρ) (λ _ _ _ _ → ≃-refl))) ⟩
  cps (I.assign e₁ e₂) p k bs with explicate-assign e₂ (there⊑ p) k bs | cps e₂ (there⊑ p) k bs
  ... | out g bs₁ t | ⟨ x₂ , h₂ ⟩ with explicate-assign e₁ here⊑ t bs₁ | cps e₁ here⊑ t bs₁
  ...   | out g' bs₂ t' | ⟨ x₁ , h₁ ⟩ =
    ⟨ ext-trans x₂ x₁ , (λ ρ κ h → h₁ ρ _ λ D → letᵗ-≃ {F = λ X → ⟦ e₂ ⟧ᴷ T (X • ρ) κ} {λ X → ⟦ t ⟧ᵗ T' (blocks bs₁ T') (X • ρ)}
                                                     ≃-refl λ V _ _ _ → h₂ (mem V • ρ) κ h) ⟩
  cps (I.case a e₁ e₂) p k bs with explicate-assign e₁ (there⊑ p) (goto Z) (bs ▷ k) | cps e₁ (there⊑ p) (goto Z) (bs ▷ k)
  ... | out g₁ bs₁ t₁ | ⟨ x₁ , h₁ ⟩
      with explicate-assign e₂ (there⊑ p) (goto (⊑-∋ (there⊑ g₁) Z)) (bs₁ ▷ t₁) | cps e₂ (there⊑ p) (goto (⊑-∋ (there⊑ g₁) Z)) (bs₁ ▷ t₁)
  ...   | out g₂ bs₂ t₂ | ⟨ x₂ , h₂ ⟩ =
    ⟨ ext-there (ext-trans (ext-there (ext-trans (ext-there ext-here) x₁)) x₂)
    , (λ ρ κ h → caseᵗ-≃ {F = λ X → ⟦ e₁ ⟧ᴷ T (X • ρ) κ} {λ X → blocks (bs₂ ▷ t₂) T' (⊑-∋ (there⊑ g₂) Z) (X • ρ)}
                         {λ X → ⟦ e₂ ⟧ᴷ T (X • ρ) κ} {λ X → blocks (bs₂ ▷ t₂) T' Z (X • ρ)} (𝒜-≃ a ρ)
         (λ V _ _ _ → ≃-trans (h₁ (mem V • ρ) κ h) (≃-reflexive (sym (blocks-ext x₂ Z T' (mem V • ρ)))))
         (λ V _ _ _ → h₂ (mem V • ρ) κ λ D → ≃-trans (h D)
            (letᵗ-≃ {F = λ Y → ⟦ k ⟧ᵗ T' (blocks bs T') (Y • drop p ρ)} {λ Y → blocks bs₁ T' (⊑-∋ g₁ Z) (Y • drop p ρ)} ≃-refl
               λ W _ _ _ → ≃-reflexive (sym (blocks-ext x₁ Z T' (mem W • drop p ρ)))))) ⟩

  tail : ∀ {Σ Bs Δ} (e : I.Exp Σ Δ Any) (bs : Blocks Σ Bs) → TAIL e bs
  tail (I.simple s) bs = ⟨ ext-here , (λ ρ → 𝒮-≃ s ρ) ⟩
  tail (I.assign e₁ e₂) bs with explicate-tail e₂ bs | tail e₂ bs
  ... | out g bs₁ t | ⟨ x₂ , h₂ ⟩ with explicate-assign e₁ here⊑ t bs₁ | cps e₁ here⊑ t bs₁
  ...   | out g' bs₂ t' | ⟨ x₁ , h₁ ⟩ =
    ⟨ ext-trans x₂ x₁ , (λ ρ → h₁ ρ _ λ D → letᵗ-≃ {F = λ X → ⟦ e₂ ⟧ᴷ T (X • ρ) λ D → D} {λ X → ⟦ t ⟧ᵗ T' (blocks bs₁ T') (X • ρ)}
                                                 ≃-refl λ V _ _ _ → h₂ (mem V • ρ)) ⟩
  tail (I.case a e₁ e₂) bs with explicate-tail e₁ bs | tail e₁ bs
  ... | out g₁ bs₁ t₁ | ⟨ x₁ , h₁ ⟩ with explicate-tail e₂ (bs₁ ▷ t₁) | tail e₂ (bs₁ ▷ t₁)
  ...   | out g₂ bs₂ t₂ | ⟨ x₂ , h₂ ⟩ =
    ⟨ ext-there (ext-trans (ext-there x₁) x₂)
    , (λ ρ → caseᵗ-≃ {F = λ X → ⟦ e₁ ⟧ᴷ T (X • ρ) λ D → D} {λ X → blocks (bs₂ ▷ t₂) T' (⊑-∋ (there⊑ g₂) Z) (X • ρ)}
                     {λ X → ⟦ e₂ ⟧ᴷ T (X • ρ) λ D → D} {λ X → blocks (bs₂ ▷ t₂) T' Z (X • ρ)} (𝒜-≃ a ρ)
         (λ V _ _ _ → ≃-trans (h₁ (mem V • ρ)) (≃-reflexive (sym (blocks-ext x₂ Z T' (mem V • ρ)))))
         (λ V _ _ _ → h₂ (mem V • ρ))) ⟩

  body-sem : ∀ {Σ Δ} (e : I.Exp Σ Δ Any) ρ → ⟦ e ⟧ᴷ T ρ (λ D → D) ≃ run (explicate-body e) T' ρ
  body-sem e ρ with explicate-tail e [] | tail e []
  ... | out _ bs t | ⟨ _ , h ⟩ = h ρ

{- Programs ------------------------------------------------------------------------------}

explicate-correct : ∀ (P : I.Program) → ⟦ P ⟧ᵢ ≃ ⟦ explicate P ⟧ᶜ
explicate-correct (I.program {Σ} ds e) = body-sem TT e (λ _ → init)
  where
  TT : ∀ k → tbl (codeᵢ {Σ}) ds k ≃ tbl (codeᶜ {Σ}) (All-map explicate-body ds) k
  TT k = ≃-trans (≃-reflexive (cong (λ es → tbl codeᵢ es k) (sym (map-id ds)))) $
    tbl-map {c = codeᵢ {Σ}} {codeᶜ {Σ}} (λ _ → Data.Unit.⊤) (λ d → d) explicate-body (λ _ → Data.Unit.tt)
      (λ TT' _ d → ΛΛᵐ-≃ λ X Y → body-sem TT' d _) ds k
    where import Data.Unit

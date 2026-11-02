{-

  Correctness of explicate control (Impμ → CFGμ,
  Mu/Compiler/Explicate.agda) in the graph model, as for the typed pass
  (proof/Correctness/Graph/ExplicateCorrect.agda): the CFGμ program
  (Mu/Semantics/GraphModel/CFG.agda) means what the Impμ program does
  (Mu/Semantics/GraphModel/Imp.agda, continuation-passing).

  explicate-assign e p k bs is e in continuation-passing style, as the
  semantics of Impμ is: its tail, with its blocks, means e run with the
  continuation that assigns the next slot of the frame cut by p and runs
  k with the blocks bs (asg); explicate-tail e means e run with the
  continuation that returns the value. Each case is a congruence; a case
  passes its continuation to its branches, which in CFGμ reach it
  through the join point, the block that holds k. A label made earlier
  means the same with the blocks added after it (Ext, ext-at).

-}

module Mu.proof.Correctness.GraphModel.ExplicateCorrect where

open import proof.Framework.GraphModel.Prelude
open import proof.Framework.GraphModel.Ops
open import Framework.Membership using (_⊑_; here⊑; there⊑; ⊑-∋; ⊑-trans)
open import Mu.Language.Type
import Mu.Language.Imp as I
open import Mu.Language.CFG
open import Mu.Compiler.Explicate
open import Mu.Semantics.GraphModel.Ops using (Table; tables)
open import Mu.proof.Semantics.GraphModel.CFG using (⟦_⟧ᵗ; blocks; run; drop; 𝒮-≃; 𝒜)
  renaming (code′ to codeᶜ; table to tableᶜ; ⟦_⟧ₚ to ⟦_⟧ᶜ)
open import Mu.Semantics.GraphModel.Imp using (⟦_⟧ᴷ) renaming (code′ to codeᵢ; table to tableᵢ; ⟦_⟧ₚ to ⟦_⟧ᵢ)
open import Mu.proof.Semantics.GraphModel.Binders using (let-≃; case-≃)
open import Mu.Framework.AllUtil using (All; []; _∷_) renaming (map to All-map)

open import Data.List using (List; []; _∷_; length)
open import Data.Nat using (ℕ; _≟_)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong-app)
open import Relation.Nullary using (yes; no)

{- the continuations of Impμ ------------------------------------------------------------}

κ-≃ : ∀ {Σ Δ A} (e : I.Exp Σ Δ A) {T : Table Σ} {σ} {κ κ' : 𝒫 Value → 𝒫 Value} → (∀ D → κ D ≃ κ' D) → ⟦ e ⟧ᴷ T σ κ ≃ ⟦ e ⟧ᴷ T σ κ'
κ-≃ (I.simple s) h = h _
κ-≃ (I.assign e₁ e₂) {T} {σ} h = κ-≃ e₁ λ D → let-≃ (≃-refl {D = D}) λ X _ _ → κ-≃ e₂ {T = T} {X • σ} h
κ-≃ (I.case a e₁ e₂) {T} {σ} h =
  case-≃ (≃-refl {D = 𝒜 a T σ}) (λ X _ _ → κ-≃ e₁ {T = T} {X • σ} h) (λ X _ _ → κ-≃ e₂ {T = T} {X • σ} h)

{- blocks that extend others -----------------------------------------------------------}

data Ext {Σ R} : ∀ {Bs Bs'} → Bs ⊑ Bs' → Blocks Σ R Bs → Blocks Σ R Bs' → Set where
  here : ∀ {Bs} {bs : Blocks Σ R Bs} → Ext here⊑ bs bs
  there : ∀ {Bs Bs' Δ g bs bs'} {t : Tail Σ R Bs' Δ} → Ext {Bs = Bs} g bs bs' → Ext (there⊑ g) bs (bs' ▷ t)

ext-trans : ∀ {Σ R Bs Bs' Bs''} {g : Bs ⊑ Bs'} {g' : Bs' ⊑ Bs''} {bs bs' bs''}
  → Ext {Σ} {R} g bs bs' → Ext g' bs' bs'' → Ext (⊑-trans g g') bs bs''
ext-trans e here = e
ext-trans e (there e') = there (ext-trans e e')

ext-at : ∀ {Σ R Bs Bs'} {g : Bs ⊑ Bs'} {bs : Blocks Σ R Bs} {bs' : Blocks Σ R Bs'} {T : Table Σ} → Ext g bs bs' → ∀ {Δ} (l : Bs ∋ Δ)
  → blocks bs T l ≡ blocks bs' T (⊑-∋ g l)
ext-at here l = refl
ext-at (there e) l = ext-at e l

{- The pass preserves meanings -----------------------------------------------------------}

module _ {Σ R} {T T' : Table Σ} (TT : ∀ {s} (f : Σ ∋ s) → T f ≃ T' f) where

  {- assign the next slot of the frame cut by p, then k with the blocks bs -}
  asg : ∀ {Bs Δ Δ' A} → Δ' ⊑ Δ → Tail Σ R Bs (A ∷ Δ') → Blocks Σ R Bs → Env Value → 𝒫 Value → 𝒫 Value
  asg p k bs σ D = ⋆ ⟨ Λ ⟨ (λ X → ⟦ k ⟧ᵗ T' (blocks bs T') (X • drop p σ)) , ptt ⟩ , ⟨ D , ptt ⟩ ⟩

  Good : ∀ {Bs Δ} → (Env Value → 𝒫 Value) → Blocks Σ R Bs → Out Σ R Bs Δ → Set₁
  Good F bs (out g bs' t) = Ext g bs bs' × (∀ σ → F σ ≃ ⟦ t ⟧ᵗ T' (blocks bs' T') σ)

  cps : ∀ {Bs Δ Δ' A} (e : I.Exp Σ Δ A) (p : Δ' ⊑ Δ) (k : Tail Σ R Bs (A ∷ Δ')) (bs : Blocks Σ R Bs)
    → Good (λ σ → ⟦ e ⟧ᴷ T σ (asg p k bs σ)) bs (explicate-assign e p k bs)
  cps (I.simple s) p k bs = ⟨ here , (λ σ → ⋆-≃ (≃-refl {D = Λ ⟨ (λ X → ⟦ k ⟧ᵗ T' (blocks bs T') (X • drop p σ)) , ptt ⟩}) (𝒮-≃ TT s σ)) ⟩
  cps (I.assign e₁ e₂) p k bs with explicate-assign e₂ (there⊑ p) k bs | cps e₂ (there⊑ p) k bs
  ... | out g bs₁ t | ⟨ x₂ , h₂ ⟩ with explicate-assign e₁ here⊑ t bs₁ | cps e₁ here⊑ t bs₁
  ...   | out g' bs₂ t₁ | ⟨ x₁ , h₁ ⟩ =
    ⟨ ext-trans x₂ x₁ , (λ σ → ≃-trans (κ-≃ e₁ λ D → let-≃ (≃-refl {D = D}) λ X _ _ → h₂ (X • σ)) (h₁ σ)) ⟩
  cps (I.case a e₁ e₂) p k bs with explicate-assign e₁ (there⊑ p) (goto Z) (bs ▷ k) | cps e₁ (there⊑ p) (goto Z) (bs ▷ k)
  ... | out g₁ bs₁ t₁ | ⟨ x₁ , h₁ ⟩
      with explicate-assign e₂ (there⊑ p) (goto (⊑-∋ (there⊑ g₁) Z)) (bs₁ ▷ t₁)
         | cps e₂ (there⊑ p) (goto (⊑-∋ (there⊑ g₁) Z)) (bs₁ ▷ t₁)
  ...   | out g₂ bs₂ t₂ | ⟨ x₂ , h₂ ⟩ =
    ⟨ there (ext-trans (there (ext-trans (there here) x₁)) x₂)
    , (λ σ → case-≃ (𝒜≃ a σ) (λ X _ _ → ≃-trans (h₁ (X • σ)) (≃-reflexive (cong-app (ext-at x₂ Z) _)))
        (λ X _ _ → ≃-trans (κ-≃ e₂ λ D →
           ≃-reflexive (cong (λ F → ⋆ ⟨ Λ ⟨ (λ X → F (X • drop p σ)) , ptt ⟩ , ⟨ D , ptt ⟩ ⟩) (ext-at x₁ Z))) (h₂ (X • σ)))) ⟩
    where
    𝒜≃ : ∀ {Δ A} (a : I.Atm Σ Δ A) σ → 𝒜 a T σ ≃ 𝒜 a T' σ
    𝒜≃ a σ = 𝒮-≃ TT (I.atm a) σ

  tl : ∀ {Bs Δ} (e : I.Exp Σ Δ R) (bs : Blocks Σ R Bs) → Good (λ σ → ⟦ e ⟧ᴷ T σ (λ D → D)) bs (explicate-tail e bs)
  tl (I.simple s) bs = ⟨ here , 𝒮-≃ TT s ⟩
  tl (I.assign e₁ e₂) bs with explicate-tail e₂ bs | tl e₂ bs
  ... | out g bs₁ t | ⟨ x₂ , h₂ ⟩ with explicate-assign e₁ here⊑ t bs₁ | cps e₁ here⊑ t bs₁
  ...   | out g' bs₂ t₁ | ⟨ x₁ , h₁ ⟩ =
    ⟨ ext-trans x₂ x₁ , (λ σ → ≃-trans (κ-≃ e₁ λ D → let-≃ (≃-refl {D = D}) λ X _ _ → h₂ (X • σ)) (h₁ σ)) ⟩
  tl (I.case a e₁ e₂) bs with explicate-tail e₁ bs | tl e₁ bs
  ... | out g₁ bs₁ t₁ | ⟨ x₁ , h₁ ⟩ with explicate-tail e₂ (bs₁ ▷ t₁) | tl e₂ (bs₁ ▷ t₁)
  ...   | out g₂ bs₂ t₂ | ⟨ x₂ , h₂ ⟩ =
    ⟨ there (ext-trans (there x₁) x₂)
    , (λ σ → case-≃ (𝒮-≃ TT (I.atm a) σ) (λ X _ _ → ≃-trans (h₁ (X • σ)) (≃-reflexive (cong-app (ext-at x₂ Z) _)))
        (λ X _ _ → h₂ (X • σ))) ⟩

  body-≃ : ∀ {Δ} (e : I.Exp Σ Δ R) σ → ⟦ e ⟧ᴷ T σ (λ D → D) ≃ run (explicate-body e) T' σ
  body-≃ e σ with explicate-tail e [] | tl e []
  ... | out _ bs t | ⟨ _ , h ⟩ = h σ

{- Programs ------------------------------------------------------------------------------}

table-explicate : ∀ {Σ ss} (ds : All (λ s → I.Exp Σ (Args s) (DSig.cod s)) ss) {s} (f : Σ ∋ s)
  → tables codeᵢ ds f ≃ tables codeᶜ (All-map explicate-body ds) f
table-explicate [] f = ≃-refl
table-explicate {ss = _ ∷ ss} (d ∷ ds) f with lvl f ≟ length ss
... | yes _ = ΛΛ-≃ λ X Y → body-≃ (table-explicate ds) d _
... | no _ = table-explicate ds f

explicate-correct : ∀ {A} (P : I.Program A) → ⟦ P ⟧ᵢ ≃ ⟦ explicate P ⟧ᶜ
explicate-correct (I.program ds e) = body-≃ (table-explicate ds) e _

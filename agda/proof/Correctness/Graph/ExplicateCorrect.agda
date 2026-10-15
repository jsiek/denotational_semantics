{-

  Correctness of typed explicate control (Impᵀ → CFGᵀ,
  Compiler/Explicate.agda) in the graph model: the CFGᵀ program
  (Semantics/Graph/Typed/CFG.agda) means what the Impᵀ program does
  (Semantics/Graph/Typed/Imp.agda, continuation-passing).

  explicate-assign e p k bs is e in continuation-passing style, as the
  semantics of Impᵀ is: its tail, with its blocks, means e run with the
  continuation that assigns the next slot of the frame cut by p and runs
  k with the blocks bs (asg); explicate-tail e means e run with the
  continuation that returns the value. Each case is a congruence; a case
  passes its continuation to its branches, which in CFGᵀ reach it
  through the join point, the block that holds k. A label made earlier
  means the same with the blocks added after it (Ext, ext-at).

-}

module proof.Correctness.Graph.ExplicateCorrect where

open import proof.Framework.GraphModel.Prelude
open import proof.Framework.GraphModel.Ops
open import Framework.Membership using (_⊑_; here⊑; there⊑; ⊑-∋; ⊑-trans)
open import Language.Typed.Type hiding (_≟_)
import Language.Typed.Imp as I
open import Language.Typed.CFG
open import Compiler.Explicate
open import proof.Semantics.Graph.Typed.Ops using (Table; tables)
open import proof.Semantics.Graph.Typed.CFG using (⟦_⟧ᵗ; blocks; run; drop; 𝒮-≃; 𝒜)
  renaming (code′ to codeᶜ; table to tableᶜ; ⟦_⟧ₚ to ⟦_⟧ᶜ)
open import Semantics.Graph.Typed.Imp using (⟦_⟧ᴷ) renaming (code′ to codeᵢ; table to tableᵢ; ⟦_⟧ₚ to ⟦_⟧ᵢ)

open import Data.List using (List; []; _∷_; length)
open import Data.List.Relation.Unary.All using (All; []; _∷_) renaming (map to All-map)
open import Data.Nat using (ℕ; _≟_)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong-app)
open import Relation.Nullary using (yes; no)

{- the continuations of Impᵀ ------------------------------------------------------------}

κ-≃ : ∀ {Σ Δ A} (e : I.Exp Σ Δ A) {T : Table Σ} {σ} {κ κ' : 𝒫 Value → 𝒫 Value} → (∀ D → κ D ≃ κ' D) → ⟦ e ⟧ᴷ T σ κ ≃ ⟦ e ⟧ᴷ T σ κ'
κ-≃ (I.simple s) h = h _
κ-≃ (I.assign e₁ e₂) {T} {σ} {κ} {κ'} h =
  κ-≃ e₁ λ D → ⋆-≃ (Λ-≃ {λ X → ⟦ e₂ ⟧ᴷ T (X • σ) κ} {λ X → ⟦ e₂ ⟧ᴷ T (X • σ) κ'} λ _ _ _ → κ-≃ e₂ h) (≃-refl {D = D})
κ-≃ (I.case a e₁ e₂) {T} {σ} {κ} {κ'} h =
  𝒞-≃ {F = λ X → ⟦ e₁ ⟧ᴷ T (X • σ) κ} {λ X → ⟦ e₁ ⟧ᴷ T (X • σ) κ'} {λ X → ⟦ e₂ ⟧ᴷ T (X • σ) κ} {λ X → ⟦ e₂ ⟧ᴷ T (X • σ) κ'}
    (≃-refl {D = 𝒜 a T σ}) (λ _ _ _ → κ-≃ e₁ h) (λ _ _ _ → κ-≃ e₂ h)

{- blocks that extend others -----------------------------------------------------------}

data Ext {Σ} : ∀ {Bs Bs'} → Bs ⊑ Bs' → Blocks Σ Bs → Blocks Σ Bs' → Set where
  here : ∀ {Bs} {bs : Blocks Σ Bs} → Ext here⊑ bs bs
  there : ∀ {Bs Bs' Δ g bs bs'} {t : Tail Σ Bs' Δ} → Ext {Bs = Bs} g bs bs' → Ext (there⊑ g) bs (bs' ▷ t)

ext-trans : ∀ {Σ Bs Bs' Bs''} {g : Bs ⊑ Bs'} {g' : Bs' ⊑ Bs''} {bs bs' bs''}
  → Ext {Σ} g bs bs' → Ext g' bs' bs'' → Ext (⊑-trans g g') bs bs''
ext-trans e here = e
ext-trans e (there e') = there (ext-trans e e')

ext-at : ∀ {Σ Bs Bs'} {g : Bs ⊑ Bs'} {bs bs'} {T : Table Σ} → Ext g bs bs' → ∀ {Δ} (l : Bs ∋ Δ)
  → blocks bs' T (⊑-∋ g l) ≡ blocks bs T l
ext-at here l = refl
ext-at (there e) l = ext-at e l

{- The pass preserves meanings -----------------------------------------------------------}

module _ {Σ} {T T' : Table Σ} (TT : ∀ {n} (f : Σ ∋ n) → T f ≃ T' f) where

  {- assign the next slot of the frame cut by p, then k with the blocks bs -}
  asg : ∀ {Bs Δ Δ' A} → Δ' ⊑ Δ → Tail Σ Bs (A ∷ Δ') → Blocks Σ Bs → Env Value → 𝒫 Value → 𝒫 Value
  asg p k bs σ D = ⋆ ⟨ Λ ⟨ (λ X → ⟦ k ⟧ᵗ T (blocks bs T) (X • drop p σ)) , ptt ⟩ , ⟨ D , ptt ⟩ ⟩

  Good : ∀ {Bs Δ} → Blocks Σ Bs → Out Σ Bs Δ → (Env Value → 𝒫 Value) → Set₁
  Good bs (out g bs' t) F = Ext g bs bs' × (∀ σ → ⟦ t ⟧ᵗ T (blocks bs' T) σ ≃ F σ)

  cps : ∀ {Bs Δ Δ' A} (e : I.Exp Σ Δ A) (p : Δ' ⊑ Δ) (k : Tail Σ Bs (A ∷ Δ')) (bs : Blocks Σ Bs)
    → Good bs (explicate-assign e p k bs) (λ σ → ⟦ e ⟧ᴷ T' σ (asg p k bs σ))
  cps (I.simple s) p k bs = ⟨ here , (λ σ → ⋆-≃ (≃-refl {D = Λ ⟨ (λ X → ⟦ k ⟧ᵗ T (blocks bs T) (X • drop p σ)) , ptt ⟩}) (𝒮-≃ TT s σ)) ⟩
  cps (I.assign e₁ e₂) p k bs with explicate-assign e₂ (there⊑ p) k bs | cps e₂ (there⊑ p) k bs
  ... | out g bs₁ t | ⟨ x₂ , h₂ ⟩ with explicate-assign e₁ here⊑ t bs₁ | cps e₁ here⊑ t bs₁
  ...   | out g' bs₂ t₁ | ⟨ x₁ , h₁ ⟩ =
    ⟨ ext-trans x₂ x₁ , (λ σ → ≃-trans (h₁ σ) (κ-≃ e₁ λ D → ⋆-≃ (Λ-≃ {λ X → ⟦ t ⟧ᵗ T (blocks bs₁ T) (X • σ)}
        {λ X → ⟦ e₂ ⟧ᴷ T' (X • σ) (asg p k bs σ)} λ _ _ _ → h₂ _) ≃-refl)) ⟩
  cps (I.case a e₁ e₂) p k bs with explicate-assign e₁ (there⊑ p) (goto Z) (bs ▷ k) | cps e₁ (there⊑ p) (goto Z) (bs ▷ k)
  ... | out g₁ bs₁ t₁ | ⟨ x₁ , h₁ ⟩
      with explicate-assign e₂ (there⊑ p) (goto (⊑-∋ (there⊑ g₁) Z)) (bs₁ ▷ t₁)
         | cps e₂ (there⊑ p) (goto (⊑-∋ (there⊑ g₁) Z)) (bs₁ ▷ t₁)
  ...   | out g₂ bs₂ t₂ | ⟨ x₂ , h₂ ⟩ =
    ⟨ there (ext-trans (there (ext-trans (there here) x₁)) x₂)
    , (λ σ → 𝒞-≃ {F = λ X → blocks (bs₂ ▷ t₂) T (⊑-∋ (there⊑ g₂) Z) (X • σ)} {λ X → ⟦ e₁ ⟧ᴷ T' (X • σ) (asg p k bs σ)}
                 {λ X → ⟦ t₂ ⟧ᵗ T (blocks bs₂ T) (X • σ)} {λ X → ⟦ e₂ ⟧ᴷ T' (X • σ) (asg p k bs σ)} (𝒜≃ a σ)
        (λ _ _ _ → ≃-trans (≃-reflexive (cong-app (ext-at x₂ Z) _)) (h₁ _))
        (λ _ _ _ → ≃-trans (h₂ _) (κ-≃ e₂ λ D →
           ≃-reflexive (cong (λ F → ⋆ ⟨ Λ ⟨ (λ X → F (X • drop p σ)) , ptt ⟩ , ⟨ D , ptt ⟩ ⟩) (ext-at x₁ Z))))) ⟩
    where
    𝒜≃ : ∀ {Δ A} (a : I.Atm Σ Δ A) σ → 𝒜 a T σ ≃ 𝒜 a T' σ
    𝒜≃ a σ = 𝒮-≃ TT (I.atm a) σ

  tl : ∀ {Bs Δ} (e : I.Exp Σ Δ Any) (bs : Blocks Σ Bs) → Good bs (explicate-tail e bs) (λ σ → ⟦ e ⟧ᴷ T' σ (λ D → D))
  tl (I.simple s) bs = ⟨ here , 𝒮-≃ TT s ⟩
  tl (I.assign e₁ e₂) bs with explicate-tail e₂ bs | tl e₂ bs
  ... | out g bs₁ t | ⟨ x₂ , h₂ ⟩ with explicate-assign e₁ here⊑ t bs₁ | cps e₁ here⊑ t bs₁
  ...   | out g' bs₂ t₁ | ⟨ x₁ , h₁ ⟩ =
    ⟨ ext-trans x₂ x₁ , (λ σ → ≃-trans (h₁ σ) (κ-≃ e₁ λ D → ⋆-≃ (Λ-≃ {λ X → ⟦ t ⟧ᵗ T (blocks bs₁ T) (X • σ)}
        {λ X → ⟦ e₂ ⟧ᴷ T' (X • σ) (λ D → D)} λ _ _ _ → h₂ _) ≃-refl)) ⟩
  tl (I.case a e₁ e₂) bs with explicate-tail e₁ bs | tl e₁ bs
  ... | out g₁ bs₁ t₁ | ⟨ x₁ , h₁ ⟩ with explicate-tail e₂ (bs₁ ▷ t₁) | tl e₂ (bs₁ ▷ t₁)
  ...   | out g₂ bs₂ t₂ | ⟨ x₂ , h₂ ⟩ =
    ⟨ there (ext-trans (there x₁) x₂)
    , (λ σ → 𝒞-≃ {F = λ X → blocks (bs₂ ▷ t₂) T (⊑-∋ (there⊑ g₂) Z) (X • σ)} {λ X → ⟦ e₁ ⟧ᴷ T' (X • σ) (λ D → D)}
                 {λ X → ⟦ t₂ ⟧ᵗ T (blocks bs₂ T) (X • σ)} {λ X → ⟦ e₂ ⟧ᴷ T' (X • σ) (λ D → D)} (𝒮-≃ TT (I.atm a) σ)
        (λ _ _ _ → ≃-trans (≃-reflexive (cong-app (ext-at x₂ Z) _)) (h₁ _)) (λ _ _ _ → h₂ _)) ⟩

  body-≃ : ∀ {Δ} (e : I.Exp Σ Δ Any) σ → run (explicate-body e) T σ ≃ ⟦ e ⟧ᴷ T' σ (λ D → D)
  body-≃ e σ with explicate-tail e [] | tl e []
  ... | out _ bs t | ⟨ _ , h ⟩ = h σ

{- Programs ------------------------------------------------------------------------------}

table-explicate : ∀ {Σ ns} (ds : All (λ n → I.Exp Σ (Any ∷ ⟪ tup n ⟫ ∷ []) Any) ns) {n} (f : Σ ∋ n)
  → tables codeᶜ (All-map explicate-body ds) f ≃ tables codeᵢ ds f
table-explicate [] f = ≃-refl
table-explicate {ns = _ ∷ ns} (d ∷ ds) f with lvl f ≟ length ns
... | yes _ = ΛΛ-≃ λ X Y → body-≃ (table-explicate ds) d _
... | no _ = table-explicate ds f

explicate-correct : ∀ (P : I.Program) → ⟦ explicate P ⟧ᶜ ≃ ⟦ P ⟧ᵢ
explicate-correct (I.program ds e) = body-≃ (table-explicate ds) e _

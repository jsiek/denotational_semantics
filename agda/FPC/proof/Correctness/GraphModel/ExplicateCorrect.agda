{-

  Correctness of explicate control (Impμ → CFGμ,
  FPC/Compiler/Explicate.agda) in the graph model, as for the typed pass
  (ISWIM/proof/Correctness/Graph/ExplicateCorrect.agda): the CFGμ program
  (FPC/Semantics/GraphModel/CFG.agda) means what the Impμ program does
  (FPC/Semantics/GraphModel/Imp.agda, continuation-passing).

  explicate-assign e x p k bs is e in continuation-passing style, as the
  semantics of Impμ is: its tail, with its blocks, means e run with the
  continuation that writes slot x of the frame where e starts and runs
  k with the blocks bs (asg); explicate-tail e means e run with the
  continuation that returns the value. Each case is a congruence; a case
  passes its continuation to its branches, which in CFGμ reach it
  through the join point, the block that holds k. A label made earlier
  means the same with the blocks added after it (Ext, ext-at).

  In CFGμ, k runs in the frame that e leaves, in which e has written
  slots of its own, while the continuation of Impμ runs k in the frame
  where e starts. Each slot that e writes is not initialized where e
  starts, and k reads only slots initialized there or slot x, so the
  two frames agree on the slots that k reads (agree-fresh, agree-≔), and
  k means the same in both (tail-agree, asg-fresh).

-}

module FPC.proof.Correctness.GraphModel.ExplicateCorrect where

open import proof.Framework.GraphModel.Prelude
open import proof.Framework.GraphModel.Ops
open import Framework.Membership using (_⊑_; here⊑; there⊑; ⊑-∋; ⊑-trans)
open import FPC.Language.Type
import FPC.Language.Imp as I
open I using (⊆-refl; ⊆-⊕⊕)
open import FPC.Language.CFG hiding (_⊆_)
open import FPC.Compiler.Explicate
open import FPC.Semantics.GraphModel.Ops using (Table; tables; _[_≔_])
open import FPC.proof.Semantics.GraphModel.CFG using (⟦_⟧ᵗ; blocks; run; 𝒮-≃;
  𝒜; tail-agree; blocks-agree; agree-≔; agree-fresh) renaming (code′ to codeᶜ;
  table to tableᶜ; ⟦_⟧ₚ to ⟦_⟧ᶜ)
open import FPC.Semantics.GraphModel.Imp using (⟦_⟧ᴷ) renaming (code′ to codeᵢ;
  table to tableᵢ; ⟦_⟧ₚ to ⟦_⟧ᵢ)
open import FPC.proof.Semantics.GraphModel.Binders using (let-≃; case-≃)
open import FPC.Framework.AllUtil using (All; []; _∷_) renaming (map to All-map)

open import Data.List using (List; []; _∷_; length)
open import Data.Nat using (ℕ; _≟_)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong;
  cong-app)
open import Relation.Nullary using (yes; no)

{- the continuations of Impμ --------------------------------------------------}

κ-≃ : ∀ {Σ Δ I A} (e : I.Exp Σ Δ I A) {T : Table Σ} {σ}
  {κ κ' : 𝒫 Value → 𝒫 Value}
  → (∀ D → κ D ≃ κ' D)
  → ⟦ e ⟧ᴷ T σ κ ≃ ⟦ e ⟧ᴷ T σ κ'
κ-≃ (I.simple s) h = h _
κ-≃ (I.assign x _ e₁ e₂) {T} {σ} h =
  κ-≃ e₁ λ D → let-≃ (≃-refl {D = D}) λ X _ _ →
    κ-≃ e₂ {T = T} {σ [ idx x ≔ X ]} h
κ-≃ (I.case a x _ y _ e₁ e₂) {T} {σ} h =
  case-≃ (≃-refl {D = 𝒜 a T σ}) (λ X _ _ → κ-≃ e₁ {T = T} {σ [ idx x ≔ X ]} h)
    (λ X _ _ → κ-≃ e₂ {T = T} {σ [ idx y ≔ X ]} h)

{- blocks that extend others --------------------------------------------------}

data Ext {Σ R Δ} : ∀ {Bs Bs' : List (Inits Δ)} → Bs ⊑ Bs' → Blocks Σ R Δ Bs
  → Blocks Σ R Δ Bs' → Set where
  here : ∀ {Bs} {bs : Blocks Σ R Δ Bs} → Ext here⊑ bs bs
  there : ∀ {Bs Bs' I g bs bs'} {t : Tail Σ R Δ Bs' I}
    → Ext {Bs = Bs} g bs bs'
    → Ext (there⊑ g) bs (bs' ▷ t)

ext-trans : ∀ {Σ R Δ} {Bs Bs' Bs'' : List (Inits Δ)}
  → {g : Bs ⊑ Bs'}
  → {g' : Bs' ⊑ Bs''}
  → ∀ {bs bs' bs''}
  → Ext {Σ} {R} g bs bs'
  → Ext g' bs' bs''
  → Ext (⊑-trans g g') bs bs''
ext-trans e here = e
ext-trans e (there e') = there (ext-trans e e')

ext-at : ∀ {Σ R Δ} {Bs Bs' : List (Inits Δ)}
  → {g : Bs ⊑ Bs'}
  → {bs : Blocks Σ R Δ Bs} {bs' : Blocks Σ R Δ Bs'} {T : Table Σ}
  → Ext g bs bs'
  → ∀ {I} (l : Bs ∋ I)
  → blocks bs T l ≡ blocks bs' T (⊑-∋ g l)
ext-at here l = refl
ext-at (there e) l = ext-at e l

{- The pass preserves meanings ------------------------------------------------}

module _ {Σ R} {T T' : Table Σ} (TT : ∀ {s} (f : Σ ∋ s) → T f ≃ T' f) where

  {- write slot x of the frame σ, then k with the blocks bs -}
  asg : ∀ {Δ Bs A} {J : Inits Δ} → Δ ∋ A → Tail Σ R Δ Bs J
    → Blocks Σ R Δ Bs → Env Value → 𝒫 Value → 𝒫 Value
  asg x k bs σ D =
    ⋆
    ⟨ Λ ⟨ (λ X → ⟦ k ⟧ᵗ T' (blocks bs T') (σ [ idx x ≔ X ])) , ptt ⟩
      , ⟨ D , ptt ⟩ ⟩

  {- a write to a slot y that is not initialized where the assignment
     starts does not change what asg means -}
  asg-fresh : ∀ {Δ Bs A B} {I J : Inits Δ} (x : Δ ∋ A)
    → .(J I.⊆ I ⊕ x)
    → (k : Tail Σ R Δ Bs J) (bs : Blocks Σ R Δ Bs) (y : Δ ∋ B)
    → .(y I.∉ I)
    → ∀ σ Y D
    → asg x k bs σ D ≃ asg x k bs (σ [ idx y ≔ Y ]) D
  asg-fresh {I = I} x p k bs y n σ Y D =
    let-≃ (≃-refl {D = D}) λ X _ _ →
      tail-agree {T = T'} {T'} (λ f → ≃-refl) k
        (blocks-agree {T = T'} {T'} (λ f → ≃-refl) bs)
        {σ [ idx x ≔ X ]} {σ [ idx y ≔ Y ] [ idx x ≔ X ]}
        (agree-≔ {I = I} {σ = σ} {σ [ idx y ≔ Y ]} x p
          (agree-fresh {I = I} {σ = σ} y n))

  Good : ∀ {Δ Bs} {I : Inits Δ} → (Env Value → 𝒫 Value) → Blocks Σ R Δ Bs
    → Out Σ R Δ Bs I → Set₁
  Good F bs (out g bs' t) =
    Ext g bs bs' × (∀ σ → F σ ≃ ⟦ t ⟧ᵗ T' (blocks bs' T') σ)

  cps : ∀ {Δ Bs A} {I J : Inits Δ} (e : I.Exp Σ Δ I A)
    → (x : Δ ∋ A)
    → .(p : J I.⊆ I ⊕ x)
    → (k : Tail Σ R Δ Bs J) (bs : Blocks Σ R Δ Bs)
    → Good (λ σ → ⟦ e ⟧ᴷ T σ (asg x k bs σ)) bs (explicate-assign e x p k bs)
  cps (I.simple s) x p k bs =
    ⟨ here
      ,
      (λ σ →
        ⋆-≃
          (≃-refl
            {D =
              Λ ⟨ (λ X → ⟦ k ⟧ᵗ T' (blocks bs T') (σ [ idx x ≔ X ])) , ptt ⟩})
          (𝒮-≃ TT s σ)) ⟩
  cps {I = I} {J} (I.assign y n e₁ e₂) x p k bs
    with explicate-assign e₂ x (⊆-⊕⊕ {I = I} {J} x y p) k bs
       | cps e₂ x (⊆-⊕⊕ {I = I} {J} x y p) k bs
  ... | out g bs₁ t | ⟨ x₂ , h₂ ⟩
    with explicate-assign e₁ y (⊆-refl {I = I ⊕ y}) t bs₁
       | cps e₁ y (⊆-refl {I = I ⊕ y}) t bs₁
  ...   | out g' bs₂ t₁ | ⟨ x₁ , h₁ ⟩ =
    ⟨ ext-trans x₂ x₁
        ,
        (λ σ →
          ≃-trans
            (κ-≃ e₁ λ D → let-≃ (≃-refl {D = D}) λ Y _ _ →
              ≃-trans
                (κ-≃ e₂ (asg-fresh {I = I} x p k bs y n σ Y))
                (h₂ (σ [ idx y ≔ Y ])))
            (h₁ σ)) ⟩
  cps {I = I} {J} (I.case a y n₁ z n₂ e₁ e₂) x p k bs
    with explicate-assign e₁ x (⊆-⊕⊕ {I = I} {J} x y p) (goto Z) (bs ▷ k)
       | cps e₁ x (⊆-⊕⊕ {I = I} {J} x y p) (goto Z) (bs ▷ k)
  ... | out g₁ bs₁ t₁ | ⟨ x₁ , h₁ ⟩
    with explicate-assign e₂ x (⊆-⊕⊕ {I = I} {J} x z p)
           (goto (⊑-∋ (there⊑ g₁) Z)) (bs₁ ▷ t₁)
       | cps e₂ x (⊆-⊕⊕ {I = I} {J} x z p)
           (goto (⊑-∋ (there⊑ g₁) Z)) (bs₁ ▷ t₁)
  ...   | out g₂ bs₂ t₂ | ⟨ x₂ , h₂ ⟩ =
    ⟨ there (ext-trans (there (ext-trans (there here) x₁)) x₂)
    ,
      (λ σ →
        case-≃ (𝒮-≃ TT (I.atm a) σ)
        (λ Y _ _ →
          ≃-trans (κ-≃ e₁ (asg-fresh {I = I} x p k bs y n₁ σ Y))
            (≃-trans (h₁ (σ [ idx y ≔ Y ]))
              (≃-reflexive (cong-app (ext-at x₂ Z) _))))
        (λ Y _ _ →
          ≃-trans
            (κ-≃ e₂ λ D →
              ≃-trans (asg-fresh {I = I} x p k bs z n₂ σ Y D)
                (≃-reflexive
                  (cong
                    (λ F →
                      ⋆
                      ⟨ Λ ⟨ (λ X → F (σ [ idx z ≔ Y ] [ idx x ≔ X ])) , ptt ⟩
                        , ⟨ D , ptt ⟩ ⟩)
                    (ext-at x₁ Z))))
            (h₂ (σ [ idx z ≔ Y ])))) ⟩

  tl : ∀ {Δ Bs} {I : Inits Δ} (e : I.Exp Σ Δ I R) (bs : Blocks Σ R Δ Bs)
    → Good (λ σ → ⟦ e ⟧ᴷ T σ (λ D → D)) bs (explicate-tail e bs)
  tl (I.simple s) bs = ⟨ here , 𝒮-≃ TT s ⟩
  tl {I = I} (I.assign x _ e₁ e₂) bs with explicate-tail e₂ bs | tl e₂ bs
  ... | out g bs₁ t | ⟨ x₂ , h₂ ⟩
    with explicate-assign e₁ x (⊆-refl {I = I ⊕ x}) t bs₁
       | cps e₁ x (⊆-refl {I = I ⊕ x}) t bs₁
  ...   | out g' bs₂ t₁ | ⟨ x₁ , h₁ ⟩ =
    ⟨ ext-trans x₂ x₁
        ,
        (λ σ →
          ≃-trans
            (κ-≃ e₁ λ D → let-≃ (≃-refl {D = D}) λ X _ _ →
              h₂ (σ [ idx x ≔ X ]))
            (h₁ σ)) ⟩
  tl (I.case a x _ y _ e₁ e₂) bs with explicate-tail e₁ bs | tl e₁ bs
  ... | out g₁ bs₁ t₁ | ⟨ x₁ , h₁ ⟩
    with explicate-tail e₂ (bs₁ ▷ t₁) | tl e₂ (bs₁ ▷ t₁)
  ...   | out g₂ bs₂ t₂ | ⟨ x₂ , h₂ ⟩ =
    ⟨ there (ext-trans (there x₁) x₂)
    ,
      (λ σ →
        case-≃ (𝒮-≃ TT (I.atm a) σ)
        (λ X _ _ →
          ≃-trans (h₁ (σ [ idx x ≔ X ]))
            (≃-reflexive (cong-app (ext-at x₂ Z) _)))
        (λ X _ _ → h₂ (σ [ idx y ≔ X ]))) ⟩

  body-≃ : ∀ {Δ} {I : Inits Δ} (e : I.Exp Σ Δ I R) σ
    → ⟦ e ⟧ᴷ T σ (λ D → D)
      ≃ ⟦ Out.tail (explicate-tail e []) ⟧ᵗ T'
        (blocks (Out.made (explicate-tail e [])) T') σ
  body-≃ e σ with explicate-tail e [] | tl e []
  ... | out _ bs t | ⟨ _ , h ⟩ = h σ

{- Programs -------------------------------------------------------------------}

table-explicate : ∀ {Σ ss} (ds : All (λ s → I.Body Σ (Args s) (DSig.cod s)) ss)
  {s} (f : Σ ∋ s)
  → tables codeᵢ ds f ≃ tables codeᶜ (All-map explicate-body ds) f
table-explicate [] f = ≃-refl
table-explicate {ss = _ ∷ ss} (I.body Δ p e ∷ ds) f with lvl f ≟ length ss
... | yes _ = ΛΛ-≃ λ X Y → body-≃ (table-explicate ds) e _
... | no _ = table-explicate ds f

explicate-correct : ∀ {A} (P : I.Program A) → ⟦ P ⟧ᵢ ≃ ⟦ explicate P ⟧ᶜ
explicate-correct (I.program ds (I.body Δ p e)) =
  body-≃ (table-explicate ds) e _

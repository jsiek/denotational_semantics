{-

  Correctness of explicate control (Impμ → CFGμ,
  Mu/Compiler/Explicate.agda) in Scott domains
  (Mu/Semantics/Scott/{Imp,CFG}.agda), as in the graph model
  (Mu/proof/Correctness/Graph/ExplicateCorrect.agda), with equality of
  values in place of equality of sets.

  explicate-assign e p k bs is e in continuation-passing style, as the
  semantics of Impμ is: its tail, with its blocks, means e run with the
  continuation that assigns the next slot of the frame cut by p and runs
  k with the blocks bs (asg); explicate-tail e means e run with the
  continuation that returns the value (idK). Each case is a congruence;
  a case passes its continuation to its branches, which in CFGμ reach it
  through the join point, the block that holds k. A label made earlier
  means the same with the blocks added after it (Ext, ext-at).

  The continuations are continuous maps, so the graph model's κ-≃ is
  just a congruence (ap). The compiler takes apart the output of a
  recursive call with `with`; Out is a record, so the proof uses its
  projections instead (a `with` while meanings are in scope is slow to
  check: tl by `with`, as in the graph model, does not check in 6
  minutes).

-}

open import MLTT.Spartan hiding (inl; inr; cases)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons
open import UF.Base using (ap₂)

open import Framework.Membership using (_⊑_; here⊑; there⊑; ⊑-∋; ⊑-trans)
open import Mu.Language.Type
import Mu.Language.Imp as I
open import Mu.Language.CFG
open import Mu.Compiler.Explicate
open import Mu.Framework.AllUtil using (All; []; _∷_) renaming (map to All-map)
open import Framework.abt.GSubst using (_•_)
open import Data.List using (List; []; _∷_; length)

module Mu.proof.Correctness.Scott.ExplicateCorrect
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : propext 𝓤₀)
       where

open import Framework.Scott.Base pt fe
open import proof.Framework.Scott.Ops pt fe pe renaming (app to appᵈ; inl to inlᵈ; inr to inrᵈ; tuple to tupleᵈ)
open import proof.Framework.Scott.Semantics pt fe pe
open import Mu.Semantics.Scott.Ops pt fe pe
open import Mu.Semantics.Scott.Imp pt fe pe using (⟦_⟧ᴷ; K; idK; underK)
  renaming (code′ to codeᵢ; table to tableᵢ; ⟦_⟧ₚ to ⟦_⟧ᵢ)
open import Mu.Semantics.Scott.CFG pt fe pe using (⟦_⟧ᵗ; blocks; run; drop; 𝒜; 𝒮)
  renaming (code′ to codeᶜ′; table to tableᶜ; ⟦_⟧ₚ to ⟦_⟧ᶜ)
open import Mu.proof.Semantics.Scott.BackEndLemmas pt fe pe using (codeᶜ-cong; tables-cons; 𝒜-＝; 𝒮-＝)

{- blocks that extend others -----------------------------------------------------------}

data Ext {Σ R} : ∀ {Bs Bs'} → Bs ⊑ Bs' → Blocks Σ R Bs → Blocks Σ R Bs' → Set where
  here : ∀ {Bs} {bs : Blocks Σ R Bs} → Ext here⊑ bs bs
  there : ∀ {Bs Bs' Δ g bs bs'} {t : Tail Σ R Bs' Δ} → Ext {Bs = Bs} g bs bs' → Ext (there⊑ g) bs (bs' ▷ t)

ext-trans : ∀ {Σ R Bs Bs' Bs''} {g : Bs ⊑ Bs'} {g' : Bs' ⊑ Bs''} {bs bs' bs''}
  → Ext {Σ} {R} g bs bs' → Ext g' bs' bs'' → Ext (⊑-trans g g') bs bs''
ext-trans e here = e
ext-trans e (there e') = there (ext-trans e e')

ext-at : ∀ {Σ R Bs Bs'} {g : Bs ⊑ Bs'} {bs : Blocks Σ R Bs} {bs' : Blocks Σ R Bs'} (T : Table Σ) → Ext g bs bs' → ∀ {Δ} (l : Bs ∋ Δ)
  → blocks bs T l ＝ blocks bs' T (⊑-∋ g l)
ext-at T here l = refl
ext-at T (there e) l = ext-at T e l

{- The pass preserves meanings -----------------------------------------------------------}

module _ {Σ R} (T T' : Table Σ) (TT : ∀ {s} (f : Σ ∋ s) → T f ＝ T' f) where

  {- assign the next slot of the frame cut by p, then k with the blocks bs -}
  asg : ∀ {Bs Δ Δ' A} → Δ' ⊑ Δ → Tail Σ R Bs (A ∷ Δ') → Blocks Σ R Bs → ⟨ Env ⟩ → ⟨ K ⟩
  asg p k bs σ = appᵈ · (lamᶜ (⟦ k ⟧ᵗ T' (blocks bs T')) · (drop p · σ))

  Good : ∀ {Bs Δ} → (⟨ Env ⟩ → ⟨ 𝔻 ⟩) → Blocks Σ R Bs → Out Σ R Bs Δ → 𝓤₁ ̇
  Good F bs (out g bs' t) = Ext g bs bs' × ((σ : ⟨ Env ⟩) → F σ ＝ ⟦ t ⟧ᵗ T' (blocks bs' T') · σ)

  {- the continuation of the right-hand side of an assignment, when its
     body e₂ runs as the tail t -}
  bind : ∀ {Bs Δ A B} (e₂ : I.Exp Σ (A ∷ Δ) B) (κ : ⟨ K ⟩) (t : Tail Σ R Bs (A ∷ Δ)) (bs : Blocks Σ R Bs) σ
    → ((X : ⟨ 𝔻 ⟩) → ⟦ e₂ ⟧ᴷ T · (X • σ) · κ ＝ ⟦ t ⟧ᵗ T' (blocks bs T') · (X • σ))
    → appᵈ · (Λ · (underK (⟦ e₂ ⟧ᴷ T) · (σ , κ))) ＝ asg here⊑ t bs σ
  bind e₂ κ t bs σ h =
    ap (appᵈ ·_) (Λ-cong (underK (⟦ e₂ ⟧ᴷ T) · (σ , κ)) (abs (⟦ t ⟧ᵗ T' (blocks bs T')) · σ) (λ X _ → h X))

  {- the two branches of a case -}
  branches : ∀ {Δ A B} (a : I.Atm Σ Δ (A ⊹ B)) (F₁ F₂ G₁ G₂ : DCPO[ 𝔻 , 𝔻 ]) σ
    → ((X : ⟨ 𝔻 ⟩) → F₁ · X ＝ G₁ · X) → ((X : ⟨ 𝔻 ⟩) → F₂ · X ＝ G₂ · X)
    → cases · (𝒜 a T · σ) · (strict · F₁ , strict · F₂) ＝ cases · (𝒜 a T' · σ) · (strict · G₁ , strict · G₂)
  branches a F₁ F₂ G₁ G₂ σ h₁ h₂ =
    ap₂ (λ x y → cases · x · y) (𝒜-＝ T T' TT a σ)
      (ap₂ _,_ (ap (strict ·_) (to-continuous-function-＝ 𝔻 𝔻 {F₁} {G₁} h₁))
               (ap (strict ·_) (to-continuous-function-＝ 𝔻 𝔻 {F₂} {G₂} h₂)))

  cps : ∀ {Bs Δ Δ' A} (e : I.Exp Σ Δ A) (p : Δ' ⊑ Δ) (k : Tail Σ R Bs (A ∷ Δ')) (bs : Blocks Σ R Bs)
    → Good (λ σ → ⟦ e ⟧ᴷ T · σ · asg p k bs σ) bs (explicate-assign e p k bs)
  cps (I.simple s) p k bs = here , λ σ → ap (asg p k bs σ ·_) (𝒮-＝ T T' TT s σ)
  cps (I.assign e₁ e₂) p k bs =
    ext-trans (pr₁ c₂) (pr₁ c₁) ,
    λ σ → ap (⟦ e₁ ⟧ᴷ T · σ ·_) (bind e₂ (asg p k bs σ) (Out.tail o₂) (Out.made o₂) σ (λ X → pr₂ c₂ (X • σ)))
          ∙ pr₂ c₁ σ
   where
    o₂ = explicate-assign e₂ (there⊑ p) k bs
    c₂ = cps e₂ (there⊑ p) k bs
    c₁ = cps e₁ here⊑ (Out.tail o₂) (Out.made o₂)
  cps (I.case a e₁ e₂) p k bs =
    there (ext-trans (there (ext-trans (there here) (pr₁ c₁))) (pr₁ c₂)) ,
    λ σ → branches a (underK (⟦ e₁ ⟧ᴷ T) · (σ , asg p k bs σ)) (underK (⟦ e₂ ⟧ᴷ T) · (σ , asg p k bs σ))
            (abs (blocks (Out.made o₂) T' (⊑-∋ (Out.grows o₂) Z)) · σ) (abs (⟦ Out.tail o₂ ⟧ᵗ T' (blocks (Out.made o₂) T')) · σ) σ
            (λ X → pr₂ c₁ (X • σ) ∙ ap (λ N → N · (X • σ)) (ext-at T' (pr₁ c₂) Z))
            (λ X → ap (λ N → ⟦ e₂ ⟧ᴷ T · (X • σ) · (appᵈ · (Λ · (abs N · (drop p · σ))))) (ext-at T' (pr₁ c₁) Z)
                   ∙ pr₂ c₂ (X • σ))
   where
    o₁ = explicate-assign e₁ (there⊑ p) (goto Z) (bs ▷ k)
    c₁ = cps e₁ (there⊑ p) (goto Z) (bs ▷ k)
    o₂ = explicate-assign e₂ (there⊑ p) (goto (⊑-∋ (there⊑ (Out.grows o₁)) Z)) (Out.made o₁ ▷ Out.tail o₁)
    c₂ = cps e₂ (there⊑ p) (goto (⊑-∋ (there⊑ (Out.grows o₁)) Z)) (Out.made o₁ ▷ Out.tail o₁)

  tl : ∀ {Bs Δ} (e : I.Exp Σ Δ R) (bs : Blocks Σ R Bs) → Good (λ σ → ⟦ e ⟧ᴷ T · σ · idK) bs (explicate-tail e bs)
  tl (I.simple s) bs = here , 𝒮-＝ T T' TT s
  tl (I.assign e₁ e₂) bs =
    ext-trans (pr₁ c₂) (pr₁ c₁) ,
    λ σ → ap (⟦ e₁ ⟧ᴷ T · σ ·_) (bind e₂ idK (Out.tail o₂) (Out.made o₂) σ (λ X → pr₂ c₂ (X • σ)))
          ∙ pr₂ c₁ σ
   where
    o₂ = explicate-tail e₂ bs
    c₂ = tl e₂ bs
    c₁ = cps e₁ here⊑ (Out.tail o₂) (Out.made o₂)
  tl (I.case a e₁ e₂) bs =
    there (ext-trans (there (pr₁ c₁)) (pr₁ c₂)) ,
    λ σ → branches a (underK (⟦ e₁ ⟧ᴷ T) · (σ , idK)) (underK (⟦ e₂ ⟧ᴷ T) · (σ , idK))
            (abs (blocks (Out.made o₂) T' (⊑-∋ (Out.grows o₂) Z)) · σ) (abs (⟦ Out.tail o₂ ⟧ᵗ T' (blocks (Out.made o₂) T')) · σ) σ
            (λ X → pr₂ c₁ (X • σ) ∙ ap (λ N → N · (X • σ)) (ext-at T' (pr₁ c₂) Z))
            (λ X → pr₂ c₂ (X • σ))
   where
    o₁ = explicate-tail e₁ bs
    c₁ = tl e₁ bs
    o₂ = explicate-tail e₂ (Out.made o₁ ▷ Out.tail o₁)
    c₂ = tl e₂ (Out.made o₁ ▷ Out.tail o₁)

  body-＝ : ∀ {Δ} (e : I.Exp Σ Δ R) σ → ⟦ e ⟧ᴷ T · σ · idK ＝ run (explicate-body e) T' · σ
  body-＝ e σ = pr₂ (tl e []) σ

{- Programs ------------------------------------------------------------------------------}

table-explicate : ∀ {Σ ss} (ds : All (λ s → I.Exp Σ (Args s) (DSig.cod s)) ss) {s} (f : Σ ∋ s)
  → tables codeᵢ ds f ＝ tables codeᶜ′ (All-map explicate-body ds) f
table-explicate [] f = refl
table-explicate (d ∷ ds) f =
  tables-cons codeᵢ codeᶜ′ d ds (explicate-body d) (All-map explicate-body ds) f
    (codeᶜ-cong (∘₁ Env (K ⟹₁ 𝔻) 𝔻 (⟦ d ⟧ᴷ T) (at-point₁ K 𝔻 idK)) (run (explicate-body d) T')
       (λ X Y _ _ → body-＝ T T' (table-explicate ds) d (env₂ X Y)))
    (table-explicate ds f)
 where
  T = tables codeᵢ ds
  T' = tables codeᶜ′ (All-map explicate-body ds)

explicate-correct : ∀ {A} (P : I.Program A) → ⟦ P ⟧ᵢ ＝ ⟦ explicate P ⟧ᶜ
explicate-correct (I.program ds e) = body-＝ (tableᵢ ds) (tableᶜ (All-map explicate-body ds)) (table-explicate ds) e ρ₀

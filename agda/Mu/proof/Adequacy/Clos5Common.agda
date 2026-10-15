{-

  What the graph model makes of the table of a Clos5μ program, for the
  adequacy of X86μ (Mu/proof/Adequacy/X86Compiled.agda), as
  in the typed pipeline (proof/Adequacy/Clos5Common.agda and
  Clos5Soundness.agda), without the Clos5 machine:

  * the definitions older than a definition f (older f, drop f);
    definition f means its code with the table of the older ones
    (table-at), and the older definitions mean the same in the table
    of all of them as in their own (agree);
  * the semantics in a table depends only on the references a term
    makes (tbl-mono), and a definition of a program that globalize
    produces refers only to older ones (olderAt).

-}

module Mu.proof.Adequacy.Clos5Common where

open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.Domain using (Value; ■; _•_)
open import proof.Framework.GraphModel.Continuity
  using (pair-good; 𝒯-good; proj-good; inl-good; inr-good; 𝒞-good; letD-good)
open import proof.Framework.GraphModel.ContinuityBase using (Good; mono)
open import proof.Framework.GraphModel.DOpSig using (results-rel-pres)
open import proof.Framework.GraphModel.Env using (•-~)
open import proof.Semantics.Graph.Prim using (primD-good)
open import Mu.Language.Type
open import Mu.Language.Clos5
open import Mu.proof.Semantics.Graph.Ops using (Table; tables; ConT; callc-good)
open import Mu.proof.Semantics.Graph.Clos5 using (⟦_⟧[_]; ⟦_⟧s[_]; ok)
open import Mu.proof.Compiler.GlobalizeOlder using (Older; Olders; OlderDefs)
open import Mu.Framework.AllUtil using (All; []; _∷_; lookup; pos)

open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_; length; replicate)
open import Data.Nat using (ℕ; _<_; _≟_)
open import Data.Nat.Properties using (<-irrefl; <-trans; ≤-refl; m<n⇒m<1+n)
open import Data.Product using (proj₁) renaming (_,_ to ⟨_,_⟩)
open import Data.Unit using (⊤)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Level using (Lift; lift; lower)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)
open import Relation.Nullary using (yes; no)

{- The older definitions ---------------------------------------------------------}

lvl< : ∀ {A : Set} {Γ : List A} {a} (x : Γ ∋ a) → lvl x < length Γ
lvl< Z = ≤-refl
lvl< (S x) = m<n⇒m<1+n (lvl< x)

older : ∀ {ss : List DSig} {s} → ss ∋ s → List DSig
older {_ ∷ ss} Z = ss
older (S f) = older f

drop : ∀ {P : DSig → Set} {ss s} (f : ss ∋ s) → All P ss → All P (older f)
drop Z (_ ∷ ps) = ps
drop (S f) (_ ∷ ps) = drop f ps

older-lvl : ∀ {ss : List DSig} {s} (f : ss ∋ s) → length (older f) ≡ lvl f
older-lvl Z = refl
older-lvl (S f) = older-lvl f

module _ {Σ : List DSig} {D : DSig → Set} (cd : Table Σ → ∀ {s} → D s → 𝒫 Value) where

  {- definition g of a part ps of the table, reached through r -}
  table-at′ : ∀ {ss} (ps : All D ss) (r : ∀ {s} → ss ∋ s → Σ ∋ s) → (∀ {s} (g : ss ∋ s) → lvl (r g) ≡ lvl g)
    → ∀ {s} (g : ss ∋ s) → tables cd ps (r g) ≡ cd (tables cd (drop g ps)) (lookup ps g)
  table-at′ {_ ∷ ss} (p ∷ ps) r rl Z with lvl (r Z) ≟ length ss
  ... | yes _ = refl
  ... | no ne = ⊥-elim (ne (rl Z))
  table-at′ {_ ∷ ss} (p ∷ ps) r rl (S g) with lvl (r (S g)) ≟ length ss
  ... | yes e = ⊥-elim (<-irrefl (trans (sym (rl (S g))) e) (lvl< g))
  ... | no _ = table-at′ ps (λ x → r (S x)) (λ x → rl (S x)) g

  table-at : (ps : All D Σ) → ∀ {s} (f : Σ ∋ s) → tables cd ps f ≡ cd (tables cd (drop f ps)) (lookup ps f)
  table-at ps = table-at′ ps (λ x → x) (λ _ → refl)

  {- the definitions older than f mean the same without the newer ones -}
  agree : ∀ {ss s} (ps : All D ss) (f : ss ∋ s) {s'} (g : Σ ∋ s') → lvl g < length (older f)
    → tables cd ps g ≡ tables cd (drop f ps) g
  agree {_ ∷ ss} (p ∷ ps) Z g g< with lvl g ≟ length ss
  ... | yes e = ⊥-elim (<-irrefl e g<)
  ... | no _ = refl
  agree {_ ∷ ss} (p ∷ ps) (S f) g g< with lvl g ≟ length ss
  ... | yes e = ⊥-elim (<-irrefl e (<-trans g< (subst (_< length ss) (sym (older-lvl f)) (lvl< f))))
  ... | no _ = agree ps f g g<

{- The semantics in the table depends only on the references a term makes ---------}

private
  m1 : ∀ {g} → Good ⊤ (■ ∷ []) g → ∀ {D E} → D ⊆ E → g ⟨ D , ptt ⟩ ⊆ g ⟨ E , ptt ⟩
  m1 G D⊆ = lower (mono G _ _ ⟨ lift D⊆ , ptt ⟩)
  m2 : ∀ {g} → Good ⊤ (■ ∷ ■ ∷ []) g → ∀ {D D' E E'} → D ⊆ D' → E ⊆ E' → g ⟨ D , ⟨ E , ptt ⟩ ⟩ ⊆ g ⟨ D' , ⟨ E' , ptt ⟩ ⟩
  m2 G D⊆ E⊆ = lower (mono G _ _ ⟨ lift D⊆ , ⟨ lift E⊆ , ptt ⟩ ⟩)
  ⊆r : ∀ {D : 𝒫 Value} → D ⊆ D
  ⊆r _ z = z

module _ {Σ : List DSig} where

  tbl-mono : ∀ {Γ A} {T T' : Table Σ} {k} (M : Tm Σ Γ A) → ConT T → Older k M
    → (∀ {s} (g : Σ ∋ s) → lvl g < k → T g ⊆ T' g) → ∀ ρ → ⟦ M ⟧[ T ] ρ ⊆ ⟦ M ⟧[ T' ] ρ
  tbl-monos : ∀ {Γ Δ} {T T' : Table Σ} {k} (Ms : All (Tm Σ Γ) Δ) → ConT T → Olders k Ms
    → (∀ {s} (g : Σ ∋ s) → lvl g < k → T g ⊆ T' g) → ∀ ρ
    → results-rel-pres _⊆_ (replicate (length Δ) ■) (⟦ Ms ⟧s[ T ] ρ) (⟦ Ms ⟧s[ T' ] ρ)
  tbl-mono (` x) cT o h ρ = ⊆r
  tbl-mono (fun-ref f) cT o h ρ = h f o
  tbl-mono (pack L M) cT ⟨ o₁ , o₂ ⟩ h ρ = m2 pair-good (tbl-mono L cT o₁ h ρ) (tbl-mono M cT o₂ h ρ)
  tbl-mono (callc L M) cT ⟨ o₁ , o₂ ⟩ h ρ = m2 callc-good (tbl-mono L cT o₁ h ρ) (tbl-mono M cT o₂ h ρ)
  tbl-mono (lit B c) cT o h ρ = ⊆r
  tbl-mono (tuple {Δ} Ms) cT o h ρ = lower (mono (𝒯-good {⊤} (length Δ)) _ _ (tbl-monos Ms cT o h ρ))
  tbl-mono (get i M) cT o h ρ = m1 (proj-good (pos i)) (tbl-mono M cT o h ρ)
  tbl-mono (inl M) cT o h ρ = m1 inl-good (tbl-mono M cT o h ρ)
  tbl-mono (inr M) cT o h ρ = m1 inr-good (tbl-mono M cT o h ρ)
  tbl-mono {T = T} (case L M N) cT ⟨ o₁ , ⟨ o₂ , o₃ ⟩ ⟩ h ρ =
    lower (mono (𝒞-good {⊤}) _ _ ⟨ lift (tbl-mono L cT o₁ h ρ) , ⟨ body M o₂ , ⟨ body N o₃ , ptt ⟩ ⟩ ⟩)
    where
    body : ∀ {B C} (B' : Tm Σ (B ∷ _) C) → Older _ B' → ∀ X X' → X ⊆ X' → Lift _ (⟦ B' ⟧[ T ] (X • ρ) ⊆ ⟦ B' ⟧[ _ ] (X' • ρ))
    body B' oB X X' X⊆ = lift λ d d∈ → tbl-mono B' cT oB h (X' • ρ) d (proj₁ (ok cT B') (•-~ _⊆_ (λ _ → ⊆r) X⊆) d d∈)
  tbl-mono (prim p L M) cT ⟨ o₁ , o₂ ⟩ h ρ = m2 (primD-good p) (tbl-mono L cT o₁ h ρ) (tbl-mono M cT o₂ h ρ)
  tbl-mono {T = T} (let′ M N) cT ⟨ o₁ , o₂ ⟩ h ρ =
    lower (mono (letD-good {⊤}) _ _ ⟨ lift (tbl-mono M cT o₁ h ρ)
      , ⟨ (λ X X' X⊆ → lift λ d d∈ → tbl-mono N cT o₂ h (X' • ρ) d (proj₁ (ok cT N) (•-~ _⊆_ (λ _ → ⊆r) X⊆) d d∈)) , ptt ⟩ ⟩)
  tbl-mono (fold M) cT o h ρ = tbl-mono M cT o h ρ
  tbl-mono (unfold M) cT o h ρ = tbl-mono M cT o h ρ
  tbl-monos [] cT o h ρ = ptt
  tbl-monos (M ∷ Ms) cT ⟨ o , os ⟩ h ρ = ⟨ lift (tbl-mono M cT o h ρ) , tbl-monos Ms cT os h ρ ⟩

  olderAt : ∀ {ss s} {ps : All (Code Σ) ss} → OlderDefs ps → (f : ss ∋ s) → Older (length (older f)) (lookup ps f)
  olderAt {ps = p ∷ ps} ⟨ o , _ ⟩ Z = o
  olderAt {ps = p ∷ ps} ⟨ _ , os ⟩ (S f) = olderAt os f

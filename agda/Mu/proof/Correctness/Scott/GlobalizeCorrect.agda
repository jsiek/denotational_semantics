{-

  Correctness of globalize (Clos4μ → Clos5μ) in Scott domains
  (Mu/Semantics/Scott/{Clos4,Clos5}.agda), as in the graph model
  (Mu/proof/Correctness/Graph/GlobalizeCorrect.agda), with equality of
  values in place of equality of sets: the pass preserves meanings
  exactly.

  The definitions made so far (Made, each over the older ones) have
  their own table (made). Then:
  * wk-sem: weakening a term to a bigger table changes nothing when the
    bigger table agrees on the references it is weakened along;
  * glob-ok: what glob makes means what the source means, with the table
    of the definitions it made, which extends the table it was given
    (Ext);
  * table-close: the table of a program, each definition weakened to the
    whole table (close), agrees with made, by the levels of the
    references.

  The proof has the graph model's structure, taking apart what glob
  makes by `with`. Two things keep Agda fast here (otherwise each takes
  minutes): the predicates OK, OKs, Cong₁ and Cong₂ are records, and a
  `with` is never checked while an equation between meanings is in
  scope (a `with` that is followed by another keeps the OK it matched
  whole). So the end theorem, itself an equation, takes glob's result
  apart by programO and globalize-eq instead.

-}

open import MLTT.Spartan hiding (inl; inr; cases)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons
open import UF.Base using (ap₂; happly)

open import Framework.Primitives using (Int)
open import Mu.Language.Type renaming (unroll to unrollᵗ)
open import Framework.Membership using (_⊑_; here⊑; there⊑; ⊑-∋; ⊑-trans)
import Mu.Language.Clos4 as S
open import Mu.Language.Clos5
open import Mu.Compiler.Globalize
open import Mu.Framework.AllUtil using (All; []; _∷_; pos)
open import proof.Framework.Lookup using (lvl-<; lvl-⊑; ⊑-∋-trans)
open import Framework.abt.GSubst using (_•_)

open import Data.Fin using (zero; suc)
open import Data.List using (List; []; _∷_; length)
open import Data.Nat.Properties using (<-irrefl)
import Relation.Binary.PropositionalEquality as Eq

module Mu.proof.Correctness.Scott.GlobalizeCorrect
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : propext 𝓤₀)
       where

open import Framework.Scott.Base pt fe
open import proof.Framework.Scott.Ops pt fe pe renaming (app to appᵈ; inl to inlᵈ; inr to inrᵈ; tuple to tupleᵈ; case to caseᵈ)
open import proof.Framework.Scott.Semantics pt fe pe
open import Semantics.Scott.Prim pt fe pe using (primD)
open import Mu.Semantics.Scott.Ops pt fe pe
open import Mu.Semantics.Scott.Clos4 pt fe pe renaming (⟦_⟧ to ⟦_⟧₄; ⟦_⟧s to ⟦_⟧s₄)
open import Mu.Semantics.Scott.Clos5 pt fe pe

≡→＝ : ∀ {A : Set} {x y : A} → x Eq.≡ y → x ＝ y
≡→＝ Eq.refl = refl

{- the code of a closure, of bodies that agree -}
codeᶜ-cong : (N N' : Den Env) → ((ρ : ⟨ Env ⟩) → N · ρ ＝ N' · ρ) → codeᶜ N ＝ codeᶜ N'
codeᶜ-cong N N' h =
  Λ-cong (∘₁ 𝔻 (𝔻 ⟹₁ 𝔻) 𝔻 (curry₁ 𝔻 𝔻 𝔻 B) Λ) (∘₁ 𝔻 (𝔻 ⟹₁ 𝔻) 𝔻 (curry₁ 𝔻 𝔻 𝔻 B') Λ)
    (λ X _ → Λ-cong (curry₁ 𝔻 𝔻 𝔻 B · X) (curry₁ 𝔻 𝔻 𝔻 B' · X) (λ Y _ → h (env₂ X Y)))
 where
  B B' : DCPO[ 𝔻 ×₁ 𝔻 , 𝔻 ]
  B = ∘₁ (𝔻 ×₁ 𝔻) Env 𝔻 env₂ᶜ N
  B' = ∘₁ (𝔻 ×₁ 𝔻) Env 𝔻 env₂ᶜ N'

{- Changing the table -----------------------------------------------------------------}

module _ {Σ Σ'} (r : ∀ {s} → Σ ∋ s → Σ' ∋ s) (T : Table Σ') (T' : Table Σ)
         (h : ∀ {s} (f : Σ ∋ s) → T' f ＝ T (r f)) where
  wk-sem : ∀ {Γ A} (M : Tm Σ Γ A) (ρ : ⟨ Env ⟩) → ⟦ M ⟧[ T' ] · ρ ＝ ⟦ wk r M ⟧[ T ] · ρ
  wks-sem : ∀ {Γ Δ} (Ms : All (Tm Σ Γ) Δ) (ρ : ⟨ Env ⟩) → ⟦ Ms ⟧s[ T' ] · ρ ＝ ⟦ wks r Ms ⟧s[ T ] · ρ
  wk-sem (` x) ρ = refl
  wk-sem (fun-ref f) ρ = h f
  wk-sem (pack L M) ρ = ap₂ (λ a b → pair · a · b) (wk-sem L ρ) (wk-sem M ρ)
  wk-sem (callc L M) ρ = ap₂ (λ a b → appᵈ · (appᵈ · (car · a) · (cdr · a)) · b) (wk-sem L ρ) (wk-sem M ρ)
  wk-sem (lit B c) ρ = refl
  wk-sem (tuple {Δ} Ms) ρ = ap (tupleᵈ (length Δ) ·_) (wks-sem Ms ρ)
  wk-sem (get i M) ρ = ap (proj (pos i) ·_) (wk-sem M ρ)
  wk-sem (inl M) ρ = ap (inlᵈ ·_) (wk-sem M ρ)
  wk-sem (inr M) ρ = ap (inrᵈ ·_) (wk-sem M ρ)
  wk-sem (case L M N) ρ =
    caseᶜ-cong ⟦ L ⟧[ T' ] ⟦ wk r L ⟧[ T ] ⟦ M ⟧[ T' ] ⟦ wk r M ⟧[ T ] ⟦ N ⟧[ T' ] ⟦ wk r N ⟧[ T ] ρ ρ
      (wk-sem L ρ) (λ d _ → wk-sem M (d • ρ)) (λ d _ → wk-sem N (d • ρ))
  wk-sem (prim p L M) ρ = ap₂ (λ a b → primD p · a · b) (wk-sem L ρ) (wk-sem M ρ)
  wk-sem (let′ M N) ρ =
    letᶜ-cong ⟦ M ⟧[ T' ] ⟦ wk r M ⟧[ T ] ⟦ N ⟧[ T' ] ⟦ wk r N ⟧[ T ] ρ ρ (wk-sem M ρ) (λ d _ → wk-sem N (d • ρ))
  wk-sem (fold M) ρ = wk-sem M ρ
  wk-sem (unfold M) ρ = wk-sem M ρ
  wks-sem [] ρ = refl
  wks-sem (M ∷ Ms) ρ = dfunext fe λ { zero → wk-sem M ρ ; (suc i) → happly (wks-sem Ms ρ) i }

{- The table of the definitions made so far ---------------------------------------------}

made : ∀ {Σ} → Made Σ → Table Σ
made (D ▷ N) Z = code′ (made D) N
made (D ▷ N) (S f) = made D f

{- D' extends D along s -}
record Ext {Σ Σ'} (s : Σ ⊑ Σ') (D : Made Σ) (D' : Made Σ') : 𝓤₁ ̇ where
  constructor mk-ext
  field agrees : ∀ {t} (f : Σ ∋ t) → made D' (⊑-∋ s f) ＝ made D f
open Ext

ext-trans : ∀ {Σ₀ Σ₁ Σ₂} {s₁ : Σ₀ ⊑ Σ₁} {s₂ : Σ₁ ⊑ Σ₂} {D₀ D₁ D₂}
  → Ext s₁ D₀ D₁ → Ext s₂ D₁ D₂ → Ext (⊑-trans s₁ s₂) D₀ D₂
ext-trans {s₁ = s₁} {s₂} {D₂ = D₂} e₁ e₂ = mk-ext λ f →
  ap (λ g → made D₂ g) (≡→＝ (⊑-∋-trans s₁ s₂ f)) ∙ agrees e₂ (⊑-∋ s₁ f) ∙ agrees e₁ f

{- a term made before more definitions, weakened to them -}
wk-made : ∀ {Σ Σ' Γ A} {s : Σ ⊑ Σ'} {D D'} → Ext s D D' → (M : Tm Σ Γ A) (ρ : ⟨ Env ⟩)
  → ⟦ M ⟧[ made D ] · ρ ＝ ⟦ wk (⊑-∋ s) M ⟧[ made D' ] · ρ
wk-made {s = s} {D} {D'} e = wk-sem (⊑-∋ s) (made D') (made D) (λ f → agrees e f ⁻¹)

{- What glob makes ----------------------------------------------------------------------}

record OK {Σ Γ A} (M : S.Tm Γ A) (D : Made Σ) (o : Out Σ (λ Σ' → Tm Σ' Γ A)) : 𝓤₁ ̇ where
  constructor mk-ok
  field ok-ext : Ext (Out.grows o) D (Out.made o)
        ok-sem : (ρ : ⟨ Env ⟩) → ⟦ M ⟧₄ · ρ ＝ ⟦ Out.res o ⟧[ made (Out.made o) ] · ρ
open OK

record OKs {Σ Γ Δ} (Ms : All (S.Tm Γ) Δ) (D : Made Σ) (o : Out Σ (λ Σ' → All (Tm Σ' Γ) Δ)) : 𝓤₁ ̇ where
  constructor mk-oks
  field oks-ext : Ext (Out.grows o) D (Out.made o)
        oks-sem : (ρ : ⟨ Env ⟩) → ⟦ Ms ⟧s₄ · ρ ＝ ⟦ Out.res o ⟧s[ made (Out.made o) ] · ρ

{- a construct of one or two operands means the same when they do -}
record Cong₁ {Γ Γ₁ A B} (f : ∀ {Σ'} → Tm Σ' Γ₁ A → Tm Σ' Γ B) (M : S.Tm Γ₁ A) (M₄ : S.Tm Γ B) : 𝓤₁ ̇ where
  constructor mk-cong₁
  field cong₁ : ∀ {Σ'} (T : Table Σ') M' → ((ρ : ⟨ Env ⟩) → ⟦ M ⟧₄ · ρ ＝ ⟦ M' ⟧[ T ] · ρ)
                → (ρ : ⟨ Env ⟩) → ⟦ M₄ ⟧₄ · ρ ＝ ⟦ f M' ⟧[ T ] · ρ
open Cong₁

record Cong₂ {Γ Γ₁ Γ₂ A B C} (f : ∀ {Σ'} → Tm Σ' Γ₁ A → Tm Σ' Γ₂ B → Tm Σ' Γ C) (L : S.Tm Γ₁ A) (M : S.Tm Γ₂ B)
             (M₄ : S.Tm Γ C) : 𝓤₁ ̇ where
  constructor mk-cong₂
  field cong₂ : ∀ {Σ'} (T : Table Σ') L' M' → ((ρ : ⟨ Env ⟩) → ⟦ L ⟧₄ · ρ ＝ ⟦ L' ⟧[ T ] · ρ)
                → ((ρ : ⟨ Env ⟩) → ⟦ M ⟧₄ · ρ ＝ ⟦ M' ⟧[ T ] · ρ) → (ρ : ⟨ Env ⟩) → ⟦ M₄ ⟧₄ · ρ ＝ ⟦ f L' M' ⟧[ T ] · ρ
open Cong₂

glob-ok : ∀ {Σ Γ A} (M : S.Tm Γ A) (D : Made Σ) → OK M D (glob M D)
globs-ok : ∀ {Σ Γ Δ} (Ms : All (S.Tm Γ) Δ) (D : Made Σ) → OKs Ms D (globs Ms D)
glob₁-ok : ∀ {Σ Γ Γ₁ A B} (f : ∀ {Σ'} → Tm Σ' Γ₁ A → Tm Σ' Γ B) (M : S.Tm Γ₁ A) (D : Made Σ) {M₄ : S.Tm Γ B}
  → Cong₁ f M M₄ → OK M₄ D (glob₁ f M D)
glob₂-ok : ∀ {Σ Γ Γ₁ Γ₂ A B C} (f : ∀ {Σ'} → Tm Σ' Γ₁ A → Tm Σ' Γ₂ B → Tm Σ' Γ C) (L : S.Tm Γ₁ A) (M : S.Tm Γ₂ B)
  (D : Made Σ) {M₄ : S.Tm Γ C} → Cong₂ f L M M₄ → OK M₄ D (glob₂ f L M D)

glob-ok (S.` x) D = mk-ok (mk-ext (λ f → refl)) λ ρ → refl
glob-ok (S.code N) D with glob N D | glob-ok N D
... | out s D' N' | mk-ok e h = mk-ok (mk-ext (agrees e)) λ ρ → codeᶜ-cong ⟦ N ⟧₄ ⟦ N' ⟧[ made D' ] h
glob-ok (S.pack L M) D = glob₂-ok pack L M D {M₄ = S.pack L M} (mk-cong₂ λ T L' M' hL hM ρ → ap₂ (λ a b → pair · a · b) (hL ρ) (hM ρ))
glob-ok (S.callc L M) D = glob₂-ok callc L M D {M₄ = S.callc L M}
  (mk-cong₂ λ T L' M' hL hM ρ → ap₂ (λ a b → appᵈ · (appᵈ · (car · a) · (cdr · a)) · b) (hL ρ) (hM ρ))
glob-ok (S.lit B c) D = mk-ok (mk-ext (λ f → refl)) λ ρ → refl
glob-ok (S.tuple {Δ} Ms) D with globs Ms D | globs-ok Ms D
... | out s D' Ms' | mk-oks e h = mk-ok e λ ρ → ap (tupleᵈ (length Δ) ·_) (h ρ)
glob-ok (S.get i M) D = glob₁-ok (get i) M D {M₄ = S.get i M} (mk-cong₁ λ T M' h ρ → ap (proj (pos i) ·_) (h ρ))
glob-ok (S.inl {B = B} M) D = glob₁-ok (inl {B = B}) M D {M₄ = S.inl M} (mk-cong₁ λ T M' h ρ → ap (inlᵈ ·_) (h ρ))
glob-ok (S.inr {A} M) D = glob₁-ok (inr {A = A}) M D {M₄ = S.inr M} (mk-cong₁ λ T M' h ρ → ap (inrᵈ ·_) (h ρ))
glob-ok (S.case L M N) D with glob L D | glob-ok L D
... | out s₁ D₁ L' | o₁ with glob M D₁ | glob-ok M D₁
...   | out s₂ D₂ M' | o₂ with glob N D₂ | glob-ok N D₂
...     | out s₃ D₃ N' | mk-ok e₃ h₃ =
  mk-ok (ext-trans (ok-ext o₁) (ext-trans (ok-ext o₂) e₃)) λ ρ →
    caseᶜ-cong ⟦ L ⟧₄ ⟦ wk (⊑-∋ (⊑-trans s₂ s₃)) L' ⟧[ made D₃ ] ⟦ M ⟧₄ ⟦ wk (⊑-∋ s₃) M' ⟧[ made D₃ ]
      ⟦ N ⟧₄ ⟦ N' ⟧[ made D₃ ] ρ ρ (ok-sem o₁ ρ ∙ wk-made (ext-trans (ok-ext o₂) e₃) L' ρ)
      (λ d _ → ok-sem o₂ (d • ρ) ∙ wk-made e₃ M' (d • ρ)) (λ d _ → h₃ (d • ρ))
glob-ok (S.prim p L M) D =
  glob₂-ok (prim p) L M D {M₄ = S.prim p L M} (mk-cong₂ λ T L' M' hL hM ρ → ap₂ (λ a b → primD p · a · b) (hL ρ) (hM ρ))
glob-ok (S.let′ M N) D = glob₂-ok let′ M N D {M₄ = S.let′ M N}
  (mk-cong₂ λ T M' N' hM hN ρ → letᶜ-cong ⟦ M ⟧₄ ⟦ M' ⟧[ T ] ⟦ N ⟧₄ ⟦ N' ⟧[ T ] ρ ρ (hM ρ) (λ d _ → hN (d • ρ)))
glob-ok (S.fold {A} M) D = glob₁-ok (fold {A = A}) M D {M₄ = S.fold M} (mk-cong₁ λ T M' h → h)
glob-ok (S.unfold {A} M) D = glob₁-ok (unfold {A = A}) M D {M₄ = S.unfold M} (mk-cong₁ λ T M' h → h)

globs-ok [] D = mk-oks (mk-ext (λ f → refl)) λ ρ → refl
globs-ok (M ∷ Ms) D with glob M D | glob-ok M D
... | out s₁ D₁ M' | o₁ with globs Ms D₁ | globs-ok Ms D₁
...   | out s₂ D₂ Ms' | mk-oks e₂ h₂ =
  mk-oks (ext-trans (ok-ext o₁) e₂) λ ρ → dfunext fe λ { zero → ok-sem o₁ ρ ∙ wk-made e₂ M' ρ ; (suc i) → happly (h₂ ρ) i }

glob₁-ok f M D c with glob M D | glob-ok M D
... | out s D' M' | mk-ok e h = mk-ok e (cong₁ c (made D') M' h)

glob₂-ok f L M D c with glob L D | glob-ok L D
... | out s₁ D₁ L' | o₁ with glob M D₁ | glob-ok M D₁
...   | out s₂ D₂ M' | mk-ok e₂ h₂ = mk-ok (ext-trans (ok-ext o₁) e₂) (cong₂ c (made D₂) (wk (⊑-∋ s₂) L') M' (λ ρ → ok-sem o₁ ρ ∙ wk-made e₂ L' ρ) h₂)

{- The table of the program ------------------------------------------------------------}

table-close : ∀ {Σ Σ'} (D : Made Σ') (s : Σ' ⊑ Σ) {t} (f : Σ' ∋ t) → made D f ＝ tables code′ (close D s) (⊑-∋ s f)
table-close (D ▷ N) s Z =
  codeᶜ-cong ⟦ N ⟧[ made D ] ⟦ wk (⊑-∋ s') N ⟧[ tables code′ (close D s') ]
    (wk-sem (⊑-∋ s') (tables code′ (close D s')) (made D) (table-close D s') N)
  ∙ tables-yes code′ (wk (⊑-∋ s') N) (close D s') (⊑-∋ s Z) (lvl-⊑ s Z) ⁻¹
  where s' = ⊑-trans (there⊑ here⊑) s
table-close (D ▷ N) s (S f) =
  table-close D s' f
  ∙ ap (λ g → tables code′ (close D s') g) (≡→＝ (⊑-∋-trans (there⊑ here⊑) s f))
  ∙ tables-no code′ (wk (⊑-∋ s') N) (close D s') (⊑-∋ s (S f))
      (λ eq → <-irrefl (Eq.trans (Eq.sym (lvl-⊑ s (S f))) eq) (lvl-< f)) ⁻¹
  where s' = ⊑-trans (there⊑ here⊑) s

wk-id : ∀ {Σ Γ A} (M : Tm Σ Γ A) → wk (λ f → f) M Eq.≡ M
wks-id : ∀ {Σ Γ Δ} (Ms : All (Tm Σ Γ) Δ) → wks (λ f → f) Ms Eq.≡ Ms
wk-id (` x) = Eq.refl
wk-id (fun-ref f) = Eq.refl
wk-id (pack L M) = Eq.cong₂ pack (wk-id L) (wk-id M)
wk-id (callc L M) = Eq.cong₂ callc (wk-id L) (wk-id M)
wk-id (lit B c) = Eq.refl
wk-id (tuple Ms) = Eq.cong tuple (wks-id Ms)
wk-id (get i M) = Eq.cong (get i) (wk-id M)
wk-id (inl M) = Eq.cong inl (wk-id M)
wk-id (inr M) = Eq.cong inr (wk-id M)
wk-id (case L M N) = Eq.cong₂ (λ L' (P : _ × _) → case L' (pr₁ P) (pr₂ P)) (wk-id L) (Eq.cong₂ _,_ (wk-id M) (wk-id N))
wk-id (prim p L M) = Eq.cong₂ (prim p) (wk-id L) (wk-id M)
wk-id (let′ M N) = Eq.cong₂ let′ (wk-id M) (wk-id N)
wk-id (fold {A} M) = Eq.cong (fold {A = A}) (wk-id M)
wk-id (unfold {A} M) = Eq.cong (unfold {A = A}) (wk-id M)
wks-id [] = Eq.refl
wks-id (M ∷ Ms) = Eq.cong₂ _∷_ (wk-id M) (wks-id Ms)

{- The pass preserves the meaning of a closed program -----------------------------------}

programO : ∀ {A} → Out [] (λ Σ' → Tm Σ' [] A) → Program A
programO (out _ D M') = program (close D here⊑) M'

globalize-eq : ∀ {A} (M : S.Tm [] A) → globalize M Eq.≡ programO (glob M [])
globalize-eq M with glob M []
... | out _ _ _ = Eq.refl

program-ok : ∀ {A} (M : S.Tm [] A) o → OK M [] o → ⟦ M ⟧₄ · ρ₀ ＝ ⟦ programO o ⟧ₚ
program-ok M (out _ D M') (mk-ok _ h) =
  h ρ₀
  ∙ wk-sem (λ f → f) (tables code′ (close D here⊑)) (made D) (table-close D here⊑) M' ρ₀
  ∙ ap (λ N → ⟦ N ⟧[ tables code′ (close D here⊑) ] · ρ₀) (≡→＝ (wk-id M'))

globalize-correct : ∀ {A} (M : S.Tm [] A) → ⟦ M ⟧₄ · ρ₀ ＝ ⟦ globalize M ⟧ₚ
globalize-correct M = program-ok M (glob M []) (glob-ok M []) ∙ ap ⟦_⟧ₚ (≡→＝ (globalize-eq M)) ⁻¹

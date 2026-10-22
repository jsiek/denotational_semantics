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

  Unlike the graph-model proof, the recursive lemmas use no `with` (it
  makes Agda very slow here): what glob makes is taken apart by
  auxiliary functions on its result (codeO, glob₂O, ...), equal to glob
  by syntactic lemmas (glob-code, glob₂-eq, ...), and the tables of
  Mu/Semantics/Scott/Ops.agda by tables-yes and tables-no. The
  predicates OK, OKs, Cong₁ and Cong₂ are records, so that Agda compares
  them by their indices rather than by unfolding them to meanings, and
  the recursion glob-ok only calls a lemma for each construct.

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

{- (records, as are Cong₁ and Cong₂ below, so that Agda compares them by
   their indices, never by unfolding them to meanings) -}
record OK {Σ Γ A} (M : S.Tm Γ A) (D : Made Σ) (o : Out Σ (λ Σ' → Tm Σ' Γ A)) : 𝓤₁ ̇ where
  constructor mk-ok
  field ok-ext : Ext (Out.grows o) D (Out.made o)
        ok-sem : (ρ : ⟨ Env ⟩) → ⟦ M ⟧₄ · ρ ＝ ⟦ Out.res o ⟧[ made (Out.made o) ] · ρ

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

{- glob, taken apart: what it does with the result of a recursive call -}
codeO : ∀ {Σ Γ Δ A B} → Out Σ (λ Σ' → Code Σ' (sig Δ A B)) → Out Σ (λ Σ' → Tm Σ' Γ (code Δ A B))
codeO (out s D' N') = out (there⊑ s) (D' ▷ N') (fun-ref Z)

tupleO : ∀ {Σ Γ Δ} → Out Σ (λ Σ' → All (Tm Σ' Γ) Δ) → Out Σ (λ Σ' → Tm Σ' Γ (tup Δ))
tupleO (out s D' Ms') = out s D' (tuple Ms')

glob₁O : ∀ {Σ Γ Γ₁ A B} → (∀ {Σ'} → Tm Σ' Γ₁ A → Tm Σ' Γ B) → Out Σ (λ Σ' → Tm Σ' Γ₁ A) → Out Σ (λ Σ' → Tm Σ' Γ B)
glob₁O f (out s D' M') = out s D' (f M')

glob₂O′ : ∀ {Σ Σ₁ Γ Γ₁ Γ₂ A B C} → (∀ {Σ'} → Tm Σ' Γ₁ A → Tm Σ' Γ₂ B → Tm Σ' Γ C)
  → Σ ⊑ Σ₁ → Tm Σ₁ Γ₁ A → Out Σ₁ (λ Σ' → Tm Σ' Γ₂ B) → Out Σ (λ Σ' → Tm Σ' Γ C)
glob₂O′ f s₁ L' (out s₂ D₂ M') = out (⊑-trans s₁ s₂) D₂ (f (wk (⊑-∋ s₂) L') M')

glob₂O : ∀ {Σ Γ Γ₁ Γ₂ A B C} → (∀ {Σ'} → Tm Σ' Γ₁ A → Tm Σ' Γ₂ B → Tm Σ' Γ C)
  → S.Tm Γ₂ B → Out Σ (λ Σ' → Tm Σ' Γ₁ A) → Out Σ (λ Σ' → Tm Σ' Γ C)
glob₂O f M (out s₁ D₁ L') = glob₂O′ f s₁ L' (glob M D₁)

globsO′ : ∀ {Σ Σ₁ Γ A Δ} → Σ ⊑ Σ₁ → Tm Σ₁ Γ A → Out Σ₁ (λ Σ' → All (Tm Σ' Γ) Δ) → Out Σ (λ Σ' → All (Tm Σ' Γ) (A ∷ Δ))
globsO′ s₁ M' (out s₂ D₂ Ms') = out (⊑-trans s₁ s₂) D₂ (wk (⊑-∋ s₂) M' ∷ Ms')

globsO : ∀ {Σ Γ A Δ} → All (S.Tm Γ) Δ → Out Σ (λ Σ' → Tm Σ' Γ A) → Out Σ (λ Σ' → All (Tm Σ' Γ) (A ∷ Δ))
globsO Ms (out s₁ D₁ M') = globsO′ s₁ M' (globs Ms D₁)

caseO″ : ∀ {Σ Σ₁ Σ₂ Γ A B C} → Σ ⊑ Σ₁ → Σ₁ ⊑ Σ₂ → Tm Σ₁ Γ (A ⊹ B) → Tm Σ₂ (A ∷ Γ) C
  → Out Σ₂ (λ Σ' → Tm Σ' (B ∷ Γ) C) → Out Σ (λ Σ' → Tm Σ' Γ C)
caseO″ s₁ s₂ L' M' (out s₃ D₃ N') =
  out (⊑-trans s₁ (⊑-trans s₂ s₃)) D₃ (case (wk (⊑-∋ (⊑-trans s₂ s₃)) L') (wk (⊑-∋ s₃) M') N')

caseO′ : ∀ {Σ Σ₁ Γ A B C} → Σ ⊑ Σ₁ → Tm Σ₁ Γ (A ⊹ B) → S.Tm (B ∷ Γ) C
  → Out Σ₁ (λ Σ' → Tm Σ' (A ∷ Γ) C) → Out Σ (λ Σ' → Tm Σ' Γ C)
caseO′ s₁ L' N (out s₂ D₂ M') = caseO″ s₁ s₂ L' M' (glob N D₂)

caseO : ∀ {Σ Γ A B C} → S.Tm (A ∷ Γ) C → S.Tm (B ∷ Γ) C → Out Σ (λ Σ' → Tm Σ' Γ (A ⊹ B)) → Out Σ (λ Σ' → Tm Σ' Γ C)
caseO M N (out s₁ D₁ L') = caseO′ s₁ L' N (glob M D₁)

{- (these mention no values, so `with` is harmless) -}
module _ {Σ} (D : Made Σ) where
  glob-code : ∀ {Γ Δ A B} (N : S.Tm (A ∷ tup Δ ∷ []) B) → glob {Γ = Γ} (S.code N) D Eq.≡ codeO (glob N D)
  glob-code N with glob N D
  ... | out _ _ _ = Eq.refl

  glob-tuple : ∀ {Γ Δ} (Ms : All (S.Tm Γ) Δ) → glob (S.tuple Ms) D Eq.≡ tupleO (globs Ms D)
  glob-tuple Ms with globs Ms D
  ... | out _ _ _ = Eq.refl

  glob₁-eq : ∀ {Γ Γ₁ A B} (f : ∀ {Σ'} → Tm Σ' Γ₁ A → Tm Σ' Γ B) (M : S.Tm Γ₁ A) → glob₁ f M D Eq.≡ glob₁O f (glob M D)
  glob₁-eq f M with glob M D
  ... | out _ _ _ = Eq.refl

  glob₂-eq : ∀ {Γ Γ₁ Γ₂ A B C} (f : ∀ {Σ'} → Tm Σ' Γ₁ A → Tm Σ' Γ₂ B → Tm Σ' Γ C) (L : S.Tm Γ₁ A) (M : S.Tm Γ₂ B)
    → glob₂ f L M D Eq.≡ glob₂O f M (glob L D)
  glob₂-eq f L M with glob L D
  ... | out _ D₁ _ with glob M D₁
  ...   | out _ _ _ = Eq.refl

  globs-eq : ∀ {Γ A Δ} (M : S.Tm Γ A) (Ms : All (S.Tm Γ) Δ) → globs (M ∷ Ms) D Eq.≡ globsO Ms (glob M D)
  globs-eq M Ms with glob M D
  ... | out _ D₁ _ with globs Ms D₁
  ...   | out _ _ _ = Eq.refl

  glob-case : ∀ {Γ A B C} (L : S.Tm Γ (A ⊹ B)) (M : S.Tm (A ∷ Γ) C) (N : S.Tm (B ∷ Γ) C)
    → glob (S.case L M N) D Eq.≡ caseO M N (glob L D)
  glob-case L M N with glob L D
  ... | out _ D₁ _ with glob M D₁
  ...   | out _ D₂ _ with glob N D₂
  ...     | out _ _ _ = Eq.refl

{- what each part makes means what the source does -}
code-ok : ∀ {Σ Γ Δ A B} (N : S.Tm (A ∷ tup Δ ∷ []) B) (D : Made Σ) o → OK N D o → OK {Γ = Γ} (S.code N) D (codeO o)
code-ok N D (out s D' N') (mk-ok e h) = mk-ok (mk-ext (agrees e)) λ ρ → codeᶜ-cong ⟦ N ⟧₄ ⟦ N' ⟧[ made D' ] h

tuple-ok : ∀ {Σ Γ Δ} (Ms : All (S.Tm Γ) Δ) (D : Made Σ) o → OKs Ms D o → OK (S.tuple Ms) D (tupleO o)
tuple-ok {Δ = Δ} Ms D (out s D' Ms') (mk-oks e h) = mk-ok e λ ρ → ap (tupleᵈ (length Δ) ·_) (h ρ)

glob₁-ok : ∀ {Σ Γ Γ₁ A B} (f : ∀ {Σ'} → Tm Σ' Γ₁ A → Tm Σ' Γ B) (M : S.Tm Γ₁ A) (D : Made Σ) {M₄ : S.Tm Γ B} o
  → OK M D o → Cong₁ f M M₄ → OK M₄ D (glob₁O f o)
glob₁-ok f M D (out s D' M') (mk-ok e h) c = mk-ok e (cong₁ c (made D') M' h)

module _ {Σ Γ Γ₁ Γ₂ A B C} (f : ∀ {Σ'} → Tm Σ' Γ₁ A → Tm Σ' Γ₂ B → Tm Σ' Γ C) (L : S.Tm Γ₁ A) (M : S.Tm Γ₂ B)
         (D : Made Σ) {M₄ : S.Tm Γ C} (c : Cong₂ f L M M₄) where
  glob₂-ok′ : ∀ {Σ₁} (s₁ : Σ ⊑ Σ₁) (D₁ : Made Σ₁) (L' : Tm Σ₁ Γ₁ A) → Ext s₁ D D₁ → ((ρ : ⟨ Env ⟩) → ⟦ L ⟧₄ · ρ ＝ ⟦ L' ⟧[ made D₁ ] · ρ)
    → ∀ o → OK M D₁ o → OK M₄ D (glob₂O′ f s₁ L' o)
  glob₂-ok′ s₁ D₁ L' e₁ h₁ (out s₂ D₂ M') (mk-ok e₂ h₂) =
    mk-ok (ext-trans e₁ e₂) (cong₂ c (made D₂) (wk (⊑-∋ s₂) L') M' (λ ρ → h₁ ρ ∙ wk-made e₂ L' ρ) h₂)

  glob₂-ok : ∀ o → OK L D o → (∀ {Σ'} (D' : Made Σ') → OK M D' (glob M D')) → OK M₄ D (glob₂O f M o)
  glob₂-ok (out s₁ D₁ L') (mk-ok e₁ h₁) okM = glob₂-ok′ s₁ D₁ L' e₁ h₁ (glob M D₁) (okM D₁)

  glob₂-sem : OK L D (glob L D) → (∀ {Σ'} (D' : Made Σ') → OK M D' (glob M D')) → OK M₄ D (glob₂ f L M D)
  glob₂-sem okL okM = Eq.subst (OK M₄ D) (Eq.sym (glob₂-eq D f L M)) (glob₂-ok (glob L D) okL okM)

module _ {Σ Γ A Δ} (M : S.Tm Γ A) (Ms : All (S.Tm Γ) Δ) (D : Made Σ) where
  globs-ok′ : ∀ {Σ₁} (s₁ : Σ ⊑ Σ₁) (D₁ : Made Σ₁) (M' : Tm Σ₁ Γ A) → Ext s₁ D D₁ → ((ρ : ⟨ Env ⟩) → ⟦ M ⟧₄ · ρ ＝ ⟦ M' ⟧[ made D₁ ] · ρ)
    → ∀ o → OKs Ms D₁ o → OKs (M ∷ Ms) D (globsO′ s₁ M' o)
  globs-ok′ s₁ D₁ M' e₁ h₁ (out s₂ D₂ Ms') (mk-oks e₂ h₂) =
    mk-oks (ext-trans e₁ e₂) λ ρ → dfunext fe λ { zero → h₁ ρ ∙ wk-made e₂ M' ρ ; (suc i) → happly (h₂ ρ) i }

  globs-ok∷ : ∀ o → OK M D o → (∀ {Σ'} (D' : Made Σ') → OKs Ms D' (globs Ms D')) → OKs (M ∷ Ms) D (globsO Ms o)
  globs-ok∷ (out s₁ D₁ M') (mk-ok e₁ h₁) okMs = globs-ok′ s₁ D₁ M' e₁ h₁ (globs Ms D₁) (okMs D₁)

module _ {Σ Γ A B C} (L : S.Tm Γ (A ⊹ B)) (M : S.Tm (A ∷ Γ) C) (N : S.Tm (B ∷ Γ) C) (D : Made Σ) where
  case-ok″ : ∀ {Σ₁ Σ₂} (s₁ : Σ ⊑ Σ₁) (s₂ : Σ₁ ⊑ Σ₂) (D₁ : Made Σ₁) (D₂ : Made Σ₂) (L' : Tm Σ₁ Γ (A ⊹ B)) (M' : Tm Σ₂ (A ∷ Γ) C)
    → Ext s₁ D D₁ → ((ρ : ⟨ Env ⟩) → ⟦ L ⟧₄ · ρ ＝ ⟦ L' ⟧[ made D₁ ] · ρ)
    → Ext s₂ D₁ D₂ → ((ρ : ⟨ Env ⟩) → ⟦ M ⟧₄ · ρ ＝ ⟦ M' ⟧[ made D₂ ] · ρ)
    → ∀ o → OK N D₂ o → OK (S.case L M N) D (caseO″ s₁ s₂ L' M' o)
  case-ok″ s₁ s₂ D₁ D₂ L' M' e₁ h₁ e₂ h₂ (out s₃ D₃ N') (mk-ok e₃ h₃) =
    mk-ok (ext-trans e₁ (ext-trans e₂ e₃)) λ ρ →
      caseᶜ-cong ⟦ L ⟧₄ ⟦ wk (⊑-∋ (⊑-trans s₂ s₃)) L' ⟧[ made D₃ ] ⟦ M ⟧₄ ⟦ wk (⊑-∋ s₃) M' ⟧[ made D₃ ]
        ⟦ N ⟧₄ ⟦ N' ⟧[ made D₃ ] ρ ρ (h₁ ρ ∙ wk-made (ext-trans e₂ e₃) L' ρ)
        (λ d _ → h₂ (d • ρ) ∙ wk-made e₃ M' (d • ρ)) (λ d _ → h₃ (d • ρ))

  case-ok′ : ∀ {Σ₁} (s₁ : Σ ⊑ Σ₁) (D₁ : Made Σ₁) (L' : Tm Σ₁ Γ (A ⊹ B)) → Ext s₁ D D₁ → ((ρ : ⟨ Env ⟩) → ⟦ L ⟧₄ · ρ ＝ ⟦ L' ⟧[ made D₁ ] · ρ)
    → (∀ {Σ'} (D' : Made Σ') → OK N D' (glob N D')) → ∀ o → OK M D₁ o → OK (S.case L M N) D (caseO′ s₁ L' N o)
  case-ok′ s₁ D₁ L' e₁ h₁ okN (out s₂ D₂ M') (mk-ok e₂ h₂) = case-ok″ s₁ s₂ D₁ D₂ L' M' e₁ h₁ e₂ h₂ (glob N D₂) (okN D₂)

  case-ok : ∀ o → OK L D o → (∀ {Σ'} (D' : Made Σ') → OK M D' (glob M D')) → (∀ {Σ'} (D' : Made Σ') → OK N D' (glob N D'))
    → OK (S.case L M N) D (caseO M N o)
  case-ok (out s₁ D₁ L') (mk-ok e₁ h₁) okM okN = case-ok′ s₁ D₁ L' e₁ h₁ okN (glob M D₁) (okM D₁)

glob₁-sem : ∀ {Σ Γ Γ₁ A B} (f : ∀ {Σ'} → Tm Σ' Γ₁ A → Tm Σ' Γ B) (M : S.Tm Γ₁ A) (D : Made Σ) {M₄ : S.Tm Γ B}
  → OK M D (glob M D) → Cong₁ f M M₄ → OK M₄ D (glob₁ f M D)
glob₁-sem f M D {M₄} ok c = Eq.subst (OK M₄ D) (Eq.sym (glob₁-eq D f M)) (glob₁-ok f M D {M₄ = M₄} (glob M D) ok c)

{- each construct, given what glob makes of its parts (not recursive, so
   that the recursion of glob-ok below is only a skeleton) -}
code-sem : ∀ {Σ Γ Δ A B} (N : S.Tm (A ∷ tup Δ ∷ []) B) (D : Made Σ) → OK N D (glob N D)
  → OK {Γ = Γ} (S.code N) D (glob (S.code N) D)
code-sem {Γ = Γ} N D ok = Eq.subst (OK {Γ = Γ} (S.code N) D) (Eq.sym (glob-code D N)) (code-ok {Γ = Γ} N D (glob N D) ok)

tuple-sem : ∀ {Σ Γ Δ} (Ms : All (S.Tm Γ) Δ) (D : Made Σ) → OKs Ms D (globs Ms D) → OK (S.tuple Ms) D (glob (S.tuple Ms) D)
tuple-sem Ms D ok = Eq.subst (OK (S.tuple Ms) D) (Eq.sym (glob-tuple D Ms)) (tuple-ok Ms D (globs Ms D) ok)

case-sem : ∀ {Σ Γ A B C} (L : S.Tm Γ (A ⊹ B)) (M : S.Tm (A ∷ Γ) C) (N : S.Tm (B ∷ Γ) C) (D : Made Σ)
  → OK L D (glob L D) → (∀ {Σ'} (D' : Made Σ') → OK M D' (glob M D')) → (∀ {Σ'} (D' : Made Σ') → OK N D' (glob N D'))
  → OK (S.case L M N) D (glob (S.case L M N) D)
case-sem L M N D okL okM okN =
  Eq.subst (OK (S.case L M N) D) (Eq.sym (glob-case D L M N)) (case-ok L M N D (glob L D) okL okM okN)

globs-sem : ∀ {Σ Γ A Δ} (M : S.Tm Γ A) (Ms : All (S.Tm Γ) Δ) (D : Made Σ) → OK M D (glob M D)
  → (∀ {Σ'} (D' : Made Σ') → OKs Ms D' (globs Ms D')) → OKs (M ∷ Ms) D (globs (M ∷ Ms) D)
globs-sem M Ms D ok okMs = Eq.subst (OKs (M ∷ Ms) D) (Eq.sym (globs-eq D M Ms)) (globs-ok∷ M Ms D (glob M D) ok okMs)

{- the constructs of one or two operands -}
module _ {Σ Γ} (D : Made Σ) where
  pack-sem : ∀ {Δ A B} (L : S.Tm Γ (code Δ A B)) (M : S.Tm Γ (tup Δ)) → OK L D (glob L D)
    → (∀ {Σ'} (D' : Made Σ') → OK M D' (glob M D')) → OK (S.pack L M) D (glob (S.pack L M) D)
  pack-sem L M = glob₂-sem pack L M D {M₄ = S.pack L M} (mk-cong₂ λ T L' M' hL hM ρ → ap₂ (λ a b → pair · a · b) (hL ρ) (hM ρ))

  callc-sem : ∀ {A B} (L : S.Tm Γ (A ⇒ B)) (M : S.Tm Γ A) → OK L D (glob L D)
    → (∀ {Σ'} (D' : Made Σ') → OK M D' (glob M D')) → OK (S.callc L M) D (glob (S.callc L M) D)
  callc-sem L M = glob₂-sem callc L M D {M₄ = S.callc L M}
    (mk-cong₂ λ T L' M' hL hM ρ → ap₂ (λ a b → appᵈ · (appᵈ · (car · a) · (cdr · a)) · b) (hL ρ) (hM ρ))

  prim-sem : ∀ p (L M : S.Tm Γ (base Int)) → OK L D (glob L D)
    → (∀ {Σ'} (D' : Made Σ') → OK M D' (glob M D')) → OK (S.prim p L M) D (glob (S.prim p L M) D)
  prim-sem p L M = glob₂-sem (prim p) L M D {M₄ = S.prim p L M} (mk-cong₂ λ T L' M' hL hM ρ → ap₂ (λ a b → primD p · a · b) (hL ρ) (hM ρ))

  let-sem : ∀ {A B} (M : S.Tm Γ A) (N : S.Tm (A ∷ Γ) B) → OK M D (glob M D)
    → (∀ {Σ'} (D' : Made Σ') → OK N D' (glob N D')) → OK (S.let′ M N) D (glob (S.let′ M N) D)
  let-sem M N = glob₂-sem let′ M N D {M₄ = S.let′ M N}
    (mk-cong₂ λ T M' N' hM hN ρ → letᶜ-cong ⟦ M ⟧₄ ⟦ M' ⟧[ T ] ⟦ N ⟧₄ ⟦ N' ⟧[ T ] ρ ρ (hM ρ) (λ d _ → hN (d • ρ)))

  get-sem : ∀ {Δ A} (i : Δ ∋ A) (M : S.Tm Γ (tup Δ)) → OK M D (glob M D) → OK (S.get i M) D (glob (S.get i M) D)
  get-sem i M ok = glob₁-sem (get i) M D {M₄ = S.get i M} ok (mk-cong₁ λ T M' h ρ → ap (proj (pos i) ·_) (h ρ))

  inl-sem : ∀ {A B} (M : S.Tm Γ A) → OK M D (glob M D) → OK (S.inl {B = B} M) D (glob (S.inl M) D)
  inl-sem {B = B} M ok = glob₁-sem (inl {B = B}) M D {M₄ = S.inl M} ok (mk-cong₁ λ T M' h ρ → ap (inlᵈ ·_) (h ρ))

  inr-sem : ∀ {A B} (M : S.Tm Γ B) → OK M D (glob M D) → OK (S.inr {A = A} M) D (glob (S.inr M) D)
  inr-sem {A = A} M ok = glob₁-sem (inr {A = A}) M D {M₄ = S.inr M} ok (mk-cong₁ λ T M' h ρ → ap (inrᵈ ·_) (h ρ))

  fold-sem : ∀ {A} (M : S.Tm Γ (unrollᵗ A)) → OK M D (glob M D) → OK (S.fold {A = A} M) D (glob (S.fold {A = A} M) D)
  fold-sem {A} M ok = glob₁-sem (fold {A = A}) M D {M₄ = S.fold {A = A} M} ok (mk-cong₁ λ T M' h → h)

  unfold-sem : ∀ {A} (M : S.Tm Γ (μ A)) → OK M D (glob M D) → OK (S.unfold M) D (glob (S.unfold M) D)
  unfold-sem {A} M ok = glob₁-sem (unfold {A = A}) M D {M₄ = S.unfold M} ok (mk-cong₁ λ T M' h → h)

glob-ok : ∀ {Σ Γ A} (M : S.Tm Γ A) (D : Made Σ) → OK M D (glob M D)
globs-ok : ∀ {Σ Γ Δ} (Ms : All (S.Tm Γ) Δ) (D : Made Σ) → OKs Ms D (globs Ms D)

glob-ok (S.` x) D = mk-ok (mk-ext (λ f → refl)) λ ρ → refl
glob-ok {Γ = Γ} (S.code N) D = code-sem {Γ = Γ} N D (glob-ok N D)
glob-ok (S.pack L M) D = pack-sem D L M (glob-ok L D) (glob-ok M)
glob-ok (S.callc L M) D = callc-sem D L M (glob-ok L D) (glob-ok M)
glob-ok (S.lit B c) D = mk-ok (mk-ext (λ f → refl)) λ ρ → refl
glob-ok (S.tuple Ms) D = tuple-sem Ms D (globs-ok Ms D)
glob-ok (S.get i M) D = get-sem D i M (glob-ok M D)
glob-ok (S.inl {B = B} M) D = inl-sem D {B = B} M (glob-ok M D)
glob-ok (S.inr {A} M) D = inr-sem D {A = A} M (glob-ok M D)
glob-ok (S.case L M N) D = case-sem L M N D (glob-ok L D) (glob-ok M) (glob-ok N)
glob-ok (S.prim p L M) D = prim-sem D p L M (glob-ok L D) (glob-ok M)
glob-ok (S.let′ M N) D = let-sem D M N (glob-ok M D) (glob-ok N)
glob-ok (S.fold {A} M) D = fold-sem D {A = A} M (glob-ok M D)
glob-ok (S.unfold {A} M) D = unfold-sem D {A = A} M (glob-ok M D)

globs-ok [] D = mk-oks (mk-ext (λ f → refl)) λ ρ → refl
globs-ok (M ∷ Ms) D = globs-sem M Ms D (glob-ok M D) (globs-ok Ms)

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

{-

  Correctness of typed globalize (Clos4ᵀ → Clos5ᵀ) in the graph model
  (Semantics/Graph/Typed/{Clos4,Clos5}.agda): the pass preserves
  denotations exactly.

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

-}

module proof.Correctness.Graph.GlobalizeCorrect where

open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.DOpSig
open import proof.Framework.GraphModel.Domain
open import proof.Framework.GraphModel.Ops renaming (inl to inlD; inr to inrD)
open import proof.Framework.GraphModel.ContinuityBase using (mono)
open import proof.Semantics.Graph.Prim using (primD-≃)
open import proof.Semantics.Graph.Typed.Ops
open import Semantics.Graph.Typed.Clos5
open import proof.Semantics.Graph.Typed.Clos4 using () renaming (⟦_⟧ to ⟦_⟧₄; ⟦_⟧s to ⟦_⟧s₄)
open import Language.Typed.Type hiding (_≟_)
open import Framework.Membership using (_⊑_; here⊑; there⊑; ⊑-∋; ⊑-trans)
import Language.Typed.Clos4 as S
open import Language.Typed.Clos5
open import Compiler.Globalize
open import proof.Framework.Lookup using (lvl-<; lvl-⊑; ⊑-∋-trans)

open import Data.Empty using (⊥-elim)
open import Data.Fin using (zero; suc)
open import Data.List using (List; []; _∷_; length)
open import Data.Nat using (ℕ; _≟_)
open import Data.Nat.Properties using (<-irrefl)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Unit using (⊤)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Data.Vec using (Vec; []; _∷_)
open import Level using (lift)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary using (yes; no)

pair-≃ : ∀ {D D' E E'} → D ≃ D' → E ≃ E' → pair ⟨ D , ⟨ E , ptt ⟩ ⟩ ≃ pair ⟨ D' , ⟨ E' , ptt ⟩ ⟩
pair-≃ a b = mono-≃ pair-mono ⟨ lift a , ⟨ lift b , ptt ⟩ ⟩

callc-≃ : ∀ {D D' E E'} → D ≃ D' → E ≃ E' → callcᵈ ⟨ D , ⟨ E , ptt ⟩ ⟩ ≃ callcᵈ ⟨ D' , ⟨ E' , ptt ⟩ ⟩
callc-≃ a b = mono-≃ (mono (callc-good {⊤})) ⟨ lift a , ⟨ lift b , ptt ⟩ ⟩

{- Changing the table -----------------------------------------------------------------}

module _ {Σ Σ'} (r : ∀ {n} → Σ ∋ n → Σ' ∋ n) {T : Table Σ'} {T' : Table Σ}
         (h : ∀ {n} (f : Σ ∋ n) → T (r f) ≃ T' f) where
  wk-sem : ∀ {Γ A} (M : Tm Σ Γ A) ρ → ⟦ wk r M ⟧[ T ] ρ ≃ ⟦ M ⟧[ T' ] ρ
  wks-sem : ∀ {Γ n} (Ms : Vec (Tm Σ Γ Any) n) ρ i → nthD (⟦ wks r Ms ⟧s[ T ] ρ) i ≃ nthD (⟦ Ms ⟧s[ T' ] ρ) i
  wk-sem (` x) ρ = ≃-refl
  wk-sem (fun-ref f) ρ = h f
  wk-sem (pack L M) ρ = pair-≃ (wk-sem L ρ) (wk-sem M ρ)
  wk-sem (callc L M) ρ = callc-≃ (wk-sem L ρ) (wk-sem M ρ)
  wk-sem (lit B c) ρ = ≃-refl
  wk-sem (tuple Ms) ρ = 𝒯-≃ _ (wks-sem Ms ρ)
  wk-sem (get i M) ρ = proj-≃ i (wk-sem M ρ)
  wk-sem (inl M) ρ = inl-≃ (wk-sem M ρ)
  wk-sem (inr M) ρ = inr-≃ (wk-sem M ρ)
  wk-sem (case L M N) ρ = 𝒞-≃ {F = λ X → ⟦ wk r M ⟧[ T ] (X • ρ)} {λ X → ⟦ M ⟧[ T' ] (X • ρ)}
    {λ X → ⟦ wk r N ⟧[ T ] (X • ρ)} {λ X → ⟦ N ⟧[ T' ] (X • ρ)} (wk-sem L ρ) (λ _ _ _ → wk-sem M _) (λ _ _ _ → wk-sem N _)
  wk-sem (prim p L M) ρ = primD-≃ p (wk-sem L ρ) (wk-sem M ρ)
  wk-sem (let′ M N) ρ = letD-≃ {F = λ X → ⟦ wk r N ⟧[ T ] (X • ρ)} {λ X → ⟦ N ⟧[ T' ] (X • ρ)} (wk-sem M ρ) (λ _ _ _ → wk-sem N _)
  wk-sem (inject G M) ρ = wk-sem M ρ
  wk-sem (project t M) ρ = project-≃ fun₄ t (wk-sem M ρ)
  wks-sem (M ∷ Ms) ρ zero = wk-sem M ρ
  wks-sem (M ∷ Ms) ρ (suc i) = wks-sem Ms ρ i

{- The table of the definitions made so far ---------------------------------------------}

made : ∀ {Σ} → Made Σ → Table Σ
made (D ▷ N) Z = code′ (made D) N
made (D ▷ N) (S f) = made D f

{- D' extends D along s -}
record Ext {Σ Σ'} (s : Σ ⊑ Σ') (D : Made Σ) (D' : Made Σ') : Set₁ where
  constructor ext
  field at : ∀ {n} (f : Σ ∋ n) → made D' (⊑-∋ s f) ≡ made D f
open Ext

ext-trans : ∀ {Σ₀ Σ₁ Σ₂} {s₁ : Σ₀ ⊑ Σ₁} {s₂ : Σ₁ ⊑ Σ₂} {D₀ D₁ D₂}
  → Ext s₁ D₀ D₁ → Ext s₂ D₁ D₂ → Ext (⊑-trans s₁ s₂) D₀ D₂
ext-trans {s₁ = s₁} {s₂} {D₂ = D₂} e₁ e₂ = ext λ f →
  trans (cong (made D₂) (⊑-∋-trans s₁ s₂ f)) (trans (at e₂ _) (at e₁ f))

{- a term made before more definitions, weakened to them -}
wk-made : ∀ {Σ Σ' Γ A} {s : Σ ⊑ Σ'} {D D'} → Ext s D D' → (M : Tm Σ Γ A) → ∀ ρ
  → ⟦ wk (⊑-∋ s) M ⟧[ made D' ] ρ ≃ ⟦ M ⟧[ made D ] ρ
wk-made e = wk-sem _ (λ f → ≃-reflexive (at e f))

{- What glob makes ----------------------------------------------------------------------}

OK : ∀ {Σ Γ A} → S.Tm Γ A → Made Σ → Out Σ (λ Σ' → Tm Σ' Γ A) → Set₁
OK M D (out s D' M') = Ext s D D' × (∀ ρ → ⟦ M' ⟧[ made D' ] ρ ≃ ⟦ M ⟧₄ ρ)

OKs : ∀ {Σ Γ n} → Vec (S.Tm Γ Any) n → Made Σ → Out Σ (λ Σ' → Vec (Tm Σ' Γ Any) n) → Set₁
OKs Ms D (out s D' Ms') = Ext s D D' × (∀ ρ i → nthD (⟦ Ms' ⟧s[ made D' ] ρ) i ≃ nthD (⟦ Ms ⟧s₄ ρ) i)

{- a construct of one or two operands means the same when they do -}
Cong₁ : ∀ {Γ Γ₁ A B} → (∀ {Σ'} → Tm Σ' Γ₁ A → Tm Σ' Γ B) → S.Tm Γ₁ A → S.Tm Γ B → Set₁
Cong₁ f M M₄ = ∀ {Σ'} {T : Table Σ'} {M'} → (∀ ρ → ⟦ M' ⟧[ T ] ρ ≃ ⟦ M ⟧₄ ρ) → ∀ ρ → ⟦ f M' ⟧[ T ] ρ ≃ ⟦ M₄ ⟧₄ ρ

Cong₂ : ∀ {Γ Γ₁ Γ₂ A B C} → (∀ {Σ'} → Tm Σ' Γ₁ A → Tm Σ' Γ₂ B → Tm Σ' Γ C) → S.Tm Γ₁ A → S.Tm Γ₂ B → S.Tm Γ C → Set₁
Cong₂ f L M M₄ = ∀ {Σ'} {T : Table Σ'} {L' M'} → (∀ ρ → ⟦ L' ⟧[ T ] ρ ≃ ⟦ L ⟧₄ ρ) → (∀ ρ → ⟦ M' ⟧[ T ] ρ ≃ ⟦ M ⟧₄ ρ)
  → ∀ ρ → ⟦ f L' M' ⟧[ T ] ρ ≃ ⟦ M₄ ⟧₄ ρ

glob-ok : ∀ {Σ Γ A} (M : S.Tm Γ A) (D : Made Σ) → OK M D (glob M D)
globs-ok : ∀ {Σ Γ n} (Ms : Vec (S.Tm Γ Any) n) (D : Made Σ) → OKs Ms D (globs Ms D)
glob₁-ok : ∀ {Σ Γ Γ₁ A B} (f : ∀ {Σ'} → Tm Σ' Γ₁ A → Tm Σ' Γ B) (M : S.Tm Γ₁ A) (D : Made Σ) {M₄ : S.Tm Γ B} → Cong₁ f M M₄ → OK M₄ D (glob₁ f M D)
glob₂-ok : ∀ {Σ Γ Γ₁ Γ₂ A B C} (f : ∀ {Σ'} → Tm Σ' Γ₁ A → Tm Σ' Γ₂ B → Tm Σ' Γ C) (L : S.Tm Γ₁ A) (M : S.Tm Γ₂ B) (D : Made Σ) {M₄ : S.Tm Γ C}
  → Cong₂ f L M M₄ → OK M₄ D (glob₂ f L M D)

glob-ok (S.` x) D = ⟨ ext (λ f → refl) , (λ ρ → ≃-refl) ⟩
glob-ok (S.code N) D with glob N D | glob-ok N D
... | out s D' N' | ⟨ e , h ⟩ = ⟨ ext (at e) , (λ ρ → ΛΛ-≃ λ X Y → h _) ⟩
glob-ok (S.pack L M) D = glob₂-ok pack L M D {M₄ = S.pack L M} λ hL hM ρ → pair-≃ (hL ρ) (hM ρ)
glob-ok (S.callc L M) D = glob₂-ok callc L M D {M₄ = S.callc L M} λ hL hM ρ → callc-≃ (hL ρ) (hM ρ)
glob-ok (S.lit B c) D = ⟨ ext (λ f → refl) , (λ ρ → ≃-refl) ⟩
glob-ok (S.tuple Ms) D with globs Ms D | globs-ok Ms D
... | out s D' Ms' | ⟨ e , h ⟩ = ⟨ e , (λ ρ → 𝒯-≃ _ (h ρ)) ⟩
glob-ok (S.get i M) D = glob₁-ok (get i) M D {M₄ = S.get i M} λ h ρ → proj-≃ i (h ρ)
glob-ok (S.inl M) D = glob₁-ok inl M D {M₄ = S.inl M} λ h ρ → inl-≃ (h ρ)
glob-ok (S.inr M) D = glob₁-ok inr M D {M₄ = S.inr M} λ h ρ → inr-≃ (h ρ)
glob-ok (S.case L M N) D with glob L D | glob-ok L D
... | out s₁ D₁ L' | ⟨ e₁ , h₁ ⟩ with glob M D₁ | glob-ok M D₁
...   | out s₂ D₂ M' | ⟨ e₂ , h₂ ⟩ with glob N D₂ | glob-ok N D₂
...     | out s₃ D₃ N' | ⟨ e₃ , h₃ ⟩ =
  ⟨ ext-trans e₁ (ext-trans e₂ e₃)
  , (λ ρ → 𝒞-≃ {F = λ X → ⟦ wk (⊑-∋ s₃) M' ⟧[ made D₃ ] (X • ρ)} {λ X → ⟦ M ⟧₄ (X • ρ)}
                {λ X → ⟦ N' ⟧[ made D₃ ] (X • ρ)} {λ X → ⟦ N ⟧₄ (X • ρ)} (≃-trans (wk-made (ext-trans e₂ e₃) L' ρ) (h₁ ρ))
                (λ _ _ _ → ≃-trans (wk-made e₃ M' _) (h₂ _)) (λ _ _ _ → h₃ _)) ⟩
glob-ok (S.prim p L M) D = glob₂-ok (prim p) L M D {M₄ = S.prim p L M} λ hL hM ρ → primD-≃ p (hL ρ) (hM ρ)
glob-ok (S.let′ M N) D = glob₂-ok let′ M N D {M₄ = S.let′ M N} λ {_} {T} {_} {N'} hL hM ρ →
  letD-≃ {F = λ X → ⟦ N' ⟧[ T ] (X • ρ)} {λ X → ⟦ N ⟧₄ (X • ρ)} (hL ρ) (λ _ _ _ → hM _)
glob-ok (S.inject G M) D = glob₁-ok (inject G) M D {M₄ = S.inject G M} λ h → h
glob-ok (S.project t M) D = glob₁-ok (project t) M D {M₄ = S.project t M} λ h ρ → project-≃ fun₄ t (h ρ)

globs-ok [] D = ⟨ ext (λ f → refl) , (λ ρ ()) ⟩
globs-ok (M ∷ Ms) D with glob M D | glob-ok M D
... | out s₁ D₁ M' | ⟨ e₁ , h₁ ⟩ with globs Ms D₁ | globs-ok Ms D₁
...   | out s₂ D₂ Ms' | ⟨ e₂ , h₂ ⟩ =
  ⟨ ext-trans e₁ e₂ , (λ { ρ zero → ≃-trans (wk-made e₂ M' ρ) (h₁ ρ) ; ρ (suc i) → h₂ ρ i }) ⟩

glob₁-ok f M D c with glob M D | glob-ok M D
... | out s D' M' | ⟨ e , h ⟩ = ⟨ e , c h ⟩

glob₂-ok f L M D c with glob L D | glob-ok L D
... | out s₁ D₁ L' | ⟨ e₁ , h₁ ⟩ with glob M D₁ | glob-ok M D₁
...   | out s₂ D₂ M' | ⟨ e₂ , h₂ ⟩ = ⟨ ext-trans e₁ e₂ , c (λ ρ → ≃-trans (wk-made e₂ L' ρ) (h₁ ρ)) h₂ ⟩

{- The table of the program ------------------------------------------------------------}

table-close : ∀ {Σ Σ'} (D : Made Σ') (s : Σ' ⊑ Σ) {n} (f : Σ' ∋ n) → tables code′ (close D s) (⊑-∋ s f) ≃ made D f
table-close {Σ} (_▷_ {Σ''} D N) s f with lvl (⊑-∋ s f) ≟ length Σ'' | lvl-⊑ s f
table-close (D ▷ N) s Z | yes _ | _ =
  ΛΛ-≃ λ X Y → wk-sem _ (table-close D (⊑-trans (there⊑ here⊑) s)) N _
table-close (D ▷ N) s Z | no ne | eq = ⊥-elim (ne eq)
table-close (D ▷ N) s (S f) | yes eq | eq' = ⊥-elim (<-irrefl (trans (sym eq') eq) (lvl-< f))
table-close (D ▷ N) s (S f) | no _ | _ =
  subst (λ g → tables code′ (close D s') g ≃ made D f) (⊑-∋-trans (there⊑ here⊑) s f) (table-close D s' f)
  where s' = ⊑-trans (there⊑ here⊑) s

wk-id : ∀ {Σ Γ A} (M : Tm Σ Γ A) → wk (λ f → f) M ≡ M
wks-id : ∀ {Σ Γ n} (Ms : Vec (Tm Σ Γ Any) n) → wks (λ f → f) Ms ≡ Ms
wk-id (` x) = refl
wk-id (fun-ref f) = refl
wk-id (pack L M) = cong₂ pack (wk-id L) (wk-id M)
wk-id (callc L M) = cong₂ callc (wk-id L) (wk-id M)
wk-id (lit B c) = refl
wk-id (tuple Ms) = cong tuple (wks-id Ms)
wk-id (get i M) = cong (get i) (wk-id M)
wk-id (inl M) = cong inl (wk-id M)
wk-id (inr M) = cong inr (wk-id M)
wk-id (case L M N) = cong₂ (λ L' (P : _ × _) → case L' (proj₁ P) (proj₂ P)) (wk-id L) (cong₂ ⟨_,_⟩ (wk-id M) (wk-id N))
wk-id (prim p L M) = cong₂ (prim p) (wk-id L) (wk-id M)
wk-id (let′ M N) = cong₂ let′ (wk-id M) (wk-id N)
wk-id (inject G M) = cong (inject G) (wk-id M)
wk-id (project t M) = cong (project t) (wk-id M)
wks-id [] = refl
wks-id (M ∷ Ms) = cong₂ _∷_ (wk-id M) (wks-id Ms)

{- The pass preserves the meaning of a closed program -----------------------------------}

globalize-correct : ∀ (M : S.Tm [] Any) → ⟦ M ⟧₄ (λ _ → init) ≃ ⟦ globalize M ⟧ₚ
globalize-correct M with glob M [] | glob-ok M []
... | out _ D M' | ⟨ _ , h ⟩ = ≃-sym (≃-trans (subst (λ N → ⟦ N ⟧[ table (close D here⊑) ] (λ _ → init) ≃ ⟦ M' ⟧[ made D ] (λ _ → init)) (wk-id M') (wk-sem (λ f → f) (table-close D here⊑) M' _)) (h _))

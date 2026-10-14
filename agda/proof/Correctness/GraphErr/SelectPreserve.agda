{-

  CFGᵀ is preserved by CFGᵀ with the X86 checks (SelectCheck.agda):
  each value of the first is related (⊑, SelectRel.agda) to the meaning
  of the second, for every CFGᵀ program. The other direction of
  SelectReflect.agda: the same relation and invariant (SR, ER), with
  the sides swapped.

  The checks of the second only add an error to what it computes, and
  its tests (of a project, and the loads of a call) have values when
  their operand has a value of the right kind, which a related value of
  CFGᵀ gives. The second binds the whole set where CFGᵀ binds finite
  parts of it, and contains them, since it is continuous
  (SelectCheckOk.agda).

-}

module proof.Correctness.GraphErr.SelectPreserve where

open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.Domain
open import proof.Framework.GraphModel.DomainUtilBase using (Nth; Lefts; Rights)
open import proof.Framework.GraphModel.DOpSig using (Results)
open import proof.Framework.GraphModel.OpsBase using (nthD; Mono₁; Finitary; ℬ)
open import proof.Framework.GraphModel.Ops using (⋆; pair; car; cdr; proj; 𝒯; 𝒞) renaming (inl to inlᴰ; inr to inrᴰ)
open import proof.Framework.GraphModel.ErrorMonad
open import proof.Framework.GraphModel.Env using (Env; nonempty-env; extend-nonempty-env; •-~)
open import proof.Framework.GraphModel.TypedOk using (Ok; fin₁; fin₂)
open import proof.Framework.GraphModel.TypedBinders using (callcᵈ)
open import proof.Semantics.Graph.Prim using (primD; out)
open import proof.Semantics.GraphErr.Typed.Clos5 using (tbl; tbl-val; tbl-con)
open import proof.Correctness.GraphErr.SelectCheckOk
open import Semantics.GraphErr.Prim using (primᵐ)
open import Semantics.GraphErr.Typed.Ops using (init; caseᵗ; projectᵠ; keep; hit; kindᶠ; checkedᵠ; primᵗ; getᵗ)
open import Semantics.GraphErr.Typed.Clos4 using (kind₄)
open import Semantics.GraphErr.Typed.Imp using (⌞_⌟; letᵗ)
open import Semantics.GraphErr.Typed.CFG using (Table; 𝒜; 𝒮; BEnv; drop; ⟦_⟧ᵗ; blocks; run; codeᶜ; ⟦_⟧ᶜ)
open import Semantics.GraphErr.Typed.Clos5 using (⟦_⟧[_]; ⟦_⟧s[_])
open import proof.Correctness.GraphErr.SelectCheck
open import proof.Correctness.GraphErr.SelectRel
open import proof.Correctness.GraphErr.SelectReflect
  using (Kd; SR; ER; module ER; ℬ-val; βᵛ; βᵛ⁻; ⌊⌋⊇; kind₄-prod; kind₄-tup; kind₄-base; kind₄-inj; ⊑-kok; ⊑-Kd; ⊑*-∈; ⊑*-from;
         code-fun; out-⊑; lefts-con; rights-con; cdrs-con; 𝒞ˡ-⊇; 𝒞ʳ-⊇; drop-idx; drop-con; drop-ne; pair-elim; inl-elim; inr-elim;
         ℬ-r; no-bad; nth-atm; 𝒯-r; 𝒯ᵐ-kok; er-ext; lvl-type)
open ER
open import proof.Semantics.GraphErr.Typed.Clos5 using (con)
open import proof.Semantics.GraphErr.Typed.CFG using (codeᶜ-con; drop-ok)
open import Framework.Primitives using (Int)
open import Framework.Membership using (here⊑; there⊑; ⊑-∋) renaming (_⊑_ to _≤ₗ_)
open import Language.Prim using (Prim; sub; eq; δ)
open import Language.Typed.Type hiding (_≟_)
import Language.Typed.Mon as M
open import Language.Typed.Imp using (Atm; var; lit; ref; Simple; atm; pack; callc; tuple; get; inl; inr; prim; inject; project)
open import Language.Typed.CFG using (Tail; return; seq; goto; case; Blocks; _▷_; Body; body; Program; program)

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin; zero; suc)
open import Data.Integer using (+_)
open import Data.List using (List; []; _∷_; length; replicate)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (ℕ; zero; suc; _≟_)
open import Data.Product using (_×_; proj₁; proj₂; Σ-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Data.Vec using (Vec; []; _∷_)
open import Level using (lift; lower)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst; subst₂)
open import Relation.Nullary using (yes; no)

{- Operators that check, on the right ---------------------------------------------}

{- a primitive -}
prim-p : ∀ p {A B A' B'} → Val A → Val B → Val A' → Val B'
  → (∀ k → const {Int} k ∈ A → const {Int} k ∈ A') → (∀ k → const {Int} k ∈ B → const {Int} k ∈ B')
  → Lifted _⊑_ (primᵗ p A B) (primᵐ p ⟨ A' , ⟨ B' , ptt ⟩ ⟩ ⇂ Kd (out-flat p))
prim-p p {A} {B} {A'} {B'} vA vB vA' vB' ia ib w w∈
  with βᵛ {B} {λ Y → primD p ⟨ ⌊ A ⌋ , ⟨ Y , ptt ⟩ ⟩} vB w (βᵛ {A} {λ X → B ≫= λ Y → primD p ⟨ X , ⟨ Y , ptt ⟩ ⟩} vA w w∈)
... | ⟨ n , ⟨ m , ⟨ n∈ , ⟨ m∈ , refl ⟩ ⟩ ⟩ ⟩ =
  out-⊑ p n m (βᵛ⁻ {A'} {λ X → B' ≫= λ Y → checked (base Int) X (checked (base Int) Y (primD p ⟨ X , ⟨ Y , ptt ⟩ ⟩))} vA' _
    (βᵛ⁻ {B'} {λ Y → checked (base Int) ⌊ A' ⌋ (checked (base Int) Y (primD p ⟨ ⌊ A' ⌋ , ⟨ Y , ptt ⟩ ⟩))} vB' _
      (inj₂ (inj₂ ⟨ n , ⟨ m , ⟨ ⌊⌋⊇ (proj₁ vA') _ (ia n (proj₁ n∈)) , ⟨ ⌊⌋⊇ (proj₁ vB') _ (ib m (proj₁ m∈)) , refl ⟩ ⟩ ⟩ ⟩))))

{- a project -}
project-p : ∀ t {A A'} → Val A → Val A' → Lifted _⊑_ A A'
  → Lifted _⊑_ (projectᵠ kind₄ t A) (strictᵐ (test t A') A' ⇂ Kd (flat t))
project-p t {A} {A'} vA vA' r w w∈ with βᵛ {A} {λ X → checkedᵠ kind₄ (kindᶠ (flat t)) X (keep kind₄ t X)} vA w w∈
... | inj₁ ⟨ refl , ⟨ d , ⟨ d∈ , dk ⟩ ⟩ ⟩ = let ⟨ e , ⟨ e∈ , ke ⟩ ⟩ = ⊑-wit d (r d (proj₁ d∈)) (proj₂ d∈) in
  lift ⟨ inj₁ ⟨ refl , bad t ⟨ e∈ , (λ e≡ → proj₂ d∈ (kind-ω (trans (sym ke) (cong kind e≡)))) ⟩ (λ k → dk (trans (cong kind₄ (sym ke)) k)) ⟩ , inj₁ refl ⟩
  where
  bad : ∀ t {e} → e ∈ ⌊ A' ⌋ → kind₄ (kind e) ≢ kindᶠ (flat t) → ω ∈ test t A'
  bad tint e∈ ne = βᵛ⁻ {A'} {λ X → ℬ Int (+ 0) ptt ≫= λ Y → checked (base Int) X (checked (base Int) Y (primD sub ⟨ X , ⟨ Y , ptt ⟩ ⟩))} vA' ω
    (βᵛ⁻ {ℬ Int (+ 0) ptt} {λ Y → checked (base Int) ⌊ A' ⌋ (checked (base Int) Y (primD sub ⟨ ⌊ A' ⌋ , ⟨ Y , ptt ⟩ ⟩))} ℬ-val ω
       (inj₁ ⟨ refl , ⟨ _ , ⟨ e∈ , (λ k → ne (cong kind₄ k)) ⟩ ⟩ ⟩))
  bad tsum e∈ ne = βᵛ⁻ {A'} {λ X → checked inj X (isinlD X)} vA' ω (inj₁ ⟨ refl , ⟨ _ , ⟨ e∈ , (λ k → ne (cong kind₄ k)) ⟩ ⟩ ⟩)
  bad tfun e∈ ne = βᵛ⁻ {A'} {λ X → checked prod X (car ⟨ X , ptt ⟩)} vA' ω (inj₁ ⟨ refl , ⟨ _ , ⟨ e∈ , (λ k → ne (cong kind₄ k)) ⟩ ⟩ ⟩)
  bad (ttup n i) e∈ ne = βᵛ⁻ {A'} {λ X → checked (tup (suc n)) X (proj i ⟨ X , ptt ⟩)} vA' ω (inj₁ ⟨ refl , ⟨ _ , ⟨ e∈ , (λ k → ne (cong kind₄ k)) ⟩ ⟩ ⟩)
... | inj₂ ⟨ w∈′ , ⟨ h , wk ⟩ ⟩ =
  ⊑-mono w (λ e e∈ → ⟨ inj₂ ⟨ conv t w rw h wk , proj₁ e∈ ⟩ , proj₂ e∈ ⟩) (⊑-Kd w wk (r w (proj₁ w∈′)))
  where
  rw = r w (proj₁ w∈′)
  w≢ = proj₂ w∈′
  conv : ∀ t z → z ⊑ A' → hit t ⌊ A ⌋ → kind₄ (kind z) ≡ kindᶠ (flat t) → Conv (test t A')
  conv tint z rz _ wk with z | wk | rz
  ... | const {Int} n | refl | lift n∈ =
    ⟨ const (n Data.Integer.- + 0) , ⟨ βᵛ⁻ {A'} {λ X → ℬ Int (+ 0) ptt ≫= λ Y → checked (base Int) X (checked (base Int) Y (primD sub ⟨ X , ⟨ Y , ptt ⟩ ⟩))} vA' _
       (βᵛ⁻ {ℬ Int (+ 0) ptt} {λ Y → checked (base Int) ⌊ A' ⌋ (checked (base Int) Y (primD sub ⟨ ⌊ A' ⌋ , ⟨ Y , ptt ⟩ ⟩))} ℬ-val _
          (inj₂ (inj₂ ⟨ n , ⟨ + 0 , ⟨ ⟨ n∈ , (λ ()) ⟩ , ⟨ ⟨ ⟨ refl , refl ⟩ , (λ ()) ⟩ , refl ⟩ ⟩ ⟩ ⟩))) , (λ ()) ⟩ ⟩
    where import Data.Integer
  conv tsum z rz _ wk with z | wk | rz
  ... | left u | refl | ⟨ _ , ru ⟩ = let ⟨ x , x∈ ⟩ = ⊑-ne u ru in
    ⟨ left ⟨⟩ , ⟨ βᵛ⁻ {A'} {λ X → checked inj X (isinlD X)} vA' _ (inj₂ (inj₁ ⟨ x , ⟨ ⟨ x∈ , (λ ()) ⟩ , refl ⟩ ⟩)) , (λ ()) ⟩ ⟩
  ... | right u | refl | ⟨ _ , ru ⟩ = let ⟨ x , x∈ ⟩ = ⊑-ne u ru in
    ⟨ right ⟨⟩ , ⟨ βᵛ⁻ {A'} {λ X → checked inj X (isinlD X)} vA' _ (inj₂ (inj₂ ⟨ x , ⟨ ⟨ x∈ , (λ ()) ⟩ , refl ⟩ ⟩)) , (λ ()) ⟩ ⟩
  conv tfun (const _) _ _ ()
  conv tfun (_ ↦ _) _ _ ()
  conv tfun ν _ _ ()
  conv tfun ω _ _ ()
  conv tfun (tup[ _ ] _) _ _ ()
  conv tfun (left _) _ _ ()
  conv tfun (right _) _ _ ()
  conv tfun ⟨⟩ _ _ ()
  conv tfun ⦅ u , v ⦆ ⟨ _ , ⟨ _ , lift ⟨ c , ⟨ ⟨ y , p∈ ⟩ , c≢ ⟩ ⟩ ⟩ ⟩ _ _ =
    ⟨ c , ⟨ βᵛ⁻ {A'} {λ X → checked prod X (car ⟨ X , ptt ⟩)} vA' _ (inj₂ ⟨ y , ⟨ p∈ , (λ ()) ⟩ ⟩) , c≢ ⟩ ⟩
  conv (ttup n i) _ _ ⟨ e , e∈ ⟩ _ with r _ (proj₁ e∈)
  ... | ⟨ lift e≢ , re ⟩ with ⊑-wit e re e≢
  ...   | ⟨ e' , ⟨ e'∈ , ke ⟩ ⟩ =
    ⟨ e' , ⟨ βᵛ⁻ {A'} {λ X → checked (tup (suc n)) X (proj i ⟨ X , ptt ⟩)} vA' _ (inj₂ ⟨ e'∈ , (λ ()) ⟩)
         , (λ e'≡ → e≢ (kind-ω (trans (sym ke) (cong kind e'≡)))) ⟩ ⟩

{- a call -}
callc-p : ∀ {F A F' A'} → Val F → Con F → Val A → Val F' → Val A' → Con F' → Con A'
  → Lifted _⊑_ F (F' ⇂ Kd fun) → Lifted _⊑_ A A'
  → Lifted _⊑_ (binds 2 ⟨ F , ⟨ A , ptt ⟩ ⟩ callcᵈ)
               (strictᵐ (carᵐ ⟨ F' , ptt ⟩) (strictᵐ (cdrᵐ ⟨ F' , ptt ⟩) (strictᵐ A'
                  (callᵐ ⟨ carᵐ ⟨ F' , ptt ⟩ , ⟨ cdrᵐ ⟨ F' , ptt ⟩ , ⟨ A' , ptt ⟩ ⟩ ⟩))))
callc-p {F} {A} {F'} {A'} vF cF vA vF' vA' cF' cA' rF rA w w∈
  with βᵛ {A} {λ Y → ⋆ ⟨ ⋆ ⟨ car ⟨ ⌊ F ⌋ , ptt ⟩ , ⟨ cdr ⟨ ⌊ F ⌋ , ptt ⟩ , ptt ⟩ ⟩ , ⟨ Y , ptt ⟩ ⟩} vA w
         (βᵛ {F} {λ P → A ≫= λ Y → ⋆ ⟨ ⋆ ⟨ car ⟨ P , ptt ⟩ , ⟨ cdr ⟨ P , ptt ⟩ , ptt ⟩ ⟩ , ⟨ Y , ptt ⟩ ⟩} vF w w∈)
... | ⟨ U , ⟨ ⟨ V , ⟨ ⟨ e₀ , p∈ ⟩ , ⟨ V⊆ , _ ⟩ ⟩ ⟩ , ⟨ U⊆ , _ ⟩ ⟩ ⟩ with rF _ (proj₁ p∈)
... | ⟨ cdF , ⟨ ⟨ lift e₀≢ , re ⟩ , lift ⟨ c , ⟨ ⟨ y , q∈ ⟩ , c≢ ⟩ ⟩ ⟩ ⟩ =
  ⊑-mono w into (cdF E X cE (Con-⊆ cA' ⌊⌋-⊆) (λ _ → proj₂) (λ _ → proj₂) rV rU)
  where
  Q = F' ⇂ Kd fun
  C = carᵐ ⟨ F' , ptt ⟩
  D = cdrᵐ ⟨ F' , ptt ⟩
  E = ⌊ Cdrs Q ⌋
  X = ⌊ A' ⌋
  cE : Con E
  cE = Con-⊆ (cdrs-con {Q} (Con-⊆ cF' (λ _ → proj₁))) ⌊⌋-⊆
  toC : ∀ {u} → u ∈ Cars Q → u ∈ C
  toC ⟨ z , z∈ ⟩ = βᵛ⁻ {F'} {λ X → checked prod X (car ⟨ X , ptt ⟩)} vF' _ (inj₂ ⟨ z , ⟨ proj₁ z∈ , (λ ()) ⟩ ⟩)
  toD : ∀ {v} → v ∈ Cdrs Q → v ∈ D
  toD ⟨ z , z∈ ⟩ = βᵛ⁻ {F'} {λ X → checked prod X (cdr ⟨ X , ptt ⟩)} vF' _ (inj₂ ⟨ z , ⟨ proj₁ z∈ , (λ ()) ⟩ ⟩)
  cC : Conv C
  cC = ⟨ c , ⟨ toC ⟨ y , q∈ ⟩ , c≢ ⟩ ⟩
  cD : Conv D
  cD = let ⟨ v , ⟨ v∈ , v≢ ⟩ ⟩ = ⊑-val e₀ e₀≢ re in ⟨ v , ⟨ toD v∈ , v≢ ⟩ ⟩
  rV : V ⊑* (E ⇂ₖ kind e₀)
  rV = ⊑*-from V λ v v∈ → let ⟨ u' , q∈′ ⟩ = V⊆ v v∈ ; r = rF _ (proj₁ q∈′) in
    subst (λ k → v ⊑ (E ⇂ₖ k)) (~-kind v e₀ (proj₂ (cF _ _ (proj₁ q∈′) (proj₁ p∈))))
      (⊑-kind v (⊑-⌊⌋ v (lower (proj₁ (proj₁ (proj₂ r)))) (proj₂ (proj₁ (proj₂ r)))))
  rU : U ⊑* X
  rU = ⊑*-from U λ x x∈ → ⊑-⌊⌋ x (proj₂ (U⊆ x x∈)) (rA x (proj₁ (U⊆ x x∈)))
  into : ⋆ ⟨ ⋆ ⟨ Cars Q , ⟨ E ⇂ₖ kind e₀ , ptt ⟩ ⟩ , ⟨ X , ptt ⟩ ⟩
    ⊆ strictᵐ C (strictᵐ D (strictᵐ A' (callᵐ ⟨ C , ⟨ D , ⟨ A' , ptt ⟩ ⟩ ⟩)))
  into z ⟨ U' , ⟨ ⟨ V' , ⟨ e∈ , ⟨ V'⊆ , neV' ⟩ ⟩ ⟩ , ⟨ U'⊆ , neU' ⟩ ⟩ ⟩ =
    inj₂ ⟨ cC , inj₂ ⟨ cD , inj₂ ⟨ Val⇒Conv vA' , inj₂ ⟨ cC , inj₂ ⟨ cD , inj₂ ⟨ Val⇒Conv vA' , inj₂
      ⟨ U' , ⟨ ⟨ V' , ⟨ ⟨ toC e∈ , (λ ()) ⟩ , ⟨ (λ v v∈ → ⟨ toD (proj₁ (proj₁ (V'⊆ v v∈))) , proj₂ (proj₁ (V'⊆ v v∈)) ⟩) , neV' ⟩ ⟩ ⟩
           , ⟨ U'⊆ , neU' ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩

{- The relation preserved ----------------------------------------------------------}

module Sim {Σ : List ℕ} {T Tᶜ : Table}
  (TR : ∀ {n} (f : Σ ∋ n) → SR (code n) (T (lvl f)) (Tᶜ (lvl f)))
  (TV : ∀ k → Val (T k)) (TVᶜ : ∀ k → Val (Tᶜ k)) (TCᶜ : ∀ k → Con (Tᶜ k)) where

  module _ {Δ : Ctx} {ρ ρᶜ : Env Value} (h : ER {Δ} ρ ρᶜ) (cρ : Con-env ρᶜ) (NE : nonempty-env ρᶜ) where

    vl : ∀ {A} (a : Atm Σ Δ A) → Val (𝒜 a T ρ)
    vl (var x) = valᶜ h x
    vl (lit B c) = ℬ-val
    vl (ref f) = TV _

    vr : ∀ {A} (a : Atm Σ Δ A) → Val (𝒜 a Tᶜ ρᶜ)
    vr (var x) = ⟨ clean h x , NE (idx x) ⟩
    vr (lit B c) = ℬ-val
    vr (ref f) = TVᶜ _

    cr : ∀ {A} (a : Atm Σ Δ A) → Con (𝒜 a Tᶜ ρᶜ)
    cr a = con TCᶜ M.⌜ a ⌝ᵃ cρ

    ar : ∀ {A} (a : Atm Σ Δ A) → SR A (𝒜 a T ρ) (𝒜 a Tᶜ ρᶜ)
    ar (var x) = rel h x
    ar (lit B c) = ℬ-r
    ar (ref f) = TR f

    aclᶠ : (a : Atm Σ Δ ⟪ fun ⟫) → Con (𝒜 a T ρ)
    aclᶠ (var x) = conᶜ h x

    simP : ∀ {A} (s : Simple Σ Δ A) → SR A (𝒮 s T ρ) (𝒮ᶜ s Tᶜ ρᶜ)
    simP (atm a) = ar a
    simP (pack {n} c e) d d∈ with pair-elim (βᵛ {F = λ Y → pair ⟨ ⌊ 𝒜 c T ρ ⌋ , ⟨ Y , ptt ⟩ ⟩} (vl e) d (βᵛ {F = λ X → 𝒜 e T ρ ≫= λ Y → pair ⟨ X , ⟨ Y , ptt ⟩ ⟩} (vl c) d d∈))
    ... | ⟨ u , ⟨ v , ⟨ refl , ⟨ ⟨ u∈ , _ ⟩ , ⟨ v∈ , v≢ ⟩ ⟩ ⟩ ⟩ ⟩ =
      ⟨ subst (λ k → Code k u (Cars Q)) (sym kv) (code-mono (tup n) u C⊆ (ar c u u∈))
      , ⟨ ⟨ lift v≢ , ⊑-mono v E⊆ rv ⟩ , lift cvQ ⟩ ⟩
      where
      C' = 𝒜 c Tᶜ ρᶜ
      E' = 𝒜 e Tᶜ ρᶜ
      Q = pairᵐ ⟨ C' , ⟨ E' , ptt ⟩ ⟩ ⇂ Kd fun
      rv = ar e v v∈
      kv : kind v ≡ tup n
      kv = kind₄-tup (⊑-kok v rv v≢)
      in-Q : ∀ {x y} → x ∈ C' → y ∈ E' → ⦅ x , y ⦆ ∈ Q
      in-Q x∈ y∈ = ⟨ βᵛ⁻ {F = λ X → E' ≫= λ Y → pair ⟨ X , ⟨ Y , ptt ⟩ ⟩} (vr c) _
                       (βᵛ⁻ {F = λ Y → pair ⟨ ⌊ C' ⌋ , ⟨ Y , ptt ⟩ ⟩} (vr e) _
                          ⟨ ⟨ x∈ , proj₁ (vr c) _ x∈ ⟩ , ⟨ y∈ , proj₁ (vr e) _ y∈ ⟩ ⟩) , inj₂ refl ⟩
      C⊆ : C' ⊆ Cars Q
      C⊆ x x∈ = let ⟨ y , y∈ ⟩ = proj₂ (vr e) in ⟨ y , in-Q x∈ y∈ ⟩
      E⊆ : (E' ⇂ Kd (tup n)) ⊆ Cdrs Q
      E⊆ y ⟨ y∈ , _ ⟩ = let ⟨ x , x∈ ⟩ = proj₂ (vr c) in ⟨ x , in-Q x∈ y∈ ⟩
      cvQ : Conv (Cars Q)
      cvQ = let ⟨ x , x∈ ⟩ = proj₂ (vr c) ; ⟨ y , y∈ ⟩ = proj₂ (vr e) in ⟨ x , ⟨ ⟨ y , in-Q x∈ y∈ ⟩ , proj₁ (vr c) x x∈ ⟩ ⟩
    simP (callc f a) = callc-p (vl f) (aclᶠ f) (vl a) (vr f) (vr a) (cr f) (cr a) (ar f) (ar a)
    simP (tuple {n = n} as) d d∈ =
      ⊑-⇂ d (λ e e∈ _ → 𝒯ᵐ-kok n e e∈) (binds-lift n ⊑-lift cons rels (λ cl hs → 𝒯-r n cl hs) d d∈)
      where
      cons : ∀ i → Con (nthD (⟦ M.⌜ as ⌝ᵛ ⟧s[ Tᶜ ] ρᶜ) i)
      cons i = subst Con (sym (nth-atm as Tᶜ ρᶜ i)) (cr (Data.Vec.lookup as i))
      rels : ∀ i → Lifted _⊑_ (nthD (⟦ M.⌜ as ⌝ᵛ ⟧s[ T ] ρ) i) (nthD (⟦ M.⌜ as ⌝ᵛ ⟧s[ Tᶜ ] ρᶜ) i)
      rels i x x∈ = subst (x ⊑_) (sym (nth-atm as Tᶜ ρᶜ i))
                      (ar (Data.Vec.lookup as i) x (subst (λ D → D x) (nth-atm as T ρ i) x∈))
    simP (get {n} i a) w w∈ = ⊑-mono w N⊆ (proj₂ (ar a (tup[ i ] w) (proj₁ t∈)))
      where
      t∈ : tup[ i ] w ∈ ⌊ 𝒜 a T ρ ⌋
      t∈ = βᵛ {F = λ X → proj i ⟨ X , ptt ⟩} (vl a) w w∈
      N⊆ : Nth i (𝒜 a Tᶜ ρᶜ ⇂ Kd (tup n)) ⊆ 𝒮ᶜ (get i a) Tᶜ ρᶜ
      N⊆ e ⟨ e∈ , _ ⟩ = βᵛ⁻ {F = λ X → checked (tup n) X (proj i ⟨ X , ptt ⟩)} (vr a) e (inj₂ ⟨ e∈ , proj₁ (vr a) _ e∈ ⟩)
    simP (inl a) d d∈ with inl-elim {d = d} (βᵛ {F = λ X → inlᴰ ⟨ X , ptt ⟩} (vl a) d d∈)
    ... | ⟨ x , ⟨ refl , ⟨ x∈ , x≢ ⟩ ⟩ ⟩ = ⟨ lift x≢ , ⊑-mono x L⊆ (ar a x x∈) ⟩
      where
      L⊆ : 𝒜 a Tᶜ ρᶜ ⊆ Lefts (𝒮ᶜ (inl a) Tᶜ ρᶜ ⇂ Kd sum)
      L⊆ e e∈ = ⟨ βᵛ⁻ {F = λ X → inlᴰ ⟨ X , ptt ⟩} (vr a) _ ⟨ e∈ , proj₁ (vr a) _ e∈ ⟩ , inj₂ refl ⟩
    simP (inr a) d d∈ with inr-elim {d = d} (βᵛ {F = λ X → inrᴰ ⟨ X , ptt ⟩} (vl a) d d∈)
    ... | ⟨ x , ⟨ refl , ⟨ x∈ , x≢ ⟩ ⟩ ⟩ = ⟨ lift x≢ , ⊑-mono x R⊆ (ar a x x∈) ⟩
      where
      R⊆ : 𝒜 a Tᶜ ρᶜ ⊆ Rights (𝒮ᶜ (inr a) Tᶜ ρᶜ ⇂ Kd sum)
      R⊆ e e∈ = ⟨ βᵛ⁻ {F = λ X → inrᴰ ⟨ X , ptt ⟩} (vr a) _ ⟨ e∈ , proj₁ (vr a) _ e∈ ⟩ , inj₂ refl ⟩
    simP (prim p a b) = prim-p p (vl a) (vl b) (vr a) (vr b)
      (λ k k∈ → proj₁ (lower (ar a _ k∈))) (λ k k∈ → proj₁ (lower (ar b _ k∈)))
    simP (inject G a) d d∈ = ⊑-mono d (λ _ → proj₁) (ar a d d∈)
    simP (project t a) = project-p t (vl a) (vr a) (ar a)

    sr-ω : ∀ {A} (s : Simple Σ Δ A) → ω ∈ 𝒮 s T ρ → ω ∈ 𝒮ᶜ s Tᶜ ρᶜ
    sr-ω (atm a) ω∈ = ⊥-elim (proj₁ (vl a) ω ω∈ refl)
    sr-ω {Any} s ω∈ = lower (simP s ω ω∈)
    sr-ω {⟪ G ⟫} s ω∈ = proj₁ (lower (simP s ω ω∈))

    sr-conv : ∀ {A} (s : Simple Σ Δ A) → Conv (𝒮 s T ρ) → Conv (𝒮ᶜ s Tᶜ ρᶜ)
    sr-conv (atm a) _ = Val⇒Conv (vr a)
    sr-conv {Any} s ⟨ d , ⟨ d∈ , d≢ ⟩ ⟩ = ⊑-val d d≢ (simP s d d∈)
    sr-conv {⟪ G ⟫} s ⟨ d , ⟨ d∈ , d≢ ⟩ ⟩ = let ⟨ e , ⟨ e∈ , e≢ ⟩ ⟩ = ⊑-val d d≢ (simP s d d∈) in ⟨ e , ⟨ proj₁ e∈ , e≢ ⟩ ⟩

    sr-mem : ∀ {A} (s : Simple Σ Δ A) V → mem V ⊆ ⌊ 𝒮 s T ρ ⌋ → SR A (mem V) ⌊ 𝒮ᶜ s Tᶜ ρᶜ ⌋
    sr-mem {code n} (atm a) V V⊆ u u∈ = code-mono (tup n) u (⌊⌋-clean (proj₁ (vr a))) (ar a u (proj₁ (V⊆ u u∈)))
    sr-mem {Any} s V V⊆ x x∈ = ⊑-⌊⌋ x (proj₂ (V⊆ x x∈)) (simP s x (proj₁ (V⊆ x x∈)))
    sr-mem {⟪ G ⟫} s V V⊆ x x∈ =
      ⊑-mono x (λ e e∈ → ⟨ ⟨ proj₁ (proj₁ e∈) , proj₂ e∈ ⟩ , proj₂ (proj₁ e∈) ⟩) (⊑-⌊⌋ x (proj₂ (V⊆ x x∈)) (simP s x (proj₁ (V⊆ x x∈))))

  BR : ∀ {Bs} → BEnv Bs → BEnv Bs → Set₁
  BR {Bs} B Bᶜ = ∀ {Δ} (l : Bs ∋ Δ) {ρ ρᶜ} → ER {Δ} ρ ρᶜ → Con-env ρᶜ → nonempty-env ρᶜ → Lifted _⊑_ (B l ρ) (Bᶜ l ρᶜ)

  tail-p : ∀ {Bs Δ} (t : Tail Σ Bs Δ) {B Bᶜ : BEnv Bs} → BR B Bᶜ → (∀ {Δ'} (l : Bs ∋ Δ') → Ok (Bᶜ l))
    → ∀ {ρ ρᶜ} → ER {Δ} ρ ρᶜ → Con-env ρᶜ → nonempty-env ρᶜ → Lifted _⊑_ (⟦ t ⟧ᵗ T B ρ) (⟦ t ⟧ᶜᵗ Tᶜ Bᶜ ρᶜ)
  tail-p (return s) br oB h cρ NE = simP h cρ NE s
  tail-p (goto l) br oB h cρ NE = br l h cρ NE
  tail-p (seq {Δ'} {A} p s t) {B} {Bᶜ} br oB {ρ} {ρᶜ} h cρ NE w (inj₁ ⟨ refl , ω∈ ⟩) =
    lift (proj₂ (letᵐ-unfold {𝒮ᶜ s Tᶜ ρᶜ} {λ X → ⟦ t ⟧ᶜᵗ Tᶜ Bᶜ (X • drop p ρᶜ)}) ω (inj₁ ⟨ refl , sr-ω h cρ NE s ω∈ ⟩))
  tail-p (seq {Δ'} {A} p s t) {B} {Bᶜ} br oB {ρ} {ρᶜ} h cρ NE w (inj₂ ⟨ _ , ⟨ V , ⟨ ⟨ ⟨ w∈′ , ⟨ neV , cV ⟩ ⟩ , nV ⟩ , ⟨ V⊆ , _ ⟩ ⟩ ⟩ ⟩) =
    ⊑-mono w (λ y y∈ → proj₂ (letᵐ-≫= {D} {F} mF cD (λ _ → fin)) y (inj₂ ⟨ cv , y∈ ⟩)) (tail-p t br oB h′ cρ′ NE′ w w∈′)
    where
    D = 𝒮ᶜ s Tᶜ ρᶜ
    F = λ X → ⟦ t ⟧ᶜᵗ Tᶜ Bᶜ (X • drop p ρᶜ)
    cD : Con D
    cD = proj₂ (proj₂ (simple-ok TCᶜ s)) cρ
    cv : Conv D
    cv = sr-conv h cρ NE s (let ⟨ v , v∈ ⟩ = E≢[]⇒nonempty-mem neV in ⟨ v , V⊆ v v∈ ⟩)
    okF = drop-ok p (tail-okᶜ TCᶜ t oB)
    mF : Mono₁ F
    mF {X} {Y} X⊆ = proj₁ okF {X • ρᶜ} {Y • ρᶜ} (λ { zero → X⊆ ; (suc i) → λ _ z → z })
    fin : Finitary F ⌊ D ⌋
    fin = fin₁ okF NE cv
    h′ = er-ext p h (sr-mem h cρ NE s V V⊆) (noerr-val V neV nV) (≈⇒Con cV) (λ _ → proj₂)
    cρ′ = Con-• (Con-⊆ cD ⌊⌋-⊆) (drop-con p cρ)
    NE′ = extend-nonempty-env (drop-ne p NE) cv
  tail-p (case {Δ'} a p l₁ l₂) {B} {Bᶜ} br oB {ρ} {ρᶜ} h cρ NE w w∈
    with βᵛ {𝒜 a T ρ} {λ X → 𝒞 ⟨ X ⇂ ValPayload , ⟨ (λ X → B l₁ (X • drop p ρ)) , ⟨ (λ X → B l₂ (X • drop p ρ)) , ptt ⟩ ⟩ ⟩}
           (vl h cρ NE a) w w∈
  ... | inj₁ ⟨ v , ⟨ V , ⟨ all , ⟨ w∈′ , c ⟩ ⟩ ⟩ ⟩ =
    ⊑-mono w (λ y y∈ → βᵛ⁻ {A'} {λ X → checked inj X (𝒞 ⟨ X ⇂ ValPayload , ⟨ F₁ , ⟨ F₂ , ptt ⟩ ⟩ ⟩)} (vr h cρ NE a) y
       (inj₂ (𝒞ˡ-⊇ {⌊ A' ⌋ ⇂ ValPayload} {F₁} {F₂} cY (fin₁ (drop-ok p (oB l₁)) NE neY) (λ d y → y) y y∈)))
      (br l₁ (er-ext p h rY (noerr-val (v ∷ V) (λ ()) (λ ω∈ → proj₂ (all ω ω∈) refl)) (≈⇒Con c) (λ _ → proj₂))
             (Con-• cY (drop-con p cρ)) (extend-nonempty-env (drop-ne p NE) neY) w w∈′)
    where
    A' = 𝒜 a Tᶜ ρᶜ
    F₁ = λ X → Bᶜ l₁ (X • drop p ρᶜ)
    F₂ = λ X → Bᶜ l₂ (X • drop p ρᶜ)
    Y : 𝒫 Value
    Y d = (⌊ A' ⌋ ⇂ ValPayload) (left d)
    cY : Con Y
    cY = Con-⊆ (lefts-con (Con-⊆ (cr h cρ NE a) ⌊⌋-⊆)) (λ d y → proj₁ y)
    rY : SR Any (mem (v ∷ V)) Y
    rY x x∈ = ⊑-mono x (λ e e∈ → ⟨ ⟨ proj₁ (proj₁ e∈) , (λ ()) ⟩ , proj₂ e∈ ⟩)
                (⊑-⇂ x (λ e e∈ ke ω≡ → proj₂ (all x x∈) (kind-ω (trans (sym ke) (cong kind ω≡))))
                  (proj₂ (ar h cρ NE a (left x) (proj₁ (proj₁ (all x x∈))))))
    neY : nonempty Y
    neY = ⊑-ne v (rY v (here refl))
  ... | inj₂ ⟨ v , ⟨ V , ⟨ all , ⟨ w∈′ , c ⟩ ⟩ ⟩ ⟩ =
    ⊑-mono w (λ y y∈ → βᵛ⁻ {A'} {λ X → checked inj X (𝒞 ⟨ X ⇂ ValPayload , ⟨ F₁ , ⟨ F₂ , ptt ⟩ ⟩ ⟩)} (vr h cρ NE a) y
       (inj₂ (𝒞ʳ-⊇ {⌊ A' ⌋ ⇂ ValPayload} {F₁} {F₂} cY (fin₁ (drop-ok p (oB l₂)) NE neY) (λ d y → y) y y∈)))
      (br l₂ (er-ext p h rY (noerr-val (v ∷ V) (λ ()) (λ ω∈ → proj₂ (all ω ω∈) refl)) (≈⇒Con c) (λ _ → proj₂))
             (Con-• cY (drop-con p cρ)) (extend-nonempty-env (drop-ne p NE) neY) w w∈′)
    where
    A' = 𝒜 a Tᶜ ρᶜ
    F₁ = λ X → Bᶜ l₁ (X • drop p ρᶜ)
    F₂ = λ X → Bᶜ l₂ (X • drop p ρᶜ)
    Y : 𝒫 Value
    Y d = (⌊ A' ⌋ ⇂ ValPayload) (right d)
    cY : Con Y
    cY = Con-⊆ (rights-con (Con-⊆ (cr h cρ NE a) ⌊⌋-⊆)) (λ d y → proj₁ y)
    rY : SR Any (mem (v ∷ V)) Y
    rY x x∈ = ⊑-mono x (λ e e∈ → ⟨ ⟨ proj₁ (proj₁ e∈) , (λ ()) ⟩ , proj₂ e∈ ⟩)
                (⊑-⇂ x (λ e e∈ ke ω≡ → proj₂ (all x x∈) (kind-ω (trans (sym ke) (cong kind ω≡))))
                  (proj₂ (ar h cρ NE a (right x) (proj₁ (proj₁ (all x x∈))))))
    neY : nonempty Y
    neY = ⊑-ne v (rY v (here refl))

  blocks-p : ∀ {Bs} (bs : Blocks Σ Bs) → BR (blocks bs T) (blocksᶜ bs Tᶜ)
  blocks-p (bs ▷ t) Z = tail-p t (blocks-p bs) (blocks-okᶜ TCᶜ bs)
  blocks-p (bs ▷ t) (S l) = blocks-p bs l

  run-p : ∀ {Δ} (b : Body Σ Δ) {ρ ρᶜ} → ER {Δ} ρ ρᶜ → Con-env ρᶜ → nonempty-env ρᶜ → Lifted _⊑_ (run b T ρ) (runᶜ b Tᶜ ρᶜ)
  run-p (body bs t) = tail-p t (blocks-p bs) (blocks-okᶜ TCᶜ bs)

  code-p : ∀ {n} (b : Body Σ (Any ∷ ⟪ tup n ⟫ ∷ [])) → SR (code n) (codeᶜ T b) (codeᶜʰ Tᶜ b)
  code-p {n} b = code-ΛΛ λ V U w neV neU cV cU nV nU w∈ E X cE cX clE clX rV rU →
    ⊑-mono w (into E X cE cX clE clX (neE V neV E rV) (neX U neU X rU))
      (run-p b (h′ V U neV neU cV cU nV nU E X clE clX rV rU)
         (Con-• cX (Con-• (Con-⊆ cE (λ _ → proj₁)) (λ _ → Con-⌈⌉ ω)))
         (extend-nonempty-env (extend-nonempty-env (λ _ → ⟨ ω , refl ⟩) (neE V neV E rV)) (neX U neU X rU)) w w∈)
    where
    neE : ∀ V → V ≢ [] → ∀ E → V ⊑* (E ⇂ₖ tup n) → nonempty (E ⇂ₖ tup n)
    neE V neV E rV = let ⟨ v , v∈ ⟩ = E≢[]⇒nonempty-mem neV in ⊑-ne v (⊑*-∈ rV v∈)
    neX : ∀ U → U ≢ [] → ∀ X → U ⊑* X → nonempty X
    neX U neU X rU = let ⟨ u , u∈ ⟩ = E≢[]⇒nonempty-mem neU in ⊑-ne u (⊑*-∈ rU u∈)
    h′ : ∀ V U → V ≢ [] → U ≢ [] → V ≈ V → U ≈ U → NoErr V → NoErr U → ∀ E X → Clean E → Clean X
      → V ⊑* (E ⇂ₖ tup n) → U ⊑* X → ER {Any ∷ ⟪ tup n ⟫ ∷ []} (mem U • mem V • λ _ → init) (X • (E ⇂ₖ tup n) • λ _ → init)
    h′ V U neV neU cV cU nV nU E X clE clX rV rU = record
      { rel = λ { Z → λ x x∈ → ⊑*-∈ rU x∈
                ; (S Z) → λ x x∈ → ⊑-⇂ x (λ e e∈ ke → inj₂ (cong kind₄ (proj₂ e∈))) (⊑*-∈ rV x∈) }
      ; valᶜ = λ { Z → noerr-val U neU nU ; (S Z) → noerr-val V neV nV }
      ; conᶜ = λ { Z → ≈⇒Con cU ; (S Z) → ≈⇒Con cV }
      ; clean = λ { Z → clX ; (S Z) → λ d d∈ → clE d (proj₁ d∈) } }
    into : ∀ E X → Con E → Con X → Clean E → Clean X → nonempty (E ⇂ₖ tup n) → nonempty X
      → runᶜ b Tᶜ (X • (E ⇂ₖ tup n) • λ _ → init) ⊆ ⋆ ⟨ ⋆ ⟨ codeᶜʰ Tᶜ b , ⟨ E ⇂ₖ tup n , ptt ⟩ ⟩ , ⟨ X , ptt ⟩ ⟩
    into E X cE cX clE clX neE′ neX′ y y∈ with fin₂ (run-okᶜ TCᶜ b) neE′ neX′ y y∈
    ... | ⟨ V' , ⟨ U' , ⟨ neV' , ⟨ neU' , ⟨ V'⊆ , ⟨ U'⊆ , y∈′ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ =
      ⟨ U' , ⟨ ⟨ V' , ⟨ ⟨ ⟨ ⟨ y∈F , ⟨ neU' , cU' ⟩ ⟩ , ⟨ neV' , cV' ⟩ ⟩ , ⟨ nV' , nU' ⟩ ⟩ , ⟨ V'⊆ , neV' ⟩ ⟩ ⟩ , ⟨ U'⊆ , neU' ⟩ ⟩ ⟩
      where
      cV' = Con⇒≈ V' (Con-⊆ cE (λ _ → proj₁)) V'⊆
      cU' = Con⇒≈ U' cX U'⊆
      nV' : NoErr V'
      nV' ω∈ = clE ω (proj₁ (V'⊆ ω ω∈)) refl
      nU' : NoErr U'
      nU' ω∈ = clX ω (U'⊆ ω ω∈) refl
      y∈F = proj₂ (letᵐ-entries (noerr-val V' neV' nV')) y
              ⟨ V' , ⟨ neV' , ⟨ cV' , ⟨ nV' , ⟨ (λ _ z → z)
              , proj₂ (letᵐ-entries (noerr-val U' neU' nU')) y ⟨ U' , ⟨ neU' , ⟨ cU' , ⟨ nU' , ⟨ (λ _ z → z) , y∈′ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩

{- Tables ------------------------------------------------------------------------------}

tbl-p : ∀ {Σ ns} (s : ns ≤ₗ Σ) (ds : All (λ n → Body Σ (Any ∷ ⟪ tup n ⟫ ∷ [])) ns)
  → ∀ {n} (f : Σ ∋ n) → SR (code n) (tbl (codeᶜ {Σ}) ds (lvl f)) (tbl (codeᶜʰ {Σ}) ds (lvl f))
tbl-p s [] {n} f = errcode-rel (tup n)
tbl-p {Σ} {_ ∷ ns} s (d ∷ ds) {n} f with lvl f ≟ length ns
... | yes e = subst (λ k → SR (code k) (codeᶜ (tbl codeᶜ ds) d) (codeᶜʰ (tbl codeᶜʰ ds) d)) (sym (lvl-type s f e))
  (Sim.code-p (tbl-p s' ds) (tbl-val (λ _ → ΛΛᵐ-val) ds) (tbl-val (λ _ → ΛΛᵐ-val) ds) (tbl-con {c = codeᶜʰ {Σ}} (λ TC b → codeᶜʰ-con TC b) ds) d)
  where s' = Framework.Membership.⊑-trans (there⊑ here⊑) s
        import Framework.Membership
... | no _ = tbl-p (Framework.Membership.⊑-trans (there⊑ here⊑) s) ds f
  where import Framework.Membership

{- CFGᵀ is preserved by CFGᵀ with checks -}
preserve : ∀ (P : Program) → Lifted _⊑_ ⟦ P ⟧ᶜ ⟦ P ⟧ᶜʰ
preserve (program {Σ} ds b) =
  Sim.run-p (tbl-p here⊑ ds) (tbl-val (λ _ → ΛΛᵐ-val) ds) (tbl-val (λ _ → ΛΛᵐ-val) ds) (tbl-con {c = codeᶜʰ {Σ}} (λ TC b → codeᶜʰ-con TC b) ds) b
    (record { rel = λ () ; valᶜ = λ () ; conᶜ = λ () ; clean = λ () }) (λ _ → Con-⌈⌉ ω) (λ _ → ⟨ ω , refl ⟩)

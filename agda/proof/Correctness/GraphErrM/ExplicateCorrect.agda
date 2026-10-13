{-

  Correctness of explicate control (Imp → CFG, Compiler/Explicate.agda)
  in the graph model with errors, against the continuation-passing
  semantics of Imp (Semantics/GraphErrM/ImpK.agda): the meaning of the
  CFG program (Semantics/GraphErrM/CFG.agda) is that of the Imp program,
  for every program.

    explicate-correct : ⟦ explicate P ⟧ᶜ ≃ ⟦ P ⟧ᴷₚ

  The proof is that of the graph model (proof/Correctness/Graph/
  {ExplicateCommon,ExplicateCorrectK}.agda): explicate-assign e x k means
  e run with the continuation that assigns x and runs k (cps), and
  explicate-tail e means e run with halt (tail); each case is a
  congruence. With errors, the frame checks of an assignment and of a
  case are the same on both sides (frameᵐ: an error once the value is
  computed), as are the frames of called bodies (max(2, n) slots), so the
  congruences carry over; a jump to a missing block, {ω}, never happens
  on explicate's output, whose jumps go to blocks it made.

-}

open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.DOpSig using (RRs; mono-≃)
open import proof.Framework.GraphModel.Domain
open import proof.Framework.GraphModel.OpsBase using (nthD-≃)
open import proof.Framework.GraphModel.ErrorMonad
open import proof.Semantics.GraphErrM.Prim using (primᵐ-≃)
open import Language.Imp as I
  using (var; lit; fun-ref; atm; app; fst; snd; tuple; get; prim; simple; case; assign; body; program)
import Language.CFG as C
import Language.ISWIM as ISWIM
open import Compiler.Explicate
open import Compiler.Pipeline using (compile-imp; compile-cfg)
open import Compiler.EncloseScope using (Closed)
open import Semantics.GraphErrM.ImpK
  using (Store; _[_↦_]; frameᵐ; Table; 𝒜; 𝒜s; 𝒮; zeros; frame; tables; Kont; halt; ⟦_⟧ᴷ[_]; ⟦_⟧ᴷₚ)
  renaming (code to codeᴷ)
open import Semantics.GraphErrM.CFG
  using (Blocks; blocks; ⟦_⟧ₚ)
  renaming (⟦_⟧[_] to ⟪_⟫[_]; code to codeₜ)

open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_; _++_; length; replicate; map)
open import Data.List.Properties using (++-assoc; length-++; length-map)
open import Data.Nat using (ℕ; _<_; _≤_; _≟_; _<?_; _⊔_)
open import Data.Nat.Properties using (<-irrefl; m≤n+m; <-≤-trans; n<1+n)
open import Data.Product using (_×_; Σ-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Level using (lift)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (yes; no)

module proof.Correctness.GraphErrM.ExplicateCorrect where

open import proof.Framework.GraphModel.ErrorMonad using (ΛΛᵐ-≃)

{- Blocks -----------------------------------------------------------------------------}

{- bs' is bs with newer blocks -}
infix 4 _≼_
_≼_ : List C.Tail → List C.Tail → Set
bs ≼ bs' = Σ[ more ∈ List C.Tail ] bs' ≡ more ++ bs

≼-refl : ∀ {bs} → bs ≼ bs
≼-refl = ⟨ [] , refl ⟩

≼-trans : ∀ {bs₁ bs₂ bs₃} → bs₁ ≼ bs₂ → bs₂ ≼ bs₃ → bs₁ ≼ bs₃
≼-trans {bs₁} ⟨ m₁ , refl ⟩ ⟨ m₂ , refl ⟩ = ⟨ m₂ ++ m₁ , sym (++-assoc m₂ m₁ bs₁) ⟩

≼-∷ : ∀ {t bs} → bs ≼ t ∷ bs
≼-∷ {t} = ⟨ t ∷ [] , refl ⟩

grows-assign : ∀ e x k bs → bs ≼ proj₂ (explicate-assign e x k bs)
grows-assign (simple s) x k bs = ≼-refl
grows-assign (assign y e₁ e₂) x k bs =
  ≼-trans (grows-assign e₂ x k bs) (grows-assign e₁ y _ _)
grows-assign (case a y e₁ e₂) x k bs =
  ≼-trans ≼-∷ (≼-trans (grows-assign e₁ x _ _) (≼-trans ≼-∷ (≼-trans (grows-assign e₂ x _ _) ≼-∷)))

grows-tail : ∀ e bs → bs ≼ proj₂ (explicate-tail e bs)
grows-tail (simple s) bs = ≼-refl
grows-tail (assign x e₁ e₂) bs = ≼-trans (grows-tail e₂ bs) (grows-assign e₁ x _ _)
grows-tail (case a x e₁ e₂) bs =
  ≼-trans (grows-tail e₁ bs) (≼-trans ≼-∷ (≼-trans (grows-tail e₂ _) ≼-∷))

module _ (T : Table) (n : ℕ) where

  {- the blocks of bs keep their labels among newer blocks -}
  blocks-≼ : ∀ more bs l → l < length bs → blocks T n (more ++ bs) l ≡ blocks T n bs l
  blocks-≼ [] bs l l< = refl
  blocks-≼ (t ∷ more) bs l l< with l ≟ length (more ++ bs)
  ... | yes refl = ⊥-elim (<-irrefl refl (<-≤-trans l< (subst (length bs ≤_) (sym (length-++ more))
                                                             (m≤n+m (length bs) (length more)))))
  ... | no _ = blocks-≼ more bs l l<

  blocks-at : ∀ {t bs bs''} → t ∷ bs ≼ bs'' → blocks T n bs'' (length bs) ≡ ⟪ t ⟫[ T ] n (blocks T n bs)
  blocks-at {t} {bs} ⟨ more , refl ⟩ = trans (blocks-≼ more (t ∷ bs) (length bs) (n<1+n _)) top
    where
    top : blocks T n (t ∷ bs) (length bs) ≡ ⟪ t ⟫[ T ] n (blocks T n bs)
    top with length bs ≟ length bs
    ... | yes _ = refl
    ... | no ne = ⊥-elim (ne refl)

at-σ : ∀ {F G : Store → 𝒫 Value} → F ≡ G → ∀ σ → F σ ≃ G σ
at-σ eq σ = ≃-reflexive (cong (λ f → f σ) eq)

{- CFG and Imp check the slots alike -}
frameᵐ-≃ : ∀ n {x D D' E E'} → D ≃ D' → E ≃ E' → frameᵐ n x D E ≃ frameᵐ n x D' E'
frameᵐ-≃ n {x} D≃ E≃ with x <? n
... | yes _ = E≃
... | no _ = ⟨ ≫=-mono (proj₁ D≃) (λ _ w z → z) , ≫=-mono (proj₂ D≃) (λ _ w z → z) ⟩

{- Tables that agree ------------------------------------------------------------------}

module Agreeing {T T' : Table} (TT : ∀ k → T k ≃ T' k) (n : ℕ) where

  B : List C.Tail → Blocks
  B bs = blocks T n bs

  𝒜-≃ : ∀ a σ → 𝒜 T n σ a ≃ 𝒜 T' n σ a
  𝒜-≃ (var x) σ = ≃-refl
  𝒜-≃ (lit B k) σ = ≃-refl
  𝒜-≃ (fun-ref k) σ = TT k

  𝒜s-≃ : ∀ as σ → RRs (replicate (length as) ■) (𝒜s T n σ as) (𝒜s T' n σ as)
  𝒜s-≃ [] σ = ptt
  𝒜s-≃ (a ∷ as) σ = ⟨ lift (𝒜-≃ a σ) , 𝒜s-≃ as σ ⟩

  𝒮-≃ : ∀ s σ → 𝒮 T n σ s ≃ 𝒮 T' n σ s
  𝒮-≃ (atm a) σ = 𝒜-≃ a σ
  𝒮-≃ (app f e a) σ = callᵐ-≃ (𝒜-≃ f σ) (𝒜-≃ e σ) (𝒜-≃ a σ)
  𝒮-≃ (I.pair a b) σ = pairᵐ-≃ (𝒜-≃ a σ) (𝒜-≃ b σ)
  𝒮-≃ (fst a) σ = carᵐ-≃ (𝒜-≃ a σ)
  𝒮-≃ (snd a) σ = cdrᵐ-≃ (𝒜-≃ a σ)
  𝒮-≃ (tuple as) σ = 𝒯ᵐ-≃ (length as) (nthD-≃ _ _ (𝒜s-≃ as σ))
  𝒮-≃ (get i a) σ = projᵐ-≃ i (𝒜-≃ a σ)
  𝒮-≃ (I.inl a) σ = inlᵐ-≃ (𝒜-≃ a σ)
  𝒮-≃ (I.inr a) σ = inrᵐ-≃ (𝒜-≃ a σ)
  𝒮-≃ (prim p a b) σ = primᵐ-≃ p (𝒜-≃ a σ) (𝒜-≃ b σ)

  {- a jump to the block that holds k means the same with newer blocks -}
  goto-≃ : ∀ {k bs bs₁ bs''} → k ∷ bs ≼ bs₁ → bs₁ ≼ bs'' → ∀ σ
    → ⟪ C.goto (length bs) ⟫[ T ] n (B bs'') σ ≃ ⟪ C.goto (length bs) ⟫[ T ] n (B bs₁) σ
  goto-≃ e₁ e = at-σ (trans (blocks-at T n (≼-trans e₁ e)) (sym (blocks-at T n e₁)))

{- The continuations ------------------------------------------------------------------}

module _ (n : ℕ) where

  {- assign x the value, then K, as x := s; K does in CFG -}
  assignK : ℕ → (Store → 𝒫 Value) → Kont
  assignK x K D σ = frameᵐ n x D (letᵐ ⟨ D , ⟨ (λ X → K (σ [ x ↦ X ])) , ptt ⟩ ⟩)

  assignK-≃ : ∀ {x} {K K' : Store → 𝒫 Value} {D D' σ} → (∀ σ' → K σ' ≃ K' σ') → D ≃ D'
    → assignK x K D σ ≃ assignK x K' D' σ
  assignK-≃ {x} {K} {K'} {σ = σ} K≃ D≃ =
    frameᵐ-≃ n {x} D≃ (letᵐ-≃ {F = λ X → K (σ [ x ↦ X ])} {λ X → K' (σ [ x ↦ X ])} D≃ (λ V _ _ _ → K≃ _))

{- The pass preserves meanings ----------------------------------------------------------}

module _ {T T' : Table} (TT : ∀ k → T k ≃ T' k) (n : ℕ) where

  open Agreeing TT n

  {- k means the same with newer blocks -}
  Stable : List C.Tail → C.Tail → Set₁
  Stable bs k = ∀ bs'' → bs ≼ bs'' → ∀ σ → ⟪ k ⟫[ T ] n (B bs'') σ ≃ ⟪ k ⟫[ T ] n (B bs) σ

  goto-stable : ∀ {k bs bs₁} → k ∷ bs ≼ bs₁ → Stable bs₁ (C.goto (length bs))
  goto-stable e₁ bs'' e = goto-≃ e₁ e

  {- explicate-assign e x k: e, then assign x and run k -}
  cps : ∀ e x k bs → Stable bs k → ∀ bs'' → proj₂ (explicate-assign e x k bs) ≼ bs'' → ∀ σ {κ : Kont}
    → (∀ D σ' → κ D σ' ≃ assignK n x (⟪ k ⟫[ T ] n (B bs)) D σ')
    → ⟪ proj₁ (explicate-assign e x k bs) ⟫[ T ] n (B bs'') σ ≃ ⟦ e ⟧ᴷ[ T' ] n σ κ
  cps (simple s) x k bs st bs'' ext σ κ≃ =
    ≃-trans (assignK-≃ n {x} (st bs'' ext) (𝒮-≃ s σ)) (≃-sym (κ≃ _ σ))
  cps (assign y e₁ e₂) x k bs st bs'' ext σ {κ} κ≃ =
    cps e₁ y t' bs₁ st' bs'' ext σ λ D σ' → ≃-sym (assignK-≃ n {y} (λ σ'' → cps e₂ x k bs st bs₁ ≼-refl σ'' κ≃) ≃-refl)
    where
    t' = proj₁ (explicate-assign e₂ x k bs)
    bs₁ = proj₂ (explicate-assign e₂ x k bs)
    st' : Stable bs₁ t'
    st' bs₂ e σ' = ≃-trans (cps e₂ x k bs st bs₂ e σ' κ≃) (≃-sym (cps e₂ x k bs st bs₁ ≼-refl σ' κ≃))
  cps (case a y e₁ e₂) x k bs st bs'' ext σ {κ} κ≃ =
    frameᵐ-≃ n {y} (payloadᵐ-≃ (𝒜-≃ a σ))
     (𝒞ᵐ-≃ {F = λ Y → B bs'' (length bs₂) (σ [ y ↦ Y ])} {λ Y → ⟦ e₁ ⟧ᴷ[ T' ] n (σ [ y ↦ Y ]) κ}
           {λ Y → B bs'' (length bs₄) (σ [ y ↦ Y ])} {λ Y → ⟦ e₂ ⟧ᴷ[ T' ] n (σ [ y ↦ Y ]) κ}
      (𝒜-≃ a σ)
      (λ v V _ _ → ≃-trans (at-σ (blocks-at T n (≼-trans (grows-assign e₂ x (C.goto l) bs₃) (≼-trans ≼-∷ ext))) _)
                           (cps e₁ x (C.goto l) bs₁ (goto-stable ≼-refl) bs₂ ≼-refl _ (κ≃' ≼-refl)))
      (λ v V _ _ → ≃-trans (at-σ (blocks-at T n ext) _)
                           (cps e₂ x (C.goto l) bs₃ (goto-stable e₁₃) bs₄ ≼-refl _ (κ≃' e₁₃))))
    where
    l = length bs
    bs₁ = k ∷ bs
    t₁ = proj₁ (explicate-assign e₁ x (C.goto l) bs₁)
    bs₂ = proj₂ (explicate-assign e₁ x (C.goto l) bs₁)
    bs₃ = t₁ ∷ bs₂
    bs₄ = proj₂ (explicate-assign e₂ x (C.goto l) bs₃)
    e₁₃ : bs₁ ≼ bs₃
    e₁₃ = ≼-trans (grows-assign e₁ x (C.goto l) bs₁) ≼-∷
    {- the join point: a jump to the block that holds k -}
    κ≃' : ∀ {bs'} → bs₁ ≼ bs' → ∀ D σ' → κ D σ' ≃ assignK n x (⟪ C.goto l ⟫[ T ] n (B bs')) D σ'
    κ≃' e D σ' = ≃-trans (κ≃ D σ') (≃-reflexive (cong (λ K → assignK n x K D σ') (sym (blocks-at T n e))))

  {- explicate-tail e: e, then halt -}
  tail : ∀ e bs bs'' → proj₂ (explicate-tail e bs) ≼ bs'' → ∀ σ
    → ⟪ proj₁ (explicate-tail e bs) ⟫[ T ] n (B bs'') σ ≃ ⟦ e ⟧ᴷ[ T' ] n σ halt
  tail (simple s) bs bs'' ext σ = 𝒮-≃ s σ
  tail (assign x e₁ e₂) bs bs'' ext σ =
    cps e₁ x t₂ bs₁ st bs'' ext σ λ D σ' → ≃-sym (assignK-≃ n {x} (λ σ'' → tail e₂ bs bs₁ ≼-refl σ'') ≃-refl)
    where
    t₂ = proj₁ (explicate-tail e₂ bs)
    bs₁ = proj₂ (explicate-tail e₂ bs)
    st : Stable bs₁ t₂
    st bs₂ e σ' = ≃-trans (tail e₂ bs bs₂ e σ') (≃-sym (tail e₂ bs bs₁ ≼-refl σ'))
  tail (case a x e₁ e₂) bs bs'' ext σ =
    frameᵐ-≃ n {x} (payloadᵐ-≃ (𝒜-≃ a σ))
     (𝒞ᵐ-≃ {F = λ Y → B bs'' (length bs₁) (σ [ x ↦ Y ])} {λ Y → ⟦ e₁ ⟧ᴷ[ T' ] n (σ [ x ↦ Y ]) halt}
           {λ Y → B bs'' (length bs₃) (σ [ x ↦ Y ])} {λ Y → ⟦ e₂ ⟧ᴷ[ T' ] n (σ [ x ↦ Y ]) halt}
      (𝒜-≃ a σ)
      (λ v V _ _ → ≃-trans (at-σ (blocks-at T n (≼-trans (grows-tail e₂ bs₂) (≼-trans ≼-∷ ext))) _)
                           (tail e₁ bs bs₁ ≼-refl _))
      (λ v V _ _ → ≃-trans (at-σ (blocks-at T n ext) _) (tail e₂ bs₂ bs₃ ≼-refl _)))
    where
    t₁ = proj₁ (explicate-tail e₁ bs)
    bs₁ = proj₂ (explicate-tail e₁ bs)
    bs₂ = t₁ ∷ bs₁
    bs₃ = proj₂ (explicate-tail e₂ bs₂)

{- Programs -----------------------------------------------------------------------------}

table-≃ : ∀ ds k → tables codeₜ (map explicate-body ds) k ≃ tables codeᴷ ds k
table-≃ [] k = ≃-refl
table-≃ (body n e ∷ bs) k with k ≟ length (map explicate-body bs) | k ≟ length bs
... | yes _ | yes _ = ΛΛᵐ-≃ λ X Y → tail (table-≃ bs) (2 ⊔ n) e [] _ ≼-refl (frame X Y)
... | no _ | no _ = table-≃ bs k
... | yes k≡ | no k≢ = ⊥-elim (k≢ (trans k≡ (length-map explicate-body bs)))
... | no k≢ | yes k≡ = ⊥-elim (k≢ (trans k≡ (sym (length-map explicate-body bs))))

explicate-correct : ∀ (P : I.Program) → ⟦ explicate P ⟧ₚ ≃ ⟦ P ⟧ᴷₚ
explicate-correct (program ds (body n e)) = tail (table-≃ ds) n e [] _ ≼-refl zeros

{- for the programs the compiler produces -}
explicate-correct-compile : ∀ (M : ISWIM.AST) → Closed M → ⟦ compile-cfg M ⟧ₚ ≃ ⟦ compile-imp M ⟧ᴷₚ
explicate-correct-compile M _ = explicate-correct (compile-imp M)

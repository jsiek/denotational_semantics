{-

  Correctness of explicate control (Imp → CFG, Compile/Explicate.agda)
  against the continuation-passing semantics of Imp (Sem/ImpK.agda): the
  meaning of the CFG program (Sem/CFG.agda) is that of the Imp program.

    explicate-correct : ⟦ explicate P ⟧ₚ ≃ ⟦ P ⟧ᴷₚ

  explicate-assign e x k is e in continuation-passing style, and so is
  the semantics: the tail it makes means e run with the continuation
  that assigns x and runs k (cps),

    ⟪ explicate-assign e x k ⟫ ≃ ⟦ e ⟧ᴷ (assignK x ⟪ k ⟫)

  and explicate-tail e means e run with halt (tail). Each case is a
  congruence: a nested assignment y := e₁; e₂ is e₁ with the
  continuation that assigns y and runs e₂, on both sides, and a case
  passes the continuation to its branches, which in CFG reach it through
  the join point, the block that holds k.

  A tail made at the blocks bs runs with any newer blocks (≼, blocks-at),
  so the meaning of a continuation does not depend on the blocks added
  after it (Stable).

-}

open import SetsAsPredicates
open import Compiler.Model.Graph.Domain.ISWIM.Domain
open import Compiler.Model.Graph.Domain.ISWIM.Ops
open import Compiler.Lang.Imp as I
  using (var; lit; fun-ref; atm; app; fst; snd; tuple; get; prim; simple; case; assign; body; program)
import Compiler.Lang.CFG as C
open import Compiler.Compile.Explicate
open import Compiler.Compile.Pipeline using (compile-imp; compile-cfg)
open import Compiler.Model.Graph.Sem.Imp using (𝒜s)
open import Compiler.Model.Graph.Sem.ImpK
  using (Store; _[_↦_]; 𝒜; 𝒮; Table; zeros; frame; Kont; halt; ⟦_⟧ᴷ[_]; ⟦_⟧ᴷₚ)
  renaming (checked to checkedᴷ; table to tableᴷ)
open import Compiler.Model.Graph.Sem.CFG
  using (Blocks; blocks; checked; ⟦_⟧ₚ)
  renaming (⟦_⟧[_] to ⟪_⟫[_]; table to tableₜ)
open import Compiler.Model.Graph.Correctness.GlobalizeCorrect
  using (RRs; nthD-≃; pair-≃; car-≃; cdr-≃; prim-≃; ΛΛ-≃)
open import Compiler.Model.Graph.Correctness.ConcretizeCorrect
  using (⋆-≃; 𝒯-≃; proj-≃; inl-≃; inr-≃; 𝒞-≃)
open import Compiler.Model.Graph.Correctness.RCOCorrect using (Λ-≃)
open import Compiler.Model.Graph.Correctness.LiftLocalsCorrectK using (compile-imp-same)
open import Compiler.Model.Graph.Correctness.CompilerCorrect using (Same; Same-trans; ≃→Same)
open import Compiler.Model.Graph.Correctness.DelayFiniteCommon using (ρ₀)
open import Compiler.Model.Graph.Sem.ISWIM using () renaming (⟦_⟧ to ⟦_⟧ᵢ)
import Compiler.Lang.ISWIM as ISWIM
open import Primitives using (base-rep)

open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_; _++_; length; replicate; map)
open import Data.List.Properties using (++-assoc; length-++; length-map)
open import Data.Nat using (ℕ; _<_; _≤_; _≟_; _<?_)
open import Data.Nat.Properties using (<-irrefl; m≤n+m; <-≤-trans; n<1+n)
open import Data.Product using (_×_; Σ-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Level using (lift)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (yes; no)

module Compiler.Model.Graph.Correctness.ExplicateCorrectK where

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

{- The continuations ------------------------------------------------------------------}

module _ (n : ℕ) where

  {- assign x the value, then K, as x := s; K does in CFG -}
  assignK : ℕ → (Store → 𝒫 Value) → Kont
  assignK x K D σ = checked n x (⋆ ⟨ Λ ⟨ (λ X → K (σ [ x ↦ X ])) , ptt ⟩ , ⟨ D , ptt ⟩ ⟩)

  assignK-≃ : ∀ {x} {K K' : Store → 𝒫 Value} {D D' σ} → (∀ σ' → K σ' ≃ K' σ') → D ≃ D' → assignK x K D σ ≃ assignK x K' D' σ
  assignK-≃ {x} {K} {K'} {σ = σ} K≃ D≃ with x <? n
  ... | yes _ = ⋆-≃ (Λ-≃ {λ X → K (σ [ x ↦ X ])} {λ X → K' (σ [ x ↦ X ])} λ V _ _ → K≃ _) D≃
  ... | no _ = ≃-refl

  {- CFG and Imp check the slots alike -}
  checked-≃ : ∀ {x D D'} → D ≃ D' → checked n x D ≃ checkedᴷ n x D'
  checked-≃ {x} eq with x <? n
  ... | yes _ = eq
  ... | no _ = ≃-refl

  {- y := e₂; then κ, in Imp: assign y, then K -}
  assignᴷ-≃ : ∀ {y} {K F : Store → 𝒫 Value} {D σ} → (∀ σ' → K σ' ≃ F σ') → assignK y K D σ
    ≃ checkedᴷ n y (⋆ ⟨ Λ ⟨ (λ X → F (σ [ y ↦ X ])) , ptt ⟩ , ⟨ D , ptt ⟩ ⟩)
  assignᴷ-≃ {y} {K} {F} {D} {σ} K≃ =
    checked-≃ {y} {⋆ ⟨ Λ ⟨ K' , ptt ⟩ , ⟨ D , ptt ⟩ ⟩} {⋆ ⟨ Λ ⟨ F' , ptt ⟩ , ⟨ D , ptt ⟩ ⟩}
      (⋆-≃ {Λ ⟨ K' , ptt ⟩} {Λ ⟨ F' , ptt ⟩} {D} {D} (Λ-≃ {K'} {F'} λ V _ _ → K≃ _) ≃-refl)
    where K' = λ X → K (σ [ y ↦ X ])
          F' = λ X → F (σ [ y ↦ X ])

{- The pass preserves meanings ----------------------------------------------------------}

{- for tables T (of CFG) and T' (of Imp) that agree -}
module _ {T T' : Table} (TT : ∀ k → T k ≃ T' k) (n : ℕ) where

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
  𝒮-≃ (app f e a) σ = ⋆-≃ (⋆-≃ (𝒜-≃ f σ) (𝒜-≃ e σ)) (𝒜-≃ a σ)
  𝒮-≃ (I.pair a b) σ = pair-≃ ⟨ lift (𝒜-≃ a σ) , ⟨ lift (𝒜-≃ b σ) , ptt ⟩ ⟩
  𝒮-≃ (fst a) σ = car-≃ ⟨ lift (𝒜-≃ a σ) , ptt ⟩
  𝒮-≃ (snd a) σ = cdr-≃ ⟨ lift (𝒜-≃ a σ) , ptt ⟩
  𝒮-≃ (tuple as) σ = 𝒯-≃ (length as) (nthD-≃ _ _ (𝒜s-≃ as σ))
  𝒮-≃ (get i a) σ = proj-≃ i (𝒜-≃ a σ)
  𝒮-≃ (I.inl a) σ = inl-≃ (𝒜-≃ a σ)
  𝒮-≃ (I.inr a) σ = inr-≃ (𝒜-≃ a σ)
  𝒮-≃ (prim p a b) σ = prim-≃ p ⟨ lift (𝒜-≃ a σ) , ⟨ lift (𝒜-≃ b σ) , ptt ⟩ ⟩

  {- k means the same with newer blocks -}
  Stable : List C.Tail → C.Tail → Set₁
  Stable bs k = ∀ bs'' → bs ≼ bs'' → ∀ σ → ⟪ k ⟫[ T ] n (B bs'') σ ≃ ⟪ k ⟫[ T ] n (B bs) σ

  {- a jump to the block that holds k -}
  goto-stable : ∀ {k bs bs₁} → k ∷ bs ≼ bs₁ → Stable bs₁ (C.goto (length bs))
  goto-stable e₁ bs'' e σ =
    ≃-reflexive (cong (λ f → f σ) (trans (blocks-at T n (≼-trans e₁ e)) (sym (blocks-at T n e₁))))

  {- explicate-assign e x k: e, then assign x and run k -}
  cps : ∀ e x k bs → Stable bs k → ∀ bs'' → proj₂ (explicate-assign e x k bs) ≼ bs'' → ∀ σ {κ : Kont}
    → (∀ D σ' → κ D σ' ≃ assignK n x (⟪ k ⟫[ T ] n (B bs)) D σ')
    → ⟪ proj₁ (explicate-assign e x k bs) ⟫[ T ] n (B bs'') σ ≃ ⟦ e ⟧ᴷ[ T' ] n σ κ
  cps (simple s) x k bs st bs'' ext σ κ≃ =
    ≃-trans (assignK-≃ n {x} (st bs'' ext) (𝒮-≃ s σ)) (≃-sym (κ≃ _ σ))
  cps (assign y e₁ e₂) x k bs st bs'' ext σ {κ} κ≃ =
    cps e₁ y t' bs₁ st' bs'' ext σ λ D σ' → ≃-sym (assignᴷ-≃ n {y} {F = λ σ'' → ⟦ e₂ ⟧ᴷ[ T' ] n σ'' κ} (λ σ'' → cps e₂ x k bs st bs₁ ≼-refl σ'' κ≃))
    where
    t' = proj₁ (explicate-assign e₂ x k bs)
    bs₁ = proj₂ (explicate-assign e₂ x k bs)
    st' : Stable bs₁ t'
    st' bs₂ e σ' = ≃-trans (cps e₂ x k bs st bs₂ e σ' κ≃) (≃-sym (cps e₂ x k bs st bs₁ ≼-refl σ' κ≃))
  cps (case a y e₁ e₂) x k bs st bs'' ext σ {κ} κ≃ =
    checked-≃ n {y} (𝒞-≃ {F = λ Y → B bs'' (length bs₂) (σ [ y ↦ Y ])} {λ Y → ⟦ e₁ ⟧ᴷ[ T' ] n (σ [ y ↦ Y ]) κ}
                         {λ Y → B bs'' (length bs₄) (σ [ y ↦ Y ])} {λ Y → ⟦ e₂ ⟧ᴷ[ T' ] n (σ [ y ↦ Y ]) κ}
      (𝒜-≃ a σ)
      (λ v V _ → ≃-trans (at-σ (blocks-at T n (≼-trans (grows-assign e₂ x (C.goto l) bs₃) (≼-trans ≼-∷ ext))) _)
                         (cps e₁ x (C.goto l) bs₁ (goto-stable ≼-refl) bs₂ ≼-refl _ (κ≃' ≼-refl)))
      (λ v V _ → ≃-trans (at-σ (blocks-at T n ext) _)
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
    at-σ : ∀ {F G : Store → 𝒫 Value} → F ≡ G → ∀ σ → F σ ≃ G σ
    at-σ eq σ = ≃-reflexive (cong (λ f → f σ) eq)
    {- the join point: a jump to the block that holds k -}
    κ≃' : ∀ {bs'} → bs₁ ≼ bs' → ∀ D σ' → κ D σ' ≃ assignK n x (⟪ C.goto l ⟫[ T ] n (B bs')) D σ'
    κ≃' e D σ' = ≃-trans (κ≃ D σ') (≃-reflexive (cong (λ K → assignK n x K D σ') (sym (blocks-at T n e))))

  {- explicate-tail e: e, then halt -}
  tail : ∀ e bs bs'' → proj₂ (explicate-tail e bs) ≼ bs'' → ∀ σ
    → ⟪ proj₁ (explicate-tail e bs) ⟫[ T ] n (B bs'') σ ≃ ⟦ e ⟧ᴷ[ T' ] n σ halt
  tail (simple s) bs bs'' ext σ = 𝒮-≃ s σ
  tail (assign x e₁ e₂) bs bs'' ext σ =
    cps e₁ x t₂ bs₁ st bs'' ext σ λ D σ' → ≃-sym (assignᴷ-≃ n {x} {F = λ σ'' → ⟦ e₂ ⟧ᴷ[ T' ] n σ'' halt} (λ σ'' → tail e₂ bs bs₁ ≼-refl σ''))
    where
    t₂ = proj₁ (explicate-tail e₂ bs)
    bs₁ = proj₂ (explicate-tail e₂ bs)
    st : Stable bs₁ t₂
    st bs₂ e σ' = ≃-trans (tail e₂ bs bs₂ e σ') (≃-sym (tail e₂ bs bs₁ ≼-refl σ'))
  tail (case a x e₁ e₂) bs bs'' ext σ =
    checked-≃ n {x} (𝒞-≃ {F = λ Y → B bs'' (length bs₁) (σ [ x ↦ Y ])} {λ Y → ⟦ e₁ ⟧ᴷ[ T' ] n (σ [ x ↦ Y ]) halt}
                         {λ Y → B bs'' (length bs₃) (σ [ x ↦ Y ])} {λ Y → ⟦ e₂ ⟧ᴷ[ T' ] n (σ [ x ↦ Y ]) halt}
      (𝒜-≃ a σ)
      (λ v V _ → ≃-trans (at-σ (blocks-at T n (≼-trans (grows-tail e₂ bs₂) (≼-trans ≼-∷ ext))) _)
                         (tail e₁ bs bs₁ ≼-refl _))
      (λ v V _ → ≃-trans (at-σ (blocks-at T n ext) _) (tail e₂ bs₂ bs₃ ≼-refl _)))
    where
    t₁ = proj₁ (explicate-tail e₁ bs)
    bs₁ = proj₂ (explicate-tail e₁ bs)
    bs₂ = t₁ ∷ bs₁
    bs₃ = proj₂ (explicate-tail e₂ bs₂)
    at-σ : ∀ {F G : Store → 𝒫 Value} → F ≡ G → ∀ σ → F σ ≃ G σ
    at-σ eq σ = ≃-reflexive (cong (λ f → f σ) eq)

{- Programs -----------------------------------------------------------------------------}

table-≃ : ∀ ds k → tableₜ (map explicate-body ds) k ≃ tableᴷ ds k
table-≃ [] k = ≃-refl
table-≃ (body n e ∷ bs) k with k ≟ length (map explicate-body bs) | k ≟ length bs
... | yes _ | yes _ = ΛΛ-≃ λ X Y → tail (table-≃ bs) n e [] _ ≼-refl (frame X Y)
... | no _ | no _ = table-≃ bs k
... | yes k≡ | no k≢ = ⊥-elim (k≢ (trans k≡ (length-map explicate-body bs)))
... | no k≢ | yes k≡ = ⊥-elim (k≢ (trans k≡ (sym (length-map explicate-body bs))))

explicate-correct : ∀ P → ⟦ explicate P ⟧ₚ ≃ ⟦ P ⟧ᴷₚ
explicate-correct (program ds (body n e)) = tail (table-≃ ds) n e [] _ ≼-refl zeros

{- The whole compiler, into CFG ---------------------------------------------------

  compile-cfg = explicate ∘ compile-imp (Compile/Pipeline.agda): the
  result produces the same constants as the ISWIM program, and produces
  something exactly when it does. -}

compile-cfg-same : ∀ (M : ISWIM.AST) → Same (⟦ M ⟧ᵢ ρ₀) ⟦ compile-cfg M ⟧ₚ
compile-cfg-same M = Same-trans (compile-imp-same M) (≃→Same (≃-sym (explicate-correct (compile-imp M))))

compile-cfg-correct-const : ∀ (M : ISWIM.AST) → ∀ {B} (c : base-rep B)
  → (const c ∈ ⟦ M ⟧ᵢ ρ₀ → const c ∈ ⟦ compile-cfg M ⟧ₚ)
  × (const c ∈ ⟦ compile-cfg M ⟧ₚ → const c ∈ ⟦ M ⟧ᵢ ρ₀)
compile-cfg-correct-const M = proj₁ (compile-cfg-same M)

compile-cfg-correct-nonempty : ∀ (M : ISWIM.AST)
  → (nonempty (⟦ M ⟧ᵢ ρ₀) → nonempty ⟦ compile-cfg M ⟧ₚ)
  × (nonempty ⟦ compile-cfg M ⟧ₚ → nonempty (⟦ M ⟧ᵢ ρ₀))
compile-cfg-correct-nonempty M = proj₂ (compile-cfg-same M)

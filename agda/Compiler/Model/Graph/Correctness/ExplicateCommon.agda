{-

  What the two proofs of explicate control (Imp → CFG,
  Compile/Explicate.agda) have in common: the proof against the
  continuation-passing semantics of Imp (ExplicateCorrectK.agda, the
  main one) and the proof against the direct semantics
  (ExplicateCorrect.agda, an alternative).

  A tail made at the blocks bs runs with any newer blocks (≼, blocks-at),
  so a jump to the block that holds a continuation means the same with
  newer blocks (goto-≃). Atoms and simple expressions mean the same for
  tables that agree (𝒜-≃, 𝒮-≃).

  Given the correctness of explicate for either semantics ℐ of Imp
  programs, and of the compiler into Imp for it, the whole compiler into
  CFG is correct (Into).

-}

open import SetsAsPredicates
open import GraphModel.Domain
open import Compiler.Lang.Imp as I
  using (var; lit; fun-ref; atm; app; fst; snd; tuple; get; prim; simple; case; assign)
import Compiler.Lang.CFG as C
open import Compiler.Compile.Explicate
open import Compiler.Compile.Pipeline using (compile-imp; compile-cfg)
open import Compiler.Model.Graph.Sem.Imp using (Store; checked; 𝒜; 𝒜s; 𝒮; Table)
open import Compiler.Model.Graph.Sem.CFG using (Blocks; blocks; ⟦_⟧ₚ) renaming (⟦_⟧[_] to ⟪_⟫[_])
open import Compiler.Model.Graph.Correctness.GlobalizeCorrect
  using (RRs; nthD-≃; pair-≃; car-≃; cdr-≃; prim-≃)
open import Compiler.Model.Graph.Correctness.ConcretizeCorrect
  using (⋆-≃; 𝒯-≃; proj-≃; inl-≃; inr-≃)
open import Compiler.Model.Graph.Correctness.CompilerCorrect using (Same; Same-trans; ≃→Same)
open import Compiler.Model.Graph.Correctness.DelayFiniteCommon using (ρ₀)
open import Compiler.Model.Graph.Sem.ISWIM using () renaming (⟦_⟧ to ⟦_⟧ᵢ)
import Compiler.Lang.ISWIM as ISWIM
open import Primitives using (base-rep)

open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_; _++_; length; replicate)
open import Data.List.Properties using (++-assoc; length-++)
open import Data.Nat using (ℕ; _<_; _≤_; _≟_; _<?_)
open import Data.Nat.Properties using (<-irrefl; m≤n+m; <-≤-trans; n<1+n)
open import Data.Product using (_×_; Σ-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Level using (lift)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (yes; no)

module Compiler.Model.Graph.Correctness.ExplicateCommon where

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
checked-≃ : ∀ n {x D D'} → D ≃ D' → checked n x D ≃ checked n x D'
checked-≃ n {x} eq with x <? n
... | yes _ = eq
... | no _ = ≃-refl

{- Tables that agree ------------------------------------------------------------------}

{- for tables T (of CFG) and T' (of Imp) that agree -}
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
  𝒮-≃ (app f e a) σ = ⋆-≃ (⋆-≃ (𝒜-≃ f σ) (𝒜-≃ e σ)) (𝒜-≃ a σ)
  𝒮-≃ (I.pair a b) σ = pair-≃ ⟨ lift (𝒜-≃ a σ) , ⟨ lift (𝒜-≃ b σ) , ptt ⟩ ⟩
  𝒮-≃ (fst a) σ = car-≃ ⟨ lift (𝒜-≃ a σ) , ptt ⟩
  𝒮-≃ (snd a) σ = cdr-≃ ⟨ lift (𝒜-≃ a σ) , ptt ⟩
  𝒮-≃ (tuple as) σ = 𝒯-≃ (length as) (nthD-≃ _ _ (𝒜s-≃ as σ))
  𝒮-≃ (get i a) σ = proj-≃ i (𝒜-≃ a σ)
  𝒮-≃ (I.inl a) σ = inl-≃ (𝒜-≃ a σ)
  𝒮-≃ (I.inr a) σ = inr-≃ (𝒜-≃ a σ)
  𝒮-≃ (prim p a b) σ = prim-≃ p ⟨ lift (𝒜-≃ a σ) , ⟨ lift (𝒜-≃ b σ) , ptt ⟩ ⟩

  {- a jump to the block that holds k means the same with newer blocks -}
  goto-≃ : ∀ {k bs bs₁ bs''} → k ∷ bs ≼ bs₁ → bs₁ ≼ bs'' → ∀ σ
    → ⟪ C.goto (length bs) ⟫[ T ] n (B bs'') σ ≃ ⟪ C.goto (length bs) ⟫[ T ] n (B bs₁) σ
  goto-≃ e₁ e = at-σ (trans (blocks-at T n (≼-trans e₁ e)) (sym (blocks-at T n e₁)))

{- The whole compiler, into CFG ---------------------------------------------------

  compile-cfg = explicate ∘ compile-imp (Compile/Pipeline.agda): given
  that explicate and compile-imp preserve meanings, for a semantics ℐ of
  Imp programs, the result produces the same constants as the ISWIM
  program, and produces something exactly when it does. -}

module Into (ℐ : I.Program → 𝒫 Value)
  (compile-imp-same : ∀ (M : ISWIM.AST) → Same (⟦ M ⟧ᵢ ρ₀) (ℐ (compile-imp M)))
  (explicate-correct : ∀ P → ⟦ explicate P ⟧ₚ ≃ ℐ P) where

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

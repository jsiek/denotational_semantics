{-

  Correctness of select instructions (CFG → X86, Compiler/Select.agda) in
  the graph model with errors: the meaning of the X86 program
  (Untyped/Semantics/GraphErr/X86.agda) is that of the CFG program
  (Semantics/GraphErr/CFG.agda).

    select-correct : ⟦ select P ⟧ₚ ≃ ⟪ P ⟫ₚ

  The X86 state is the CFG store, with any registers and flag. The
  instructions of x := r, then κ, mean x := r; K in CFG when κ means K
  with any registers and flag (sel, Fits); those of return r leave the
  value of r in %rax. A slot is written as CFG binds (frameᵐ, letᵐ).
  The writes to registers and the flag before the final move are strict
  (strictᵐ, a bind), but they change nothing (strictᵐ-skip): the atoms
  are nonempty (Atom, Inv), so each holds ω or a value; the value of r
  has a value only when they do; and an error in one is an error of r,
  left to right.

  case a x l₁ l₂ tests the tag of a, binds the payload and branches on
  the flag; this is 𝒞ᵐ on a when a slot never holds both an inl and an
  inr (Tagged), which holds since the binders bind only consistent sets
  (case-core).

  The start of a global definition moves %rdi and %rsi to slots 0 and 1
  of its frame of max(2, n) slots, as CFG binds them; this binds finite
  parts of the parameters, where CFG runs the body with them whole, so
  it needs that the meaning of a CFG tail is monotone in the store
  (Mono, frame-≃).

-}

open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.DOpSig using (Results; results-rel-pres)
open import proof.Framework.GraphModel.Domain
open import proof.Framework.GraphModel.ErrorMonad
open import proof.Semantics.GraphErr.Prim using (primᵐ; primᵐ-≃; primᵐ-good)
open import proof.Framework.GraphModel.ContinuityBase using (mono)
open import Framework.GraphModel.Ops using (⋆)
open import Untyped.Language.Imp as I using (var; lit; fun-ref; atm; app; fst; snd; tuple; get; prim)
import Language.Prim as P
import Untyped.Language.CFG as C
import Language.ISWIM as ISWIM
open import Language.X86 hiding (fst; snd; get)
open import Untyped.Compiler.Select
open import Untyped.Compiler.Pipeline using (compile-x86; compile-cfg)
open import Compiler.CaptureScope using (Closed)
open import Untyped.Semantics.GraphErr.Imp using (𝒜; 𝒜s; 𝒮; frame)
open import Untyped.Semantics.GraphErr.CFG
  using () renaming (⟦_⟧[_] to ⟪_⟫[_]; Blocks to Blocksₜ; blocks to blocksₜ; table to tableₜ; code to codeₜ; ⟦_⟧ₚ to ⟪_⟫ₚ)
open import Untyped.Semantics.GraphErr.X86
open import Untyped.proof.Correctness.GraphErr.ExplicateCorrect using (module Agreeing; frameᵐ-≃)
open import Framework.Primitives using (Int)
open import Framework.GraphModel.OpsBase using (ℬ)

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Integer using (+_)
open import Data.List using (List; []; _∷_; _++_; length; replicate; map)
open import Data.List.Properties using (++-identityʳ; length-map)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (ℕ; suc; _≤_; _⊔_; _≟_; _<?_; s≤s; z≤n)
open import Data.Nat.Properties using (m≤m⊔n; ≤-trans)
open import Data.Product using (Σ; Σ-syntax; _×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt; ⊤)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Level using (lift; lower)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂)
open import Relation.Nullary using (yes; no)

module Untyped.proof.Correctness.GraphErr.SelectCorrect where

primᵐ-ω : ∀ p {D E} → ω ∈ D → ω ∈ primᵐ p ⟨ D , ⟨ E , ptt ⟩ ⟩
primᵐ-ω p ω∈ = inj₁ ⟨ refl , ω∈ ⟩

primᵐ-val : ∀ p {D E w} → w ∈ primᵐ p ⟨ D , ⟨ E , ptt ⟩ ⟩ → w ≢ ω → Conv D
primᵐ-val p (inj₁ ⟨ refl , _ ⟩) w≢ = ⊥-elim (w≢ refl)
primᵐ-val p (inj₂ ⟨ c , _ ⟩) _ = c

{- The atoms: nonempty, and no slot holds both an inl and an inr -------------------------}

Tagged : 𝒫 Value → Set
Tagged D = ∀ {u v} → left u ∈ D → right v ∈ D → ⊥

Atom : 𝒫 Value → Set
Atom D = Tagged D × nonempty D

Inv : Store → Set
Inv σ = ∀ y → Atom (σ y)

atom-≈ : ∀ {V} → V ≢ [] → V ≈ V → Atom (mem V)
atom-≈ {V} ne c = ⟨ (λ l r → ≈⇒Every V V c _ _ l r) , ne-mem ne (λ _ z → z) ⟩

atom-zero : Atom (ℬ Int (+ 0) ptt)
atom-zero = ⟨ (λ ()) , ⟨ const {Int} (+ 0) , ⟨ refl , refl ⟩ ⟩ ⟩

inv-zeros : Inv zeros
inv-zeros _ = atom-zero

inv-↦ : ∀ {σ x X} → Inv σ → Atom X → Inv (σ [ x ↦ X ])
inv-↦ {x = x} i t y with y ≟ x
... | yes _ = t
... | no _ = i y

atom-table : ∀ ds k → Atom (table ds k)
atom-table [] k = ⟨ (λ { ⟨ () , _ ⟩ _ }) , ⟨ ν , ⟨ tt , tt ⟩ ⟩ ⟩
atom-table (b ∷ bs) k with k ≟ length bs
... | yes _ = ⟨ (λ { ⟨ () , _ ⟩ _ }) , ⟨ ν , ⟨ tt , tt ⟩ ⟩ ⟩
... | no _ = atom-table bs k

{- case: test, bind the payload, and branch on the flag ----------------------------------}

{- an error of the test or of the payload is one of the scrutinee or its kind -}
Err : 𝒫 Value → Set
Err A = ω ∈ A ⊎ (Conv A × Bad inj ⌊ A ⌋)

isinl-ω : ∀ {A} → ω ∈ isinlᵐ A → Err A
isinl-ω (inj₁ ⟨ _ , ω∈ ⟩) = inj₁ ω∈
isinl-ω (inj₂ ⟨ c , inj₁ ⟨ _ , b ⟩ ⟩) = inj₂ ⟨ c , b ⟩
isinl-ω (inj₂ ⟨ c , inj₂ (inj₁ ⟨ _ , ⟨ _ , () ⟩ ⟩) ⟩)
isinl-ω (inj₂ ⟨ c , inj₂ (inj₂ ⟨ _ , ⟨ _ , () ⟩ ⟩) ⟩)

payload-ω : ∀ {A} → ω ∈ payloadᵐ A → Err A
payload-ω (inj₁ ⟨ _ , ω∈ ⟩) = inj₁ ω∈
payload-ω (inj₂ ⟨ c , inj₁ ⟨ _ , b ⟩ ⟩) = inj₂ ⟨ c , b ⟩
payload-ω (inj₂ ⟨ c , inj₂ (inj₁ ⟨ _ , ω≢ ⟩) ⟩) = ⊥-elim (ω≢ refl)
payload-ω (inj₂ ⟨ c , inj₂ (inj₂ ⟨ _ , ω≢ ⟩) ⟩) = ⊥-elim (ω≢ refl)

err-isinl : ∀ {A} → Err A → ω ∈ isinlᵐ A
err-isinl (inj₁ ω∈) = inj₁ ⟨ refl , ω∈ ⟩
err-isinl (inj₂ ⟨ c , b ⟩) = inj₂ ⟨ c , inj₁ ⟨ refl , b ⟩ ⟩

err-case : ∀ {A F₁ F₂} → Err A → ω ∈ 𝒞ᵐ ⟨ A , ⟨ F₁ , ⟨ F₂ , ptt ⟩ ⟩ ⟩
err-case (inj₁ ω∈) = inj₁ ⟨ refl , ω∈ ⟩
err-case (inj₂ ⟨ c , b ⟩) = inj₂ ⟨ c , inj₁ ⟨ refl , b ⟩ ⟩

{- a payload is that of an injection, whose tag the flag holds, or an error -}
payload-has : ∀ {A d} → d ∈ payloadᵐ A → Has (isinlᵐ A)
payload-has (inj₁ ⟨ _ , ω∈ ⟩) = inj₁ (inj₁ ⟨ refl , ω∈ ⟩)
payload-has (inj₂ ⟨ c , inj₁ ⟨ _ , b ⟩ ⟩) = inj₁ (inj₂ ⟨ c , inj₁ ⟨ refl , b ⟩ ⟩)
payload-has {d = d} (inj₂ ⟨ c , inj₂ (inj₁ l) ⟩) = inj₂ ⟨ left ⟨⟩ , ⟨ inj₂ ⟨ c , inj₂ (inj₁ ⟨ d , ⟨ proj₁ l , refl ⟩ ⟩) ⟩ , (λ ()) ⟩ ⟩
payload-has {d = d} (inj₂ ⟨ c , inj₂ (inj₂ r) ⟩) = inj₂ ⟨ right ⟨⟩ , ⟨ inj₂ ⟨ c , inj₂ (inj₂ ⟨ d , ⟨ proj₁ r , refl ⟩ ⟩) ⟩ , (λ ()) ⟩ ⟩

case-core : ∀ n x {A : 𝒫 Value} {F₁ F₂ : 𝒫 Value → 𝒫 Value} → Tagged A
  → strictᵐ (isinlᵐ A) (frameᵐ n x (payloadᵐ A)
       (letᵐ ⟨ payloadᵐ A , ⟨ (λ X → 𝒞ᵐ ⟨ isinlᵐ A , ⟨ (λ _ → F₁ X) , ⟨ (λ _ → F₂ X) , ptt ⟩ ⟩ ⟩) , ptt ⟩ ⟩))
    ≃ frameᵐ n x (payloadᵐ A) (𝒞ᵐ ⟨ A , ⟨ F₁ , ⟨ F₂ , ptt ⟩ ⟩ ⟩)
case-core n x {A} {F₁} {F₂} tg with x <? n
... | yes _ = ⟨ to , from ⟩
  where
  I = isinlᵐ A
  P = payloadᵐ A
  H = λ X → 𝒞ᵐ ⟨ I , ⟨ (λ _ → F₁ X) , ⟨ (λ _ → F₂ X) , ptt ⟩ ⟩ ⟩
  C = 𝒞ᵐ ⟨ A , ⟨ F₁ , ⟨ F₂ , ptt ⟩ ⟩ ⟩

  {- the payloads in a branch are all of the one injection -}
  lefts : ∀ {u} V → left u ∈ ⌊ A ⌋ → mem V ⊆ ⌊ P ⌋ → ∀ d → d ∈ mem V → (⌊ A ⌋ ⇂ ValPayload) (left d)
  lefts V l V⊆ d d∈ with V⊆ d d∈
  ... | ⟨ inj₁ ⟨ refl , _ ⟩ , d≢ ⟩ = ⊥-elim (d≢ refl)
  ... | ⟨ inj₂ ⟨ _ , inj₁ ⟨ refl , _ ⟩ ⟩ , d≢ ⟩ = ⊥-elim (d≢ refl)
  ... | ⟨ inj₂ ⟨ _ , inj₂ (inj₁ l') ⟩ , _ ⟩ = l'
  ... | ⟨ inj₂ ⟨ _ , inj₂ (inj₂ ⟨ ⟨ r , _ ⟩ , _ ⟩) ⟩ , _ ⟩ = ⊥-elim (tg (proj₁ l) r)
  rights : ∀ {u} V → right u ∈ ⌊ A ⌋ → mem V ⊆ ⌊ P ⌋ → ∀ d → d ∈ mem V → (⌊ A ⌋ ⇂ ValPayload) (right d)
  rights V r V⊆ d d∈ with V⊆ d d∈
  ... | ⟨ inj₁ ⟨ refl , _ ⟩ , d≢ ⟩ = ⊥-elim (d≢ refl)
  ... | ⟨ inj₂ ⟨ _ , inj₁ ⟨ refl , _ ⟩ ⟩ , d≢ ⟩ = ⊥-elim (d≢ refl)
  ... | ⟨ inj₂ ⟨ _ , inj₂ (inj₁ ⟨ ⟨ l , _ ⟩ , _ ⟩) ⟩ , _ ⟩ = ⊥-elim (tg l (proj₁ r))
  ... | ⟨ inj₂ ⟨ _ , inj₂ (inj₂ r') ⟩ , _ ⟩ = r'

  branch : ∀ V → V ≢ [] → V ≈ V → mem V ⊆ ⌊ P ⌋ → H (mem V) ⊆ C
  branch V ne c V⊆ w (inj₁ ⟨ refl , ω∈ ⟩) = err-case {F₁ = F₁} {F₂} (isinl-ω ω∈)
  branch V ne c V⊆ w (inj₂ ⟨ _ , inj₁ ⟨ refl , ⟨ _ , ⟨ ⟨ inj₂ ⟨ _ , inj₂ (inj₁ ⟨ _ , ⟨ _ , refl ⟩ ⟩) ⟩ , _ ⟩ , k ⟩ ⟩ ⟩ ⟩) = ⊥-elim (k refl)
  branch V ne c V⊆ w (inj₂ ⟨ _ , inj₁ ⟨ refl , ⟨ _ , ⟨ ⟨ inj₂ ⟨ _ , inj₂ (inj₂ ⟨ _ , ⟨ _ , refl ⟩ ⟩) ⟩ , _ ⟩ , k ⟩ ⟩ ⟩ ⟩) = ⊥-elim (k refl)
  branch V ne c V⊆ w (inj₂ ⟨ _ , inj₁ ⟨ refl , ⟨ _ , ⟨ ⟨ inj₁ ⟨ refl , _ ⟩ , ω≢ ⟩ , _ ⟩ ⟩ ⟩ ⟩) = ⊥-elim (ω≢ refl)
  branch V ne c V⊆ w (inj₂ ⟨ _ , inj₁ ⟨ refl , ⟨ _ , ⟨ ⟨ inj₂ ⟨ _ , inj₁ ⟨ refl , _ ⟩ ⟩ , ω≢ ⟩ , _ ⟩ ⟩ ⟩ ⟩) = ⊥-elim (ω≢ refl)
  branch (v ∷ V) ne c V⊆ w (inj₂ ⟨ _ , inj₂ (inj₁ ⟨ u , ⟨ _ , ⟨ ls , ⟨ w∈ , _ ⟩ ⟩ ⟩ ⟩) ⟩) with ls u (here refl)
  ... | ⟨ ⟨ inj₂ ⟨ cA , inj₂ (inj₁ ⟨ a , ⟨ l∈ , refl ⟩ ⟩) ⟩ , _ ⟩ , _ ⟩ =
    inj₂ ⟨ cA , inj₂ (inj₁ ⟨ v , ⟨ V , ⟨ lefts (v ∷ V) l∈ V⊆ , ⟨ w∈ , c ⟩ ⟩ ⟩ ⟩) ⟩
  ... | ⟨ ⟨ inj₂ ⟨ _ , inj₂ (inj₂ ⟨ _ , ⟨ _ , () ⟩ ⟩) ⟩ , _ ⟩ , _ ⟩
  ... | ⟨ ⟨ inj₂ ⟨ _ , inj₁ ⟨ () , _ ⟩ ⟩ , _ ⟩ , _ ⟩
  ... | ⟨ ⟨ inj₁ ⟨ () , _ ⟩ , _ ⟩ , _ ⟩
  branch (v ∷ V) ne c V⊆ w (inj₂ ⟨ _ , inj₂ (inj₂ ⟨ u , ⟨ _ , ⟨ rs , ⟨ w∈ , _ ⟩ ⟩ ⟩ ⟩) ⟩) with rs u (here refl)
  ... | ⟨ ⟨ inj₂ ⟨ cA , inj₂ (inj₂ ⟨ a , ⟨ r∈ , refl ⟩ ⟩) ⟩ , _ ⟩ , _ ⟩ =
    inj₂ ⟨ cA , inj₂ (inj₂ ⟨ v , ⟨ V , ⟨ rights (v ∷ V) r∈ V⊆ , ⟨ w∈ , c ⟩ ⟩ ⟩ ⟩) ⟩
  ... | ⟨ ⟨ inj₂ ⟨ _ , inj₂ (inj₁ ⟨ _ , ⟨ _ , () ⟩ ⟩) ⟩ , _ ⟩ , _ ⟩
  ... | ⟨ ⟨ inj₂ ⟨ _ , inj₁ ⟨ () , _ ⟩ ⟩ , _ ⟩ , _ ⟩
  ... | ⟨ ⟨ inj₁ ⟨ () , _ ⟩ , _ ⟩ , _ ⟩
  branch [] ne = ⊥-elim (ne refl)

  to : strictᵐ I (letᵐ ⟨ P , ⟨ H , ptt ⟩ ⟩) ⊆ C
  to w (inj₁ ⟨ refl , ω∈ ⟩) = err-case {F₁ = F₁} {F₂} (isinl-ω ω∈)
  to w (inj₂ ⟨ _ , w∈ ⟩) with proj₁ (letᵐ-unfold {P} {H}) w w∈
  ... | inj₁ ⟨ refl , ω∈ ⟩ = err-case {F₁ = F₁} {F₂} (payload-ω ω∈)
  ... | inj₂ ⟨ _ , ⟨ V , ⟨ ⟨ ⟨ w∈' , ⟨ ne , c ⟩ ⟩ , _ ⟩ , ⟨ V⊆ , _ ⟩ ⟩ ⟩ ⟩ = branch V ne c V⊆ w w∈'

  from : C ⊆ strictᵐ I (letᵐ ⟨ P , ⟨ H , ptt ⟩ ⟩)
  from w (inj₁ ⟨ refl , ω∈ ⟩) = inj₁ ⟨ refl , err-isinl (inj₁ ω∈) ⟩
  from w (inj₂ ⟨ c , inj₁ ⟨ refl , b ⟩ ⟩) = inj₁ ⟨ refl , err-isinl (inj₂ ⟨ c , b ⟩) ⟩
  from w (inj₂ ⟨ cA , inj₂ (inj₁ ⟨ v , ⟨ V , ⟨ ls , ⟨ w∈ , c ⟩ ⟩ ⟩ ⟩) ⟩) =
    inj₂ ⟨ ⟨ left ⟨⟩ , ⟨ tag , (λ ()) ⟩ ⟩ , proj₂ (letᵐ-unfold {P} {H}) w
      (inj₂ ⟨ ⟨ v , ⟨ pay v (here refl) , vω (here refl) ⟩ ⟩
            , ⟨ v ∷ V , ⟨ ⟨ ⟨ inj₂ ⟨ ⟨ left ⟨⟩ , ⟨ tag , (λ ()) ⟩ ⟩
                                 , inj₂ (inj₁ ⟨ ⟨⟩ , ⟨ [] , ⟨ (λ { _ (here refl) → ⟨ ⟨ tag , (λ ()) ⟩ , (λ ()) ⟩ }) , ⟨ w∈ , ≈-single ⟩ ⟩ ⟩ ⟩) ⟩
                          , ⟨ (λ ()) , c ⟩ ⟩ , (λ ω∈ → vω ω∈ refl) ⟩
                      , ⟨ (λ d d∈ → ⟨ pay d d∈ , vω d∈ ⟩) , (λ ()) ⟩ ⟩ ⟩ ⟩) ⟩
    where
    tag = inj₂ ⟨ cA , inj₂ (inj₁ ⟨ v , ⟨ proj₁ (ls v (here refl)) , refl ⟩ ⟩) ⟩
    vω : ∀ {d} → d ∈ mem (v ∷ V) → d ≢ ω
    vω d∈ = proj₂ (ls _ d∈)
    pay : ∀ d → d ∈ mem (v ∷ V) → d ∈ P
    pay d d∈ = inj₂ ⟨ cA , inj₂ (inj₁ (ls d d∈)) ⟩
  from w (inj₂ ⟨ cA , inj₂ (inj₂ ⟨ v , ⟨ V , ⟨ rs , ⟨ w∈ , c ⟩ ⟩ ⟩ ⟩) ⟩) =
    inj₂ ⟨ ⟨ right ⟨⟩ , ⟨ tag , (λ ()) ⟩ ⟩ , proj₂ (letᵐ-unfold {P} {H}) w
      (inj₂ ⟨ ⟨ v , ⟨ pay v (here refl) , vω (here refl) ⟩ ⟩
            , ⟨ v ∷ V , ⟨ ⟨ ⟨ inj₂ ⟨ ⟨ right ⟨⟩ , ⟨ tag , (λ ()) ⟩ ⟩
                                 , inj₂ (inj₂ ⟨ ⟨⟩ , ⟨ [] , ⟨ (λ { _ (here refl) → ⟨ ⟨ tag , (λ ()) ⟩ , (λ ()) ⟩ }) , ⟨ w∈ , ≈-single ⟩ ⟩ ⟩ ⟩) ⟩
                          , ⟨ (λ ()) , c ⟩ ⟩ , (λ ω∈ → vω ω∈ refl) ⟩
                      , ⟨ (λ d d∈ → ⟨ pay d d∈ , vω d∈ ⟩) , (λ ()) ⟩ ⟩ ⟩ ⟩) ⟩
    where
    tag = inj₂ ⟨ cA , inj₂ (inj₂ ⟨ v , ⟨ proj₁ (rs v (here refl)) , refl ⟩ ⟩) ⟩
    vω : ∀ {d} → d ∈ mem (v ∷ V) → d ≢ ω
    vω d∈ = proj₂ (rs _ d∈)
    pay : ∀ d → d ∈ mem (v ∷ V) → d ∈ P
    pay d d∈ = inj₂ ⟨ cA , inj₂ (inj₂ (rs d d∈)) ⟩
... | no _ = strictᵐ-skip (λ w w∈ → has w∈) (λ ω∈ → inj₁ ⟨ refl , err-payload (isinl-ω ω∈) ⟩) (λ { w (inj₁ ⟨ refl , _ ⟩) w≢ → ⊥-elim (w≢ refl) ; w (inj₂ ⟨ _ , refl ⟩) w≢ → ⊥-elim (w≢ refl) })
  where
  err-payload : Err A → ω ∈ payloadᵐ A
  err-payload (inj₁ ω∈) = inj₁ ⟨ refl , ω∈ ⟩
  err-payload (inj₂ ⟨ c , b ⟩) = inj₂ ⟨ c , inj₁ ⟨ refl , b ⟩ ⟩
  has : ∀ {w} → w ∈ (payloadᵐ A ≫= λ _ → ⌈ ω ⌉) → Has (isinlᵐ A)
  has (inj₁ ⟨ _ , ω∈ ⟩) = inj₁ (err-isinl (payload-ω ω∈))
  has (inj₂ ⟨ ⟨ d , ⟨ d∈ , _ ⟩ ⟩ , _ ⟩) = payload-has d∈

{- The meaning of a CFG tail is monotone in the store ------------------------------------}

infix 4 _⊆ₛ_
_⊆ₛ_ : Store → Store → Set
σ ⊆ₛ σ' = ∀ y → σ y ⊆ σ' y

module Mono (T : Table) (n : ℕ) where

  ↦-mono : ∀ {σ σ' x X Y} → σ ⊆ₛ σ' → X ⊆ Y → σ [ x ↦ X ] ⊆ₛ σ' [ x ↦ Y ]
  ↦-mono {x = x} s X⊆ y with y ≟ x
  ... | yes _ = X⊆
  ... | no _ = s y

  𝒜-mono : ∀ a {σ σ'} → σ ⊆ₛ σ' → 𝒜 T n σ a ⊆ 𝒜 T n σ' a
  𝒜-mono (var x) s with x <? n
  ... | yes _ = s x
  ... | no _ = λ _ z → z
  𝒜-mono (lit B k) s = λ _ z → z
  𝒜-mono (fun-ref k) s = λ _ z → z

  𝒜s-mono : ∀ as {σ σ'} → σ ⊆ₛ σ' → results-rel-pres _⊆_ (replicate (length as) ■) (𝒜s T n σ as) (𝒜s T n σ' as)
  𝒜s-mono [] s = ptt
  𝒜s-mono (a ∷ as) s = ⟨ lift (𝒜-mono a s) , 𝒜s-mono as s ⟩

  𝒮-mono : ∀ r {σ σ'} → σ ⊆ₛ σ' → 𝒮 T n σ r ⊆ 𝒮 T n σ' r
  𝒮-mono (atm a) s = 𝒜-mono a s
  𝒮-mono (app f e a) s =
    lower (mono (callᵐ-good {⊤}) _ _ ⟨ lift (𝒜-mono f s) , ⟨ lift (𝒜-mono e s) , ⟨ lift (𝒜-mono a s) , ptt ⟩ ⟩ ⟩)
  𝒮-mono (I.pair a b) s = lower (mono (pairᵐ-good {⊤}) _ _ ⟨ lift (𝒜-mono a s) , ⟨ lift (𝒜-mono b s) , ptt ⟩ ⟩)
  𝒮-mono (fst a) s = lower (mono (carᵐ-good {⊤}) _ _ ⟨ lift (𝒜-mono a s) , ptt ⟩)
  𝒮-mono (snd a) s = lower (mono (cdrᵐ-good {⊤}) _ _ ⟨ lift (𝒜-mono a s) , ptt ⟩)
  𝒮-mono (tuple as) s = lower (mono (𝒯ᵐ-good {⊤} (length as)) _ _ (𝒜s-mono as s))
  𝒮-mono (get i a) s = lower (mono (projᵐ-good {⊤} i) _ _ ⟨ lift (𝒜-mono a s) , ptt ⟩)
  𝒮-mono (I.inl a) s = lower (mono (inlᵐ-good {⊤}) _ _ ⟨ lift (𝒜-mono a s) , ptt ⟩)
  𝒮-mono (I.inr a) s = lower (mono (inrᵐ-good {⊤}) _ _ ⟨ lift (𝒜-mono a s) , ptt ⟩)
  𝒮-mono (prim p a b) s = lower (mono (primᵐ-good {⊤} p) _ _ ⟨ lift (𝒜-mono a s) , ⟨ lift (𝒜-mono b s) , ptt ⟩ ⟩)

  frameᵐ-mono : ∀ x {D D' E E'} → D ⊆ D' → E ⊆ E' → frameᵐ n x D E ⊆ frameᵐ n x D' E'
  frameᵐ-mono x D⊆ E⊆ with x <? n
  ... | yes _ = E⊆
  ... | no _ = ≫=-mono D⊆ (λ _ w z → z)

  MonoB : Blocksₜ → Set₁
  MonoB B = ∀ l {σ σ'} → σ ⊆ₛ σ' → B l σ ⊆ B l σ'

  tail-mono : ∀ t {B} → MonoB B → ∀ {σ σ'} → σ ⊆ₛ σ' → ⟪ t ⟫[ T ] n B σ ⊆ ⟪ t ⟫[ T ] n B σ'
  tail-mono (C.return r) mB s = 𝒮-mono r s
  tail-mono (C.seq x r t) mB s = frameᵐ-mono x (𝒮-mono r s) (lower (mono (letᵐ-good {⊤}) _ _
    ⟨ lift (𝒮-mono r s) , ⟨ (λ X Y X⊆ → lift (tail-mono t mB (↦-mono s X⊆))) , ptt ⟩ ⟩))
  tail-mono (C.goto l) mB s = mB l s
  tail-mono (C.case a x l₁ l₂) mB s = frameᵐ-mono x (payloadᵐ-mono (𝒜-mono a s)) (lower (mono (𝒞ᵐ-good {⊤}) _ _
    ⟨ lift (𝒜-mono a s) , ⟨ (λ X Y X⊆ → lift (mB l₁ (↦-mono s X⊆))) , ⟨ (λ X Y X⊆ → lift (mB l₂ (↦-mono s X⊆))) , ptt ⟩ ⟩ ⟩))

  blocks-mono : ∀ bs → MonoB (blocksₜ T n bs)
  blocks-mono [] l s = λ _ z → z
  blocks-mono (t ∷ bs) l s with l ≟ length bs
  ... | yes _ = tail-mono t (blocks-mono bs) s
  ... | no _ = blocks-mono bs l s

{- The pass preserves meanings ---------------------------------------------------------}

{- for tables T (of X86) and T' (of CFG) that agree, in a frame of n slots -}
module _ {T T' : Table} (TT : ∀ k → T k ≃ T' k) (TL : ∀ k → Atom (T k)) (n : ℕ) where

  open Agreeing TT n using (𝒜-≃; 𝒮-≃)

  atm-≡ : ∀ a {σ ρ} → 𝒪 T n σ ρ (select-atm a) ≡ 𝒜 T n σ a
  atm-≡ (var x) = refl
  atm-≡ (lit B k) = refl
  atm-≡ (fun-ref k) = refl

  atm-≃ : ∀ a {σ ρ} → 𝒪 T n σ ρ (select-atm a) ≃ 𝒜 T' n σ a
  atm-≃ a {σ} = ≃-trans (≃-reflexive (atm-≡ a)) (𝒜-≃ a σ)

  atm-atom : ∀ a {σ ρ} → Inv σ → Atom (𝒪 T n σ ρ (select-atm a))
  atm-atom (var x) i with x <? n
  ... | yes _ = i x
  ... | no _ = ⟨ (λ ()) , ⟨ ω , refl ⟩ ⟩
  atm-atom (lit B k) i = ⟨ (λ ()) , ⟨ const k , ⟨ refl , refl ⟩ ⟩ ⟩
  atm-atom (fun-ref k) i = TL k

  atm-has : ∀ a {σ ρ} → Inv σ → Has (𝒪 T n σ ρ (select-atm a))
  atm-has a i = ne-has (proj₂ (atm-atom a i))

  𝒪s-≡ : ∀ as {σ ρ} → _≡_ {A = Σ ℕ λ m → Results (𝒫 Value) (replicate m ■)}
    ⟨ length (map select-atm as) , 𝒪s T n σ ρ (map select-atm as) ⟩ ⟨ length as , 𝒜s T n σ as ⟩
  𝒪s-≡ [] = refl
  𝒪s-≡ (a ∷ as) = cong₂ (λ D p → ⟨ suc (proj₁ p) , ⟨ D , proj₂ p ⟩ ⟩) (atm-≡ a) (𝒪s-≡ as)

  {- κ, what runs after d is assigned, means K with any registers and flag; or
     returns d -}
  Fits : Loc → Kont → (Store → 𝒫 Value) → Set₁
  Fits (var x) κ K = ∀ σ → Inv σ → ∀ ρ φ → κ σ ρ φ ≃ K σ
  Fits (reg g) κ K = ∀ σ ρ φ → κ σ ρ φ ≃ ρ g

  {- d := D; K, in CFG -}
  after : Loc → (Store → 𝒫 Value) → Store → 𝒫 Value → 𝒫 Value
  after (var x) K σ D = frameᵐ n x D (letᵐ ⟨ D , ⟨ (λ X → K (σ [ x ↦ X ])) , ptt ⟩ ⟩)
  after (reg g) K σ D = D

  ≔-same : ∀ g {ρ D} → (ρ [ g ≔ D ]) g ≡ D
  ≔-same rax = refl
  ≔-same rdi = refl
  ≔-same rsi = refl

  put-≃ : ∀ d {κ K D D' σ ρ φ} → Fits d κ K → Inv σ → D ≃ D' → put n d D κ σ ρ φ ≃ after d K σ D'
  put-≃ (var x) {κ} {K} {σ = σ} {ρ} {φ} fits i D≃ =
    frameᵐ-≃ n {x} D≃ (letᵐ-≃ {F = λ X → κ (σ [ x ↦ X ]) ρ φ} {λ X → K (σ [ x ↦ X ])} D≃
      (λ V ne c _ → fits _ (inv-↦ i (atom-≈ ne c)) ρ φ))
  put-≃ (reg g) {D = D} {σ = σ} {ρ} {φ} fits i D≃ =
    ≃-trans (strictᵐ-self (≃-trans (fits σ (ρ [ g ≔ D ]) φ) (≃-reflexive (≔-same g)))) D≃

  {- an assignment needs its value -}
  put-has : ∀ d {D κ σ ρ φ} w → w ∈ put n d D κ σ ρ φ → Has D
  put-has (var x) {D} {κ} {σ} {ρ} {φ} w w∈ with x <? n
  ... | yes _ = ≫=-has {F = λ X → ⋆ ⟨ Λᵐ ⟨ (λ X → κ (σ [ x ↦ X ]) ρ φ) , ptt ⟩ , ⟨ X , ptt ⟩ ⟩} (proj₁ (letᵐ-unfold {D} {λ X → κ (σ [ x ↦ X ]) ρ φ}) w w∈)
  ... | no _ = ≫=-has {F = λ _ → ⌈ ω ⌉} w∈
  put-has (reg g) {D} {κ} {σ} {ρ} {φ} w w∈ = ≫=-has {F = λ _ → κ σ (ρ [ g ≔ D ]) φ} w∈

  put-val : ∀ d {D κ σ ρ φ} w → w ∈ put n d D κ σ ρ φ → w ≢ ω → Conv D
  put-val (var x) {D} {κ} {σ} {ρ} {φ} w w∈ w≢ with x <? n
  ... | yes _ = proj₁ (≫=-conv {F = λ X → ⋆ ⟨ Λᵐ ⟨ (λ X → κ (σ [ x ↦ X ]) ρ φ) , ptt ⟩ , ⟨ X , ptt ⟩ ⟩} (proj₁ (letᵐ-unfold {D} {λ X → κ (σ [ x ↦ X ]) ρ φ}) w w∈) w≢)
  ... | no _ = proj₁ (≫=-conv {F = λ _ → ⌈ ω ⌉} w∈ w≢)
  put-val (reg g) {D} {κ} {σ} {ρ} {φ} w w∈ w≢ = proj₁ (≫=-conv {F = λ _ → κ σ (ρ [ g ≔ D ]) φ} w∈ w≢)

  put-ω : ∀ d {D κ σ ρ φ} → ω ∈ D → ω ∈ put n d D κ σ ρ φ
  put-ω (var x) {D} {κ} {σ} {ρ} {φ} ω∈ with x <? n
  ... | yes _ = proj₂ (letᵐ-unfold {D} {λ X → κ (σ [ x ↦ X ]) ρ φ}) ω (inj₁ ⟨ refl , ω∈ ⟩)
  ... | no _ = inj₁ ⟨ refl , ω∈ ⟩
  put-ω (reg g) ω∈ = inj₁ ⟨ refl , ω∈ ⟩

  {- the last write of the instructions of r, into d -}
  put-strict : ∀ d {D κ K D' σ ρ φ} → Fits d κ K → Inv σ → D ≃ D'
    → strictᵐ D (put n d D κ σ ρ φ) ≃ after d K σ D'
  put-strict d f i D≃ = strictᵐ-≃′ (put-≃ d f i D≃) (put-has d) (put-ω d) (put-val d)

  {- the instructions of r into d, then is -}
  sel : ∀ r d is {κ K} → Fits d (⟦ is ⟧ˢ T n κ) K → ∀ σ → Inv σ → ∀ ρ φ
    → ⟦ select-simple r d ++ is ⟧ˢ T n κ σ ρ φ ≃ after d K σ (𝒮 T' n σ r)
  sel (atm a) d is f σ i ρ φ = put-≃ d f i (atm-≃ a)
  sel (app g e a) d is {κ} f σ i ρ φ = strictᵐ-≃′ LA (λ _ _ → atm-has e i) ωE valE
    where
    E = 𝒪 T n σ ρ (select-atm e)
    ρ₁ = ρ [ rdi ≔ E ]
    A = 𝒪 T n σ ρ₁ (select-atm a)
    ρ₂ = ρ₁ [ rsi ≔ A ]
    G = 𝒪 T n σ ρ₂ (select-atm g)
    R = callᵐ ⟨ G , ⟨ E , ⟨ A , ptt ⟩ ⟩ ⟩
    Y = put n d R (⟦ is ⟧ˢ T n κ) σ (called R) init
    LR : strictᵐ R Y ≃ _
    LR = put-strict d f i (callᵐ-≃ (atm-≃ g) (atm-≃ e) (atm-≃ a))
    ωA : ω ∈ A → ω ∈ strictᵐ R Y
    ωA ωa with atm-has e i
    ... | inj₁ ωe = inj₁ ⟨ refl , callᵐ-ω (atm-has g i) (inj₁ ωe) ⟩
    ... | inj₂ ve = inj₁ ⟨ refl , callᵐ-ω (atm-has g i) (inj₂ ⟨ ve , ωa ⟩) ⟩
    valA : ∀ w → w ∈ strictᵐ R Y → w ≢ ω → Conv A
    valA w (inj₁ ⟨ refl , _ ⟩) w≢ = ⊥-elim (w≢ refl)
    valA w (inj₂ ⟨ ⟨ r , ⟨ r∈ , r≢ ⟩ ⟩ , _ ⟩) _ = proj₂ (callᵐ-conv {G} r∈ r≢)
    LA : strictᵐ A (strictᵐ R Y) ≃ _
    LA = strictᵐ-≃′ LR (λ _ _ → atm-has a i) ωA valA
    ωE : ω ∈ E → ω ∈ strictᵐ A (strictᵐ R Y)
    ωE ωe with atm-has a i
    ... | inj₁ ωa = inj₁ ⟨ refl , ωa ⟩
    ... | inj₂ va = inj₂ ⟨ va , inj₁ ⟨ refl , callᵐ-ω (atm-has g i) (inj₁ ωe) ⟩ ⟩
    valE : ∀ w → w ∈ strictᵐ A (strictᵐ R Y) → w ≢ ω → Conv E
    valE w (inj₁ ⟨ refl , _ ⟩) w≢ = ⊥-elim (w≢ refl)
    valE w (inj₂ ⟨ _ , inj₁ ⟨ refl , _ ⟩ ⟩) w≢ = ⊥-elim (w≢ refl)
    valE w (inj₂ ⟨ _ , inj₂ ⟨ ⟨ r , ⟨ r∈ , r≢ ⟩ ⟩ , _ ⟩ ⟩) _ = proj₁ (callᵐ-conv {G} r∈ r≢)
  sel (I.pair a b) d is f σ i ρ φ = put-≃ d f i (pairᵐ-≃ (atm-≃ a) (atm-≃ b))
  sel (fst a) d is f σ i ρ φ = put-≃ d f i (carᵐ-≃ (atm-≃ a))
  sel (snd a) d is f σ i ρ φ = put-≃ d f i (cdrᵐ-≃ (atm-≃ a))
  sel (tuple as) d is f σ i ρ φ =
    put-≃ d f i (≃-trans (≃-reflexive (cong (λ p → 𝒯ᵐ (proj₁ p) (proj₂ p)) (𝒪s-≡ as))) (𝒮-≃ (tuple as) σ))
  sel (get j a) d is f σ i ρ φ = put-≃ d f i (projᵐ-≃ j (atm-≃ a))
  sel (I.inl a) d is f σ i ρ φ = put-≃ d f i (inlᵐ-≃ (atm-≃ a))
  sel (I.inr a) d is f σ i ρ φ = put-≃ d f i (inrᵐ-≃ (atm-≃ a))
  sel (prim P.sub a b) d is {κ} f σ i ρ φ =
    strictᵐ-≃′ (put-strict d f i (primᵐ-≃ P.sub (atm-≃ a) (atm-≃ b))) (λ _ _ → atm-has a i)
      (λ ωa → inj₁ ⟨ refl , primᵐ-ω P.sub ωa ⟩) valA
    where
    A = 𝒪 T n σ ρ (select-atm a)
    Q = primᵐ P.sub ⟨ A , ⟨ 𝒪 T n σ (ρ [ rax ≔ A ]) (select-atm b) , ptt ⟩ ⟩
    valA : ∀ w → w ∈ strictᵐ Q (put n d Q (⟦ is ⟧ˢ T n κ) σ (ρ [ rax ≔ A ] [ rax ≔ Q ]) φ) → w ≢ ω → Conv A
    valA w (inj₁ ⟨ refl , _ ⟩) w≢ = ⊥-elim (w≢ refl)
    valA w (inj₂ ⟨ ⟨ r , ⟨ r∈ , r≢ ⟩ ⟩ , _ ⟩) _ = primᵐ-val P.sub r∈ r≢
  sel (prim P.eq a b) d is f σ i ρ φ = put-strict d f i (primᵐ-≃ P.eq (atm-≃ a) (atm-≃ b))

  {- the blocks B (of X86) and B' (of CFG) agree -}
  BR : Blocks → Blocksₜ → Set₁
  BR B B' = ∀ l σ → Inv σ → ∀ ρ φ → B l σ ρ φ ≃ B' l σ

  tail : ∀ t {B B'} → BR B B' → ∀ σ → Inv σ → ∀ ρ φ → ⟦ select-tail t ⟧ᵇ T n B σ ρ φ ≃ ⟪ t ⟫[ T' ] n B' σ
  tail (C.return r) {B} br σ i ρ φ =
    ≃-trans (≃-reflexive (cong (λ is → ⟦ is ⟧ˢ T n (⟦ retq ⟧ʲ B) σ ρ φ) (sym (++-identityʳ (select-simple r (reg rax))))))
            (sel r (reg rax) [] {K = λ _ → ∅} (λ σ ρ φ → ≃-refl) σ i ρ φ)
  tail (C.seq x r t) br σ i ρ φ = sel r (var x) _ (λ σ' i' ρ' φ' → tail t br σ' i' ρ' φ') σ i ρ φ
  tail (C.goto l) br σ i ρ φ = br l σ i ρ φ
  tail (C.case a x l₁ l₂) {B} {B'} br σ i ρ φ =
    ≃-trans (case-core n x {A} {F₁} {F₂} (proj₁ (atm-atom a i)))
      (frameᵐ-≃ n {x} (payloadᵐ-≃ (atm-≃ a))
        (𝒞ᵐ-≃ {F = F₁} {λ X → B' l₁ (σ [ x ↦ X ])} {F₂} {λ X → B' l₂ (σ [ x ↦ X ])}
          (atm-≃ a) (λ V ne c _ → br l₁ _ (inv-↦ i (atom-≈ ne c)) ρ _)
                        (λ V ne c _ → br l₂ _ (inv-↦ i (atom-≈ ne c)) ρ _)))
    where
    A = 𝒪 T n σ ρ (select-atm a)
    F₁ = λ X → B l₁ (σ [ x ↦ X ]) ρ (isinlᵐ A)
    F₂ = λ X → B l₂ (σ [ x ↦ X ]) ρ (isinlᵐ A)

  blocks-≃ : ∀ bs → BR (blocks T n (map select-tail bs)) (blocksₜ T' n bs)
  blocks-≃ [] l σ i ρ φ = ≃-refl
  blocks-≃ (t ∷ bs) l σ i ρ φ with l ≟ length (map select-tail bs) | l ≟ length bs
  ... | yes _ | yes _ = tail t (blocks-≃ bs) σ i ρ φ
  ... | no _ | no _ = blocks-≃ bs l σ i ρ φ
  ... | yes l≡ | no l≢ = ⊥-elim (l≢ (trans l≡ (length-map select-tail bs)))
  ... | no l≢ | yes l≡ = ⊥-elim (l≢ (trans l≡ (sym (length-map select-tail bs))))

  {- the prologue binds parts of the parameters; F is the rest of the start -}
  frame-≃ : 2 ≤ n → ∀ {F G : Store → 𝒫 Value} → (∀ σ → Inv σ → F σ ≃ G σ) → (∀ {σ σ'} → σ ⊆ₛ σ' → G σ ⊆ G σ')
    → ∀ {V U} → V ≢ [] → V ≈ V → NoErr V → U ≢ [] → U ≈ U → NoErr U
    → frameᵐ n 0 (mem V) (letᵐ ⟨ mem V , ⟨ (λ X → frameᵐ n 1 (mem U)
        (letᵐ ⟨ mem U , ⟨ (λ Y → F (zeros [ 0 ↦ X ] [ 1 ↦ Y ])) , ptt ⟩ ⟩)) , ptt ⟩ ⟩)
      ≃ G (frame (mem V) (mem U))
  frame-≃ le {F} {G} FG mono {V} {U} neV cV nV neU cU nU with 0 <? n | 1 <? n
  ... | no ¬p | _ = ⊥-elim (¬p (≤-trans (s≤s z≤n) le))
  ... | yes _ | no ¬p = ⊥-elim (¬p le)
  ... | yes _ | yes _ =
    ≃-trans (letᵐ-entries (noerr-val V neV nV))
      ⟨ to , (λ w w∈ → ⟨ V , ⟨ neV , ⟨ cV , ⟨ nV , ⟨ (λ _ z → z) , proj₂ (letᵐ-entries (noerr-val U neU nU)) w
                         ⟨ U , ⟨ neU , ⟨ cU , ⟨ nU , ⟨ (λ _ z → z) , proj₂ (FG _ (i V U neV cV neU cU)) w (mono s' w w∈) ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩) ⟩
    where
    s' : frame (mem V) (mem U) ⊆ₛ zeros [ 0 ↦ mem V ] [ 1 ↦ mem U ]
    s' 0 = λ _ z → z
    s' 1 = λ _ z → z
    s' (suc (suc y)) = λ _ z → z
    i : ∀ V' U' → V' ≢ [] → V' ≈ V' → U' ≢ [] → U' ≈ U' → Inv (zeros [ 0 ↦ mem V' ] [ 1 ↦ mem U' ])
    i V' U' neV' cV' neU' cU' 0 = atom-≈ neV' cV'
    i V' U' neV' cV' neU' cU' 1 = atom-≈ neU' cU'
    i V' U' neV' cV' neU' cU' (suc (suc y)) = atom-zero
    to : _
    to w ⟨ V' , ⟨ neV' , ⟨ cV' , ⟨ nV' , ⟨ V'⊆ , w∈ ⟩ ⟩ ⟩ ⟩ ⟩
        with proj₁ (letᵐ-entries (noerr-val U neU nU)) w w∈
    ... | ⟨ U' , ⟨ neU' , ⟨ cU' , ⟨ _ , ⟨ U'⊆ , w∈' ⟩ ⟩ ⟩ ⟩ ⟩ = mono s w (proj₁ (FG _ (i V' U' neV' cV' neU' cU')) w w∈')
      where
      s : zeros [ 0 ↦ mem V' ] [ 1 ↦ mem U' ] ⊆ₛ frame (mem V) (mem U)
      s 0 = V'⊆
      s 1 = U'⊆
      s (suc (suc y)) = λ _ z → z

{- the code of a global definition, in a frame of max(2, n) slots -}
code-≃ : ∀ {T T' : Table} (TT : ∀ k → T k ≃ T' k) (TL : ∀ k → Atom (T k)) n bs t
  → code T (select-body prologue (C.body n bs t)) ≃ codeₜ T' (C.body n bs t)
code-≃ {T} {T'} TT TL n bs t = ΛΛᵐ-≃′ λ V U neV cV nV neU cU nU →
  frame-≃ TT TL m (m≤m⊔n 2 n)
    {λ σ → ⟦ select-tail t ⟧ᵇ T m (blocks T m (map select-tail bs)) σ (args (mem V) (mem U)) init}
    {⟪ t ⟫[ T' ] m (blocksₜ T' m bs)}
    (λ σ i → tail TT TL m t (blocks-≃ TT TL m bs) σ i _ init)
    (Mono.tail-mono T' m t (Mono.blocks-mono T' m bs)) neV cV nV neU cU nU
  where m = 2 ⊔ n

{- Programs -----------------------------------------------------------------------------}

table-≃ : ∀ ds k → table (map (select-body prologue) ds) k ≃ tableₜ ds k
table-≃ [] k = ≃-refl
table-≃ (C.body n bs t ∷ ds) k with k ≟ length (map (select-body prologue) ds) | k ≟ length ds
... | yes _ | yes _ = code-≃ (table-≃ ds) (atom-table (map (select-body prologue) ds)) n bs t
... | no _ | no _ = table-≃ ds k
... | yes k≡ | no k≢ = ⊥-elim (k≢ (trans k≡ (length-map (select-body prologue) ds)))
... | no k≢ | yes k≡ = ⊥-elim (k≢ (trans k≡ (sym (length-map (select-body prologue) ds))))

select-correct : ∀ (P : C.Program) → ⟦ select P ⟧ₚ ≃ ⟪ P ⟫ₚ
select-correct (C.program ds (C.body n bs t)) =
  tail TT TL n t (blocks-≃ TT TL n bs) zeros inv-zeros (called (ℬ Int (+ 0) ptt)) init
  where
  TT = table-≃ ds
  TL = atom-table (map (select-body prologue) ds)

{- The whole compiler, into X86 ----------------------------------------------------------}

select-correct-compile : ∀ (M : ISWIM.AST) → Closed M → ⟦ compile-x86 M ⟧ₚ ≃ ⟪ compile-cfg M ⟫ₚ
select-correct-compile M _ = select-correct (compile-cfg M)

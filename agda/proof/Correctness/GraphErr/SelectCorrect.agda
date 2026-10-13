{-

  Correctness of select instructions (CFG → X86, Compiler/Select.agda) in
  the graph model with errors: the meaning of the X86 program
  (Semantics/GraphErr/X86.agda) is that of the CFG program
  (Semantics/GraphErr/CFG.agda).

    select-correct : ⟦ select P ⟧ₚ ≃ ⟪ P ⟫ₚ

  The X86 state is the CFG store, with any registers and flag. The
  instructions of x := r, then κ, mean x := r; K in CFG when κ means K
  with any registers and flag (sel, Fits); those of return r leave the
  value of r in %rax. A slot is written as CFG binds (checkedᵉ, letᵉ).
  The writes to registers and the flag before the final move are strict
  (strictᵉ), but they change nothing (strict-≃): the atoms are nonempty
  (Atom, Inv), so each holds ω or a value; the value of r has a value
  only when they do; and an error in one is an error of r, left to
  right.

  case a x l₁ l₂ tests the tag of a, binds the payload and branches on
  the flag; this is 𝒞ᵉ on a when a slot never holds both an inl and an
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
open import proof.Framework.GraphModel.ErrorOps
open import proof.Semantics.GraphErr.Prim using (primᵉ; primᵉ-≃; primᵉ-mono)
open import Language.Imp as I using (var; lit; fun-ref; atm; app; fst; snd; tuple; get; prim)
import Language.Prim as P
import Language.CFG as C
import Language.ISWIM as ISWIM
open import Language.X86 hiding (fst; snd; get)
open import Compiler.Select
open import Compiler.Pipeline using (compile-x86; compile-cfg)
open import Compiler.EncloseScope using (Closed)
open import Semantics.GraphErr.Imp using (𝒜; 𝒜s; 𝒮; frame)
open import Semantics.GraphErr.CFG
  using () renaming (⟦_⟧[_] to ⟪_⟫[_]; Blocks to Blocksₜ; blocks to blocksₜ; table to tableₜ; code to codeₜ; ⟦_⟧ₚ to ⟪_⟫ₚ)
open import Semantics.GraphErr.X86
open import proof.Correctness.GraphErr.ExplicateCorrect using (module Agreeing; checkedᵉ-≃)
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
open import Data.Unit using (tt)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Level using (lift; lower)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂)
open import Relation.Nullary using (yes; no)

module proof.Correctness.GraphErr.SelectCorrect where

open import proof.Framework.GraphModel.ErrorLaws
  using (is-ω; Has; ne-has; noerr-≢; noerr-val; strict-≃; strict-self; callᵉ-ω; callᵉ-val; let-noerr)

primᵉ-ω : ∀ p {D E} → ω ∈ D → ω ∈ primᵉ p ⟨ D , ⟨ E , ptt ⟩ ⟩
primᵉ-ω p ω∈ = inj₂ ⟨ refl , inj₁ (inj₁ ω∈) ⟩

primᵉ-val : ∀ p {D E w} → w ∈ primᵉ p ⟨ D , ⟨ E , ptt ⟩ ⟩ → w ≢ ω → val∈ D
primᵉ-val p (inj₁ ⟨ k , ⟨ _ , ⟨ k∈ , _ ⟩ ⟩ ⟩) _ = ⟨ const k , ⟨ k∈ , (λ ()) ⟩ ⟩
primᵉ-val p (inj₂ ⟨ refl , _ ⟩) w≢ = ⊥-elim (w≢ refl)

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
atom-table [] k = ⟨ (λ ()) , ⟨ ν , tt ⟩ ⟩
atom-table (b ∷ bs) k with k ≟ length bs
... | yes _ = ⟨ (λ ()) , ⟨ ν , tt ⟩ ⟩
... | no _ = atom-table bs k

{- case: test, bind the payload, and branch on the flag ----------------------------------}

isinl-ω : ∀ {A} → ω ∈ isinlᵉ A → ω ∈ A ⊎ wrong IsInj A
isinl-ω (inj₁ ⟨ _ , ⟨ _ , () ⟩ ⟩)
isinl-ω (inj₂ (inj₁ ⟨ _ , ⟨ _ , () ⟩ ⟩))
isinl-ω (inj₂ (inj₂ ⟨ _ , e ⟩)) = e

payload-ω : ∀ {A} → ω ∈ payloadᵉ A → ω ∈ A ⊎ wrong IsInj A
payload-ω (inj₁ ⟨ _ , ω≢ ⟩) = ⊥-elim (ω≢ refl)
payload-ω (inj₂ (inj₁ ⟨ _ , ω≢ ⟩)) = ⊥-elim (ω≢ refl)
payload-ω (inj₂ (inj₂ ⟨ _ , e ⟩)) = e

{- a payload is that of an injection, whose tag the flag holds, or an error -}
payload-has : ∀ {A d} → d ∈ payloadᵉ A → Has (isinlᵉ A)
payload-has {d = d} (inj₁ ⟨ l∈ , _ ⟩) = inj₂ ⟨ left ⟨⟩ , ⟨ inj₁ ⟨ d , ⟨ l∈ , refl ⟩ ⟩ , (λ ()) ⟩ ⟩
payload-has {d = d} (inj₂ (inj₁ ⟨ r∈ , _ ⟩)) = inj₂ ⟨ right ⟨⟩ , ⟨ inj₂ (inj₁ ⟨ d , ⟨ r∈ , refl ⟩ ⟩) , (λ ()) ⟩ ⟩
payload-has (inj₂ (inj₂ ⟨ refl , e ⟩)) = inj₁ (inj₂ (inj₂ ⟨ refl , e ⟩))

case-core : ∀ n x {A : 𝒫 Value} {F₁ F₂ : 𝒫 Value → 𝒫 Value} → Tagged A
  → strictᵉ (isinlᵉ A) (checkedᵉ n x (payloadᵉ A)
       (letᵉ ⟨ payloadᵉ A , ⟨ (λ X → 𝒞ᵉ ⟨ isinlᵉ A , ⟨ (λ _ → F₁ X) , ⟨ (λ _ → F₂ X) , ptt ⟩ ⟩ ⟩) , ptt ⟩ ⟩))
    ≃ checkedᵉ n x (payloadᵉ A) (𝒞ᵉ ⟨ A , ⟨ F₁ , ⟨ F₂ , ptt ⟩ ⟩ ⟩)
case-core n x {A} {F₁} {F₂} tg with x <? n
... | yes _ = ⟨ to , from ⟩
  where
  I = isinlᵉ A
  L = letᵉ ⟨ payloadᵉ A , ⟨ (λ X → 𝒞ᵉ ⟨ I , ⟨ (λ _ → F₁ X) , ⟨ (λ _ → F₂ X) , ptt ⟩ ⟩ ⟩) , ptt ⟩ ⟩
  C = 𝒞ᵉ ⟨ A , ⟨ F₁ , ⟨ F₂ , ptt ⟩ ⟩ ⟩

  branch : ∀ V → V ≢ [] → V ≈ V → NoErr V → mem V ⊆ payloadᵉ A
    → 𝒞ᵉ ⟨ I , ⟨ (λ _ → F₁ (mem V)) , ⟨ (λ _ → F₂ (mem V)) , ptt ⟩ ⟩ ⟩ ⊆ C
  branch [] ne = ⊥-elim (ne refl)
  branch (v ∷ V) _ c nV V⊆ w (inj₁ ⟨ u , ⟨ _ , ⟨ ls , ⟨ w∈ , _ ⟩ ⟩ ⟩ ⟩) with ls u (here refl)
  ... | inj₁ ⟨ _ , ⟨ l∈ , _ ⟩ ⟩ = inj₁ ⟨ v , ⟨ V , ⟨ lefts , ⟨ w∈ , ⟨ c , nV ⟩ ⟩ ⟩ ⟩ ⟩
    where
    lefts : ∀ d → d ∈ mem (v ∷ V) → left d ∈ A
    lefts d d∈ with V⊆ d d∈
    ... | inj₁ ⟨ l , _ ⟩ = l
    ... | inj₂ (inj₁ ⟨ r , _ ⟩) = ⊥-elim (tg l∈ r)
    ... | inj₂ (inj₂ ⟨ refl , _ ⟩) = ⊥-elim (nV d∈)
  ... | inj₂ (inj₁ ⟨ _ , ⟨ _ , () ⟩ ⟩)
  ... | inj₂ (inj₂ ⟨ () , _ ⟩)
  branch (v ∷ V) _ c nV V⊆ w (inj₂ (inj₁ ⟨ u , ⟨ _ , ⟨ rs , ⟨ w∈ , _ ⟩ ⟩ ⟩ ⟩)) with rs u (here refl)
  ... | inj₂ (inj₁ ⟨ _ , ⟨ r∈ , _ ⟩ ⟩) = inj₂ (inj₁ ⟨ v , ⟨ V , ⟨ rights , ⟨ w∈ , ⟨ c , nV ⟩ ⟩ ⟩ ⟩ ⟩)
    where
    rights : ∀ d → d ∈ mem (v ∷ V) → right d ∈ A
    rights d d∈ with V⊆ d d∈
    ... | inj₁ ⟨ l , _ ⟩ = ⊥-elim (tg l r∈)
    ... | inj₂ (inj₁ ⟨ r , _ ⟩) = r
    ... | inj₂ (inj₂ ⟨ refl , _ ⟩) = ⊥-elim (nV d∈)
  ... | inj₁ ⟨ _ , ⟨ _ , () ⟩ ⟩
  ... | inj₂ (inj₂ ⟨ () , _ ⟩)
  branch (v ∷ V) _ c nV V⊆ w (inj₂ (inj₂ ⟨ refl , inj₁ ω∈ ⟩)) = inj₂ (inj₂ ⟨ refl , isinl-ω ω∈ ⟩)
  branch (v ∷ V) _ c nV V⊆ w (inj₂ (inj₂ ⟨ refl , inj₂ ⟨ d , ⟨ d∈ , ⟨ d≢ , ni ⟩ ⟩ ⟩ ⟩)) with d∈
  ... | inj₁ ⟨ _ , ⟨ _ , refl ⟩ ⟩ = ⊥-elim (ni tt)
  ... | inj₂ (inj₁ ⟨ _ , ⟨ _ , refl ⟩ ⟩) = ⊥-elim (ni tt)
  ... | inj₂ (inj₂ ⟨ refl , _ ⟩) = ⊥-elim (d≢ refl)

  to : strictᵉ I L ⊆ C
  to w (inj₁ ⟨ refl , ω∈ ⟩) = inj₂ (inj₂ ⟨ refl , isinl-ω ω∈ ⟩)
  to w (inj₂ ⟨ _ , inj₁ ⟨ V , ⟨ ⟨ w∈ , ⟨ ne , ⟨ c , nV ⟩ ⟩ ⟩ , ⟨ V⊆ , _ ⟩ ⟩ ⟩ ⟩) = branch V ne c nV V⊆ w w∈
  to w (inj₂ ⟨ _ , inj₂ ⟨ refl , inj₁ () ⟩ ⟩)
  to w (inj₂ ⟨ _ , inj₂ ⟨ refl , inj₂ (inj₁ ⟨ d , ⟨ d∈ , ⟨ _ , nf ⟩ ⟩ ⟩) ⟩ ⟩) = ⊥-elim (nf (Λᵉ-fun d d∈))
  to w (inj₂ ⟨ _ , inj₂ ⟨ refl , inj₂ (inj₂ ⟨ _ , ω∈ ⟩) ⟩ ⟩) = inj₂ (inj₂ ⟨ refl , payload-ω ω∈ ⟩)

  from : C ⊆ strictᵉ I L
  from w (inj₁ ⟨ v , ⟨ V , ⟨ ls , ⟨ w∈ , ⟨ c , nV ⟩ ⟩ ⟩ ⟩ ⟩) =
    inj₂ ⟨ ⟨ left ⟨⟩ , ⟨ tag , (λ ()) ⟩ ⟩
         , inj₁ ⟨ v ∷ V , ⟨ ⟨ inj₁ ⟨ ⟨⟩ , ⟨ [] , ⟨ (λ { _ (here refl) → tag }) , ⟨ w∈ , ⟨ ≈-single , (λ { (here ()) ; (there ()) }) ⟩ ⟩ ⟩ ⟩ ⟩
                              , ⟨ (λ ()) , ⟨ c , nV ⟩ ⟩ ⟩
                 , ⟨ (λ d d∈ → inj₁ ⟨ ls d d∈ , noerr-≢ nV d∈ ⟩) , ⟨ (λ ()) , nV ⟩ ⟩ ⟩ ⟩ ⟩
    where tag = inj₁ ⟨ v , ⟨ ls v (here refl) , refl ⟩ ⟩
  from w (inj₂ (inj₁ ⟨ v , ⟨ V , ⟨ rs , ⟨ w∈ , ⟨ c , nV ⟩ ⟩ ⟩ ⟩ ⟩)) =
    inj₂ ⟨ ⟨ right ⟨⟩ , ⟨ tag , (λ ()) ⟩ ⟩
         , inj₁ ⟨ v ∷ V , ⟨ ⟨ inj₂ (inj₁ ⟨ ⟨⟩ , ⟨ [] , ⟨ (λ { _ (here refl) → tag }) , ⟨ w∈ , ⟨ ≈-single , (λ { (here ()) ; (there ()) }) ⟩ ⟩ ⟩ ⟩ ⟩)
                              , ⟨ (λ ()) , ⟨ c , nV ⟩ ⟩ ⟩
                 , ⟨ (λ d d∈ → inj₂ (inj₁ ⟨ rs d d∈ , noerr-≢ nV d∈ ⟩)) , ⟨ (λ ()) , nV ⟩ ⟩ ⟩ ⟩ ⟩
    where tag = inj₂ (inj₁ ⟨ v , ⟨ rs v (here refl) , refl ⟩ ⟩)
  from w (inj₂ (inj₂ ⟨ refl , e ⟩)) = inj₁ ⟨ refl , inj₂ (inj₂ ⟨ refl , e ⟩) ⟩
... | no _ = ⟨ to , from ⟩
  where
  to : _
  to w (inj₁ ⟨ refl , ω∈ ⟩) = ⟨ refl , ⟨ ω , inj₂ (inj₂ ⟨ refl , isinl-ω ω∈ ⟩) ⟩ ⟩
  to w (inj₂ ⟨ _ , w∈ ⟩) = w∈
  from : _
  from w ⟨ refl , ⟨ d , d∈ ⟩ ⟩ with payload-has d∈
  ... | inj₁ ω∈ = inj₁ ⟨ refl , ω∈ ⟩
  ... | inj₂ v = inj₂ ⟨ v , ⟨ refl , ⟨ d , d∈ ⟩ ⟩ ⟩

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
    lower (callᵉ-mono _ _ ⟨ lift (𝒜-mono f s) , ⟨ lift (𝒜-mono e s) , ⟨ lift (𝒜-mono a s) , ptt ⟩ ⟩ ⟩)
  𝒮-mono (I.pair a b) s = lower (pairᵉ-mono _ _ ⟨ lift (𝒜-mono a s) , ⟨ lift (𝒜-mono b s) , ptt ⟩ ⟩)
  𝒮-mono (fst a) s = lower (carᵉ-mono _ _ ⟨ lift (𝒜-mono a s) , ptt ⟩)
  𝒮-mono (snd a) s = lower (cdrᵉ-mono _ _ ⟨ lift (𝒜-mono a s) , ptt ⟩)
  𝒮-mono (tuple as) s = lower (𝒯ᵉ-mono (length as) _ _ (𝒜s-mono as s))
  𝒮-mono (get i a) s = lower (projᵉ-mono i _ _ ⟨ lift (𝒜-mono a s) , ptt ⟩)
  𝒮-mono (I.inl a) s = lower (inlᵉ-mono _ _ ⟨ lift (𝒜-mono a s) , ptt ⟩)
  𝒮-mono (I.inr a) s = lower (inrᵉ-mono _ _ ⟨ lift (𝒜-mono a s) , ptt ⟩)
  𝒮-mono (prim p a b) s = lower (primᵉ-mono p _ _ ⟨ lift (𝒜-mono a s) , ⟨ lift (𝒜-mono b s) , ptt ⟩ ⟩)

  checkedᵉ-mono : ∀ x {D D' E E'} → D ⊆ D' → E ⊆ E' → checkedᵉ n x D E ⊆ checkedᵉ n x D' E'
  checkedᵉ-mono x D⊆ E⊆ with x <? n
  ... | yes _ = E⊆
  ... | no _ = λ { w ⟨ refl , ⟨ d , d∈ ⟩ ⟩ → ⟨ refl , ⟨ d , D⊆ d d∈ ⟩ ⟩ }

  MonoB : Blocksₜ → Set₁
  MonoB B = ∀ l {σ σ'} → σ ⊆ₛ σ' → B l σ ⊆ B l σ'

  tail-mono : ∀ t {B} → MonoB B → ∀ {σ σ'} → σ ⊆ₛ σ' → ⟪ t ⟫[ T ] n B σ ⊆ ⟪ t ⟫[ T ] n B σ'
  tail-mono (C.return r) mB s = 𝒮-mono r s
  tail-mono (C.seq x r t) mB s = checkedᵉ-mono x (𝒮-mono r s) (lower (letᵉ-mono _ _
    ⟨ lift (𝒮-mono r s) , ⟨ (λ X Y X⊆ → lift (tail-mono t mB (↦-mono s X⊆))) , ptt ⟩ ⟩))
  tail-mono (C.goto l) mB s = mB l s
  tail-mono (C.case a x l₁ l₂) mB s = checkedᵉ-mono x (payloadᵉ-mono (𝒜-mono a s)) (lower (𝒞ᵉ-mono _ _
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
  after (var x) K σ D = checkedᵉ n x D (letᵉ ⟨ D , ⟨ (λ X → K (σ [ x ↦ X ])) , ptt ⟩ ⟩)
  after (reg g) K σ D = D

  ≔-same : ∀ g {ρ D} → (ρ [ g ≔ D ]) g ≡ D
  ≔-same rax = refl
  ≔-same rdi = refl
  ≔-same rsi = refl

  put-≃ : ∀ d {κ K D D' σ ρ φ} → Fits d κ K → Inv σ → D ≃ D' → put n d D κ σ ρ φ ≃ after d K σ D'
  put-≃ (var x) {κ} {K} {σ = σ} {ρ} {φ} fits i D≃ =
    checkedᵉ-≃ n {x} D≃ (letᵉ-≃ {F = λ X → κ (σ [ x ↦ X ]) ρ φ} {λ X → K (σ [ x ↦ X ])} D≃
      (λ V ne c _ → fits _ (inv-↦ i (atom-≈ ne c)) ρ φ))
  put-≃ (reg g) {D = D} {σ = σ} {ρ} {φ} fits i D≃ =
    ≃-trans (strict-self (≃-trans (fits σ (ρ [ g ≔ D ]) φ) (≃-reflexive (≔-same g)))) D≃

  {- an assignment needs its value -}
  put-has : ∀ d {D κ σ ρ φ} w → w ∈ put n d D κ σ ρ φ → Has D
  put-has (var x) w w∈ with x <? n
  put-has (var x) w (inj₁ ⟨ V , ⟨ ⟨ _ , ⟨ ne , ⟨ _ , nV ⟩ ⟩ ⟩ , ⟨ V⊆ , _ ⟩ ⟩ ⟩) | yes _ = inj₂ (noerr-val V ne nV V⊆)
  put-has (var x) w (inj₂ ⟨ refl , inj₁ () ⟩) | yes _
  put-has (var x) w (inj₂ ⟨ refl , inj₂ (inj₁ ⟨ d , ⟨ d∈ , ⟨ _ , nf ⟩ ⟩ ⟩) ⟩) | yes _ = ⊥-elim (nf (Λᵉ-fun d d∈))
  put-has (var x) w (inj₂ ⟨ refl , inj₂ (inj₂ ⟨ _ , ω∈ ⟩) ⟩) | yes _ = inj₁ ω∈
  put-has (var x) w ⟨ refl , ne ⟩ | no _ = ne-has ne
  put-has (reg g) w (inj₁ ⟨ refl , ω∈ ⟩) = inj₁ ω∈
  put-has (reg g) w (inj₂ ⟨ v , _ ⟩) = inj₂ v

  put-val : ∀ d {D κ σ ρ φ} w → w ∈ put n d D κ σ ρ φ → w ≢ ω → val∈ D
  put-val (var x) w w∈ w≢ with x <? n
  put-val (var x) w (inj₁ ⟨ V , ⟨ ⟨ _ , ⟨ ne , ⟨ _ , nV ⟩ ⟩ ⟩ , ⟨ V⊆ , _ ⟩ ⟩ ⟩) w≢ | yes _ = noerr-val V ne nV V⊆
  put-val (var x) w (inj₂ ⟨ refl , _ ⟩) w≢ | yes _ = ⊥-elim (w≢ refl)
  put-val (var x) w ⟨ refl , _ ⟩ w≢ | no _ = ⊥-elim (w≢ refl)
  put-val (reg g) w (inj₁ ⟨ refl , _ ⟩) w≢ = ⊥-elim (w≢ refl)
  put-val (reg g) w (inj₂ ⟨ v , _ ⟩) w≢ = v

  put-ω : ∀ d {D κ σ ρ φ} → ω ∈ D → ω ∈ put n d D κ σ ρ φ
  put-ω (var x) ω∈ with x <? n
  ... | yes _ = inj₂ ⟨ refl , inj₂ (inj₂ ⟨ ⟨ ν , ⟨ tt , tt ⟩ ⟩ , ω∈ ⟩) ⟩
  ... | no _ = ⟨ refl , ⟨ ω , ω∈ ⟩ ⟩
  put-ω (reg g) ω∈ = inj₁ ⟨ refl , ω∈ ⟩

  {- the last write of the instructions of r, into d -}
  put-strict : ∀ d {D κ K D' σ ρ φ} → Fits d κ K → Inv σ → D ≃ D'
    → strictᵉ D (put n d D κ σ ρ φ) ≃ after d K σ D'
  put-strict d f i D≃ = strict-≃ (put-≃ d f i D≃) (put-has d) (put-ω d) (put-val d)

  {- the instructions of r into d, then is -}
  sel : ∀ r d is {κ K} → Fits d (⟦ is ⟧ˢ T n κ) K → ∀ σ → Inv σ → ∀ ρ φ
    → ⟦ select-simple r d ++ is ⟧ˢ T n κ σ ρ φ ≃ after d K σ (𝒮 T' n σ r)
  sel (atm a) d is f σ i ρ φ = put-≃ d f i (atm-≃ a)
  sel (app g e a) d is {κ} f σ i ρ φ = strict-≃ LA (λ _ _ → atm-has e i) ωE valE
    where
    E = 𝒪 T n σ ρ (select-atm e)
    ρ₁ = ρ [ rdi ≔ E ]
    A = 𝒪 T n σ ρ₁ (select-atm a)
    ρ₂ = ρ₁ [ rsi ≔ A ]
    G = 𝒪 T n σ ρ₂ (select-atm g)
    R = callᵉ ⟨ G , ⟨ E , ⟨ A , ptt ⟩ ⟩ ⟩
    Y = put n d R (⟦ is ⟧ˢ T n κ) σ (called R) init
    LR : strictᵉ R Y ≃ _
    LR = put-strict d f i (callᵉ-≃ (atm-≃ g) (atm-≃ e) (atm-≃ a))
    ωA : ω ∈ A → ω ∈ strictᵉ R Y
    ωA ωa with atm-has e i
    ... | inj₁ ωe = inj₁ ⟨ refl , callᵉ-ω (atm-has g i) (inj₁ ωe) ⟩
    ... | inj₂ ve = inj₁ ⟨ refl , callᵉ-ω (atm-has g i) (inj₂ ⟨ ve , ωa ⟩) ⟩
    valA : ∀ w → w ∈ strictᵉ R Y → w ≢ ω → val∈ A
    valA w (inj₁ ⟨ refl , _ ⟩) w≢ = ⊥-elim (w≢ refl)
    valA w (inj₂ ⟨ ⟨ r , ⟨ r∈ , r≢ ⟩ ⟩ , _ ⟩) _ = proj₂ (callᵉ-val {G} r∈ r≢)
    LA : strictᵉ A (strictᵉ R Y) ≃ _
    LA = strict-≃ LR (λ _ _ → atm-has a i) ωA valA
    ωE : ω ∈ E → ω ∈ strictᵉ A (strictᵉ R Y)
    ωE ωe with atm-has a i
    ... | inj₁ ωa = inj₁ ⟨ refl , ωa ⟩
    ... | inj₂ va = inj₂ ⟨ va , inj₁ ⟨ refl , callᵉ-ω (atm-has g i) (inj₁ ωe) ⟩ ⟩
    valE : ∀ w → w ∈ strictᵉ A (strictᵉ R Y) → w ≢ ω → val∈ E
    valE w (inj₁ ⟨ refl , _ ⟩) w≢ = ⊥-elim (w≢ refl)
    valE w (inj₂ ⟨ _ , inj₁ ⟨ refl , _ ⟩ ⟩) w≢ = ⊥-elim (w≢ refl)
    valE w (inj₂ ⟨ _ , inj₂ ⟨ ⟨ r , ⟨ r∈ , r≢ ⟩ ⟩ , _ ⟩ ⟩) _ = proj₁ (callᵉ-val {G} r∈ r≢)
  sel (I.pair a b) d is f σ i ρ φ = put-≃ d f i (pairᵉ-≃ (atm-≃ a) (atm-≃ b))
  sel (fst a) d is f σ i ρ φ = put-≃ d f i (carᵉ-≃ (atm-≃ a))
  sel (snd a) d is f σ i ρ φ = put-≃ d f i (cdrᵉ-≃ (atm-≃ a))
  sel (tuple as) d is f σ i ρ φ =
    put-≃ d f i (≃-trans (≃-reflexive (cong (λ p → 𝒯ᵉ (proj₁ p) (proj₂ p)) (𝒪s-≡ as))) (𝒮-≃ (tuple as) σ))
  sel (get j a) d is f σ i ρ φ = put-≃ d f i (projᵉ-≃ j (atm-≃ a))
  sel (I.inl a) d is f σ i ρ φ = put-≃ d f i (inlᵉ-≃ (atm-≃ a))
  sel (I.inr a) d is f σ i ρ φ = put-≃ d f i (inrᵉ-≃ (atm-≃ a))
  sel (prim P.sub a b) d is {κ} f σ i ρ φ =
    strict-≃ (put-strict d f i (primᵉ-≃ P.sub (atm-≃ a) (atm-≃ b))) (λ _ _ → atm-has a i)
      (λ ωa → inj₁ ⟨ refl , primᵉ-ω P.sub ωa ⟩) valA
    where
    A = 𝒪 T n σ ρ (select-atm a)
    Q = primᵉ P.sub ⟨ A , ⟨ 𝒪 T n σ (ρ [ rax ≔ A ]) (select-atm b) , ptt ⟩ ⟩
    valA : ∀ w → w ∈ strictᵉ Q (put n d Q (⟦ is ⟧ˢ T n κ) σ (ρ [ rax ≔ A ] [ rax ≔ Q ]) φ) → w ≢ ω → val∈ A
    valA w (inj₁ ⟨ refl , _ ⟩) w≢ = ⊥-elim (w≢ refl)
    valA w (inj₂ ⟨ ⟨ r , ⟨ r∈ , r≢ ⟩ ⟩ , _ ⟩) _ = primᵉ-val P.sub r∈ r≢
  sel (prim P.eq a b) d is f σ i ρ φ = put-strict d f i (primᵉ-≃ P.eq (atm-≃ a) (atm-≃ b))

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
      (checkedᵉ-≃ n {x} (payloadᵉ-≃ (atm-≃ a))
        (𝒞ᵉ-≃ {F = F₁} {λ X → B' l₁ (σ [ x ↦ X ])} {F₂} {λ X → B' l₂ (σ [ x ↦ X ])}
          (atm-≃ a) (λ v V c _ → br l₁ _ (inv-↦ i (atom-≈ (λ ()) c)) ρ _)
                        (λ v V c _ → br l₂ _ (inv-↦ i (atom-≈ (λ ()) c)) ρ _)))
    where
    A = 𝒪 T n σ ρ (select-atm a)
    F₁ = λ X → B l₁ (σ [ x ↦ X ]) ρ (isinlᵉ A)
    F₂ = λ X → B l₂ (σ [ x ↦ X ]) ρ (isinlᵉ A)

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
    → checkedᵉ n 0 (mem V) (letᵉ ⟨ mem V , ⟨ (λ X → checkedᵉ n 1 (mem U)
        (letᵉ ⟨ mem U , ⟨ (λ Y → F (zeros [ 0 ↦ X ] [ 1 ↦ Y ])) , ptt ⟩ ⟩)) , ptt ⟩ ⟩)
      ≃ G (frame (mem V) (mem U))
  frame-≃ le {F} {G} FG mono {V} {U} neV cV nV neU cU nU with 0 <? n | 1 <? n
  ... | no ¬p | _ = ⊥-elim (¬p (≤-trans (s≤s z≤n) le))
  ... | yes _ | no ¬p = ⊥-elim (¬p le)
  ... | yes _ | yes _ = ⟨ to , from ⟩
    where
    to : _
    to w (inj₁ ⟨ V' , ⟨ ⟨ inj₁ ⟨ U' , ⟨ ⟨ w∈ , ⟨ neU' , ⟨ cU' , _ ⟩ ⟩ ⟩ , ⟨ U'⊆ , _ ⟩ ⟩ ⟩ , ⟨ neV' , ⟨ cV' , _ ⟩ ⟩ ⟩ , ⟨ V'⊆ , _ ⟩ ⟩ ⟩) =
      mono s w (proj₁ (FG _ i) w w∈)
      where
      s : zeros [ 0 ↦ mem V' ] [ 1 ↦ mem U' ] ⊆ₛ frame (mem V) (mem U)
      s 0 = V'⊆
      s 1 = U'⊆
      s (suc (suc y)) = λ _ z → z
      i : Inv (zeros [ 0 ↦ mem V' ] [ 1 ↦ mem U' ])
      i 0 = atom-≈ neV' cV'
      i 1 = atom-≈ neU' cU'
      i (suc (suc y)) = atom-zero
    to w (inj₁ ⟨ V' , ⟨ ⟨ inj₂ ⟨ refl , e ⟩ , _ ⟩ , _ ⟩ ⟩) = ⊥-elim (let-noerr nU e)
    to w (inj₂ ⟨ refl , e ⟩) = ⊥-elim (let-noerr nV e)
    from : _
    from w w∈ = inj₁ ⟨ V , ⟨ ⟨ inj₁ ⟨ U , ⟨ ⟨ proj₂ (FG _ i) w (mono s w w∈) , ⟨ neU , ⟨ cU , nU ⟩ ⟩ ⟩
                                            , ⟨ (λ _ z → z) , ⟨ neU , nU ⟩ ⟩ ⟩ ⟩
                                , ⟨ neV , ⟨ cV , nV ⟩ ⟩ ⟩
                            , ⟨ (λ _ z → z) , ⟨ neV , nV ⟩ ⟩ ⟩ ⟩
      where
      s : frame (mem V) (mem U) ⊆ₛ zeros [ 0 ↦ mem V ] [ 1 ↦ mem U ]
      s 0 = λ _ z → z
      s 1 = λ _ z → z
      s (suc (suc y)) = λ _ z → z
      i : Inv (zeros [ 0 ↦ mem V ] [ 1 ↦ mem U ])
      i 0 = atom-≈ neV cV
      i 1 = atom-≈ neU cU
      i (suc (suc y)) = atom-zero

{- the code of a global definition, in a frame of max(2, n) slots -}
code-≃ : ∀ {T T' : Table} (TT : ∀ k → T k ≃ T' k) (TL : ∀ k → Atom (T k)) n bs t
  → code T (select-body prologue (C.body n bs t)) ≃ codeₜ T' (C.body n bs t)
code-≃ {T} {T'} TT TL n bs t = Λᵉ-≃ λ V neV cV nV → Λᵉ-≃ λ U neU cU nU →
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

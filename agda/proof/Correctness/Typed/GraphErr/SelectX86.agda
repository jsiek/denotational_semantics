{-

  Select instructions (CFGᵀ → X86, Compiler/Typed/Select.agda) is correct
  in the graph model with errors for CFGᵀ with the X86 checks
  (SelectCheck.agda): the X86 program means exactly what that does, for
  every CFGᵀ program, as in the untyped proof
  (proof/Correctness/GraphErr/SelectCorrect.agda) and the plain graph
  model's (proof/Correctness/Typed/Graph/SelectCorrect.agda).

  The X86 store holds the slots of the frame at their levels (Rel); a
  tail runs within its frame (depth-≥, Compiler/Typed/SelectFacts). The
  instructions of s into d, then κ, mean d := s; K when κ means K with
  any registers and flag (sel, Fits, after). The X86 writes to registers
  are the strict writes of CFGᵀ with checks (strictᵐ); a write of an atom
  changes nothing (an atom is a set of values, Inv). A case tests the
  tag, binds the payload and branches on the flag: 𝒞ᵐ on a slot that
  never holds both an inl and an inr (Tagged, case-core). The start of a
  definition moves %rdi and %rsi to slots 0 and 1, as the code of CFGᵀ
  with checks binds them. Blocks and definitions map one to one, by
  level.

-}

module proof.Correctness.Typed.GraphErr.SelectX86 where

open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.Domain
open import proof.Framework.GraphModel.DOpSig using (Results; RRs; mono-≃)
open import proof.Framework.GraphModel.OpsBase using (ℬ)
open import proof.Framework.GraphModel.ErrorMonad
open import proof.Framework.GraphModel.Ops using (⋆; 𝒞; payloadD)
open import proof.Framework.GraphModel.ContinuityBase using (mono)
open import proof.Framework.GraphModel.Env using (Env)
open import proof.Semantics.GraphErr.Prim using (primᵐ; primᵐ-≃)
open import proof.Semantics.GraphErr.Typed.Clos5 using (tbl)
open import Framework.Primitives using (Int)
open import Framework.Membership using (_⊑_; here⊑; there⊑; ⊑-∋)
open import proof.Framework.Lookup using (lvl-<; lvl-⊑)
import Language.Prim as P
open import Language.Typed.Type hiding (_≟_)
import Language.Typed.Mon as M
open import Language.Typed.Imp using (Atm; var; lit; ref; atm; pack; callc; tuple; get; inl; inr; prim; inject; project)
import Language.Typed.CFG as C
open C using (Tail; return; seq; goto; case; Blocks; _▷_)
import Language.X86 as L
open L using (Loc; reg; rax; rdi; rsi)
open import Compiler.Typed.Select
open import proof.Compiler.Typed.SelectFacts using (depth-≥; len-defs; len-blocks)
import Semantics.GraphErr.X86 as X
open X using (Store; read; _[_↦_]; frameᵐ; zeros; _[_≔_]; called; args)
open import Semantics.GraphErr.Typed.Ops using (init)
open import Semantics.GraphErr.Typed.CFG using (Table; 𝒜; BEnv; drop)
open import Semantics.GraphErr.Typed.Clos5 using (⟦_⟧s[_])
open import proof.Correctness.Typed.GraphErr.SelectCheck

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin)
open import Data.Integer using (0ℤ)
open import Data.List using (List; []; _∷_; _++_; length; replicate)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Nat using (ℕ; suc; _≤_; _<_; _≟_; _<?_; _⊔_; s≤s; z≤n)
open import Data.Nat.Properties using (≤-trans; <-≤-trans; m≤m⊔n; m≤n⊔m; <⇒≢; ≤-refl; n≤1+n)
open import Data.Product using (Σ; Σ-syntax; _×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt; ⊤)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Data.Vec using (Vec; []; _∷_; toList; map)
open import Level using (lift; lower)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (yes; no)

{- Stores ------------------------------------------------------------------------------}

read-in : ∀ {n σ x} → x < n → read n σ x ≡ σ x
read-in {n} {σ} {x} lt with x <? n
... | yes _ = refl
... | no ¬p = ⊥-elim (¬p lt)

frame-in : ∀ {n x D E} → x < n → frameᵐ n x D E ≡ E
frame-in {n} {x} lt with x <? n
... | yes _ = refl
... | no ¬p = ⊥-elim (¬p lt)

↦-same : ∀ {σ : Store} {x D} → (σ [ x ↦ D ]) x ≡ D
↦-same {x = x} with x ≟ x
... | yes _ = refl
... | no ne = ⊥-elim (ne refl)

↦-other : ∀ {σ : Store} {x y D} → y ≢ x → (σ [ x ↦ D ]) y ≡ σ y
↦-other {x = x} {y} ne with y ≟ x
... | yes e = ⊥-elim (ne e)
... | no _ = refl

≔-same : ∀ g {ρ : X.Regs} {D} → (ρ [ g ≔ D ]) g ≡ D
≔-same rax = refl
≔-same rdi = refl
≔-same rsi = refl

drop-idx : ∀ {Δ' Δ A} (p : Δ' ⊑ Δ) (σ : Env Value) (y : Δ' ∋ A) → drop p σ (idx y) ≡ σ (idx (⊑-∋ p y))
drop-idx here⊑ σ y = refl
drop-idx (there⊑ p) σ y = drop-idx p (λ i → σ (suc i)) y

ˢ-++ : ∀ xs {ys T n κ} → X.⟦ xs ++ ys ⟧ˢ T n κ ≡ X.⟦ xs ⟧ˢ T n (X.⟦ ys ⟧ˢ T n κ)
ˢ-++ [] = refl
ˢ-++ (i ∷ xs) {T = T} {n} = cong (X.⟦ i ⟧ⁱ T n) (ˢ-++ xs)

{- A slot holds a set of values, never both an inl and an inr -}
Tagged : 𝒫 Value → Set
Tagged D = ∀ {u v} → left u ∈ D → right v ∈ D → ⊥

Atom : 𝒫 Value → Set
Atom D = Tagged D × Val D

Inv : Store → Set
Inv σ = ∀ y → Atom (σ y)

atom-≈ : ∀ {V} → V ≢ [] → V ≈ V → NoErr V → Atom (mem V)
atom-≈ {V} ne c n = ⟨ (λ l r → ≈⇒Every V V c _ _ l r) , noerr-val V ne n ⟩

inv-↦ : ∀ {σ x X} → Inv σ → Atom X → Inv (σ [ x ↦ X ])
inv-↦ {x = x} i t y with y ≟ x
... | yes _ = t
... | no _ = i y

ℬ-atom : ∀ {B c} → Atom (ℬ B c ptt)
ℬ-atom {c = c} = ⟨ (λ ()) , ⟨ (λ { _ d∈ refl → ⊥-elim d∈ }) , ⟨ const c , ⟨ refl , refl ⟩ ⟩ ⟩ ⟩

{- strict writes ------------------------------------------------------------------------}

strict-val : ∀ {A E} → Val A → strictᵐ A E ≃ E
strict-val {A} {E} v = ≫=-val-β {A} {λ _ → E} v

strict-≫= : ∀ {D G} → strictᵐ D (D ≫= G) ≃ (D ≫= G)
strict-≫= = ⟨ (λ { w (inj₁ ⟨ refl , ω∈ ⟩) → inj₁ ⟨ refl , ω∈ ⟩ ; w (inj₂ ⟨ _ , w∈ ⟩) → w∈ })
            , (λ { w (inj₁ ⟨ refl , ω∈ ⟩) → inj₁ ⟨ refl , ω∈ ⟩ ; w (inj₂ ⟨ c , w∈ ⟩) → inj₂ ⟨ c , inj₂ ⟨ c , w∈ ⟩ ⟩ }) ⟩

{- case: test, bind the payload, and branch on the flag ------------------------------------}

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

case-core : ∀ {A : 𝒫 Value} {F₁ F₂ : 𝒫 Value → 𝒫 Value} → Tagged A
  → strictᵐ (isinlᵐ A) (letᵐ ⟨ payloadᵐ A , ⟨ (λ X → 𝒞ᵐ ⟨ isinlᵐ A , ⟨ (λ _ → F₁ X) , ⟨ (λ _ → F₂ X) , ptt ⟩ ⟩ ⟩) , ptt ⟩ ⟩)
    ≃ 𝒞ᵐ ⟨ A , ⟨ F₁ , ⟨ F₂ , ptt ⟩ ⟩ ⟩
case-core {A} {F₁} {F₂} tg = ⟨ to , from ⟩
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

{- The pass ---------------------------------------------------------------------------------}

{- for tables T (of X86) and T' (of CFGᵀ with checks) that agree, in a frame of n slots -}
module _ {T T' : Table} (TT : ∀ k → T k ≃ T' k) (TV : ∀ k → Atom (T k)) (n : ℕ) where

  {- the X86 store holds the slots of the frame at their levels -}
  Rel : Ctx → Store → Env Value → Set
  Rel Δ s σ = ∀ {A} (x : Δ ∋ A) → s (lvl x) ≃ σ (idx x)

  rel-↦ : ∀ {Δ Δ' A s σ X} (p : Δ' ⊑ Δ) → Rel Δ s σ → Rel (A ∷ Δ') (s [ length Δ' ↦ X ]) (X • drop p σ)
  rel-↦ {Δ' = Δ'} {s = s} p r Z = ≃-reflexive (↦-same {s} {length Δ'})
  rel-↦ {s = s} {σ} p r (S y) =
    ≃-trans (≃-reflexive (↦-other (<⇒≢ (lvl-< y))))
      (≃-trans (≃-trans (≃-reflexive (cong s (sym (lvl-⊑ p y)))) (r (⊑-∋ p y))) (≃-reflexive (sym (drop-idx p σ y))))

  atm-≃ : ∀ {Σ Δ A s σ} → length Δ ≤ n → Rel Δ s σ → (a : Atm Σ Δ A) → ∀ {ρ} → X.𝒪 T n s ρ (select-atm a) ≃ 𝒜 a T' σ
  atm-≃ le r (var x) = ≃-trans (≃-reflexive (read-in (<-≤-trans (lvl-< x) le))) (r x)
  atm-≃ le r (lit B c) = ≃-refl
  atm-≃ le r (ref f) = TT _

  atm-atom : ∀ {Σ Δ A s} → length Δ ≤ n → Inv s → (a : Atm Σ Δ A) → ∀ {ρ} → Atom (X.𝒪 T n s ρ (select-atm a))
  atm-atom {s = s} le i (var x) = subst Atom (sym (read-in {σ = s} (<-≤-trans (lvl-< x) le))) (i (lvl x))
  atm-atom le i (lit B c) = ℬ-atom
  atm-atom le i (ref f) = TV _

  {- d is a slot of the frame, or a register -}
  OkD : Loc → Set
  OkD (L.var x) = x < n
  OkD (reg g) = ⊤

  {- κ, what runs after d is assigned, means K of its value with any
     registers and flag; or returns d -}
  Fits : Loc → X.Kont → (𝒫 Value → 𝒫 Value) → Store → Set₁
  Fits (L.var x) κ K s = ∀ X → Atom X → ∀ ρ φ → κ (s [ x ↦ X ]) ρ φ ≃ K X
  Fits (reg g) κ K s = ∀ s' ρ φ → κ s' ρ φ ≃ ρ g

  {- d := D, then K, in CFGᵀ with checks -}
  after : Loc → (𝒫 Value → 𝒫 Value) → 𝒫 Value → 𝒫 Value
  after (L.var x) K D = letᵐ ⟨ D , ⟨ K , ptt ⟩ ⟩
  after (reg g) K D = D

  after-strict : ∀ d {K E D} → after d K (strictᵐ E D) ≃ strictᵐ E (after d K D)
  after-strict (L.var x) {K} {E} {D} =
    ≃-trans (letᵐ-unfold {strictᵐ E D} {K})
      (≃-trans (≫=-assoc {E} {λ _ → D} {λ X → ⋆ ⟨ Λᵐ ⟨ K , ptt ⟩ , ⟨ X , ptt ⟩ ⟩}
                  (λ {X} {X'} X⊆ → lower (⋆-mono ⟨ Λᵐ ⟨ K , ptt ⟩ , ⟨ X , ptt ⟩ ⟩ ⟨ Λᵐ ⟨ K , ptt ⟩ , ⟨ X' , ptt ⟩ ⟩
                                                 ⟨ lift (λ _ z → z) , ⟨ lift X⊆ , ptt ⟩ ⟩)))
        (strictᵐ-≃ ≃-refl (≃-sym (letᵐ-unfold {D} {K}))))
    where open import proof.Framework.GraphModel.Ops using (⋆-mono)
  after-strict (reg g) = ≃-refl

  put-≃ : ∀ d {κ K s D D' ρ φ} → OkD d → Fits d κ K s → D ≃ D' → X.put n d D κ s ρ φ ≃ after d K D'
  put-≃ (L.var x) {κ} {K} {s} {ρ = ρ} {φ} lt f D≃ =
    ≃-trans (≃-reflexive (frame-in lt)) (letᵐ-≃ {F = λ X → κ (s [ x ↦ X ]) ρ φ} {K} D≃ λ V ne c nv → f _ (atom-≈ ne c nv) ρ φ)
  put-≃ (reg g) {s = s} {D} {ρ = ρ} {φ} _ f D≃ =
    ≃-trans (strictᵐ-self (≃-trans (f s (ρ [ g ≔ D ]) φ) (≃-reflexive (≔-same g)))) D≃

  {- the last write of the instructions of s into d -}
  put-strict : ∀ d {κ K s D D' ρ φ} → OkD d → Fits d κ K s → D ≃ D' → strictᵐ D (X.put n d D κ s ρ φ) ≃ after d K D'
  put-strict (L.var x) {κ} {K} {s} {D} {D'} {ρ} {φ} lt f D≃ =
    ≃-trans (strictᵐ-≃ D≃ (put-≃ (L.var x) {κ} {K} {s} {D} {D'} {ρ} {φ} lt f D≃))
      (≃-trans (strictᵐ-≃ ≃-refl (letᵐ-unfold {D'} {K}))
        (≃-trans (strict-≫= {D'} {λ X → ⋆ ⟨ Λᵐ ⟨ K , ptt ⟩ , ⟨ X , ptt ⟩ ⟩}) (≃-sym (letᵐ-unfold {D'} {K}))))
  put-strict (reg g) {κ} {K} {s} {D} {D'} {ρ} {φ} lt f D≃ = ≃-trans (strictᵐ-≃ D≃ (put-≃ (reg g) {κ} {K} {s} {D} {D'} {ρ} {φ} lt f D≃)) (strictᵐ-self ≃-refl)


  {- the components of a tuple -}
  𝒪v : ∀ {Σ Δ m} → Store → X.Regs → Vec (Atm Σ Δ Any) m → Results (𝒫 Value) (replicate m ■)
  𝒪v s ρ [] = ptt
  𝒪v s ρ (a ∷ as) = ⟨ X.𝒪 T n s ρ (select-atm a) , 𝒪v s ρ as ⟩

  𝒪v-≡ : ∀ {Σ Δ m s ρ} (as : Vec (Atm Σ Δ Any) m) → _≡_ {A = Σ[ k ∈ ℕ ] Results (𝒫 Value) (replicate k ■)}
    ⟨ length (toList (map select-atm as)) , X.𝒪s T n s ρ (toList (map select-atm as)) ⟩ ⟨ m , 𝒪v s ρ as ⟩
  𝒪v-≡ [] = refl
  𝒪v-≡ (a ∷ as) = cong (λ p → ⟨ suc (proj₁ p) , ⟨ _ , proj₂ p ⟩ ⟩) (𝒪v-≡ as)

  𝒪v-≃ : ∀ {Σ Δ m s σ ρ} → length Δ ≤ n → Rel Δ s σ → (as : Vec (Atm Σ Δ Any) m)
    → RRs (replicate m ■) (𝒪v s ρ as) (⟦ M.⌜ as ⌝ᵛ ⟧s[ T' ] σ)
  𝒪v-≃ le r [] = ptt
  𝒪v-≃ le r (a ∷ as) = ⟨ lift (atm-≃ le r a) , 𝒪v-≃ le r as ⟩

  {- a project: its test, then the move -}
  proj-≃ : ∀ d {κ K s A A' ρ φ} {E E'} → OkD d → Fits d κ K s → A ≃ A' → E ≃ E'
    → strictᵐ E (X.put n d A κ s ρ φ) ≃ after d K (strictᵐ E' A')
  proj-≃ d ok f A≃ E≃ = ≃-trans (strictᵐ-≃ E≃ (put-≃ d ok f A≃)) (≃-sym (after-strict d))

  {- the instructions of s into d, then κ -}
  sel : ∀ {Σ Δ A} (s : C.Simple Σ Δ A) d {κ K st σ} → OkD d → Fits d κ K st → length Δ ≤ n → Rel Δ st σ → Inv st
    → ∀ ρ φ → X.⟦ select-simple s d ⟧ˢ T n κ st ρ φ ≃ after d K (𝒮ᶜ s T' σ)
  sel (atm a) d ok f le r i ρ φ = put-≃ d ok f (atm-≃ le r a)
  sel (pack a b) d ok f le r i ρ φ = put-≃ d ok f (pairᵐ-≃ (atm-≃ le r a) (atm-≃ le r b))
  sel (callc g a) d {st = st} ok f le r i ρ φ =
    ≃-trans (strictᵐ-≃ C≃ (strictᵐ-≃ D≃ (strictᵐ-≃ A≃ (put-strict d ok f (callᵐ-≃ C≃ D≃ A≃)))))
      (≃-sym (≃-trans (after-strict d) (strictᵐ-≃ ≃-refl (≃-trans (after-strict d) (strictᵐ-≃ ≃-refl (after-strict d))))))
    where
    C = carᵐ ⟨ X.𝒪 T n st ρ (select-atm g) , ptt ⟩
    ρ₁ = ρ [ rax ≔ C ]
    D = cdrᵐ ⟨ X.𝒪 T n st ρ₁ (select-atm g) , ptt ⟩
    ρ₂ = ρ₁ [ rdi ≔ D ]
    C≃ = carᵐ-≃ (atm-≃ le r g {ρ})
    D≃ = cdrᵐ-≃ (atm-≃ le r g {ρ₁})
    A≃ = atm-≃ le r a {ρ₂}

  sel (tuple {n = m} as) d {st = st} {σ} ok f le r i ρ φ =
    put-≃ d ok f (≃-trans (≃-reflexive (cong (λ p → 𝒯ᵐ (proj₁ p) (proj₂ p)) (𝒪v-≡ as))) (𝒯ᵐ-≃ m (nthD-≃ _ _ (𝒪v-≃ le r as))))
    where open import proof.Framework.GraphModel.OpsBase using (nthD-≃)
  sel (get j a) d ok f le r i ρ φ = put-≃ d ok f (projᵐ-≃ j (atm-≃ le r a))
  sel (inl a) d ok f le r i ρ φ = put-≃ d ok f (inlᵐ-≃ (atm-≃ le r a))
  sel (inr a) d ok f le r i ρ φ = put-≃ d ok f (inrᵐ-≃ (atm-≃ le r a))
  sel (prim P.sub a b) d ok f le r i ρ φ =
    ≃-trans (strict-val (proj₂ (atm-atom le i a))) (put-strict d ok f (primᵐ-≃ P.sub (atm-≃ le r a) (atm-≃ le r b)))
  sel (prim P.eq a b) d ok f le r i ρ φ = put-strict d ok f (primᵐ-≃ P.eq (atm-≃ le r a) (atm-≃ le r b))
  sel (inject G a) d ok f le r i ρ φ = put-≃ d ok f (atm-≃ le r a)
  sel (project tint a) d ok f le r i ρ φ =
    ≃-trans (strict-val (proj₂ (atm-atom le i a))) (proj-≃ d ok f A≃ (primᵐ-≃ P.sub A≃ ≃-refl))
    where A≃ = atm-≃ le r a
  sel (project tsum a) d ok f le r i ρ φ = proj-≃ d ok f A≃ (isinlᵐ-≃ A≃)
    where A≃ = atm-≃ le r a

  sel (project tfun a) d ok f le r i ρ φ = proj-≃ d ok f A≃ (carᵐ-≃ A≃)
    where A≃ = atm-≃ le r a
  sel (project (ttup m j) a) d ok f le r i ρ φ = proj-≃ d ok f A≃ (projᵐ-≃ j A≃)
    where A≃ = atm-≃ le r a

  {- the blocks B (of X86, by level) and B' (of CFGᵀ with checks) agree -}
  BR : ∀ {Bs} → X.Blocks → BEnv Bs → Set₁
  BR {Bs} B B' = ∀ {Δ} (l : Bs ∋ Δ) s σ → Rel Δ s σ → Inv s → ∀ ρ φ → B (lvl l) s ρ φ ≃ B' l σ

  tail : ∀ {Σ Bs Δ} (t : Tail Σ Bs Δ) {B : X.Blocks} {B' : BEnv Bs} → BR B B' → depth t ≤ n
    → ∀ s σ → Rel Δ s σ → Inv s → ∀ ρ φ → X.⟦ select-tail t ⟧ᵇ T n B s ρ φ ≃ ⟦ t ⟧ᶜᵗ T' B' σ
  tail (return r) br le s σ rl i ρ φ = sel r (reg rax) {K = λ _ → ∅} tt (λ _ _ _ → ≃-refl) le rl i ρ φ
  tail (seq {Δ'} p r t) {B} {B'} br le s σ rl i ρ φ =
    ≃-trans (≃-reflexive (cong (λ κ → κ s ρ φ) (ˢ-++ (select-simple r (L.var (length Δ'))))))
      (sel r (L.var (length Δ')) {K = λ X → ⟦ t ⟧ᶜᵗ T' B' (X • drop p σ)} (<-≤-trans (depth-≥ t) le′)
        (λ X aX ρ' φ' → tail t br le′ (s [ length Δ' ↦ X ]) (X • drop p σ) (rel-↦ p rl) (inv-↦ i aX) ρ' φ')
        (≤-trans (depth-≥ (seq p r t)) le) rl i ρ φ)
    where le′ = ≤-trans (m≤n⊔m _ (depth t)) le
  tail (goto l) br le s σ rl i ρ φ = br l s σ rl i ρ φ
  tail (case {Δ'} a p l₁ l₂) {B} {B'} br le s σ rl i ρ φ =
    ≃-trans (strictᵐ-≃ ≃-refl (≃-reflexive (frame-in (≤-trans (m≤n⊔m _ _) le))))
      (≃-trans (case-core {A} {λ X → B (lvl l₁) (s [ k ↦ X ]) ρ (isinlᵐ A)} {λ X → B (lvl l₂) (s [ k ↦ X ]) ρ (isinlᵐ A)}
                  (proj₁ (atm-atom leΔ i a)))
        (𝒞ᵐ-≃ {F = λ X → B (lvl l₁) (s [ k ↦ X ]) ρ (isinlᵐ A)} {λ X → B' l₁ (X • drop p σ)}
              {λ X → B (lvl l₂) (s [ k ↦ X ]) ρ (isinlᵐ A)} {λ X → B' l₂ (X • drop p σ)}
              (atm-≃ leΔ rl a)
              (λ V ne c nv → br l₁ _ _ (rel-↦ p rl) (inv-↦ i (atom-≈ ne c nv)) ρ _)
              (λ V ne c nv → br l₂ _ _ (rel-↦ p rl) (inv-↦ i (atom-≈ ne c nv)) ρ _)))
    where
    k = length Δ'
    leΔ = ≤-trans (depth-≥ (case a p l₁ l₂)) le
    A = X.𝒪 T n s ρ (select-atm a)

  blocks-≃ : ∀ {Σ Bs} (bs : Blocks Σ Bs) → blocks-depth bs ≤ n → BR (X.blocks T n (select-blocks bs)) (blocksᶜ bs T')
  blocks-≃ {Bs = _ ∷ Bs} (bs ▷ t) le Z s σ rl i ρ φ with length Bs ≟ length (select-blocks bs)
  ... | yes _ = tail t (blocks-≃ bs (≤-trans (m≤n⊔m _ _) le)) (≤-trans (m≤m⊔n _ _) le) s σ rl i ρ φ
  ... | no ne = ⊥-elim (ne (sym (len-blocks bs)))
  blocks-≃ (bs ▷ t) le (S l) s σ rl i ρ φ with lvl l ≟ length (select-blocks bs)
  ... | yes e = ⊥-elim (<⇒≢ (lvl-< l) (trans e (len-blocks bs)))
  ... | no _ = blocks-≃ bs (≤-trans (m≤n⊔m _ _) le) l s σ rl i ρ φ

{- the code of a definition: its start moves its arguments to slots 0 and 1 -}
code-≃ : ∀ {Σ} {T T' : Table} (TT : ∀ k → T k ≃ T' k) (TV : ∀ k → Atom (T k))
  → ∀ {m} (b : C.Body Σ (Any ∷ ⟪ tup m ⟫ ∷ [])) → X.code T (select-body prologue b) ≃ codeᶜʰ T' b
code-≃ {T = T} {T'} TT TV (C.body bs t) = ΛΛᵐ-≃ λ X Y →
  ≃-trans (≃-reflexive (frame-in (≤-trans (s≤s z≤n) (m≤m⊔n 2 L))))
    (letᵐ-≃ ≃-refl λ V neV cV nV → ≃-trans (≃-reflexive (frame-in (m≤m⊔n 2 L)))
      (letᵐ-≃ ≃-refl λ U neU cU nU →
        tail TT TV n t (blocks-≃ TT TV n bs le₁) le₂ _ _ (λ { Z → ≃-refl ; (S Z) → ≃-refl })
          (inv (atom-≈ neV cV nV) (atom-≈ neU cU nU)) _ _))
  where
  L = blocks-depth bs ⊔ depth t
  n = 2 ⊔ L
  le₁ = ≤-trans (m≤m⊔n (blocks-depth bs) (depth t)) (m≤n⊔m 2 L)
  le₂ = ≤-trans (m≤n⊔m (blocks-depth bs) (depth t)) (m≤n⊔m 2 L)
  inv : ∀ {X Y} → Atom X → Atom Y → Inv (zeros [ 0 ↦ X ] [ 1 ↦ Y ])
  inv aX aY 0 = aX
  inv aX aY 1 = aY
  inv aX aY (suc (suc y)) = ℬ-atom

{- Programs ------------------------------------------------------------------------------}

table-atom : ∀ (bs : List L.Body) k → Atom (X.table bs k)
table-atom [] k = ⟨ (λ { ⟨ () , _ ⟩ _ }) , ΛΛᵐ-val ⟩
table-atom (b ∷ bs) k with k ≟ length bs
... | yes _ = ⟨ (λ { ⟨ () , _ ⟩ _ }) , ΛΛᵐ-val ⟩
... | no _ = table-atom bs k

table-≃ : ∀ {Σ ns} (ds : All (λ n → C.Body Σ (Any ∷ ⟪ tup n ⟫ ∷ [])) ns) k
  → X.table (select-defs ds) k ≃ tbl (codeᶜʰ {Σ}) ds k
table-≃ [] k = ≃-refl
table-≃ {ns = _ ∷ ns} (d ∷ ds) k with k ≟ length (select-defs ds) | k ≟ length ns
... | yes _ | yes _ = code-≃ (table-≃ ds) (table-atom (select-defs ds)) d
... | no _ | no _ = table-≃ ds k
... | yes e | no ne = ⊥-elim (ne (trans e (len-defs ds)))
... | no ne | yes e = ⊥-elim (ne (trans e (sym (len-defs ds))))

select-check : ∀ (P : C.Program) → X.⟦ select P ⟧ₚ ≃ ⟦ P ⟧ᶜʰ
select-check (C.program ds (C.body bs t)) =
  tail (table-≃ ds) (table-atom (select-defs ds)) n t (blocks-≃ (table-≃ ds) (table-atom (select-defs ds)) n bs (m≤m⊔n _ _))
    (m≤n⊔m _ _) zeros (λ _ → init) (λ ()) (λ _ → ℬ-atom) (called (ℬ Int 0ℤ ptt)) init
  where n = blocks-depth bs ⊔ depth t

{-

  What the languages of FPC from GlobalFunμ on share in Scott domains:
  the tables of global definitions, as in the graph model
  (FPC/Semantics/GraphModel/Ops.agda), and the fixed frame of Impμ,
  CFGμ and X86μ.

  A table gives each definition of a program (Σ ∋ s) its meaning, a
  value. The definitions are given meaning newest first, each with the
  table of the older ones (tables, by the level of a reference); a
  reference to another means ⊥.

  A frame is an environment (Env), and slot x is its position idx x. A
  write to a slot updates that position in place (write i σ D, and
  writeᶜ i, continuous in the frame and the value). absAt i M is
  λ σ X. M (write i σ X), a meaning that runs after a write to position
  i, and lamAt i M is that function as a value. A definition starts in
  the frame that holds init everywhere but at the slots of its
  parameters, where its environment and then its argument are written
  (frame₂); its code is codeᶠ p N, for the parameters p and the body N.

-}

open import MLTT.Spartan using (𝓤₀; 𝓤₁; _̇; _＝_; refl; _,_; pr₁; pr₂)
open import UF.FunExt using (Fun-Ext)
open import UF.PropTrunc using (propositional-truncations-exist)
open import UF.Subsingletons using (propext)

open import FPC.Language.Type using (Type; _∋_; Z; S; lvl; idx)
open import FPC.Language.GlobalFun using (DSig)
open import Framework.Membership using (_⊑_; ⊑-∋)

open import Data.List using (List; []; _∷_; length)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Nat using (ℕ; _≟_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Empty using (⊥-elim)

module FPC.Semantics.ScottDomains.Ops
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : propext 𝓤₀)
       where

open import Framework.Scott.Base pt fe
open import Framework.Scott.Domain pt fe pe using (𝔻)
open import Framework.Scott.Ops pt fe pe using (⊥𝔻; Env; Λ)
open import Framework.Scott.Semantics pt fe pe using (Den; init; code₂)

Table : List DSig → 𝓤₁ ̇
Table Σ = ∀ {s} → Σ ∋ s → ⟨ 𝔻 ⟩

{- the table of the definitions ds (newest first), given the meaning of
   a definition with the table of the older ones -}
{- (a `with` here, in a recursive function whose type mentions 𝔻, makes
   Agda's termination check very slow) -}
choose : ∀ {P : Set} → Dec P → ⟨ 𝔻 ⟩ → ⟨ 𝔻 ⟩ → ⟨ 𝔻 ⟩
choose (yes _) d e = d
choose (no _) d e = e

tables : ∀ {Σ} {D : DSig → Set} → (Table Σ → ∀ {s} → D s → ⟨ 𝔻 ⟩) → ∀ {ss}
  → All D ss → Table Σ
tables cd [] f = ⊥𝔻
tables cd {_ ∷ ss} (d ∷ ds) f =
  choose (lvl f ≟ length ss) (cd (tables cd ds) d) (tables cd ds f)

{- the two cases of tables, as equations (proved here: reducing tables
   elsewhere is slow) -}
choose-yes : ∀ {P : Set} (q : Dec P) (d e : ⟨ 𝔻 ⟩) → P → choose q d e ＝ d
choose-yes (yes _) d e p = refl
choose-yes (no ¬p) d e p = ⊥-elim (¬p p)

choose-no : ∀ {P : Set} (q : Dec P) (d e : ⟨ 𝔻 ⟩)
  → ¬ P
  → choose q d e ＝ e
choose-no (yes p) d e ¬p = ⊥-elim (¬p p)
choose-no (no _) d e ¬p = refl

tables-yes : ∀ {Σ} {D : DSig → Set} (cd : Table Σ → ∀ {s} → D s → ⟨ 𝔻 ⟩) {s ss}
  (d : D s) (ds : All D ss) {t} (f : Σ ∋ t)
  → lvl f ≡ length ss
  → tables cd (d ∷ ds) f ＝ cd (tables cd ds) d
tables-yes cd {ss = ss} d ds f e =
  choose-yes (lvl f ≟ length ss) (cd (tables cd ds) d) (tables cd ds f) e

tables-no : ∀ {Σ} {D : DSig → Set} (cd : Table Σ → ∀ {s} → D s → ⟨ 𝔻 ⟩) {s ss}
  (d : D s) (ds : All D ss) {t} (f : Σ ∋ t)
  → ¬ (lvl f ≡ length ss)
  → tables cd (d ∷ ds) f ＝ tables cd ds f
tables-no cd {ss = ss} d ds f ne =
  choose-no (lvl f ≟ length ss) (cd (tables cd ds) d) (tables cd ds f) ne

{- Frames ---------------------------------------------------------------------}

{- the frame σ with position i set to D -}
write : ℕ → ⟨ Env ⟩ → ⟨ 𝔻 ⟩ → ⟨ Env ⟩
write i σ D j = choose (i ≟ j) D (σ j)

writeᶜ : ℕ → DCPO[ Env ×₁ 𝔻 , Env ]
writeᶜ i = f , to-Pow-continuous ℕ 𝔻 (Env ×₁ 𝔻) f (λ j → c j (i ≟ j))
 where
  f : ⟨ Env ×₁ 𝔻 ⟩ → ℕ → ⟨ 𝔻 ⟩
  f p = write i (pr₁ p) (pr₂ p)
  c : (j : ℕ) (q : Dec (i ≡ j))
    → is-continuous (Env ×₁ 𝔻) 𝔻 (λ p → choose q (pr₂ p) (pr₁ p j))
  c j (yes _) = pr₂ (snd₁ Env 𝔻)
  c j (no _) = pr₂ (∘₁ (Env ×₁ 𝔻) Env 𝔻 (fst₁ Env 𝔻) (at ℕ 𝔻 j))

{- the position that is written, and the others -}
write-same : (i : ℕ) (σ : ⟨ Env ⟩) (D : ⟨ 𝔻 ⟩) → write i σ D i ＝ D
write-same i σ D = choose-yes (i ≟ i) D (σ i) _≡_.refl

write-other : (i j : ℕ) (σ : ⟨ Env ⟩) (D : ⟨ 𝔻 ⟩)
  → ¬ (i ≡ j)
  → write i σ D j ＝ σ j
write-other i j σ D ne = choose-no (i ≟ j) D (σ j) ne

{- λ σ X. M (write i σ X), and that function as a value -}
absAt : ℕ → Den Env → DCPO[ Env , 𝔻 ⟹₁ 𝔻 ]
absAt i M = curry₁ Env 𝔻 𝔻 (∘₁ (Env ×₁ 𝔻) Env 𝔻 (writeᶜ i) M)

lamAt : ℕ → Den Env → Den Env
lamAt i M = ∘₁ Env (𝔻 ⟹₁ 𝔻) 𝔻 (absAt i M) Λ

{- the frame at the start of a definition whose environment X and
   argument Y are at positions e and a: init everywhere, then X written
   to e, then Y to a -}
frame₂ : ℕ → ℕ → ⟨ 𝔻 ⟩ → ⟨ 𝔻 ⟩ → ⟨ Env ⟩
frame₂ e a X Y = write a (write e (λ _ → init) X) Y

frame₂ᶜ : ℕ → ℕ → DCPO[ 𝔻 ×₁ 𝔻 , Env ]
frame₂ᶜ e a =
  ∘₁ (𝔻 ×₁ 𝔻) (Env ×₁ 𝔻) Env
    (pair₁ (𝔻 ×₁ 𝔻) Env 𝔻
       (∘₁ (𝔻 ×₁ 𝔻) (Env ×₁ 𝔻) Env
          (pair₁ (𝔻 ×₁ 𝔻) Env 𝔻 (const₁ (𝔻 ×₁ 𝔻) Env (λ _ → init))
             (fst₁ 𝔻 𝔻))
          (writeᶜ e))
       (snd₁ 𝔻 𝔻))
    (writeᶜ a)

{- the code of a definition whose parameters are at p (the argument at
   ⊑-∋ p Z and the environment at ⊑-∋ p (S Z)) and whose body means N -}
codeᶠ : ∀ {A B : Type} {Δ} → (A ∷ B ∷ []) ⊑ Δ → Den Env → ⟨ 𝔻 ⟩
codeᶠ p N =
  code₂ (∘₁ (𝔻 ×₁ 𝔻) Env 𝔻 (frame₂ᶜ (idx (⊑-∋ p (S Z))) (idx (⊑-∋ p Z))) N)

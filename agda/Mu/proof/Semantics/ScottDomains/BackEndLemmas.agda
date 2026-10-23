{-

  Scott domains: lemmas for the proofs of the passes of ISWIMμ from
  globalize on (globalize, remove complex operands, lift locals,
  explicate control, select instructions,
  Mu/proof/Correctness/ScottDomains/{Globalize,RCO,LiftLocals,Explicate,Select}Correct.agda).

  * seq: seq ⊥ e is ⊥, seq d d is d, and seq d (seq d e) is seq d e;
    d ⊑ e when d = e provided d is defined (below-if);
  * a strict continuous map commutes with taking a value apart
    (case-natural₂), so with a case (cases-strict-natural): the
    continuation of a case can go into its branches;
  * the code of a closure is determined by its body on defined
    arguments (code₂-cong, codeᶜ-cong);
  * the tables of two programs agree when their newest definitions and
    the tables of the older ones do (tables-cons).

-}

open import MLTT.Spartan hiding (inl; inr; cases)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons
open import UF.Base using (ap₂; happly)

open import Mu.Language.Type using (_∋_; lvl)
open import Mu.Language.GlobalFun using (DSig)
open import Data.List using (List; []; _∷_; length)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Nat using (_≟_)
open import Relation.Nullary using (Dec; yes; no)
open import Data.Fin using (zero; suc)
import Mu.Language.Imp as I
open import Mu.Framework.AllUtil using (pos)

module Mu.proof.Semantics.ScottDomains.BackEndLemmas
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : propext 𝓤₀)
       where

open import Framework.Scott.Base pt fe
open import Framework.Scott.Lift pt fe pe
open import Framework.Scott.Functor pt fe pe
open import proof.Framework.Scott.Ops pt fe pe
open import proof.Framework.Scott.Semantics pt fe pe
open import Mu.Semantics.ScottDomains.Ops pt fe pe
open import Semantics.Scott.Prim pt fe pe using (primD)
{- (re-exported: a proof that uses 𝒮-＝ on a given simple expression
   should take 𝒜 and 𝒮 from here, so that Agda compares them by name) -}
open import Mu.Semantics.ScottDomains.Imp pt fe pe using (𝒜; 𝒜s; 𝒮) public

private
 V : DCPO₁
 V = obj Val 𝔻

{- seq ---------------------------------------------------------------------------}

seq-⊥ : (e : ⟨ 𝔻 ⟩) → seq · ⊥𝔻 · e ＝ ⊥𝔻
seq-⊥ e = antisymmetry 𝔻 (seq · ⊥𝔻 · e) ⊥𝔻
  (∐ˢˢ-is-lowerbound-of-upperbounds 𝔻⊥ (λ _ → e) (defined-is-prop ⊥𝔻) ⊥𝔻 (λ p → 𝟘-elim (⊥-undefined p)))
  (⊥-is-least 𝔻⊥ (seq · ⊥𝔻 · e))

private
 value-tr : (d e : ⟨ 𝔻 ⟩) (q : d ＝ e) (p : defined d)
   → value (unroll · d) p ⊑⟨ V ⟩ value (unroll · e) (transport defined q p)
 value-tr d .d refl p = reflexivity V (value (unroll · d) p)

below-if : (d e : ⟨ 𝔻 ⟩) → (defined d → d ＝ e) → d ⊑⟨ 𝔻 ⟩ e
below-if d e h = transport (λ - → d ⊑⟨ 𝔻 ⟩ -) (roll-unroll e)
  (below-roll d (unroll · e) ((λ p → transport defined (h p) p) , (λ p → value-tr d e (h p) p)))

seq-self : (d : ⟨ 𝔻 ⟩) → seq · d · d ＝ d
seq-self d = antisymmetry 𝔻 (seq · d · d) d
  (∐ˢˢ-is-lowerbound-of-upperbounds 𝔻⊥ (λ _ → d) (defined-is-prop d) d (λ _ → reflexivity 𝔻 d))
  (below-if d (seq · d · d) (λ p → seq-defined d d p ⁻¹))

seq-seq : (d e : ⟨ 𝔻 ⟩) → seq · d · (seq · d · e) ＝ seq · d · e
seq-seq d e = seq-cong d (seq · d · e) e (λ p → seq-defined d e p)

{- strict maps and cases -------------------------------------------------------------}

{- a strict map κ commutes with a case into functions, applied, given
   what it does to each branch (stated, as cases-defined in
   proof/Framework/Scott/Values.agda, for case (A ⟹𝔻) h · d · a, so that
   an instance for cases is checked quickly) -}
opaque
 unfolding case

 case-natural₂ : (A : DCPO₁) (h h' : (t : Tag) → DCPO[ obj (Payload t) 𝔻 , A ⟹₁ 𝔻 ]) (a a' : ⟨ A ⟩)
   (κ : DCPO[ 𝔻 , 𝔻 ]) → κ · ⊥𝔻 ＝ ⊥𝔻
   → ((t : Tag) (x : ⟨ obj (Payload t) 𝔻 ⟩) → κ · (h t · x · a) ＝ h' t · x · a')
   → (d : ⟨ 𝔻 ⟩) → κ · (case (A ⟹𝔻) h · d · a) ＝ case (A ⟹𝔻) h' · d · a'
 case-natural₂ A h h' a a' κ s e d =
  ap (κ ·_) (∐ˢˢ-＝-if-continuous-and-strict (A ⟹𝔻) 𝔻⊥ (λ g → g · a) (pr₂ (at-point₁ A 𝔻 a)) refl α ρ)
  ∙ ∐ˢˢ-＝-if-continuous-and-strict 𝔻⊥ 𝔻⊥ (pr₁ κ) (pr₂ κ) s (λ q → α q · a) ρ
  ∙ ∐ˢˢ-family-＝ 𝔻⊥ {_} {λ q → κ · (α q · a)} {λ q → α' q · a'} ρ (dfunext fe λ q → e (pr₁ (v q)) (pr₂ (v q)))
  ∙ (∐ˢˢ-＝-if-continuous-and-strict (A ⟹𝔻) 𝔻⊥ (λ g → g · a') (pr₂ (at-point₁ A 𝔻 a')) refl α' ρ) ⁻¹
  where
   ρ : is-prop (defined d)
   ρ = defined-is-prop d
   v : defined d → ⟨ obj Val 𝔻 ⟩
   v q = value (unroll · d) q
   α α' : defined d → DCPO[ A , 𝔻 ]
   α q = h (pr₁ (v q)) · pr₂ (v q)
   α' q = h' (pr₁ (v q)) · pr₂ (v q)

{- a strict continuation goes into the (strict) branches of a case -}
module _ (κ : DCPO[ 𝔻 , 𝔻 ]) (s : κ · ⊥𝔻 ＝ ⊥𝔻) (f g f' g' : DCPO[ 𝔻 , 𝔻 ])
         (hf : (X : ⟨ 𝔻 ⟩) → κ · (f · X) ＝ f' · X) (hg : (X : ⟨ 𝔻 ⟩) → κ · (g · X) ＝ g' · X) where
  private
   fg fg' : ⟨ Br ⟩
   fg = strict · f , strict · g
   fg' = strict · f' , strict · g'
   e : (t : Tag) (x : ⟨ obj (Payload t) 𝔻 ⟩) → κ · (cases-br t · x · fg) ＝ cases-br t · x · fg'
   e (con B c) x = s
   e (tup n) x = s
   e left x = seq-strict κ s x (f · x) ∙ ap (seq · x ·_) (hf x)
   e right x = seq-strict κ s x (g · x) ∙ ap (seq · x ·_) (hg x)
   e fun x = s
   e pr x = s

  cases-strict-natural : (d : ⟨ 𝔻 ⟩)
    → κ · (cases · d · (strict · f , strict · g)) ＝ cases · d · (strict · f' , strict · g')
  cases-strict-natural = case-natural₂ Br cases-br cases-br fg fg' κ s e

{- code ---------------------------------------------------------------------------------}

code₂-cong : (B B' : DCPO[ 𝔻 ×₁ 𝔻 , 𝔻 ])
  → ((X Y : ⟨ 𝔻 ⟩) → defined X → defined Y → B · (X , Y) ＝ B' · (X , Y)) → code₂ B ＝ code₂ B'
code₂-cong B B' h =
 Λ-cong (∘₁ 𝔻 (𝔻 ⟹₁ 𝔻) 𝔻 (curry₁ 𝔻 𝔻 𝔻 B) Λ) (∘₁ 𝔻 (𝔻 ⟹₁ 𝔻) 𝔻 (curry₁ 𝔻 𝔻 𝔻 B') Λ)
   (λ X p → Λ-cong (curry₁ 𝔻 𝔻 𝔻 B · X) (curry₁ 𝔻 𝔻 𝔻 B' · X) (λ Y q → h X Y p q))

codeᶜ-cong : (N N' : Den Env)
  → ((X Y : ⟨ 𝔻 ⟩) → defined X → defined Y → N · env₂ X Y ＝ N' · env₂ X Y) → codeᶜ N ＝ codeᶜ N'
codeᶜ-cong N N' = code₂-cong (∘₁ (𝔻 ×₁ 𝔻) Env 𝔻 env₂ᶜ N) (∘₁ (𝔻 ×₁ 𝔻) Env 𝔻 env₂ᶜ N')

{- tables ------------------------------------------------------------------------------}

private
 choose-cong : ∀ {P : Set} (q : Dec P) (a b a' b' : ⟨ 𝔻 ⟩) → a ＝ a' → b ＝ b' → choose q a b ＝ choose q a' b'
 choose-cong (yes _) a b a' b' e₁ e₂ = e₁
 choose-cong (no _) a b a' b' e₁ e₂ = e₂

tables-cons : ∀ {Σ} {D D' : DSig → Set} (cd : Table Σ → ∀ {s} → D s → ⟨ 𝔻 ⟩) (cd' : Table Σ → ∀ {s} → D' s → ⟨ 𝔻 ⟩)
  {s₀ ss} (d : D s₀) (ds : All D ss) (d' : D' s₀) (ds' : All D' ss) {s} (f : Σ ∋ s)
  → cd (tables cd ds) d ＝ cd' (tables cd' ds') d' → tables cd ds f ＝ tables cd' ds' f
  → tables cd (d ∷ ds) f ＝ tables cd' (d' ∷ ds') f
tables-cons cd cd' {ss = ss} d ds d' ds' f =
  choose-cong (lvl f ≟ length ss) (cd (tables cd ds) d) (tables cd ds f) (cd' (tables cd' ds') d') (tables cd' ds' f)

{- atoms and simple expressions (of Impμ, CFGμ), for tables that agree -}
module _ {Σ} {T T' : Table Σ} (TT : ∀ {s} (f : Σ ∋ s) → T f ＝ T' f) where

  𝒜-＝ : ∀ {Δ A} (a : I.Atm Σ Δ A) σ → 𝒜 a T · σ ＝ 𝒜 a T' · σ
  𝒜-＝ (I.var x) σ = refl
  𝒜-＝ (I.lit B c) σ = refl
  𝒜-＝ (I.ref f) σ = TT f

  𝒜s-＝ : ∀ {Δ Δs} (as : All (I.Atm Σ Δ) Δs) σ → 𝒜s as T · σ ＝ 𝒜s as T' · σ
  𝒜s-＝ [] σ = refl
  𝒜s-＝ (a ∷ as) σ = dfunext fe λ { zero → 𝒜-＝ a σ ; (suc i) → happly (𝒜s-＝ as σ) i }

  𝒮-＝ : ∀ {Δ A} (s : I.Simple Σ Δ A) σ → 𝒮 s T · σ ＝ 𝒮 s T' · σ
  𝒮-＝ (I.atm a) σ = 𝒜-＝ a σ
  𝒮-＝ (I.pack a b) σ = ap₂ (λ x y → pair · x · y) (𝒜-＝ a σ) (𝒜-＝ b σ)
  𝒮-＝ (I.callc a b) σ = ap₂ (λ x y → app · (app · (car · x) · (cdr · x)) · y) (𝒜-＝ a σ) (𝒜-＝ b σ)
  𝒮-＝ (I.tuple {Δs} as) σ = ap (tuple (length Δs) ·_) (𝒜s-＝ as σ)
  𝒮-＝ (I.get i a) σ = ap (proj (pos i) ·_) (𝒜-＝ a σ)
  𝒮-＝ (I.inl a) σ = ap (inl ·_) (𝒜-＝ a σ)
  𝒮-＝ (I.inr a) σ = ap (inr ·_) (𝒜-＝ a σ)
  𝒮-＝ (I.prim p a b) σ = ap₂ (λ x y → primD p · x · y) (𝒜-＝ a σ) (𝒜-＝ b σ)
  𝒮-＝ (I.fold a) σ = 𝒜-＝ a σ
  𝒮-＝ (I.unfold a) σ = 𝒜-＝ a σ

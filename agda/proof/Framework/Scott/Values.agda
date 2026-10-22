{-

  Scott domains: more about values. A defined value is inj t x for the
  tag t and payload x of its unrolling (inj-view); taking a value apart
  gives a defined result only if the value is defined (case-defined,
  for the operators app, proj, cases and the primitives).

-}

open import MLTT.Spartan hiding (inl; inr; cases)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons

open import Data.Fin using (Fin)
open import Framework.Primitives using (Int)
open import Language.Prim using (Prim)

module proof.Framework.Scott.Values
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : propext 𝓤₀)
       where

open import Framework.Scott.Base pt fe
open import Framework.Scott.Lift pt fe pe
open import Framework.Scott.Functor pt fe pe
open import proof.Framework.Scott.Ops pt fe pe
open import Semantics.Scott.Prim pt fe pe using (primD; prim-br₁; prim-br₂)
open import Lifting.Miscelanea-PropExt-FunExt 𝓤₀ pe fe using (is-defined-η-＝; not-defined-⊥-＝)

{- the tag and payload of a defined value -}
view : (d : ⟨ 𝔻 ⟩) → defined d → ⟨ obj Val 𝔻 ⟩
view d q = value (unroll · d) q

inj-view : (d : ⟨ 𝔻 ⟩) (q : defined d) → d ＝ inj (pr₁ (view d q)) · pr₂ (view d q)
inj-view d q = roll-unroll d ⁻¹ ∙ ap (roll ·_) (is-defined-η-＝ q)

unroll-inj : (t : Tag) (x : ⟨ obj (Payload t) 𝔻 ⟩) → unroll · (inj t · x) ＝ η (t , x)
unroll-inj t x = unroll-roll (η (t , x))

{- the view of inj t x is (t , x) -}
view-inj : (t : Tag) (x : ⟨ obj (Payload t) 𝔻 ⟩) (q : defined (inj t · x)) → view (inj t · x) q ＝ (t , x)
view-inj t x q = lemma (unroll · (inj t · x)) (unroll-inj t x) q
 where
  lemma : (l : ⟨ 𝓛ᵈ (obj Val 𝔻) ⟩) → l ＝ η (t , x) → (q : is-defined l) → value l q ＝ (t , x)
  lemma .(η (t , x)) refl q = refl

{- A case into 𝔻 is defined only if the scrutinee is -}

case-defined : (h : (t : Tag) → DCPO[ obj (Payload t) 𝔻 , 𝔻 ]) (d : ⟨ 𝔻 ⟩) → defined (case 𝔻⊥ h · d) → defined d
case-defined h d = ∐ˢˢ-defined (λ q → h (pr₁ (view d q)) · pr₂ (view d q)) (defined-is-prop d)

{- and so is a case into functions, applied -}
case-defined₂ : (A : DCPO₁) (h : (t : Tag) → DCPO[ obj (Payload t) 𝔻 , A ⟹₁ 𝔻 ]) (d : ⟨ 𝔻 ⟩) (a : ⟨ A ⟩)
  → defined (case (A ⟹𝔻) h · d · a) → defined d
case-defined₂ A h d a p =
 ∐ˢˢ-defined (λ q → h (pr₁ (view d q)) · pr₂ (view d q) · a) (defined-is-prop d)
   (transport defined (∐ˢˢ-＝-if-continuous-and-strict (A ⟹𝔻) 𝔻⊥ (λ g → g · a) (pr₂ (at-point₁ A 𝔻 a)) refl
                         (λ q → h (pr₁ (view d q)) · pr₂ (view d q)) (defined-is-prop d)) p)

app-defined : (f a : ⟨ 𝔻 ⟩) → defined (app · f · a) → defined f
app-defined = case-defined₂ 𝔻 app-br

proj-defined : {n : ℕ} (i : Fin n) (d : ⟨ 𝔻 ⟩) → defined (proj i · d) → defined d
proj-defined i = case-defined (proj-br i)

component-defined : (i : Fin 2) (d : ⟨ 𝔻 ⟩) → defined (component i · d) → defined d
component-defined i = case-defined (component-br i)

cases-defined : (d : ⟨ 𝔻 ⟩) (b : ⟨ Br ⟩) → defined (cases · d · b) → defined d
cases-defined = case-defined₂ Br cases-br

primD-defined₁ : (p : Prim) (d e : ⟨ 𝔻 ⟩) → defined (primD p · d · e) → defined d
primD-defined₁ p = case-defined₂ 𝔻 (prim-br₁ p)

{- a value that is not defined is ⊥ -}
undefined-⊥ : (d : ⟨ 𝔻 ⟩) → ¬ defined d → d ＝ ⊥𝔻
undefined-⊥ d nd = roll-unroll d ⁻¹
                   ∙ ap (roll ·_) (not-defined-⊥-＝ nd ∙ not-defined-⊥-＝ ⊥-undefined ⁻¹)
                   ∙ roll-unroll ⊥𝔻

{- application is strict in its argument -}
app-arg-⊥ : (c : ⟨ 𝔻 ⟩) → app · c · ⊥𝔻 ＝ ⊥𝔻
app-arg-⊥ c = undefined-⊥ (app · c · ⊥𝔻) λ p →
  aux (pr₁ (view c (app-defined c ⊥𝔻 p))) (pr₂ (view c (app-defined c ⊥𝔻 p)))
    (transport (λ - → defined (app · - · ⊥𝔻)) (inj-view c (app-defined c ⊥𝔻 p)) p)
 where
  aux : (t : Tag) (x : ⟨ obj (Payload t) 𝔻 ⟩) → defined (app · (inj t · x) · ⊥𝔻) → 𝟘
  aux fun x q = ⊥-undefined (seq-defined-l ⊥𝔻 (x · ⊥𝔻) (transport defined (ap (_· ⊥𝔻) (case-inj (𝔻 ⟹𝔻) app-br fun x)) q))
  aux (con B k) x q = ⊥-undefined (transport defined (ap (_· ⊥𝔻) (case-inj (𝔻 ⟹𝔻) app-br (con B k) x)) q)
  aux (tup n) x q = ⊥-undefined (transport defined (ap (_· ⊥𝔻) (case-inj (𝔻 ⟹𝔻) app-br (tup n) x)) q)
  aux left x q = ⊥-undefined (transport defined (ap (_· ⊥𝔻) (case-inj (𝔻 ⟹𝔻) app-br left x)) q)
  aux right x q = ⊥-undefined (transport defined (ap (_· ⊥𝔻) (case-inj (𝔻 ⟹𝔻) app-br right x)) q)
  aux pr x q = ⊥-undefined (transport defined (ap (_· ⊥𝔻) (case-inj (𝔻 ⟹𝔻) app-br pr x)) q)

app-seq-arg : (c d e : ⟨ 𝔻 ⟩) → app · c · (seq · d · e) ＝ seq · d · (app · c · e)
app-seq-arg c d e = seq-strict (app · c) (app-arg-⊥ c) d e

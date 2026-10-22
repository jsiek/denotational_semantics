{-

  Scott domains: lemmas about the operators.

  * seq d e is e when d is defined, and depends on e only when d is
    defined; so strict functions, and function values Λ g, are equal
    when they agree on defined values; seq d e is defined only if d and e
    are; a strict continuous map commutes with seq d;
  * taking apart a value made with a tag (case-inj), and the
    computation rules of the operators that follow: application of a
    function value, case of an injection, a component of a tuple or a
    pair, a primitive on integers;
  * which values are defined: ⊥ is not; a constant, a function value,
    an injection, a tuple and a pair (of defined values) are; guard n ds
    e is e when the ds are all defined, and defined only if they are.

-}

open import MLTT.Spartan hiding (inl; inr; cases)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons
open import UF.Subsingletons-FunExt

open import Data.Fin using (Fin; zero; suc)
import Data.Nat as Nat
import Data.Empty
open import Relation.Nullary using (Dec; yes; no)
import Relation.Binary.PropositionalEquality as Eq

open import Framework.Primitives using (Int)
open import Language.Prim using (Prim; δ)

module proof.Framework.Scott.Ops
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : propext 𝓤₀)
       where

open import Framework.Scott.Base pt fe
open import Framework.Scott.Lift pt fe pe
open import Framework.Scott.Sum pt fe
open import Framework.Scott.Functor pt fe pe
open import proof.Framework.Scott.Domain pt fe pe public
open import Framework.Scott.Ops pt fe pe public
open import Semantics.Scott.Prim pt fe pe using (primD; out; prim-br₁; prim-br₂)

private
 V : DCPO₁
 V = obj Val 𝔻

 L : DCPO₁
 L = 𝓛ᵈ V

 ⊥L : ⟨ L ⟩
 ⊥L = ⊥ (𝓛ᵈ⊥ V)

{- The order --------------------------------------------------------------------}

unroll-mono : (d e : ⟨ 𝔻 ⟩) → d ⊑⟨ 𝔻 ⟩ e → unroll · d ⊑⟨ L ⟩ unroll · e
unroll-mono = monotone-if-continuous 𝔻 L unroll

below-roll : (d : ⟨ 𝔻 ⟩) (l : ⟨ L ⟩) → unroll · d ⊑⟨ L ⟩ l → d ⊑⟨ 𝔻 ⟩ roll · l
below-roll d l u = transport (λ - → - ⊑⟨ 𝔻 ⟩ roll · l) (roll-unroll d)
                     (monotone-if-continuous L 𝔻 roll (unroll · d) l u)

{- definedness goes up -}
defined-mono : (d e : ⟨ 𝔻 ⟩) → d ⊑⟨ 𝔻 ⟩ e → defined d → defined e
defined-mono d e u = pr₁ (unroll-mono d e u)

defined-is-prop : (d : ⟨ 𝔻 ⟩) → is-prop (defined d)
defined-is-prop d = being-defined-is-prop (unroll · d)

⊥-undefined : ¬ defined ⊥𝔻
⊥-undefined p = transport is-defined (unroll-roll ⊥L) (defined-mono ⊥𝔻 (roll · ⊥L) (⊥-is-least 𝔻⊥ _) p)

{- a subsingleton sup is defined only if its index is inhabited -}
∐ˢˢ-defined : {I : 𝓤₀ ̇ } (α : I → ⟨ 𝔻 ⟩) (ρ : is-prop I) → defined (∐ˢˢ 𝔻⊥ α ρ) → I
∐ˢˢ-defined {I} α ρ p = pr₁ (transport is-defined (unroll-roll l) (defined-mono _ (roll · l) below p))
 where
  l : ⟨ L ⟩
  l = (Σ i ꞉ I , defined (α i))
    , (λ q → value (unroll · α (pr₁ q)) (pr₂ q))
    , Σ-is-prop ρ (λ i → defined-is-prop (α i))
  below : ∐ˢˢ 𝔻⊥ α ρ ⊑⟨ 𝔻 ⟩ roll · l
  below = ∐ˢˢ-is-lowerbound-of-upperbounds 𝔻⊥ α ρ (roll · l)
            (λ i → below-roll (α i) l ((λ p → i , p) , (λ p → reflexivity V _)))

{- seq --------------------------------------------------------------------------}

seq-defined : (d e : ⟨ 𝔻 ⟩) → defined d → seq · d · e ＝ e
seq-defined d e p = ∐ˢˢ-＝-if-domain-holds 𝔻⊥ (being-defined-is-prop (unroll · d)) p

seq-cong : (d e e' : ⟨ 𝔻 ⟩) → (defined d → e ＝ e') → seq · d · e ＝ seq · d · e'
seq-cong d e e' h = antisymmetry 𝔻 (guarded d e) (guarded d e') (below e e' h) (below e' e (λ p → h p ⁻¹))
 where
  ρ = being-defined-is-prop (unroll · d)
  below : (x y : ⟨ 𝔻 ⟩) → (defined d → x ＝ y) → guarded d x ⊑⟨ 𝔻 ⟩ guarded d y
  below x y k = ∐ˢˢ-is-lowerbound-of-upperbounds 𝔻⊥ (λ _ → x) ρ (guarded d y)
                  (λ p → transport (λ - → - ⊑⟨ 𝔻 ⟩ guarded d y) (k p ⁻¹)
                           (∐ˢˢ-is-upperbound 𝔻⊥ (λ _ → y) ρ p))

seq-defined-l : (d e : ⟨ 𝔻 ⟩) → defined (seq · d · e) → defined d
seq-defined-l d e = ∐ˢˢ-defined (λ _ → e) (defined-is-prop d)

seq-defined-r : (d e : ⟨ 𝔻 ⟩) → defined (seq · d · e) → defined e
seq-defined-r d e p = transport defined (seq-defined d e (seq-defined-l d e p)) p

seq-idem : (d e : ⟨ 𝔻 ⟩) → seq · d · (seq · d · e) ＝ seq · d · e
seq-idem d e = seq-cong d (seq · d · e) e (seq-defined d e)

{- a strict continuous map commutes with seq d -}
seq-strict : (f : DCPO[ 𝔻 , 𝔻 ]) → f · ⊥𝔻 ＝ ⊥𝔻 → (d e : ⟨ 𝔻 ⟩) → f · (seq · d · e) ＝ seq · d · (f · e)
seq-strict f s d e = ∐ˢˢ-＝-if-continuous-and-strict 𝔻⊥ 𝔻⊥ (pr₁ f) (pr₂ f) s (λ _ → e) (defined-is-prop d)

{- Taking values apart -------------------------------------------------------------}

case-inj : (E : DCPO⊥ {𝓤₁} {𝓤₁}) (h : (t : Tag) → DCPO[ obj (Payload t) 𝔻 , E ⁻ ]) (t : Tag) (x : ⟨ obj (Payload t) 𝔻 ⟩)
  → case E h · (inj t · x) ＝ h t · x
case-inj E h t x = ap (extend V E (copair Tag Tag-is-set (λ t → obj (Payload t) 𝔻) (E ⁻) h) ·_) (unroll-roll (η (t , x)))
                   ∙ extend-η V E (copair Tag Tag-is-set (λ t → obj (Payload t) 𝔻) (E ⁻) h) (t , x)

case-⊥ : (E : DCPO⊥ {𝓤₁} {𝓤₁}) (h : (t : Tag) → DCPO[ obj (Payload t) 𝔻 , E ⁻ ]) → case E h · ⊥𝔻 ＝ ⊥ E
case-⊥ E h = antisymmetry (E ⁻) _ _ below (⊥-is-least E _)
 where
  k = extend V E (copair Tag Tag-is-set (λ t → obj (Payload t) 𝔻) (E ⁻) h)
  below : case E h · ⊥𝔻 ⊑⟨ E ⁻ ⟩ ⊥ E
  below = transport (λ - → case E h · ⊥𝔻 ⊑⟨ E ⁻ ⟩ -) (extend-⊥ V E (copair Tag Tag-is-set (λ t → obj (Payload t) 𝔻) (E ⁻) h))
            (transport (λ - → case E h · ⊥𝔻 ⊑⟨ E ⁻ ⟩ k · -) (unroll-roll ⊥L)
              (monotone-if-continuous 𝔻 (E ⁻) (case E h) ⊥𝔻 (roll · ⊥L) (⊥-is-least 𝔻⊥ _)))

{- Functions -------------------------------------------------------------------------}

app-Λ : (g : DCPO[ 𝔻 , 𝔻 ]) (d : ⟨ 𝔻 ⟩) → app · (Λ · g) · d ＝ seq · d · (g · d)
app-Λ g d = ap (_· d) (case-inj (𝔻 ⟹𝔻) app-br fun (strict · g)) ∙ seq-idem d (g · d)

app-Λ-defined : (g : DCPO[ 𝔻 , 𝔻 ]) (d : ⟨ 𝔻 ⟩) → defined d → app · (Λ · g) · d ＝ g · d
app-Λ-defined g d p = app-Λ g d ∙ seq-defined d (g · d) p

app-⊥ : (d : ⟨ 𝔻 ⟩) → app · ⊥𝔻 · d ＝ ⊥𝔻
app-⊥ d = ap (_· d) (case-⊥ (𝔻 ⟹𝔻) app-br)

{- application, at an argument, as a continuous map of the function -}
app-at : ⟨ 𝔻 ⟩ → DCPO[ 𝔻 , 𝔻 ]
app-at d = ∘₁ 𝔻 (𝔻 ⟹₁ 𝔻) 𝔻 app (at-point₁ 𝔻 𝔻 d)

app-seq : (d v y : ⟨ 𝔻 ⟩) → app · (seq · d · v) · y ＝ seq · d · (app · v · y)
app-seq d v y = seq-strict (app-at y) (app-⊥ y) d v

{- Definedness -----------------------------------------------------------------------}

Λ-defined : (g : DCPO[ 𝔻 , 𝔻 ]) → defined (Λ · g)
Λ-defined g = defined-inj fun (strict · g)

const-defined : (B : _) (k : _) → defined (const B k)
const-defined B k = defined-inj (con B k) ⋆

guard-defined : (n : ℕ) (ds : Fin n → ⟨ 𝔻 ⟩) → ((i : Fin n) → defined (ds i))
  → (e : ⟨ 𝔻 ⟩) → guard n · ds · e ＝ e
guard-defined zero ds h e = refl
guard-defined (succ n) ds h e =
 seq-defined (ds zero) _ (h zero) ∙ guard-defined n (λ i → ds (suc i)) (λ i → h (suc i)) e

guard-defined← : (n : ℕ) (ds : Fin n → ⟨ 𝔻 ⟩) (e : ⟨ 𝔻 ⟩) → defined (guard n · ds · e) → (i : Fin n) → defined (ds i)
guard-defined← (succ n) ds e p zero = seq-defined-l (ds zero) _ p
guard-defined← (succ n) ds e p (suc i) = guard-defined← n (λ i → ds (suc i)) e (seq-defined-r (ds zero) _ p) i

guard-defined-r : (n : ℕ) (ds : Fin n → ⟨ 𝔻 ⟩) (e : ⟨ 𝔻 ⟩) → defined (guard n · ds · e) → defined e
guard-defined-r n ds e p = transport defined (guard-defined n ds (guard-defined← n ds e p) e) p

{- guard n ds e depends on e only when the ds are all defined -}
guard-cong : (n : ℕ) (ds : Fin n → ⟨ 𝔻 ⟩) (e e' : ⟨ 𝔻 ⟩) → (((i : Fin n) → defined (ds i)) → e ＝ e')
  → guard n · ds · e ＝ guard n · ds · e'
guard-cong zero ds e e' h = h (λ ())
guard-cong (succ n) ds e e' h =
 seq-cong (ds zero) _ _ (λ p → guard-cong n (λ i → ds (suc i)) e e'
   (λ hs → h (λ { zero → p ; (suc i) → hs i })))

tuple-is : (n : ℕ) (ds : Fin n → ⟨ 𝔻 ⟩) → tuple n · ds ＝ guard n · ds · (inj (tup n) · ds)
tuple-is n ds = refl

tuple-defined : (n : ℕ) (ds : Fin n → ⟨ 𝔻 ⟩) → ((i : Fin n) → defined (ds i)) → defined (tuple n · ds)
tuple-defined n ds h = transport defined (guard-defined n ds h (inj (tup n) · ds) ⁻¹) (defined-inj (tup n) ds)

tuple-defined← : (n : ℕ) (ds : Fin n → ⟨ 𝔻 ⟩) → defined (tuple n · ds) → (i : Fin n) → defined (ds i)
tuple-defined← n ds = guard-defined← n ds (inj (tup n) · ds)

unit-defined : defined unit
unit-defined = defined-inj (tup 0) (λ ())

inl-defined : (d : ⟨ 𝔻 ⟩) → defined d → defined (inl · d)
inl-defined d p = transport defined (seq-defined d (inj left · d) p ⁻¹) (defined-inj left d)

inr-defined : (d : ⟨ 𝔻 ⟩) → defined d → defined (inr · d)
inr-defined d p = transport defined (seq-defined d (inj right · d) p ⁻¹) (defined-inj right d)

pair-defined : (a b : ⟨ 𝔻 ⟩) → defined a → defined b → defined (pair · a · b)
pair-defined a b p q = transport defined (guard-defined 2 (pick₂ a b) (λ { zero → p ; (suc zero) → q }) (inj pr · pick₂ a b) ⁻¹) (defined-inj pr (pick₂ a b))

pair-defined← : (a b : ⟨ 𝔻 ⟩) → defined (pair · a · b) → defined a × defined b
pair-defined← a b p = guard-defined← 2 (pick₂ a b) (inj pr · pick₂ a b) p zero , guard-defined← 2 (pick₂ a b) (inj pr · pick₂ a b) p (suc zero)

{- Computation rules ---------------------------------------------------------------}

proj-tuple : (n : ℕ) (ds : Fin n → ⟨ 𝔻 ⟩) → ((i : Fin n) → defined (ds i)) → (i : Fin n) → proj i · (tuple n · ds) ＝ ds i
proj-tuple n ds h i = ap (proj i ·_) (guard-defined n ds h (inj (tup n) · ds)) ∙ case-inj 𝔻⊥ (proj-br i) (tup n) ds ∙ at-n (n Nat.≟ n)
 where
  at-n : (q : Dec (n Eq.≡ n)) → at-tup n n i q · ds ＝ ds i
  at-n (yes Eq.refl) = refl
  at-n (no ¬q) = Data.Empty.⊥-elim (¬q Eq.refl)

car-pair : (a b : ⟨ 𝔻 ⟩) → defined a → defined b → car · (pair · a · b) ＝ a
car-pair a b p q = ap (car ·_) (guard-defined 2 (pick₂ a b) (λ { zero → p ; (suc zero) → q }) (inj pr · pick₂ a b)) ∙ case-inj 𝔻⊥ (component-br zero) pr (pick₂ a b)

cdr-pair : (a b : ⟨ 𝔻 ⟩) → defined a → defined b → cdr · (pair · a · b) ＝ b
cdr-pair a b p q = ap (cdr ·_) (guard-defined 2 (pick₂ a b) (λ { zero → p ; (suc zero) → q }) (inj pr · pick₂ a b)) ∙ case-inj 𝔻⊥ (component-br (suc zero)) pr (pick₂ a b)

cases-inl : (d : ⟨ 𝔻 ⟩) → defined d → (f g : ⟨ 𝔻 ⟹₁ 𝔻 ⟩) → cases · (inl · d) · (f , g) ＝ f · d
cases-inl d p f g = ap (λ - → cases · - · (f , g)) (seq-defined d (inj left · d) p) ∙ ap (_· (f , g)) (case-inj (Br ⟹𝔻) cases-br left d)

cases-inr : (d : ⟨ 𝔻 ⟩) → defined d → (f g : ⟨ 𝔻 ⟹₁ 𝔻 ⟩) → cases · (inr · d) · (f , g) ＝ g · d
cases-inr d p f g = ap (λ - → cases · - · (f , g)) (seq-defined d (inj right · d) p) ∙ ap (_· (f , g)) (case-inj (Br ⟹𝔻) cases-br right d)

strict-defined : (g : DCPO[ 𝔻 , 𝔻 ]) (d : ⟨ 𝔻 ⟩) → defined d → strict · g · d ＝ g · d
strict-defined g d = seq-defined d (g · d)

primD-const : (p : Prim) (n m : _) → primD p · const Int n · const Int m ＝ out (δ p n m)
primD-const p n m = ap (_· const Int m) (case-inj (𝔻 ⟹𝔻) (prim-br₁ p) (con Int n) ⋆) ∙ case-inj 𝔻⊥ (prim-br₂ p n) (con Int m) ⋆

strict-cong : (g g' : DCPO[ 𝔻 , 𝔻 ]) → ((d : ⟨ 𝔻 ⟩) → defined d → g · d ＝ g' · d)
  → strict · g ＝ strict · g'
strict-cong g g' h = to-continuous-function-＝ 𝔻 𝔻 (λ d → seq-cong d (g · d) (g' · d) (h d))

Λ-cong : (g g' : DCPO[ 𝔻 , 𝔻 ]) → ((d : ⟨ 𝔻 ⟩) → defined d → g · d ＝ g' · d)
  → Λ · g ＝ Λ · g'
Λ-cong g g' h = ap (λ - → inj fun · -) (strict-cong g g' h)

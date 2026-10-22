{-

  Correctness of delay (Clos3μ → Clos4μ) in Scott domains, the forward
  half: what a source program produces, the compiled one produces too.

  delay changes the representation of closures (a function value in
  Clos3μ, a pair of code and environment in Clos4μ), so the meanings of
  a program and its translation are related, not equal, by a logical
  relation that relates a source function to a target pair when the
  pair's code, called on its environment and related arguments, gives
  related results. In Scott domains with the universal domain 𝔻 the
  relation cannot be defined by recursion on types (μ types) nor on
  values; it is defined by recursion on the stages of the bilimit 𝔻
  (proof/Framework/Scott/Stages.agda), relating an approximation s of
  depth n of the source value (s : 𝓓 n) to the whole target value
  (Pv n s d'). A source value d and a target value d' are related when
  every approximation π∞ n d of d is (Pres).

  The relation is downward closed in s (Pv-mono), closed under directed
  sups (Pv-sup: admissible), and survives moving between stages
  (Pv-π, Pv-ε). Then an application, whose source value is the sup of
  the applications to the approximations of the argument, preserves the
  relation; and the fundamental lemma follows by induction on terms.
  (Reflection, the other half, is DelayReflect.agda.)

-}

open import MLTT.Spartan hiding (inl; inr; cases; _+_)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.Base using (transport₂; ap₂)
open import Framework.Primitives using (Base; base-rep; Int; Nat; 𝔹; Unit; Void; Blame)
open import Language.Prim using (Prim; Out; int; bool; δ)
open import Data.Bool using (true; false)
open import Data.Integer using (ℤ)
import Data.Nat as Nat
open import Relation.Nullary using (Dec; yes; no)
import Relation.Binary.PropositionalEquality as Eq

open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (_+_)

module Mu.proof.Correctness.Scott.DelayPreserve
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : propext 𝓤₀)
       where

open import Framework.Scott.Base pt fe
open import Framework.Scott.Lift pt fe pe
open import Framework.Scott.Sum pt fe
open import Framework.Scott.Functor pt fe pe
open import proof.Framework.Scott.Sum pt fe
open import proof.Framework.Scott.Ops pt fe pe renaming (app to appᵈ; inl to inlᵈ; inr to inrᵈ; tuple to tupleᵈ; pair to pairᵈ)
open import proof.Framework.Scott.Stages pt fe pe
open import proof.Framework.Scott.Values pt fe pe
open import proof.Framework.Scott.Semantics pt fe pe
open import Semantics.Scott.Prim pt fe pe using (primD; out; prim-br₁; prim-br₂)

open import DomainTheory.Lifting.LiftingDcpo pt fe 𝓤₀ pe using (module freely-add-⊥)

{- The relation, by stages -------------------------------------------------------}

{- the call of a target closure (a pair cd of code and environment) on a -}
call : (Fin 2 → ⟨ 𝔻 ⟩) → ⟨ 𝔻 ⟩ → ⟨ 𝔻 ⟩
call cd a = appᵈ · (appᵈ · cd zero · cd (suc zero)) · a

Pv : (n : ℕ) → ⟨ 𝓓 n ⟩ → ⟨ 𝔻 ⟩ → 𝓤₁ ̇
Match : (n : ℕ) (t t' : Tag) → ⟨ obj (Payload t) (𝓓 n) ⟩ → ⟨ obj (Payload t') 𝔻 ⟩ → 𝓤₁ ̇

Pv zero s d = 𝟙
Pv (succ n) s d = (p : is-defined s) → Σ q ꞉ defined d ,
  Match n (pr₁ (value s p)) (pr₁ (value (unroll · d) q)) (pr₂ (value s p)) (pr₂ (value (unroll · d) q))

Match n (con B c) (con B' c') x y = (con B c ＝ con B' c') × 𝟙 {𝓤₁}
Match n (con B c) _ x y = 𝟘
Match n (tup k) (tup k') xs ys = Σ e ꞉ k ＝ k' , ((i : Fin k) → Pv n (xs i) (ys (transport Fin e i)))
Match n (tup k) _ xs ys = 𝟘
Match n left left x y = Pv n x y
Match n left _ x y = 𝟘
Match n right right x y = Pv n x y
Match n right _ x y = 𝟘
Match n fun pr h cd = (v : ⟨ 𝓓 n ⟩) (a : ⟨ 𝔻 ⟩) → Pv n v a → Pv n (h · v) (call cd a)
Match n fun _ h y = 𝟘
Match n pr _ x y = 𝟘

Pv-prop : (n : ℕ) (s : ⟨ 𝓓 n ⟩) (d : ⟨ 𝔻 ⟩) → is-prop (Pv n s d)
Match-prop : (n : ℕ) (t t' : Tag) (x : ⟨ obj (Payload t) (𝓓 n) ⟩) (y : ⟨ obj (Payload t') 𝔻 ⟩) → is-prop (Match n t t' x y)

Pv-prop zero s d = 𝟙-is-prop
Pv-prop (succ n) s d = Π-is-prop fe (λ p → Σ-is-prop (defined-is-prop d) (λ q →
  Match-prop n (pr₁ (value s p)) (pr₁ (value (unroll · d) q)) (pr₂ (value s p)) (pr₂ (value (unroll · d) q))))

Match-prop n (con B c) (con B' c') x y = ×-is-prop K-is-set 𝟙-is-prop
Match-prop n (con B c) (tup k) x y = 𝟘-is-prop
Match-prop n (con B c) left x y = 𝟘-is-prop
Match-prop n (con B c) right x y = 𝟘-is-prop
Match-prop n (con B c) fun x y = 𝟘-is-prop
Match-prop n (con B c) pr x y = 𝟘-is-prop
Match-prop n (tup k) (tup k') xs ys = Σ-is-prop K-is-set (λ e → Π-is-prop fe (λ i → Pv-prop n (xs i) (ys (transport Fin e i))))
Match-prop n (tup k) (con B c) x y = 𝟘-is-prop
Match-prop n (tup k) left x y = 𝟘-is-prop
Match-prop n (tup k) right x y = 𝟘-is-prop
Match-prop n (tup k) fun x y = 𝟘-is-prop
Match-prop n (tup k) pr x y = 𝟘-is-prop
Match-prop n left (con B c) x y = 𝟘-is-prop
Match-prop n left (tup k) x y = 𝟘-is-prop
Match-prop n left left x y = Pv-prop n x y
Match-prop n left right x y = 𝟘-is-prop
Match-prop n left fun x y = 𝟘-is-prop
Match-prop n left pr x y = 𝟘-is-prop
Match-prop n right (con B c) x y = 𝟘-is-prop
Match-prop n right (tup k) x y = 𝟘-is-prop
Match-prop n right left x y = 𝟘-is-prop
Match-prop n right right x y = Pv-prop n x y
Match-prop n right fun x y = 𝟘-is-prop
Match-prop n right pr x y = 𝟘-is-prop
Match-prop n fun pr h cd = Π-is-prop fe (λ v → Π-is-prop fe (λ a → Π-is-prop fe (λ _ → Pv-prop n (h · v) (call cd a))))
Match-prop n fun (con B c) x y = 𝟘-is-prop
Match-prop n fun (tup k) x y = 𝟘-is-prop
Match-prop n fun left x y = 𝟘-is-prop
Match-prop n fun right x y = 𝟘-is-prop
Match-prop n fun fun x y = 𝟘-is-prop
Match-prop n pr t' x y = 𝟘-is-prop

{- Downward closed in the source -}

Pv-mono : (n : ℕ) (s s' : ⟨ 𝓓 n ⟩) (d : ⟨ 𝔻 ⟩) → s' ⊑⟨ 𝓓 n ⟩ s → Pv n s d → Pv n s' d
Match-mono : (n : ℕ) (t t' : Tag) (x x' : ⟨ obj (Payload t) (𝓓 n) ⟩) (y : ⟨ obj (Payload t') 𝔻 ⟩)
  → x' ⊑⟨ obj (Payload t) (𝓓 n) ⟩ x → Match n t t' x y → Match n t t' x' y
Match-mono-Σ : (n : ℕ) (v v' : ⟨ obj Val (𝓓 n) ⟩) (t' : Tag) (y : ⟨ obj (Payload t') 𝔻 ⟩)
  → v' ⊑⟨ obj Val (𝓓 n) ⟩ v → Match n (pr₁ v) t' (pr₂ v) y → Match n (pr₁ v') t' (pr₂ v') y

Pv-mono zero s s' d le h = ⋆
Pv-mono (succ n) s s' d (f , g) h p' =
  pr₁ (h (f p')) ,
  Match-mono-Σ n (value s (f p')) (value s' p') (pr₁ (value (unroll · d) (pr₁ (h (f p')))))
    (pr₂ (value (unroll · d) (pr₁ (h (f p'))))) (g p') (pr₂ (h (f p')))

Match-mono-Σ n (t , x) (.t , x') t' y (refl , le) m = Match-mono n t t' x x' y le m

Match-mono n (con B c) (con B' c') x x' y le m = m
Match-mono n (tup k) (tup k') xs xs' ys le (e , m) = e , (λ i → Pv-mono n (xs i) (xs' i) (ys (transport Fin e i)) (le i) (m i))
Match-mono n left left x x' y le m = Pv-mono n x x' y le m
Match-mono n right right x x' y le m = Pv-mono n x x' y le m
Match-mono n fun pr h h' cd le m v a r = Pv-mono n (h · v) (h' · v) (call cd a) (le v) (m v a r)
Match-mono n (con B c) (tup k) x x' y le ()
Match-mono n (con B c) left x x' y le ()
Match-mono n (con B c) right x x' y le ()
Match-mono n (con B c) fun x x' y le ()
Match-mono n (con B c) pr x x' y le ()
Match-mono n (tup k) (con B c) x x' y le ()
Match-mono n (tup k) left x x' y le ()
Match-mono n (tup k) right x x' y le ()
Match-mono n (tup k) fun x x' y le ()
Match-mono n (tup k) pr x x' y le ()
Match-mono n left (con B c) x x' y le ()
Match-mono n left (tup k) x x' y le ()
Match-mono n left right x x' y le ()
Match-mono n left fun x x' y le ()
Match-mono n left pr x x' y le ()
Match-mono n right (con B c) x x' y le ()
Match-mono n right (tup k) x x' y le ()
Match-mono n right left x x' y le ()
Match-mono n right fun x x' y le ()
Match-mono n right pr x x' y le ()
Match-mono n fun (con B c) x x' y le ()
Match-mono n fun (tup k) x x' y le ()
Match-mono n fun left x x' y le ()
Match-mono n fun right x x' y le ()
Match-mono n fun fun x x' y le ()
Match-mono n pr t' x x' y le ()

{- Admissible: closed under directed sups in the source -}

Pv-sup : (n : ℕ) (d : ⟨ 𝔻 ⟩) {I : 𝓤₀ ̇ } (α : I → ⟨ 𝓓 n ⟩) (δ : is-Directed (𝓓 n) α)
  → ((i : I) → Pv n (α i) d) → Pv n (∐ (𝓓 n) {I} {α} δ) d
Match-sup : (n : ℕ) (t t' : Tag) (y : ⟨ obj (Payload t') 𝔻 ⟩) {I : 𝓤₀ ̇ } (β : I → ⟨ obj (Payload t) (𝓓 n) ⟩)
  (δ : is-Directed (obj (Payload t) (𝓓 n)) β) → ((i : I) → Match n t t' (β i) y) → Match n t t' (∐ (obj (Payload t) (𝓓 n)) {I} {β} δ) y

Pv-sup zero d α δ h = ⋆
Pv-sup (succ n) d {I} α δ h = stage-sup-ind n α δ Q Q-sup h
 where
  M : defined d → (v : ⟨ obj Val (𝓓 n) ⟩) → 𝓤₁ ̇
  M q v = Match n (pr₁ v) (pr₁ (value (unroll · d) q)) (pr₂ v) (pr₂ (value (unroll · d) q))
  Q : ⟨ obj Val (𝓓 n) ⟩ → 𝓤₁ ̇
  Q v = Σ q ꞉ defined d , M q v
  Q-prop : (v : ⟨ obj Val (𝓓 n) ⟩) → is-prop (Q v)
  Q-prop v = Σ-is-prop (defined-is-prop d) (λ q → Match-prop n (pr₁ v) (pr₁ (value (unroll · d) q)) (pr₂ v) (pr₂ (value (unroll · d) q)))
  Q-sup : {K : 𝓤₀ ̇ } (γ : K → ⟨ obj Val (𝓓 n) ⟩) (ε : is-Directed (obj Val (𝓓 n)) γ) → ((k : K) → Q (γ k))
        → Q (∐ (obj Val (𝓓 n)) {K} {γ} ε)
  Q-sup {K} γ ε hγ = ∥∥-rec (Q-prop (∐ (obj Val (𝓓 n)) {K} {γ} ε)) step (inhabited-if-Directed (obj Val (𝓓 n)) γ ε)
   where
    step : K → Q (∐ (obj Val (𝓓 n)) {K} {γ} ε)
    step k = q , Σ-sup-ind Tag Tag-is-set (λ t → obj (Payload t) (𝓓 n))
                  (λ t x → Match n t (pr₁ (value (unroll · d) q)) x (pr₂ (value (unroll · d) q)))
                  (λ t β' δ' → Match-sup n t (pr₁ (value (unroll · d) q)) (pr₂ (value (unroll · d) q)) β' δ')
                  γ ε
                  (λ k' → transport (λ q' → M q' (γ k')) (defined-is-prop d (pr₁ (hγ k')) q) (pr₂ (hγ k')))
     where
      q = pr₁ (hγ k)

Match-sup n (con B c) (con B' c') y β δ h = ∥∥-rec (Match-prop n (con B c) (con B' c') (∐ (obj (Payload (con B c)) (𝓓 n)) {_} {β} δ) y) h (pr₁ δ)
Match-sup n (tup k) (tup k') ys β δ h =
  ∥∥-rec (Match-prop n (tup k) (tup k') (∐ (obj (Payload (tup k)) (𝓓 n)) {_} {β} δ) ys)
    (λ i₀ → pr₁ (h i₀) , (λ idx → Pv-sup n (ys (transport Fin (pr₁ (h i₀)) idx)) (λ j → β j idx)
       (component-is-directed (Fin k) (𝓓 n) β δ idx)
       (λ j → transport (λ e → Pv n (β j idx) (ys (transport Fin e idx))) (K-is-set (pr₁ (h j)) (pr₁ (h i₀))) (pr₂ (h j) idx))))
    (pr₁ δ)
Match-sup n left left y β δ h = Pv-sup n y β δ h
Match-sup n right right y β δ h = Pv-sup n y β δ h
Match-sup n fun pr cd β δ h v a r = Pv-sup n (call cd a) (λ j → β j · v) (pointwise-directed (𝓓 n) (𝓓 n) β δ v) (λ j → h j v a r)
Match-sup n (con B c) (tup k) y β δ h = ∥∥-rec 𝟘-is-prop h (pr₁ δ)
Match-sup n (con B c) left y β δ h = ∥∥-rec 𝟘-is-prop h (pr₁ δ)
Match-sup n (con B c) right y β δ h = ∥∥-rec 𝟘-is-prop h (pr₁ δ)
Match-sup n (con B c) fun y β δ h = ∥∥-rec 𝟘-is-prop h (pr₁ δ)
Match-sup n (con B c) pr y β δ h = ∥∥-rec 𝟘-is-prop h (pr₁ δ)
Match-sup n (tup k) (con B c) y β δ h = ∥∥-rec 𝟘-is-prop h (pr₁ δ)
Match-sup n (tup k) left y β δ h = ∥∥-rec 𝟘-is-prop h (pr₁ δ)
Match-sup n (tup k) right y β δ h = ∥∥-rec 𝟘-is-prop h (pr₁ δ)
Match-sup n (tup k) fun y β δ h = ∥∥-rec 𝟘-is-prop h (pr₁ δ)
Match-sup n (tup k) pr y β δ h = ∥∥-rec 𝟘-is-prop h (pr₁ δ)
Match-sup n left (con B c) y β δ h = ∥∥-rec 𝟘-is-prop h (pr₁ δ)
Match-sup n left (tup k) y β δ h = ∥∥-rec 𝟘-is-prop h (pr₁ δ)
Match-sup n left right y β δ h = ∥∥-rec 𝟘-is-prop h (pr₁ δ)
Match-sup n left fun y β δ h = ∥∥-rec 𝟘-is-prop h (pr₁ δ)
Match-sup n left pr y β δ h = ∥∥-rec 𝟘-is-prop h (pr₁ δ)
Match-sup n right (con B c) y β δ h = ∥∥-rec 𝟘-is-prop h (pr₁ δ)
Match-sup n right (tup k) y β δ h = ∥∥-rec 𝟘-is-prop h (pr₁ δ)
Match-sup n right left y β δ h = ∥∥-rec 𝟘-is-prop h (pr₁ δ)
Match-sup n right fun y β δ h = ∥∥-rec 𝟘-is-prop h (pr₁ δ)
Match-sup n right pr y β δ h = ∥∥-rec 𝟘-is-prop h (pr₁ δ)
Match-sup n fun (con B c) y β δ h = ∥∥-rec 𝟘-is-prop h (pr₁ δ)
Match-sup n fun (tup k) y β δ h = ∥∥-rec 𝟘-is-prop h (pr₁ δ)
Match-sup n fun left y β δ h = ∥∥-rec 𝟘-is-prop h (pr₁ δ)
Match-sup n fun right y β δ h = ∥∥-rec 𝟘-is-prop h (pr₁ δ)
Match-sup n fun fun y β δ h = ∥∥-rec 𝟘-is-prop h (pr₁ δ)
Match-sup n pr t' y β δ h = ∥∥-rec 𝟘-is-prop h (pr₁ δ)

{- Moving between stages -}

Pv-π : (n : ℕ) (s : ⟨ 𝓓 (succ n) ⟩) (d : ⟨ 𝔻 ⟩) → Pv (succ n) s d → Pv n (π n s) d
Pv-ε : (n : ℕ) (s : ⟨ 𝓓 n ⟩) (d : ⟨ 𝔻 ⟩) → Pv n s d → Pv (succ n) (ε n s) d
Match-π : (n : ℕ) (t t' : Tag) (x : ⟨ obj (Payload t) (𝓓 (succ n)) ⟩) (y : ⟨ obj (Payload t') 𝔻 ⟩)
  → Match (succ n) t t' x y → Match n t t' (fmap (Payload t) (𝓓 (succ n)) (𝓓 n) (π' n) (ε' n) x) y
Match-ε : (n : ℕ) (t t' : Tag) (x : ⟨ obj (Payload t) (𝓓 n) ⟩) (y : ⟨ obj (Payload t') 𝔻 ⟩)
  → Match n t t' x y → Match (succ n) t t' (fmap (Payload t) (𝓓 n) (𝓓 (succ n)) (ε' n) (π' n) x) y

Pv-π zero s d h = ⋆
Pv-π (succ n) s d h = transport (λ - → Pv (succ n) - d) (π-succ n s ⁻¹) (λ p →
  pr₁ (h p) , Match-π n (pr₁ (value s p)) (pr₁ (value (unroll · d) (pr₁ (h p)))) (pr₂ (value s p))
                (pr₂ (value (unroll · d) (pr₁ (h p)))) (pr₂ (h p)))

Pv-ε zero s d h p = 𝟘-elim (ε-zero-undefined s p)
Pv-ε (succ n) s d h = transport (λ - → Pv (succ (succ n)) - d) (ε-succ n s ⁻¹) (λ p →
  pr₁ (h p) , Match-ε n (pr₁ (value s p)) (pr₁ (value (unroll · d) (pr₁ (h p)))) (pr₂ (value s p))
                (pr₂ (value (unroll · d) (pr₁ (h p)))) (pr₂ (h p)))

Match-π n (con B c) (con B' c') x y m = m
Match-π n (tup k) (tup k') xs ys (e , m) = e , (λ i → Pv-π n (xs i) (ys (transport Fin e i)) (m i))
Match-π n left left x y m = Pv-π n x y m
Match-π n right right x y m = Pv-π n x y m
Match-π n fun pr h cd m v a r = Pv-π n (h · ε n v) (call cd a) (m (ε n v) a (Pv-ε n v a r))
Match-π n (con B c) (tup k') x y ()
Match-π n (con B c) left x y ()
Match-π n (con B c) right x y ()
Match-π n (con B c) fun x y ()
Match-π n (con B c) pr x y ()
Match-π n (tup k) (con B' c') x y ()
Match-π n (tup k) left x y ()
Match-π n (tup k) right x y ()
Match-π n (tup k) fun x y ()
Match-π n (tup k) pr x y ()
Match-π n left (con B' c') x y ()
Match-π n left (tup k') x y ()
Match-π n left right x y ()
Match-π n left fun x y ()
Match-π n left pr x y ()
Match-π n right (con B' c') x y ()
Match-π n right (tup k') x y ()
Match-π n right left x y ()
Match-π n right fun x y ()
Match-π n right pr x y ()
Match-π n fun (con B' c') x y ()
Match-π n fun (tup k') x y ()
Match-π n fun left x y ()
Match-π n fun right x y ()
Match-π n fun fun x y ()
Match-π n pr t' x y ()

Match-ε n (con B c) (con B' c') x y m = m
Match-ε n (tup k) (tup k') xs ys (e , m) = e , (λ i → Pv-ε n (xs i) (ys (transport Fin e i)) (m i))
Match-ε n left left x y m = Pv-ε n x y m
Match-ε n right right x y m = Pv-ε n x y m
Match-ε n fun pr h cd m v a r = Pv-ε n (h · π n v) (call cd a) (m (π n v) a (Pv-π n v a r))
Match-ε n (con B c) (tup k') x y ()
Match-ε n (con B c) left x y ()
Match-ε n (con B c) right x y ()
Match-ε n (con B c) fun x y ()
Match-ε n (con B c) pr x y ()
Match-ε n (tup k) (con B' c') x y ()
Match-ε n (tup k) left x y ()
Match-ε n (tup k) right x y ()
Match-ε n (tup k) fun x y ()
Match-ε n (tup k) pr x y ()
Match-ε n left (con B' c') x y ()
Match-ε n left (tup k') x y ()
Match-ε n left right x y ()
Match-ε n left fun x y ()
Match-ε n left pr x y ()
Match-ε n right (con B' c') x y ()
Match-ε n right (tup k') x y ()
Match-ε n right left x y ()
Match-ε n right fun x y ()
Match-ε n right pr x y ()
Match-ε n fun (con B' c') x y ()
Match-ε n fun (tup k') x y ()
Match-ε n fun left x y ()
Match-ε n fun right x y ()
Match-ε n fun fun x y ()
Match-ε n pr t' x y ()

Pv-πs : (k n : ℕ) (s : ⟨ 𝓓 (k + n) ⟩) (d : ⟨ 𝔻 ⟩) → Pv (k + n) s d → Pv n (πs k n s) d
Pv-πs zero n s d h = h
Pv-πs (succ k) n s d h = Pv-πs k n (π (k + n) s) d (Pv-π (k + n) s d h)

Pv-εs : (k n : ℕ) (s : ⟨ 𝓓 n ⟩) (d : ⟨ 𝔻 ⟩) → Pv n s d → Pv (k + n) (εs k n s) d
Pv-εs zero n s d h = h
Pv-εs (succ k) n s d h = Pv-ε (k + n) (εs k n s) d (Pv-εs k n s d h)

{- The relation between values: every approximation of the source is
   related to the target -}

Pres : ⟨ 𝔻 ⟩ → ⟨ 𝔻 ⟩ → 𝓤₁ ̇
Pres d d' = (n : ℕ) → Pv n (π∞ n · d) d'

{- an approximation related at its stage is related -}
Pres-ε : (n : ℕ) (s : ⟨ 𝓓 n ⟩) (d' : ⟨ 𝔻 ⟩) → Pv n s d' → Pres (ε∞ n · s) d'
Pres-ε n s d' h m = go (split m n)
 where
  down : (k : ℕ) (n : ℕ) → n ＝ k + m → (s : ⟨ 𝓓 n ⟩) → Pv n s d' → Pv m (π∞ m · (ε∞ n · s)) d'
  down k .(k + m) refl s h = transport (λ - → Pv m - d') (π∞-ε∞-down k m s ⁻¹) (Pv-πs k m s d' h)
  up : (k : ℕ) (m : ℕ) → m ＝ k + n → Pv m (π∞ m · (ε∞ n · s)) d'
  up k .(k + n) refl = transport (λ - → Pv (k + n) - d') (π∞-ε∞-up k n s ⁻¹) (Pv-εs k n s d' h)
  go : Split m n → Pv m (π∞ m · (ε∞ n · s)) d'
  go (lower k e) = down k n e s h
  go (higher k e) = up k m e

{- Making and taking apart related values -----------------------------------------}

{- the approximation of depth n of a payload -}
approx : (n : ℕ) (t : Tag) → ⟨ obj (Payload t) 𝔻 ⟩ → ⟨ obj (Payload t) (𝓓 n) ⟩
approx n t x = fmap (Payload t) 𝔻 (𝓓 n) (π∞ n) (ε∞ n) x

{- related payloads at every depth, of values made with tags -}
Pres-inj : (t : Tag) (x : ⟨ obj (Payload t) 𝔻 ⟩) (t' : Tag) (y : ⟨ obj (Payload t') 𝔻 ⟩)
  → ((n : ℕ) → Match n t t' (approx n t x) y) → Pres (inj t · x) (inj t' · y)
Pres-inj t x t' y h zero = ⋆
Pres-inj t x t' y h (succ n) =
  transport (λ - → Pv (succ n) - (inj t' · y)) (π∞-inj n t x ⁻¹)
    (λ p → defined-inj t' y ,
           transport (λ v → Match n t (pr₁ v) (approx n t x) (pr₂ v)) (view-inj t' y (defined-inj t' y) ⁻¹) (h n))

{- only a defined source needs to be related -}
Pres-from-defined : (d d' : ⟨ 𝔻 ⟩) → (defined d → Pres d d') → Pres d d'
Pres-from-defined d d' h zero = ⋆
Pres-from-defined d d' h (succ n) p = h (π∞-defined n d p) (succ n) p

Pres-⊥ : (d' : ⟨ 𝔻 ⟩) → Pres ⊥𝔻 d'
Pres-⊥ d' = Pres-from-defined ⊥𝔻 d' (λ q → 𝟘-elim (⊥-undefined q))

{- a defined source has a defined target -}
Pres-defined : (d d' : ⟨ 𝔻 ⟩) → Pres d d' → defined d → defined d'
Pres-defined d d' h q = pr₁ (h 1 (defined-π∞ 0 d q))

{- the payloads of a source made with a tag and of its target -}
Pres-view : (t : Tag) (x : ⟨ obj (Payload t) 𝔻 ⟩) (d' : ⟨ 𝔻 ⟩) → Pres (inj t · x) d' → (q : defined d')
  → (n : ℕ) → Match n t (pr₁ (view d' q)) (approx n t x) (pr₂ (view d' q))
Pres-view t x d' h q n =
  transport (λ q' → Match n t (pr₁ (view d' q')) (approx n t x) (pr₂ (view d' q'))) (defined-is-prop d' _ q)
    (pr₂ (transport (λ - → Pv (succ n) - d') (π∞-inj n t x) (h (succ n)) ⋆))

{- so related values are made with tags whose payloads are related -}
Pres-cases : (d d' : ⟨ 𝔻 ⟩) → Pres d d' → defined d
  → (P : ⟨ 𝔻 ⟩ → ⟨ 𝔻 ⟩ → 𝓤₁ ̇ )
  → ((t : Tag) (x : ⟨ obj (Payload t) 𝔻 ⟩) (t' : Tag) (y : ⟨ obj (Payload t') 𝔻 ⟩)
       → ((n : ℕ) → Match n t t' (approx n t x) y) → P (inj t · x) (inj t' · y))
  → P d d'
Pres-cases d d' h q P k =
  transport₂ P (inj-view d q ⁻¹) (inj-view d' q' ⁻¹)
    (k (pr₁ (view d q)) (pr₂ (view d q)) (pr₁ (view d' q')) (pr₂ (view d' q'))
       (Pres-view (pr₁ (view d q)) (pr₂ (view d q)) d' (transport (λ - → Pres - d') (inj-view d q) h) q'))
 where
  q' = Pres-defined d d' h q

{- seq -}
Pres-seq : (d d' e e' : ⟨ 𝔻 ⟩) → Pres d d' → Pres e e' → Pres (seq · d · e) (seq · d' · e')
Pres-seq d d' e e' hd he =
  Pres-from-defined (seq · d · e) (seq · d' · e') λ q →
    transport₂ Pres (seq-defined d e (seq-defined-l d e q) ⁻¹)
                    (seq-defined d' e' (Pres-defined d d' hd (seq-defined-l d e q)) ⁻¹) he

{- Constants, tuples, injections -}

Pres-const : (B : Base) (c : base-rep B) → Pres (const B c) (const B c)
Pres-const B c = Pres-inj (con B c) ⋆ (con B c) ⋆ (λ n → refl , ⋆)

Pres-unit : Pres unit unit
Pres-unit = Pres-inj (tup 0) (λ ()) (tup 0) (λ ()) (λ n → refl , (λ ()))

Pres-tuple : (k : ℕ) (ds ds' : Fin k → ⟨ 𝔻 ⟩) → ((i : Fin k) → Pres (ds i) (ds' i))
  → Pres (tupleᵈ k · ds) (tupleᵈ k · ds')
Pres-tuple k ds ds' h =
  Pres-from-defined (tupleᵈ k · ds) (tupleᵈ k · ds') λ q →
    transport₂ Pres (guard-defined k ds (tuple-defined← k ds q) (inj (tup k) · ds) ⁻¹)
                    (guard-defined k ds' (λ i → Pres-defined (ds i) (ds' i) (h i) (tuple-defined← k ds q i)) (inj (tup k) · ds') ⁻¹)
      (Pres-inj (tup k) ds (tup k) ds' (λ n → refl , (λ i → h i n)))

Pres-inl : (d d' : ⟨ 𝔻 ⟩) → Pres d d' → Pres (inlᵈ · d) (inlᵈ · d')
Pres-inl d d' h = Pres-seq d d' (inj left · d) (inj left · d') h (Pres-inj left d left d' h)

Pres-inr : (d d' : ⟨ 𝔻 ⟩) → Pres d d' → Pres (inrᵈ · d) (inrᵈ · d')
Pres-inr d d' h = Pres-seq d d' (inj right · d) (inj right · d') h (Pres-inj right d right d' h)

{- Components of tuples -}

private
 proj-br-ok : {k : ℕ} (i : Fin k) (t : Tag) (x : ⟨ obj (Payload t) 𝔻 ⟩) (t' : Tag) (y : ⟨ obj (Payload t') 𝔻 ⟩)
   → ((n : ℕ) → Match n t t' (approx n t x) y) → Pres (proj-br i t · x) (proj-br i t' · y)
 proj-br-ok {k} i (tup j) xs (tup j') ys m = aux j' (pr₁ (m 0)) ys m
  where
   aux : (j' : ℕ) → j ＝ j' → (ys : Fin j' → ⟨ 𝔻 ⟩) → ((n : ℕ) → Match n (tup j) (tup j') (approx n (tup j) xs) ys)
       → Pres (at-tup j k i (j Nat.≟ k) · xs) (at-tup j' k i (j' Nat.≟ k) · ys)
   aux .j refl ys m = at-ok (j Nat.≟ k)
    where
     at-ok : (q : Dec (j Eq.≡ k)) → Pres (at-tup j k i q · xs) (at-tup j k i q · ys)
     at-ok (yes Eq.refl) n = transport (λ e' → Pv n (π∞ n · xs i) (ys (transport Fin e' i))) (K-is-set (pr₁ (m n)) refl) (pr₂ (m n) i)
     at-ok (no _) = Pres-⊥ ⊥𝔻
 proj-br-ok i (tup j) x (con B' c') y m = 𝟘-elim (m 0)
 proj-br-ok i (tup j) x left y m = 𝟘-elim (m 0)
 proj-br-ok i (tup j) x right y m = 𝟘-elim (m 0)
 proj-br-ok i (tup j) x fun y m = 𝟘-elim (m 0)
 proj-br-ok i (tup j) x pr y m = 𝟘-elim (m 0)
 proj-br-ok i (con B c) x t' y m = Pres-⊥ (proj-br i t' · y)
 proj-br-ok i left x t' y m = Pres-⊥ (proj-br i t' · y)
 proj-br-ok i right x t' y m = Pres-⊥ (proj-br i t' · y)
 proj-br-ok i fun x t' y m = Pres-⊥ (proj-br i t' · y)
 proj-br-ok i pr x t' y m = Pres-⊥ (proj-br i t' · y)

Pres-proj : {k : ℕ} (i : Fin k) (d d' : ⟨ 𝔻 ⟩) → Pres d d' → Pres (proj i · d) (proj i · d')
Pres-proj i d d' h =
  Pres-from-defined (proj i · d) (proj i · d') λ q →
    Pres-cases d d' h (proj-defined i d q) (λ a b → Pres (proj i · a) (proj i · b))
      (λ t x t' y m → transport₂ Pres (case-inj 𝔻⊥ (proj-br i) t x ⁻¹) (case-inj 𝔻⊥ (proj-br i) t' y ⁻¹)
                        (proj-br-ok i t x t' y m))

{- Cases: related branches give related results -}

private
 cases-br-ok : (t : Tag) (x : ⟨ obj (Payload t) 𝔻 ⟩) (t' : Tag) (y : ⟨ obj (Payload t') 𝔻 ⟩)
   → ((n : ℕ) → Match n t t' (approx n t x) y)
   → (f g f' g' : DCPO[ 𝔻 , 𝔻 ])
   → ((a a' : ⟨ 𝔻 ⟩) → Pres a a' → Pres (f · a) (f' · a'))
   → ((a a' : ⟨ 𝔻 ⟩) → Pres a a' → Pres (g · a) (g' · a'))
   → Pres (cases-br t · x · (strict · f , strict · g)) (cases-br t' · y · (strict · f' , strict · g'))
 cases-br-ok left x left y m f g f' g' hf hg = Pres-seq x y (f · x) (f' · y) m (hf x y m)
 cases-br-ok right x right y m f g f' g' hf hg = Pres-seq x y (g · x) (g' · y) m (hg x y m)
 cases-br-ok left x (con B' c') y m f g f' g' hf hg = 𝟘-elim (m 0)
 cases-br-ok left x (tup k') y m f g f' g' hf hg = 𝟘-elim (m 0)
 cases-br-ok left x right y m f g f' g' hf hg = 𝟘-elim (m 0)
 cases-br-ok left x fun y m f g f' g' hf hg = 𝟘-elim (m 0)
 cases-br-ok left x pr y m f g f' g' hf hg = 𝟘-elim (m 0)
 cases-br-ok right x (con B' c') y m f g f' g' hf hg = 𝟘-elim (m 0)
 cases-br-ok right x (tup k') y m f g f' g' hf hg = 𝟘-elim (m 0)
 cases-br-ok right x left y m f g f' g' hf hg = 𝟘-elim (m 0)
 cases-br-ok right x fun y m f g f' g' hf hg = 𝟘-elim (m 0)
 cases-br-ok right x pr y m f g f' g' hf hg = 𝟘-elim (m 0)
 cases-br-ok (con B c) x t' y m f g f' g' hf hg = Pres-⊥ (cases-br t' · y · (strict · f' , strict · g'))
 cases-br-ok (tup k) x t' y m f g f' g' hf hg = Pres-⊥ (cases-br t' · y · (strict · f' , strict · g'))
 cases-br-ok fun x t' y m f g f' g' hf hg = Pres-⊥ (cases-br t' · y · (strict · f' , strict · g'))
 cases-br-ok pr x t' y m f g f' g' hf hg = Pres-⊥ (cases-br t' · y · (strict · f' , strict · g'))

Pres-case : (d d' : ⟨ 𝔻 ⟩) (f g f' g' : DCPO[ 𝔻 , 𝔻 ]) → Pres d d'
  → ((a a' : ⟨ 𝔻 ⟩) → Pres a a' → Pres (f · a) (f' · a'))
  → ((a a' : ⟨ 𝔻 ⟩) → Pres a a' → Pres (g · a) (g' · a'))
  → Pres (cases · d · (strict · f , strict · g)) (cases · d' · (strict · f' , strict · g'))
Pres-case d d' f g f' g' h hf hg =
  Pres-from-defined (cases · d · b) (cases · d' · b') λ q →
    Pres-cases d d' h (cases-defined d b q) (λ u v → Pres (cases · u · b) (cases · v · b'))
      (λ t x t' y m → transport₂ Pres (ap (_· b) (case-inj (Br ⟹𝔻) cases-br t x) ⁻¹)
                                      (ap (_· b') (case-inj (Br ⟹𝔻) cases-br t' y) ⁻¹)
                        (cases-br-ok t x t' y m f g f' g' hf hg))
 where
  b = (strict · f , strict · g)
  b' = (strict · f' , strict · g')

{- Primitives -}

Pres-out : (o : Out) → Pres (out o) (out o)
Pres-out (int z) = Pres-const Int z
Pres-out (bool true) = Pres-inl unit unit Pres-unit
Pres-out (bool false) = Pres-inr unit unit Pres-unit

private
 prim-br₂-ok : (p : Prim) (z : ℤ) (t : Tag) (x : ⟨ obj (Payload t) 𝔻 ⟩) (t' : Tag) (y : ⟨ obj (Payload t') 𝔻 ⟩)
   → ((n : ℕ) → Match n t t' (approx n t x) y) → Pres (prim-br₂ p z t · x) (prim-br₂ p z t' · y)
 prim-br₂-ok p z (con Int w) x (con B' c') y m = aux (pr₁ (m 0))
  where
   aux : con Int w ＝ con B' c' → Pres (prim-br₂ p z (con Int w) · x) (prim-br₂ p z (con B' c') · y)
   aux refl = Pres-out (δ p z w)
 prim-br₂-ok p z (con Int w) x (tup k') y m = 𝟘-elim (m 0)
 prim-br₂-ok p z (con Int w) x left y m = 𝟘-elim (m 0)
 prim-br₂-ok p z (con Int w) x right y m = 𝟘-elim (m 0)
 prim-br₂-ok p z (con Int w) x fun y m = 𝟘-elim (m 0)
 prim-br₂-ok p z (con Int w) x pr y m = 𝟘-elim (m 0)
 prim-br₂-ok p z (tup k) x t' y m = Pres-⊥ (prim-br₂ p z t' · y)
 prim-br₂-ok p z left x t' y m = Pres-⊥ (prim-br₂ p z t' · y)
 prim-br₂-ok p z right x t' y m = Pres-⊥ (prim-br₂ p z t' · y)
 prim-br₂-ok p z fun x t' y m = Pres-⊥ (prim-br₂ p z t' · y)
 prim-br₂-ok p z pr x t' y m = Pres-⊥ (prim-br₂ p z t' · y)
 prim-br₂-ok p z (con Nat c) x t' y m = Pres-⊥ (prim-br₂ p z t' · y)
 prim-br₂-ok p z (con 𝔹 c) x t' y m = Pres-⊥ (prim-br₂ p z t' · y)
 prim-br₂-ok p z (con Unit c) x t' y m = Pres-⊥ (prim-br₂ p z t' · y)
 prim-br₂-ok p z (con Void c) x t' y m = Pres-⊥ (prim-br₂ p z t' · y)
 prim-br₂-ok p z (con Blame c) x t' y m = Pres-⊥ (prim-br₂ p z t' · y)

 prim-br₁-ok : (p : Prim) (t : Tag) (x : ⟨ obj (Payload t) 𝔻 ⟩) (t' : Tag) (y : ⟨ obj (Payload t') 𝔻 ⟩)
   → ((n : ℕ) → Match n t t' (approx n t x) y) → (e e' : ⟨ 𝔻 ⟩) → Pres e e'
   → Pres (prim-br₁ p t · x · e) (prim-br₁ p t' · y · e')
 prim-br₁-ok p (con Int z) x (con B' c') y m e e' he = aux (pr₁ (m 0))
  where
   aux : con Int z ＝ con B' c' → Pres (prim-br₁ p (con Int z) · x · e) (prim-br₁ p (con B' c') · y · e')
   aux refl =
     Pres-from-defined (case 𝔻⊥ (prim-br₂ p z) · e) (case 𝔻⊥ (prim-br₂ p z) · e') λ q →
       Pres-cases e e' he (case-defined (prim-br₂ p z) e q)
         (λ u v → Pres (case 𝔻⊥ (prim-br₂ p z) · u) (case 𝔻⊥ (prim-br₂ p z) · v))
         (λ t x t' y m → transport₂ Pres (case-inj 𝔻⊥ (prim-br₂ p z) t x ⁻¹) (case-inj 𝔻⊥ (prim-br₂ p z) t' y ⁻¹)
                           (prim-br₂-ok p z t x t' y m))
 prim-br₁-ok p (con Int z) x (tup k') y m e e' he = 𝟘-elim (m 0)
 prim-br₁-ok p (con Int z) x left y m e e' he = 𝟘-elim (m 0)
 prim-br₁-ok p (con Int z) x right y m e e' he = 𝟘-elim (m 0)
 prim-br₁-ok p (con Int z) x fun y m e e' he = 𝟘-elim (m 0)
 prim-br₁-ok p (con Int z) x pr y m e e' he = 𝟘-elim (m 0)
 prim-br₁-ok p (tup k) x t' y m e e' he = Pres-⊥ (prim-br₁ p t' · y · e')
 prim-br₁-ok p left x t' y m e e' he = Pres-⊥ (prim-br₁ p t' · y · e')
 prim-br₁-ok p right x t' y m e e' he = Pres-⊥ (prim-br₁ p t' · y · e')
 prim-br₁-ok p fun x t' y m e e' he = Pres-⊥ (prim-br₁ p t' · y · e')
 prim-br₁-ok p pr x t' y m e e' he = Pres-⊥ (prim-br₁ p t' · y · e')
 prim-br₁-ok p (con Nat c) x t' y m e e' he = Pres-⊥ (prim-br₁ p t' · y · e')
 prim-br₁-ok p (con 𝔹 c) x t' y m e e' he = Pres-⊥ (prim-br₁ p t' · y · e')
 prim-br₁-ok p (con Unit c) x t' y m e e' he = Pres-⊥ (prim-br₁ p t' · y · e')
 prim-br₁-ok p (con Void c) x t' y m e e' he = Pres-⊥ (prim-br₁ p t' · y · e')
 prim-br₁-ok p (con Blame c) x t' y m e e' he = Pres-⊥ (prim-br₁ p t' · y · e')

Pres-prim : (p : Prim) (d d' e e' : ⟨ 𝔻 ⟩) → Pres d d' → Pres e e' → Pres (primD p · d · e) (primD p · d' · e')
Pres-prim p d d' e e' hd he =
  Pres-from-defined (primD p · d · e) (primD p · d' · e') λ q →
    Pres-cases d d' hd (primD-defined₁ p d e q) (λ u v → Pres (primD p · u · e) (primD p · v · e'))
      (λ t x t' y m → transport₂ Pres (ap (_· e) (case-inj (𝔻 ⟹𝔻) (prim-br₁ p) t x) ⁻¹)
                                      (ap (_· e') (case-inj (𝔻 ⟹𝔻) (prim-br₁ p) t' y) ⁻¹)
                        (prim-br₁-ok p t x t' y m e e' he))

{- Closures --------------------------------------------------------------------------

   A Clos3μ closure is its code applied to the tuple t of its free
   variables, a function value when t is defined; its translation is
   the pair of the translated code and the tuple t'. They are related
   when the tuples are and the bodies are on related arguments. -}

Pres-clos : (B B' : Den Env) (t t' : ⟨ 𝔻 ⟩) → Pres t t'
  → ((X X' Y Y' : ⟨ 𝔻 ⟩) → Pres X X' → Pres Y Y' → Pres (B · env₂ X Y) (B' · env₂ X' Y'))
  → Pres (appᵈ · codeᶜ B · t) (pairᵈ · codeᶜ B' · t')
Pres-clos B B' t t' ht hB =
  Pres-from-defined (appᵈ · codeᶜ B · t) (pairᵈ · codeᶜ B' · t') λ q →
    let qt = seq-defined-l t _ (transport defined (app-Λ G t) q)
        qt' = Pres-defined t t' ht qt
    in transport₂ Pres (code₂-env BE t qt ⁻¹)
                       (guard-defined 2 (pick₂ (codeᶜ B') t') (λ { zero → Λ-defined G' ; (suc zero) → qt' })
                          (inj pr · pick₂ (codeᶜ B') t') ⁻¹)
         (Pres-inj fun (strict · (curry₁ 𝔻 𝔻 𝔻 BE · t)) pr (pick₂ (codeᶜ B') t')
           (λ n v a r → transport (λ - → Pv n (π∞ n · (strict · (curry₁ 𝔻 𝔻 𝔻 BE · t) · (ε∞ n · v))) -)
                          (body-target t' a qt' ⁻¹)
                          (Pres-seq (ε∞ n · v) a (B · env₂ t (ε∞ n · v)) (B' · env₂ t' a) (Pres-ε n v a r)
                             (hB t t' (ε∞ n · v) a ht (Pres-ε n v a r)) n)))
 where
  BE = ∘₁ (𝔻 ×₁ 𝔻) Env 𝔻 env₂ᶜ B
  G = ∘₁ 𝔻 (𝔻 ⟹₁ 𝔻) 𝔻 (curry₁ 𝔻 𝔻 𝔻 BE) Λ
  G' = ∘₁ 𝔻 (𝔻 ⟹₁ 𝔻) 𝔻 (curry₁ 𝔻 𝔻 𝔻 (∘₁ (𝔻 ×₁ 𝔻) Env 𝔻 env₂ᶜ B')) Λ
  {- the code, called on its environment and an argument -}
  body-target : (X Y : ⟨ 𝔻 ⟩) → defined X → appᵈ · (appᵈ · codeᶜ B' · X) · Y ＝ seq · Y · (B' · env₂ X Y)
  body-target X Y qX = codeᶜ-β B' X Y ∙ seq-defined X (seq · Y · (B' · env₂ X Y)) qX

{- A call: the source is an application of a function value, the
   target a call of a pair. The approximation of depth n of the result
   is the sup of the approximations of the applications to the
   approximations of the argument (approx-∐), and each of those is
   related, by the relation of the closures at a greater depth. -}

private
 call-fun : (s : DCPO[ 𝔻 , 𝔻 ]) (cd : Fin 2 → ⟨ 𝔻 ⟩) → ((n : ℕ) → Match n fun pr (approx n fun s) cd)
   → (a a' : ⟨ 𝔻 ⟩) → Pres a a' → Pres (s · a) (call cd a')
 call-fun s cd m a a' ha n =
   transport (λ - → Pv n - (call cd a')) (approx-∐ (𝓓 n) (∘₁ 𝔻 𝔻 (𝓓 n) s (π∞ n)) a ⁻¹)
     (Pv-sup n (call cd a') (λ k → π∞ n · (s · e k a))
        (image-is-directed' 𝔻 (𝓓 n) (∘₁ 𝔻 𝔻 (𝓓 n) s (π∞ n)) {ℕ} {λ k → e k a} (e-directed a))
        (λ k → Pv-mono n (π∞ n · (s · e (k + n) a)) (π∞ n · (s · e k a)) (call cd a')
                 (monotone-if-continuous 𝔻 (𝓓 n) (∘₁ 𝔻 𝔻 (𝓓 n) s (π∞ n)) (e k a) (e (k + n) a)
                    (e-mono a k (k + n) (≤+ k n)))
                 (transport (λ - → Pv n - (call cd a')) (πs-π∞ k n (s · e (k + n) a))
                    (Pv-πs k n (π∞ (k + n) · (s · e (k + n) a)) (call cd a')
                       (m (k + n) (π∞ (k + n) · a) a' (ha (k + n)))))))

 call-ok : (t : Tag) (x : ⟨ obj (Payload t) 𝔻 ⟩) (t' : Tag) (y : ⟨ obj (Payload t') 𝔻 ⟩)
   → ((n : ℕ) → Match n t t' (approx n t x) y) → (a a' : ⟨ 𝔻 ⟩) → Pres a a'
   → Pres (app-br t · x · a) (appᵈ · (appᵈ · (component-br zero t' · y) · (component-br (suc zero) t' · y)) · a')
 call-ok fun s pr cd m a a' ha =
   Pres-from-defined (strict · s · a) (call cd a') λ q →
     transport (λ - → Pres - (call cd a')) (seq-defined a (s · a) (seq-defined-l a (s · a) q) ⁻¹) (call-fun s cd m a a' ha)
 call-ok fun s (con B' c') y m a a' ha = 𝟘-elim (m 0)
 call-ok fun s (tup k') y m a a' ha = 𝟘-elim (m 0)
 call-ok fun s left y m a a' ha = 𝟘-elim (m 0)
 call-ok fun s right y m a a' ha = 𝟘-elim (m 0)
 call-ok fun s fun y m a a' ha = 𝟘-elim (m 0)
 call-ok (con B c) x t' y m a a' ha = Pres-⊥ (appᵈ · (appᵈ · (component-br zero t' · y) · (component-br (suc zero) t' · y)) · a')
 call-ok (tup k) x t' y m a a' ha = Pres-⊥ (appᵈ · (appᵈ · (component-br zero t' · y) · (component-br (suc zero) t' · y)) · a')
 call-ok left x t' y m a a' ha = Pres-⊥ (appᵈ · (appᵈ · (component-br zero t' · y) · (component-br (suc zero) t' · y)) · a')
 call-ok right x t' y m a a' ha = Pres-⊥ (appᵈ · (appᵈ · (component-br zero t' · y) · (component-br (suc zero) t' · y)) · a')
 call-ok pr x t' y m a a' ha = Pres-⊥ (appᵈ · (appᵈ · (component-br zero t' · y) · (component-br (suc zero) t' · y)) · a')

car-inj : (t : Tag) (y : ⟨ obj (Payload t) 𝔻 ⟩) → car · (inj t · y) ＝ component-br zero t · y
car-inj t y = case-inj 𝔻⊥ (component-br zero) t y

cdr-inj : (t : Tag) (y : ⟨ obj (Payload t) 𝔻 ⟩) → cdr · (inj t · y) ＝ component-br (suc zero) t · y
cdr-inj t y = case-inj 𝔻⊥ (component-br (suc zero)) t y

app-inj : (t : Tag) (x : ⟨ obj (Payload t) 𝔻 ⟩) (a : ⟨ 𝔻 ⟩) → appᵈ · (inj t · x) · a ＝ app-br t · x · a
app-inj t x a = ap (_· a) (case-inj (𝔻 ⟹𝔻) app-br t x)

private
 call-inj-ok : (a a' : ⟨ 𝔻 ⟩) → Pres a a' → (t : Tag) (x : ⟨ obj (Payload t) 𝔻 ⟩) (t' : Tag) (y : ⟨ obj (Payload t') 𝔻 ⟩)
   → ((n : ℕ) → Match n t t' (approx n t x) y)
   → Pres (appᵈ · (inj t · x) · a) (appᵈ · (appᵈ · (car · (inj t' · y)) · (cdr · (inj t' · y))) · a')
 call-inj-ok a a' ha t x t' y m =
   transport₂ Pres (app-inj t x a ⁻¹)
     (ap₂ (λ c d → appᵈ · (appᵈ · c · d) · a') (car-inj t' y) (cdr-inj t' y) ⁻¹)
     (call-ok t x t' y m a a' ha)

Pres-call : (l l' a a' : ⟨ 𝔻 ⟩) → Pres l l' → Pres a a'
  → Pres (appᵈ · l · a) (appᵈ · (appᵈ · (car · l') · (cdr · l')) · a')
Pres-call l l' a a' hl ha =
  Pres-from-defined (appᵈ · l · a) (appᵈ · (appᵈ · (car · l') · (cdr · l')) · a') λ q →
    Pres-cases l l' hl (app-defined l a q) (λ u v → Pres (appᵈ · u · a) (appᵈ · (appᵈ · (car · v) · (cdr · v)) · a'))
      (call-inj-ok a a' ha)

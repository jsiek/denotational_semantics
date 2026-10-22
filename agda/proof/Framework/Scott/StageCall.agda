{-

  Scott domains: applying embedded approximations, for the reflection
  half of delay. An element x of stage k + 1 embedded in 𝔻 unrolls to x
  with ε∞ k applied to its payload (unroll-ε∞); so a function of depth
  k + 1 applied to Y depends only on the approximation e k Y of depth k
  of Y, and gives a value of depth k (app-ε∞). Then a call of the
  closure (c , e) of stage m + 2 on v of stage m (callₛ: the code c
  applied to its environment e and the argument v, in 𝔻) behaves well
  when moving between stages (callₛ-π, callₛ-ε).

-}

open import MLTT.Spartan hiding (inl; inr; cases; _+_)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons
open import UF.Base using (transport₂)

open import Data.Nat using (_+_)
open import Data.Fin using (Fin; zero; suc)
open import Naturals.Order
open import Notation.Order

module proof.Framework.Scott.StageCall
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : propext 𝓤₀)
       where

open import Framework.Scott.Base pt fe
open import Framework.Scott.Lift pt fe pe
open import Framework.Scott.Functor pt fe pe
open import Framework.Scott.Sum pt fe
open import proof.Framework.Scott.Ops pt fe pe
open import proof.Framework.Scott.Values pt fe pe
open import proof.Framework.Scott.Stages pt fe pe
open import Framework.Scott.Semantics pt fe pe using (module Over)

private
 L : DCPO₁
 L = obj (Liftᶠ Val) 𝔻

{- ε-exp n (εs j n x) is ε-exp n x -}
private
 ε-exp-εs : (j n : ℕ) (x : ⟨ 𝓓 n ⟩) → 𝔻-solution.ε-exp (j + n) (εs j n x) ＝ 𝔻-solution.ε-exp n x
 ε-exp-εs zero n x = refl
 ε-exp-εs (succ j) n x = 𝔻-solution.ε-exp-commutes-with-ε (j + n) (εs j n x) ∙ ε-exp-εs j n x

{- unroll (ε∞ (k + 1) x) -}
unroll-ε∞ : (k : ℕ) (x : ⟨ 𝓓 (succ k) ⟩) → unroll · (ε∞ (succ k) · x) ＝ act (Liftᶠ Val) (ε∞ k) (π∞ k) · x
unroll-ε∞ k x =
  𝔻-solution.unfold-is-sup σ
  ∙ sups-are-unique (underlying-order L) (pr₁ (axioms-of-dcpo L)) uf
      (∐-is-sup L {ℕ} {uf} (𝔻-solution.unfold-family-is-directed σ)) (ub , lub)
 where
  σ = ε∞ (succ k) · x
  c = act (Liftᶠ Val) (ε∞ k) (π∞ k) · x
  uf = 𝔻-solution.unfold-family σ
  const-from : (j : ℕ) → uf (j + succ k) ＝ c
  const-from j = ap (𝔻-solution.ε-exp (j + succ k)) (π∞-ε∞-up j (succ k) x) ∙ ε-exp-εs j (succ k) x
  ub : (n : ℕ) → uf n ⊑⟨ L ⟩ c
  ub n = transport (λ - → uf n ⊑⟨ L ⟩ -) (const-from n)
           (𝔻-solution.unfold-family-is-monotone σ n (n + succ k) (≤+ n (succ k)))
  lub : (u : ⟨ L ⟩) → ((n : ℕ) → uf n ⊑⟨ L ⟩ u) → c ⊑⟨ L ⟩ u
  lub u h = transport (λ - → - ⊑⟨ L ⟩ u) (const-from 0) (h (succ k))

{- definedness of embedded stage elements -}
defined-ε∞ : (k : ℕ) (x : ⟨ 𝓓 (succ k) ⟩) → is-defined x → defined (ε∞ (succ k) · x)
defined-ε∞ k x p = transport is-defined (unroll-ε∞ k x ⁻¹) p

ε∞-defined : (k : ℕ) (x : ⟨ 𝓓 (succ k) ⟩) → defined (ε∞ (succ k) · x) → is-defined x
ε∞-defined k x p = transport is-defined (unroll-ε∞ k x) p

ε∞-zero : (x : ⟨ 𝓓 0 ⟩) → ε∞ 0 · x ＝ ⊥𝔻
ε∞-zero x = ε∞-ε 0 x ⁻¹ ∙ undefined-⊥ (ε∞ 1 · ε 0 x) (λ p → ε-zero-undefined x (ε∞-defined 0 (ε 0 x) p))

{- the approximation of depth k, as a continuous map -}
eᶜ : ℕ → DCPO[ 𝔻 , 𝔻 ]
eᶜ k = ∘₁ 𝔻 (𝓓 k) 𝔻 (π∞ k) (ε∞ k)

e-⊥ : (k : ℕ) → e k ⊥𝔻 ＝ ⊥𝔻
e-⊥ k = undefined-⊥ (e k ⊥𝔻) (λ p → ⊥-undefined (defined-mono (e k ⊥𝔻) ⊥𝔻 (e-below k ⊥𝔻) p))

e-defined : (k : ℕ) (d : ⟨ 𝔻 ⟩) → defined d → defined (e (succ k) d)
e-defined k d q = defined-ε∞ k (π∞ (succ k) · d) (defined-π∞ k d q)

e-ε∞ : (k : ℕ) (x : ⟨ 𝓓 k ⟩) → e k (ε∞ k · x) ＝ ε∞ k · x
e-ε∞ k x = ap (ε∞ k ·_) (π∞-ε∞ k x)

e-idem : (k : ℕ) (d : ⟨ 𝔻 ⟩) → e k (e k d) ＝ e k d
e-idem k d = e-ε∞ k (π∞ k · d)

{- ε∞ n (π n x) is below ε∞ (n + 1) x -}
ε∞-π-below : (n : ℕ) (x : ⟨ 𝓓 (succ n) ⟩) → ε∞ n · π n x ⊑⟨ 𝔻 ⟩ ε∞ (succ n) · x
ε∞-π-below n x = transport (λ - → - ⊑⟨ 𝔻 ⟩ ε∞ (succ n) · x) (ε∞-ε n (π n x))
                   (monotone-if-continuous (𝓓 (succ n)) 𝔻 (ε∞ (succ n)) (ε n (π n x)) x (𝔻-solution.επ-deflation n x))

{- seq d e depends only on whether d is defined -}
seq-iff : (d d' e : ⟨ 𝔻 ⟩) → (defined d → defined d') → (defined d' → defined d) → seq · d · e ＝ seq · d' · e
seq-iff d d' e f g = antisymmetry 𝔻 (seq · d · e) (seq · d' · e) (below d d' f) (below d' d g)
 where
  below : (a b : ⟨ 𝔻 ⟩) → (defined a → defined b) → seq · a · e ⊑⟨ 𝔻 ⟩ seq · b · e
  below a b h = ∐ˢˢ-is-lowerbound-of-upperbounds 𝔻⊥ (λ _ → e) (defined-is-prop a) (seq · b · e)
                  (λ p → ＝-to-⊒ 𝔻 (seq-defined b e (h p)))

seq-⊥ : (d : ⟨ 𝔻 ⟩) → seq · d · ⊥𝔻 ＝ ⊥𝔻
seq-⊥ d = undefined-⊥ (seq · d · ⊥𝔻) (λ p → ⊥-undefined (seq-defined-r d ⊥𝔻 p))

opaque
 unfolding case

 {- an application of a rolled value -}
 app-roll : (l : ⟨ L ⟩) (Y : ⟨ 𝔻 ⟩)
   → app · (roll · l) · Y ＝ ∐ˢˢ 𝔻⊥ (λ p → app-br (pr₁ (value l p)) · pr₂ (value l p) · Y) (being-defined-is-prop l)
 app-roll l Y =
   ap (λ - → extend (obj Val 𝔻) (𝔻 ⟹𝔻) (copair Tag Tag-is-set (λ t → obj (Payload t) 𝔻) (𝔻 ⟹₁ 𝔻) app-br) · - · Y) (unroll-roll l)
   ∙ ∐ˢˢ-＝-if-continuous-and-strict (𝔻 ⟹𝔻) 𝔻⊥ (λ g → g · Y) (pr₂ (at-point₁ 𝔻 𝔻 Y)) refl
       (λ p → app-br (pr₁ (value l p)) · pr₂ (value l p)) (being-defined-is-prop l)

{- the branches of app, on the payload of an embedded element -}
private
 branch-eq : (k : ℕ) (t : Tag) (x : ⟨ obj (Payload t) (𝓓 k) ⟩) (Y : ⟨ 𝔻 ⟩)
   → app-br t · fmap (Payload t) (𝓓 k) 𝔻 (ε∞ k) (π∞ k) x · Y
     ＝ e k (app-br t · fmap (Payload t) (𝓓 k) 𝔻 (ε∞ k) (π∞ k) x · e k Y)
 fun-eq : (k : ℕ) (g : ⟨ 𝓓 k ⟹₁ 𝓓 k ⟩) (Y : ⟨ 𝔻 ⟩)
   → seq · Y · (ε∞ k · (g · (π∞ k · Y))) ＝ seq · e k Y · (ε∞ k · (g · (π∞ k · Y)))
   → seq · Y · (ε∞ k · (g · (π∞ k · Y))) ＝ e k (seq · e k Y · (ε∞ k · (g · (π∞ k · e k Y))))
 fun-eq k g Y sd =
   sd
   ∙ ap (λ - → seq · e k Y · -) (e-ε∞ k (g · (π∞ k · Y)) ⁻¹)
   ∙ seq-strict (eᶜ k) (e-⊥ k) (e k Y) (ε∞ k · (g · (π∞ k · Y))) ⁻¹
   ∙ ap (λ - → e k (seq · e k Y · (ε∞ k · (g · -)))) (π∞-ε∞ k (π∞ k · Y) ⁻¹)

 branch-eq zero fun g Y =
   fun-eq zero g Y (ap (seq · Y ·_) (ε∞-zero (g · (π∞ 0 · Y))) ∙ seq-⊥ Y ∙ seq-⊥ (e 0 Y) ⁻¹
                    ∙ ap (seq · e 0 Y ·_) (ε∞-zero (g · (π∞ 0 · Y)) ⁻¹))
 branch-eq (succ j) fun g Y =
   fun-eq (succ j) g Y (seq-iff Y (e (succ j) Y) (ε∞ (succ j) · (g · (π∞ (succ j) · Y)))
                         (e-defined j Y) (defined-mono (e (succ j) Y) Y (e-below (succ j) Y)))
 branch-eq k (con B c) x Y = e-⊥ k ⁻¹
 branch-eq k (tup n) x Y = e-⊥ k ⁻¹
 branch-eq k left x Y = e-⊥ k ⁻¹
 branch-eq k right x Y = e-⊥ k ⁻¹
 branch-eq k pr x Y = e-⊥ k ⁻¹

{- a function of depth k + 1 applied to Y depends only on e k Y, and
   gives a value of depth k -}
app-ε∞ : (k : ℕ) (f : ⟨ 𝓓 (succ k) ⟩) (Y : ⟨ 𝔻 ⟩)
  → app · (ε∞ (succ k) · f) · Y ＝ e k (app · (ε∞ (succ k) · f) · e k Y)
app-ε∞ k f Y =
  ap (λ - → app · - · Y) rolled
  ∙ app-roll l Y
  ∙ ap (λ α → ∐ˢˢ 𝔻⊥ α (being-defined-is-prop l))
       (dfunext fe (λ p → branch-eq k (pr₁ (value f p)) (pr₂ (value f p)) Y))
  ∙ ∐ˢˢ-＝-if-continuous-and-strict 𝔻⊥ 𝔻⊥ (e k) (pr₂ (eᶜ k)) (e-⊥ k)
      (λ p → app-br (pr₁ (value l p)) · pr₂ (value l p) · e k Y) (being-defined-is-prop l) ⁻¹
  ∙ ap (e k) (app-roll l (e k Y) ⁻¹)
  ∙ ap (λ - → e k (app · - · e k Y)) rolled ⁻¹
 where
  l = act (Liftᶠ Val) (ε∞ k) (π∞ k) · f
  rolled : ε∞ (succ k) · f ＝ roll · l
  rolled = roll-unroll (ε∞ (succ k) · f) ⁻¹ ∙ ap (roll ·_) (unroll-ε∞ k f)

{- A call of a closure of stage m + 2 -----------------------------------------------}

{- the code cd 0 applied to the environment cd 1 and the argument v,
   all embedded, and the result approximated at depth m -}
callₛ : (m : ℕ) → (Fin 2 → ⟨ 𝓓 (succ (succ m)) ⟩) → ⟨ 𝓓 m ⟩ → ⟨ 𝓓 m ⟩
callₛ m cd v = π∞ m · (app · (app · (ε∞ (succ (succ m)) · cd zero) · (ε∞ (succ m) · π (succ m) (cd (suc zero)))) · (ε∞ m · v))

{- as a continuous map of the closure. (Opaque, and known only through
   callᶜ-is: Agda is slow to see that its function is callₛ when it is
   applied to a sup, which it reduces.) -}
opaque
 callᶜ : (m : ℕ) → ⟨ 𝓓 m ⟩ → DCPO[ Pow (Fin 2) (𝓓 (succ (succ m))) , 𝓓 m ]
 callᶜ m v =
   ∘₁ P 𝔻 (𝓓 m)
     (O.op₂ app (O.op₂ app (∘₁ P (𝓓 (succ (succ m))) 𝔻 (at (Fin 2) (𝓓 (succ (succ m))) zero) (ε∞ (succ (succ m))))
                           (∘₁ P (𝓓 (succ (succ m))) 𝔻 (at (Fin 2) (𝓓 (succ (succ m))) (suc zero))
                              (∘₁ (𝓓 (succ (succ m))) (𝓓 (succ m)) 𝔻 (π' (succ m)) (ε∞ (succ m)))))
                (O.litᶜ (ε∞ m · v)))
     (π∞ m)
  where
   P : DCPO₁
   P = Pow (Fin 2) (𝓓 (succ (succ m)))
   module O = Over P

 callᶜ-is : (m : ℕ) (v : ⟨ 𝓓 m ⟩) (cd : Fin 2 → ⟨ 𝓓 (succ (succ m)) ⟩) → callᶜ m v · cd ＝ callₛ m cd v
 callᶜ-is m v cd = refl

callₛ-mono : (m : ℕ) (cd cd' : Fin 2 → ⟨ 𝓓 (succ (succ m)) ⟩) (v : ⟨ 𝓓 m ⟩)
  → ((i : Fin 2) → cd i ⊑⟨ 𝓓 (succ (succ m)) ⟩ cd' i) → callₛ m cd v ⊑⟨ 𝓓 m ⟩ callₛ m cd' v
callₛ-mono m cd cd' v le =
  transport₂ (λ a b → a ⊑⟨ 𝓓 m ⟩ b) (callᶜ-is m v cd) (callᶜ-is m v cd')
    (monotone-if-continuous (Pow (Fin 2) (𝓓 (succ (succ m)))) (𝓓 m) (callᶜ m v) cd cd' le)

{- moving the closure down a stage, and the argument up -}
callₛ-π : (m : ℕ) (cd : Fin 2 → ⟨ 𝓓 (succ (succ (succ m))) ⟩) (v : ⟨ 𝓓 m ⟩)
  → callₛ m (λ i → π (succ (succ m)) (cd i)) v ⊑⟨ 𝓓 m ⟩ π m (callₛ (succ m) cd (ε m v))
callₛ-π m cd v =
  transport (λ - → callₛ m (λ i → π (succ (succ m)) (cd i)) v ⊑⟨ 𝓓 m ⟩ -) (rhs-eq ⁻¹)
    (monotone-if-continuous 𝔻 (𝓓 m) (π∞ m) _ _
       (monotone-if-continuous 𝔻 𝔻 (app-at (ε∞ m · v)) _ _
          (app-mono _ _ _ _ (ε∞-π-below (succ (succ m)) (cd zero))
                            (ε∞-π-below (succ m) (π (succ (succ m)) (cd (suc zero)))))))
 where
  c' = ε∞ (succ (succ (succ m))) · cd zero
  e' = ε∞ (succ (succ m)) · π (succ (succ m)) (cd (suc zero))
  rhs-eq : π m (callₛ (succ m) cd (ε m v)) ＝ π∞ m · (app · (app · c' · e') · (ε∞ m · v))
  rhs-eq = π-π∞ m (app · (app · c' · e') · (ε∞ (succ m) · ε m v)) ∙ ap (λ - → π∞ m · (app · (app · c' · e') · -)) (ε∞-ε m v)
  app-mono : (f f' a a' : ⟨ 𝔻 ⟩) → f ⊑⟨ 𝔻 ⟩ f' → a ⊑⟨ 𝔻 ⟩ a' → app · f · a ⊑⟨ 𝔻 ⟩ app · f' · a'
  app-mono f f' a a' u w = transitivity 𝔻 _ _ _
    (monotone-if-continuous 𝔻 (𝔻 ⟹₁ 𝔻) app f f' u a)
    (monotone-if-continuous 𝔻 𝔻 (app · f') a a' w)

{- moving the closure up a stage, and the argument down -}
callₛ-ε : (m : ℕ) (cd : Fin 2 → ⟨ 𝓓 (succ (succ m)) ⟩) (w : ⟨ 𝓓 (succ m) ⟩)
  → callₛ (succ m) (λ i → ε (succ (succ m)) (cd i)) w ＝ ε m (callₛ m cd (π m w))
callₛ-ε m cd w =
  ap (λ - → π∞ (succ m) · (app · (app · - · E-e) · (ε∞ (succ m) · w))) (ε∞-ε (succ (succ m)) c)
  ∙ ap (λ - → π∞ (succ m) · (app · (app · E-c · (ε∞ (succ (succ m)) · -)) · (ε∞ (succ m) · w)))
       (𝔻-solution.ε-section-of-π (succ (succ m)) env)
  ∙ ap (λ - → π∞ (succ m) · (app · - · (ε∞ (succ m) · w))) step₁
  ∙ ap (λ - → π∞ (succ m) · -) step₂
  ∙ π∞-ε∞-up 1 m (π∞ m · Z)
 where
  c = cd zero
  env = cd (suc zero)
  E-c = ε∞ (succ (succ m)) · c
  E-e = ε∞ (succ (succ m)) · π (succ (succ m)) (ε (succ (succ m)) env)
  R = app · E-c · (ε∞ (succ m) · π (succ m) env)
  Z = app · R · (ε∞ m · π m w)
  {- the code applied to the environment, of depth m + 1 -}
  step₁ : app · E-c · (ε∞ (succ (succ m)) · env) ＝ R
  step₁ = app-ε∞ (succ m) c (ε∞ (succ (succ m)) · env)
          ∙ ap (λ - → e (succ m) (app · E-c · (ε∞ (succ m) · -))) (π∞-ε∞-down 1 (succ m) env)
          ∙ ap (λ - → e (succ m) (app · E-c · -)) (e-ε∞ (succ m) (π (succ m) env) ⁻¹)
          ∙ app-ε∞ (succ m) c (ε∞ (succ m) · π (succ m) env) ⁻¹
  R-depth : R ＝ ε∞ (succ m) · (π∞ (succ m) · R)
  R-depth = app-ε∞ (succ m) c (ε∞ (succ m) · π (succ m) env)
            ∙ e-idem (succ m) (app · E-c · e (succ m) (ε∞ (succ m) · π (succ m) env)) ⁻¹
            ∙ ap (e (succ m)) (app-ε∞ (succ m) c (ε∞ (succ m) · π (succ m) env) ⁻¹)
  {- the result, of depth m -}
  step₂ : app · R · (ε∞ (succ m) · w) ＝ ε∞ m · (π∞ m · Z)
  step₂ = ap (λ - → app · - · (ε∞ (succ m) · w)) R-depth
          ∙ app-ε∞ m (π∞ (succ m) · R) (ε∞ (succ m) · w)
          ∙ ap (λ - → e m (app · (ε∞ (succ m) · (π∞ (succ m) · R)) · (ε∞ m · -))) (π∞-ε∞-down 1 m w)
          ∙ ap (λ - → e m (app · - · (ε∞ m · π m w))) (R-depth ⁻¹)

{- the call of the approximations of a closure is below the call of the
   closure -}
callₛ-below : (m : ℕ) (cd : Fin 2 → ⟨ 𝔻 ⟩) (v : ⟨ 𝓓 m ⟩)
  → callₛ m (λ i → π∞ (succ (succ m)) · cd i) v ⊑⟨ 𝓓 m ⟩ π∞ m · (app · (app · cd zero · cd (suc zero)) · (ε∞ m · v))
callₛ-below m cd v =
  monotone-if-continuous 𝔻 (𝓓 m) (π∞ m) _ _
    (monotone-if-continuous 𝔻 𝔻 (app-at (ε∞ m · v)) _ _
       (transitivity 𝔻 _ _ _
          (monotone-if-continuous 𝔻 (𝔻 ⟹₁ 𝔻) app (e (succ (succ m)) (cd zero)) (cd zero) (e-below (succ (succ m)) (cd zero))
             (ε∞ (succ m) · π (succ m) (π∞ (succ (succ m)) · cd (suc zero))))
          (monotone-if-continuous 𝔻 𝔻 (app · cd zero) _ _
             (transport (λ - → ε∞ (succ m) · - ⊑⟨ 𝔻 ⟩ cd (suc zero)) (π-π∞ (succ m) (cd (suc zero)) ⁻¹)
                (e-below (succ m) (cd (suc zero)))))))

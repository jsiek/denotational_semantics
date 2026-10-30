{-

  Correctness of delay (EnvClosμ → PairClosμ) in Scott domains: the logical
  relations of the two halves, and what they share.

  delay changes the representation of closures (a function value in
  EnvClosμ, a pair of code and environment in PairClosμ), so the meanings of
  a program and its translation are related, not equal. In Scott
  domains with the universal domain 𝔻 the relations cannot be defined by
  recursion on types (μ types) nor on values; they are defined by
  recursion on the stages of the bilimit 𝔻
  (proof/Framework/Scott/Stages.agda), relating an approximation s of
  depth n of one value (s : 𝓓 n) to the whole other value (R δ n s w).
  Forward (preserve), the source is approximated: what the source
  produces, the target produces too. Backward (reflect), the target is:
  what the compiled program produces, the source produces too.

  Related values are defined together, and their tags are the same
  (Same), but for closures: a source function value is related to a
  target pair when calls of the pair, on arguments related to the
  function's, give results related to the function's. Forward, the
  function is approximated (M preserve n s-fun); backward, the pair is,
  and seen in an approximation of depth m + 2 a call of the pair shows
  its result at depth m only (callₛ, proof/Framework/Scott/StageCall.agda),
  so the clause for pairs at depth m + 2 speaks of depth m (Call).

  Both relations are downward closed and admissible in the approximated
  value (R-mono, R-sup), and survive moving between stages (R-π, R-ε).
  Values are related (Rel δ a w) when every approximation of a is
  related to w. The operators of EnvClosμ and PairClosμ other than closures
  and calls preserve both relations (Rel-seq, ..., Rel-prim); closures
  and calls are in DelayPreserve.agda and DelayReflect.agda.

-}

open import MLTT.Spartan hiding (inl; inr; cases; _+_)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.Base using (transport₂)

open import Framework.Primitives using (Int; Nat; 𝔹; Unit; Void; Blame)
open import Language.Prim using (Prim; Out; int; bool) renaming (δ to δᵖ)
open import Data.Bool using (true; false)
open import Data.Integer using (ℤ)
open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (_+_)
import Data.Nat as Nat
open import Relation.Nullary using (Dec; yes; no)
import Relation.Binary.PropositionalEquality as Eq

module Mu.proof.Correctness.ScottDomains.DelayRel
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : propext 𝓤₀)
       where

open import Framework.Scott.Base pt fe
open import Framework.Scott.Lift pt fe pe
open import Framework.Scott.Sum pt fe
open import Framework.Scott.Functor pt fe pe
open import proof.Framework.Scott.Sum pt fe
open import proof.Framework.Scott.Ops pt fe pe renaming (app to appᵈ; inl to inlᵈ; inr to inrᵈ; tuple to tupleᵈ)
open import proof.Framework.Scott.Stages pt fe pe
open import proof.Framework.Scott.StageCall pt fe pe
open import proof.Framework.Scott.Values pt fe pe
open import Semantics.Scott.Prim pt fe pe using (primD; out; prim-br₁; prim-br₂)

{- The relations, by stages -------------------------------------------------------}

data Dir : 𝓤₀ ̇ where
  preserve reflect : Dir

{- the tags of related values, the approximated one's first -}
data Same : Dir → Tag → Tag → 𝓤₀ ̇ where
  s-con : ∀ {δ B c} → Same δ (con B c) (con B c)
  s-tup : ∀ {δ k} → Same δ (tup k) (tup k)
  s-left : ∀ {δ} → Same δ left left
  s-right : ∀ {δ} → Same δ right right
  s-fun : Same preserve fun pr
  s-pr : Same reflect pr fun

Same-prop : ∀ {δ t t'} → is-prop (Same δ t t')
Same-prop s-con s-con = refl
Same-prop s-tup s-tup = refl
Same-prop s-left s-left = refl
Same-prop s-right s-right = refl
Same-prop s-fun s-fun = refl
Same-prop s-pr s-pr = refl

{- the call of a target closure (a pair cd of code and environment) on a -}
call : (Fin 2 → ⟨ 𝔻 ⟩) → ⟨ 𝔻 ⟩ → ⟨ 𝔻 ⟩
call cd a = appᵈ · (appᵈ · cd zero · cd (suc zero)) · a

R : Dir → (n : ℕ) → ⟨ 𝓓 n ⟩ → ⟨ 𝔻 ⟩ → 𝓤₁ ̇
Match : Dir → (n : ℕ) → ⟨ obj Val (𝓓 n) ⟩ → ⟨ obj Val 𝔻 ⟩ → 𝓤₁ ̇
M : (δ : Dir) (n : ℕ) {t t' : Tag} → Same δ t t' → ⟨ obj (Payload t) (𝓓 n) ⟩ → ⟨ obj (Payload t') 𝔻 ⟩ → 𝓤₁ ̇
Call : (n : ℕ) → (Fin 2 → ⟨ 𝓓 n ⟩) → DCPO[ 𝔻 , 𝔻 ] → 𝓤₁ ̇

R δ zero s w = 𝟙
R δ (succ n) s w = (p : is-defined s) → Σ q ꞉ defined w , Match δ n (value s p) (view w q)

Match δ n (t , x) (t' , y) = Σ e ꞉ Same δ t t' , M δ n e x y

M δ n s-con x y = 𝟙
M δ n s-tup xs ys = (i : Fin _) → R δ n (xs i) (ys i)
M δ n s-left x y = R δ n x y
M δ n s-right x y = R δ n x y
M δ n s-fun h cd = (v : ⟨ 𝓓 n ⟩) (a : ⟨ 𝔻 ⟩) → R preserve n v a → R preserve n (h · v) (call cd a)
M δ n s-pr cd s = Call n cd s

Call zero cd s = 𝟙
Call (succ zero) cd s = 𝟙
Call (succ (succ m)) cd s = (v : ⟨ 𝓓 m ⟩) (a : ⟨ 𝔻 ⟩) → R reflect m v a → R reflect m (callₛ m cd v) (strict · s · a)

{- the payloads of values with the same tags, from related values -}
M-at : ∀ {δ n t t' x y} (e : Same δ t t') → Match δ n (t , x) (t' , y) → M δ n e x y
M-at {δ} {n} {x = x} {y} e (e' , m) = transport (λ e → M δ n e x y) (Same-prop e' e) m

{- The relations are propositions ------------------------------------------------}

R-prop : (δ : Dir) (n : ℕ) (s : ⟨ 𝓓 n ⟩) (w : ⟨ 𝔻 ⟩) → is-prop (R δ n s w)
M-prop : (δ : Dir) (n : ℕ) {t t' : Tag} (e : Same δ t t') (x : ⟨ obj (Payload t) (𝓓 n) ⟩) (y : ⟨ obj (Payload t') 𝔻 ⟩)
  → is-prop (M δ n e x y)
Call-prop : (n : ℕ) (cd : Fin 2 → ⟨ 𝓓 n ⟩) (s : DCPO[ 𝔻 , 𝔻 ]) → is-prop (Call n cd s)

Match-prop : (δ : Dir) (n : ℕ) (v : ⟨ obj Val (𝓓 n) ⟩) (u : ⟨ obj Val 𝔻 ⟩) → is-prop (Match δ n v u)
Match-prop δ n (t , x) (t' , y) = Σ-is-prop Same-prop (λ e → M-prop δ n e x y)

R-prop δ zero s w = 𝟙-is-prop
R-prop δ (succ n) s w =
  Π-is-prop fe (λ p → Σ-is-prop (defined-is-prop w) (λ q → Match-prop δ n (value s p) (view w q)))

M-prop δ n s-con x y = 𝟙-is-prop
M-prop δ n s-tup xs ys = Π-is-prop fe (λ i → R-prop δ n (xs i) (ys i))
M-prop δ n s-left x y = R-prop δ n x y
M-prop δ n s-right x y = R-prop δ n x y
M-prop δ n s-fun h cd = Π-is-prop fe (λ v → Π-is-prop fe (λ a → Π-is-prop fe (λ _ → R-prop preserve n (h · v) (call cd a))))
M-prop δ n s-pr cd s = Call-prop n cd s

Call-prop zero cd s = 𝟙-is-prop
Call-prop (succ zero) cd s = 𝟙-is-prop
Call-prop (succ (succ m)) cd s =
  Π-is-prop fe (λ v → Π-is-prop fe (λ a → Π-is-prop fe (λ _ → R-prop reflect m (callₛ m cd v) (strict · s · a))))

{- Downward closed in the approximated value ---------------------------------------}

R-mono : (δ : Dir) (n : ℕ) (s s' : ⟨ 𝓓 n ⟩) (w : ⟨ 𝔻 ⟩) → s' ⊑⟨ 𝓓 n ⟩ s → R δ n s w → R δ n s' w
Match-mono : (δ : Dir) (n : ℕ) (v v' : ⟨ obj Val (𝓓 n) ⟩) (u : ⟨ obj Val 𝔻 ⟩)
  → v' ⊑⟨ obj Val (𝓓 n) ⟩ v → Match δ n v u → Match δ n v' u
M-mono : (δ : Dir) (n : ℕ) {t t' : Tag} (e : Same δ t t') (x x' : ⟨ obj (Payload t) (𝓓 n) ⟩) (y : ⟨ obj (Payload t') 𝔻 ⟩)
  → x' ⊑⟨ obj (Payload t) (𝓓 n) ⟩ x → M δ n e x y → M δ n e x' y
Call-mono : (n : ℕ) (cd cd' : Fin 2 → ⟨ 𝓓 n ⟩) (s : DCPO[ 𝔻 , 𝔻 ])
  → ((i : Fin 2) → cd' i ⊑⟨ 𝓓 n ⟩ cd i) → Call n cd s → Call n cd' s

R-mono δ zero s s' w le h = ⋆
R-mono δ (succ n) s s' w (f , g) h p' =
  pr₁ (h (f p')) , Match-mono δ n (value s (f p')) (value s' p') (view w (pr₁ (h (f p')))) (g p') (pr₂ (h (f p')))

Match-mono δ n (t , x) (.t , x') (t' , y) (refl , le) (e , m) = e , M-mono δ n e x x' y le m

M-mono δ n s-con x x' y le m = ⋆
M-mono δ n s-tup xs xs' ys le m i = R-mono δ n (xs i) (xs' i) (ys i) (le i) (m i)
M-mono δ n s-left x x' y le m = R-mono δ n x x' y le m
M-mono δ n s-right x x' y le m = R-mono δ n x x' y le m
M-mono δ n s-fun h h' cd le m v a r = R-mono preserve n (h · v) (h' · v) (call cd a) (le v) (m v a r)
M-mono δ n s-pr cd cd' s le m = Call-mono n cd cd' s le m

Call-mono zero cd cd' s le h = ⋆
Call-mono (succ zero) cd cd' s le h = ⋆
Call-mono (succ (succ m)) cd cd' s le h v a r =
  R-mono reflect m (callₛ m cd v) (callₛ m cd' v) (strict · s · a) (callₛ-mono m cd' cd v le) (h v a r)

{- Admissible: closed under directed sups of the approximated value --------------}

R-sup : (δ : Dir) (n : ℕ) (w : ⟨ 𝔻 ⟩) {I : 𝓤₀ ̇ } (α : I → ⟨ 𝓓 n ⟩) (d : is-Directed (𝓓 n) α)
  → ((i : I) → R δ n (α i) w) → R δ n (∐ (𝓓 n) {I} {α} d) w
M-sup : (δ : Dir) (n : ℕ) {t t' : Tag} (e : Same δ t t') (y : ⟨ obj (Payload t') 𝔻 ⟩) {I : 𝓤₀ ̇ }
  (β : I → ⟨ obj (Payload t) (𝓓 n) ⟩) (d : is-Directed (obj (Payload t) (𝓓 n)) β)
  → ((i : I) → M δ n e (β i) y) → M δ n e (∐ (obj (Payload t) (𝓓 n)) {I} {β} d) y
Call-sup : (n : ℕ) (s : DCPO[ 𝔻 , 𝔻 ]) {I : 𝓤₀ ̇ } (β : I → Fin 2 → ⟨ 𝓓 n ⟩) (d : is-Directed (Pow (Fin 2) (𝓓 n)) β)
  → ((i : I) → Call n (β i) s) → Call n (∐ (Pow (Fin 2) (𝓓 n)) {I} {β} d) s

R-sup δ zero w α d h = ⋆
R-sup δ (succ n) w {I} α d h = stage-sup-ind n α d Q Q-sup h
 where
  Q : ⟨ obj Val (𝓓 n) ⟩ → 𝓤₁ ̇
  Q v = Σ q ꞉ defined w , Match δ n v (view w q)
  Q-sup : {K : 𝓤₀ ̇ } (γ : K → ⟨ obj Val (𝓓 n) ⟩) (ε : is-Directed (obj Val (𝓓 n)) γ) → ((k : K) → Q (γ k))
        → Q (∐ (obj Val (𝓓 n)) {K} {γ} ε)
  Q-sup {K} γ ε hγ =
    ∥∥-rec (Σ-is-prop (defined-is-prop w) (λ q → Match-prop δ n _ (view w q)))
      (λ k → let q = pr₁ (hγ k) in
        q , Σ-sup-ind Tag Tag-is-set (λ t → obj (Payload t) (𝓓 n)) (λ t x → Match δ n (t , x) (view w q))
              (λ t β' ε' h' → ∥∥-rec (Match-prop δ n _ (view w q))
                                 (λ i → pr₁ (h' i) , M-sup δ n (pr₁ (h' i)) _ β' ε' (λ j → M-at (pr₁ (h' i)) (h' j)))
                                 (inhabited-if-Directed (obj (Payload t) (𝓓 n)) β' ε'))
              γ ε (λ k' → transport (λ q' → Match δ n (γ k') (view w q')) (defined-is-prop w (pr₁ (hγ k')) q) (pr₂ (hγ k'))))
      (inhabited-if-Directed (obj Val (𝓓 n)) γ ε)

M-sup δ n s-con y β d h = ⋆
M-sup δ n s-tup ys β d h i = R-sup δ n (ys i) (λ j → β j i) (component-is-directed (Fin _) (𝓓 n) β d i) (λ j → h j i)
M-sup δ n s-left y β d h = R-sup δ n y β d h
M-sup δ n s-right y β d h = R-sup δ n y β d h
M-sup δ n s-fun cd β d h v a r = R-sup preserve n (call cd a) (λ j → β j · v) (pointwise-directed (𝓓 n) (𝓓 n) β d v) (λ j → h j v a r)
M-sup δ n s-pr s β d h = Call-sup n s β d h

Call-sup zero s β d h = ⋆
Call-sup (succ zero) s β d h = ⋆
Call-sup (succ (succ m)) s {I} β d h v a r =
  transport (λ - → R reflect m - (strict · s · a)) (callᶜ-is m v (∐ (Pow (Fin 2) (𝓓 (succ (succ m)))) {I} {β} d))
    (transport (λ - → R reflect m - (strict · s · a))
       (continuous-∐-＝ (Pow (Fin 2) (𝓓 (succ (succ m)))) (𝓓 m) (callᶜ m v) {I} {β} d ⁻¹)
       (R-sup reflect m (strict · s · a) (λ i → callᶜ m v · β i)
          (image-is-directed' (Pow (Fin 2) (𝓓 (succ (succ m)))) (𝓓 m) (callᶜ m v) {I} {β} d)
          (λ i → transport (λ - → R reflect m - (strict · s · a)) (callᶜ-is m v (β i) ⁻¹) (h i v a r))))

{- Moving between stages -------------------------------------------------------------}

R-π : (δ : Dir) (n : ℕ) (s : ⟨ 𝓓 (succ n) ⟩) (w : ⟨ 𝔻 ⟩) → R δ (succ n) s w → R δ n (π n s) w
R-ε : (δ : Dir) (n : ℕ) (s : ⟨ 𝓓 n ⟩) (w : ⟨ 𝔻 ⟩) → R δ n s w → R δ (succ n) (ε n s) w
M-π : (δ : Dir) (n : ℕ) {t t' : Tag} (e : Same δ t t') (x : ⟨ obj (Payload t) (𝓓 (succ n)) ⟩) (y : ⟨ obj (Payload t') 𝔻 ⟩)
  → M δ (succ n) e x y → M δ n e (fmap (Payload t) (𝓓 (succ n)) (𝓓 n) (π' n) (ε' n) x) y
M-ε : (δ : Dir) (n : ℕ) {t t' : Tag} (e : Same δ t t') (x : ⟨ obj (Payload t) (𝓓 n) ⟩) (y : ⟨ obj (Payload t') 𝔻 ⟩)
  → M δ n e x y → M δ (succ n) e (fmap (Payload t) (𝓓 n) (𝓓 (succ n)) (ε' n) (π' n) x) y
Call-π : (n : ℕ) (cd : Fin 2 → ⟨ 𝓓 (succ n) ⟩) (s : DCPO[ 𝔻 , 𝔻 ]) → Call (succ n) cd s → Call n (λ i → π n (cd i)) s
Call-ε : (n : ℕ) (cd : Fin 2 → ⟨ 𝓓 n ⟩) (s : DCPO[ 𝔻 , 𝔻 ]) → Call n cd s → Call (succ n) (λ i → ε n (cd i)) s

R-π δ zero s w h = ⋆
R-π δ (succ n) s w h = transport (λ - → R δ (succ n) - w) (π-succ n s ⁻¹) (λ p →
  pr₁ (h p) , pr₁ (pr₂ (h p)) , M-π δ n (pr₁ (pr₂ (h p))) (pr₂ (value s p)) _ (pr₂ (pr₂ (h p))))

R-ε δ zero s w h p = 𝟘-elim (ε-zero-undefined s p)
R-ε δ (succ n) s w h = transport (λ - → R δ (succ (succ n)) - w) (ε-succ n s ⁻¹) (λ p →
  pr₁ (h p) , pr₁ (pr₂ (h p)) , M-ε δ n (pr₁ (pr₂ (h p))) (pr₂ (value s p)) _ (pr₂ (pr₂ (h p))))

M-π δ n s-con x y m = ⋆
M-π δ n s-tup xs ys m i = R-π δ n (xs i) (ys i) (m i)
M-π δ n s-left x y m = R-π δ n x y m
M-π δ n s-right x y m = R-π δ n x y m
M-π δ n s-fun h cd m v a r = R-π preserve n (h · ε n v) (call cd a) (m (ε n v) a (R-ε preserve n v a r))
M-π δ n s-pr cd s m = Call-π n cd s m

M-ε δ n s-con x y m = ⋆
M-ε δ n s-tup xs ys m i = R-ε δ n (xs i) (ys i) (m i)
M-ε δ n s-left x y m = R-ε δ n x y m
M-ε δ n s-right x y m = R-ε δ n x y m
M-ε δ n s-fun h cd m v a r = R-ε preserve n (h · π n v) (call cd a) (m (π n v) a (R-π preserve n v a r))
M-ε δ n s-pr cd s m = Call-ε n cd s m

Call-π zero cd s h = ⋆
Call-π (succ zero) cd s h = ⋆
Call-π (succ (succ m)) cd s h v a r =
  R-mono reflect m (π m (callₛ (succ m) cd (ε m v))) (callₛ m (λ i → π (succ (succ m)) (cd i)) v) (strict · s · a)
    (callₛ-π m cd v) (R-π reflect m (callₛ (succ m) cd (ε m v)) (strict · s · a) (h (ε m v) a (R-ε reflect m v a r)))

Call-ε zero cd s h = ⋆
Call-ε (succ zero) cd s h v a r = ⋆
Call-ε (succ (succ m)) cd s h w a r =
  transport (λ - → R reflect (succ m) - (strict · s · a)) (callₛ-ε m cd w ⁻¹)
    (R-ε reflect m (callₛ m cd (π m w)) (strict · s · a) (h (π m w) a (R-π reflect m w a r)))

R-πs : (δ : Dir) (k n : ℕ) (s : ⟨ 𝓓 (k + n) ⟩) (w : ⟨ 𝔻 ⟩) → R δ (k + n) s w → R δ n (πs k n s) w
R-πs δ zero n s w h = h
R-πs δ (succ k) n s w h = R-πs δ k n (π (k + n) s) w (R-π δ (k + n) s w h)

R-εs : (δ : Dir) (k n : ℕ) (s : ⟨ 𝓓 n ⟩) (w : ⟨ 𝔻 ⟩) → R δ n s w → R δ (k + n) (εs k n s) w
R-εs δ zero n s w h = h
R-εs δ (succ k) n s w h = R-ε δ (k + n) (εs k n s) w (R-εs δ k n s w h)

{- The relations between values: every approximation of a is related to w ---------}

record Rel (δ : Dir) (a w : ⟨ 𝔻 ⟩) : 𝓤₁ ̇ where
  constructor rel
  field stage : (n : ℕ) → R δ n (π∞ n · a) w
open Rel public

{- an approximation related at its stage is related -}
Rel-ε : ∀ {δ} (n : ℕ) {s : ⟨ 𝓓 n ⟩} {w : ⟨ 𝔻 ⟩} → R δ n s w → Rel δ (ε∞ n · s) w
Rel-ε {δ} n {s} {w} h = rel λ m → go m (split m n)
 where
  down : (m k n : ℕ) → n ＝ k + m → (s : ⟨ 𝓓 n ⟩) → R δ n s w → R δ m (π∞ m · (ε∞ n · s)) w
  down m k .(k + m) refl s h = transport (λ - → R δ m - w) (π∞-ε∞-down k m s ⁻¹) (R-πs δ k m s w h)
  up : (k m : ℕ) → m ＝ k + n → R δ m (π∞ m · (ε∞ n · s)) w
  up k .(k + n) refl = transport (λ - → R δ (k + n) - w) (π∞-ε∞-up k n s ⁻¹) (R-εs δ k n s w h)
  go : (m : ℕ) → Split m n → R δ m (π∞ m · (ε∞ n · s)) w
  go m (lower k e) = down m k n e s h
  go m (higher k e) = up k m e

{- Making and taking apart related values ------------------------------------------}

{- the approximation of depth n of a payload -}
approx : (n : ℕ) (t : Tag) → ⟨ obj (Payload t) 𝔻 ⟩ → ⟨ obj (Payload t) (𝓓 n) ⟩
approx n t x = fmap (Payload t) 𝔻 (𝓓 n) (π∞ n) (ε∞ n) x

{- related payloads at every depth, of values made with tags -}
Rel-inj : ∀ {δ t t'} (x : ⟨ obj (Payload t) 𝔻 ⟩) (y : ⟨ obj (Payload t') 𝔻 ⟩) (e : Same δ t t')
  → ((n : ℕ) → M δ n e (approx n t x) y) → Rel δ (inj t · x) (inj t' · y)
Rel-inj {δ} {t} {t'} x y e h = rel λ
  { zero → ⋆
  ; (succ n) → transport (λ - → R δ (succ n) - (inj t' · y)) (π∞-inj n t x ⁻¹)
                 (λ p → defined-inj t' y , transport (Match δ n (t , approx n t x)) (view-inj t' y (defined-inj t' y) ⁻¹) (e , h n)) }

{- only a defined approximated value needs to be related -}
Rel-from-defined : ∀ {δ a w} → (defined a → Rel δ a w) → Rel δ a w
Rel-from-defined {a = a} h = rel λ { zero → ⋆ ; (succ n) p → stage (h (π∞-defined n a p)) (succ n) p }

Rel-⊥ : ∀ {δ w} → Rel δ ⊥𝔻 w
Rel-⊥ = Rel-from-defined (λ q → 𝟘-elim (⊥-undefined q))

{- the other value of a defined one is defined -}
Rel-defined : ∀ {δ a w} → Rel δ a w → defined a → defined w
Rel-defined {a = a} h q = pr₁ (stage h 1 (defined-π∞ 0 a q))

{- the tags and payloads of the other value of one made with a tag -}
Rel-view : ∀ {δ t w} (x : ⟨ obj (Payload t) 𝔻 ⟩) → Rel δ (inj t · x) w → (q : defined w)
  → (n : ℕ) → Match δ n (t , approx n t x) (view w q)
Rel-view {δ} {t} {w} x h q n =
  transport (λ q' → Match δ n (t , approx n t x) (view w q')) (defined-is-prop w _ q)
    (pr₂ (transport (λ - → R δ (succ n) - w) (π∞-inj n t x) (stage h (succ n)) ⋆))

{- so related values, with a defined approximated one, are made with tags
   whose payloads are related -}
Rel-cases : ∀ {δ a w} → Rel δ a w → defined a → (P : ⟨ 𝔻 ⟩ → ⟨ 𝔻 ⟩ → 𝓤₁ ̇ )
  → (∀ {t t'} (x : ⟨ obj (Payload t) 𝔻 ⟩) (y : ⟨ obj (Payload t') 𝔻 ⟩) (e : Same δ t t')
       → ((n : ℕ) → M δ n e (approx n t x) y) → P (inj t · x) (inj t' · y))
  → P a w
Rel-cases {δ} {a} {w} h q P k =
  transport₂ P (inj-view a q ⁻¹) (inj-view w q' ⁻¹)
    (k (pr₂ (view a q)) (pr₂ (view w q')) (pr₁ (V 0)) (λ n → M-at (pr₁ (V 0)) (V n)))
 where
  q' = Rel-defined h q
  V = Rel-view (pr₂ (view a q)) (transport (λ - → Rel δ - w) (inj-view a q) h) q'

{- seq -}
Rel-seq : ∀ {δ d d' e e'} → Rel δ d d' → Rel δ e e' → Rel δ (seq · d · e) (seq · d' · e')
Rel-seq {δ} {d} {d'} {e} {e'} hd he =
  Rel-from-defined λ q →
    transport₂ (Rel δ) (seq-defined d e (seq-defined-l d e q) ⁻¹)
                       (seq-defined d' e' (Rel-defined hd (seq-defined-l d e q)) ⁻¹) he

{- an approximated value guarded by seq -}
Rel-seq-l : ∀ {δ d a w} → Rel δ a w → Rel δ (seq · d · a) w
Rel-seq-l {δ} {d} {a} {w} h =
  Rel-from-defined λ q → transport (λ - → Rel δ - w) (seq-defined d a (seq-defined-l d a q) ⁻¹) h

{- Constants, tuples, injections -}

Rel-const : ∀ {δ} B c → Rel δ (const B c) (const B c)
Rel-const B c = Rel-inj ⋆ ⋆ s-con (λ n → ⋆)

Rel-unit : ∀ {δ} → Rel δ unit unit
Rel-unit = Rel-inj (λ ()) (λ ()) s-tup (λ n ())

Rel-tuple : ∀ {δ} (k : ℕ) {ds ds' : Fin k → ⟨ 𝔻 ⟩} → ((i : Fin k) → Rel δ (ds i) (ds' i))
  → Rel δ (tupleᵈ k · ds) (tupleᵈ k · ds')
Rel-tuple {δ} k {ds} {ds'} h =
  Rel-from-defined λ q →
    transport₂ (Rel δ) (guard-defined k ds (tuple-defined← k ds q) (inj (tup k) · ds) ⁻¹)
                       (guard-defined k ds' (λ i → Rel-defined (h i) (tuple-defined← k ds q i)) (inj (tup k) · ds') ⁻¹)
      (Rel-inj ds ds' s-tup (λ n i → stage (h i) n))

Rel-inl : ∀ {δ d d'} → Rel δ d d' → Rel δ (inlᵈ · d) (inlᵈ · d')
Rel-inl {d = d} {d'} h = Rel-seq h (Rel-inj d d' s-left (stage h))

Rel-inr : ∀ {δ d d'} → Rel δ d d' → Rel δ (inrᵈ · d) (inrᵈ · d')
Rel-inr {d = d} {d'} h = Rel-seq h (Rel-inj d d' s-right (stage h))

{- Components of tuples -}

Rel-proj : ∀ {δ} {k : ℕ} (i : Fin k) {d d' : ⟨ 𝔻 ⟩} → Rel δ d d' → Rel δ (proj i · d) (proj i · d')
Rel-proj {δ} {k} i {d} h =
  Rel-from-defined λ q →
    Rel-cases h (proj-defined i d q) (λ a b → Rel δ (proj i · a) (proj i · b))
      (λ {t} {t'} x y e m → transport₂ (Rel δ) (case-inj 𝔻⊥ (proj-br i) t x ⁻¹) (case-inj 𝔻⊥ (proj-br i) t' y ⁻¹) (br-ok x y e m))
 where
  br-ok : ∀ {t t'} (x : ⟨ obj (Payload t) 𝔻 ⟩) (y : ⟨ obj (Payload t') 𝔻 ⟩) (e : Same δ t t')
    → ((n : ℕ) → M δ n e (approx n t x) y) → Rel δ (proj-br i t · x) (proj-br i t' · y)
  br-ok {tup j} xs ys s-tup m = at-ok (j Nat.≟ k)
   where
    at-ok : (q : Dec (j Eq.≡ k)) → Rel δ (at-tup j k i q · xs) (at-tup j k i q · ys)
    at-ok (yes Eq.refl) = rel λ n → m n i
    at-ok (no _) = Rel-⊥
  br-ok x y s-con m = Rel-⊥
  br-ok x y s-left m = Rel-⊥
  br-ok x y s-right m = Rel-⊥
  br-ok x y s-fun m = Rel-⊥
  br-ok x y s-pr m = Rel-⊥

{- Cases: related branches give related results -}

Rel-case : ∀ {δ d d'} (f g f' g' : DCPO[ 𝔻 , 𝔻 ]) → Rel δ d d'
  → (∀ {a a'} → Rel δ a a' → Rel δ (f · a) (f' · a'))
  → (∀ {a a'} → Rel δ a a' → Rel δ (g · a) (g' · a'))
  → Rel δ (cases · d · (strict · f , strict · g)) (cases · d' · (strict · f' , strict · g'))
Rel-case {δ} {d} f g f' g' h hf hg =
  Rel-from-defined λ q →
    Rel-cases h (cases-defined d b q) (λ u v → Rel δ (cases · u · b) (cases · v · b'))
      (λ {t} {t'} x y e m → transport₂ (Rel δ) (ap (_· b) (case-inj (Br ⟹𝔻) cases-br t x) ⁻¹)
                                               (ap (_· b') (case-inj (Br ⟹𝔻) cases-br t' y) ⁻¹)
                              (br-ok x y e m))
 where
  b = (strict · f , strict · g)
  b' = (strict · f' , strict · g')
  br-ok : ∀ {t t'} (x : ⟨ obj (Payload t) 𝔻 ⟩) (y : ⟨ obj (Payload t') 𝔻 ⟩) (e : Same δ t t')
    → ((n : ℕ) → M δ n e (approx n t x) y) → Rel δ (cases-br t · x · b) (cases-br t' · y · b')
  br-ok x y s-left m = Rel-seq (rel m) (hf (rel m))
  br-ok x y s-right m = Rel-seq (rel m) (hg (rel m))
  br-ok x y s-con m = Rel-⊥
  br-ok x y s-tup m = Rel-⊥
  br-ok x y s-fun m = Rel-⊥
  br-ok x y s-pr m = Rel-⊥

{- Primitives -}

Rel-out : ∀ {δ} (o : Out) → Rel δ (out o) (out o)
Rel-out (int z) = Rel-const Int z
Rel-out (bool true) = Rel-inl Rel-unit
Rel-out (bool false) = Rel-inr Rel-unit

Rel-prim : ∀ {δ} (p : Prim) {d d' e e' : ⟨ 𝔻 ⟩} → Rel δ d d' → Rel δ e e' → Rel δ (primD p · d · e) (primD p · d' · e')
Rel-prim {δ} p {d} {d'} {e} {e'} hd he =
  Rel-from-defined λ q →
    Rel-cases hd (primD-defined₁ p d e q) (λ u v → Rel δ (primD p · u · e) (primD p · v · e'))
      (λ {t} {t'} x y s m → transport₂ (Rel δ) (ap (_· e) (case-inj (𝔻 ⟹𝔻) (prim-br₁ p) t x) ⁻¹)
                                               (ap (_· e') (case-inj (𝔻 ⟹𝔻) (prim-br₁ p) t' y) ⁻¹)
                              (br₁-ok x y s))
 where
  br₂-ok : (z : ℤ) {t t' : Tag} (x : ⟨ obj (Payload t) 𝔻 ⟩) (y : ⟨ obj (Payload t') 𝔻 ⟩) → Same δ t t'
    → Rel δ (prim-br₂ p z t · x) (prim-br₂ p z t' · y)
  br₂-ok z x y (s-con {B = Int} {w}) = Rel-out (δᵖ p z w)
  br₂-ok z x y (s-con {B = Nat}) = Rel-⊥
  br₂-ok z x y (s-con {B = 𝔹}) = Rel-⊥
  br₂-ok z x y (s-con {B = Unit}) = Rel-⊥
  br₂-ok z x y (s-con {B = Void}) = Rel-⊥
  br₂-ok z x y (s-con {B = Blame}) = Rel-⊥
  br₂-ok z x y s-tup = Rel-⊥
  br₂-ok z x y s-left = Rel-⊥
  br₂-ok z x y s-right = Rel-⊥
  br₂-ok z x y s-fun = Rel-⊥
  br₂-ok z x y s-pr = Rel-⊥

  br₁-ok : ∀ {t t'} (x : ⟨ obj (Payload t) 𝔻 ⟩) (y : ⟨ obj (Payload t') 𝔻 ⟩) → Same δ t t'
    → Rel δ (prim-br₁ p t · x · e) (prim-br₁ p t' · y · e')
  br₁-ok x y (s-con {B = Int} {z}) =
    Rel-from-defined λ q →
      Rel-cases he (case-defined (prim-br₂ p z) e q) (λ u v → Rel δ (case 𝔻⊥ (prim-br₂ p z) · u) (case 𝔻⊥ (prim-br₂ p z) · v))
        (λ {t} {t'} x y s m → transport₂ (Rel δ) (case-inj 𝔻⊥ (prim-br₂ p z) t x ⁻¹) (case-inj 𝔻⊥ (prim-br₂ p z) t' y ⁻¹)
                                (br₂-ok z x y s))
  br₁-ok x y (s-con {B = Nat}) = Rel-⊥
  br₁-ok x y (s-con {B = 𝔹}) = Rel-⊥
  br₁-ok x y (s-con {B = Unit}) = Rel-⊥
  br₁-ok x y (s-con {B = Void}) = Rel-⊥
  br₁-ok x y (s-con {B = Blame}) = Rel-⊥
  br₁-ok x y s-tup = Rel-⊥
  br₁-ok x y s-left = Rel-⊥
  br₁-ok x y s-right = Rel-⊥
  br₁-ok x y s-fun = Rel-⊥
  br₁-ok x y s-pr = Rel-⊥

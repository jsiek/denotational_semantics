{-

  Correctness of delay (Clos3μ → Clos4μ) in Scott domains, the backward
  half: what the compiled program produces, the source produces too.

  The relation is the mirror image of DelayPreserve.agda's: it relates a
  whole source value d to an approximation k of depth n of the target
  value (Rf n d k), by recursion on the stage n, and says that what k
  shows of the target, d has. A source function is related to a target
  pair (c , e) when calls of the pair, on arguments related to the
  source's arguments, give results related to the source's results.
  Seen in an approximation of depth m + 2, a call of the pair shows its
  result at depth m only (callₛ, proof/Framework/Scott/StageCall.agda:
  the code and the environment are one and two levels down the
  approximation), so the clause for pairs at depth m + 2 speaks of
  depth m, and depths 0 and 1 show nothing of a call.

  The relation is downward closed and admissible in the target (Rf-mono,
  Rf-sup), and survives moving between stages (Rf-π, Rf-ε: a call of a
  closure approximated less is below, or equal to, the approximation of
  the call). Values are related (Refl) when the source is related to
  every approximation of the target. The fundamental lemma is in
  DelayReflectTerms.agda.

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
open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (_+_)
import Data.Nat as Nat
open import Relation.Nullary using (Dec; yes; no)
import Relation.Binary.PropositionalEquality as Eq

module Mu.proof.Correctness.Scott.DelayReflect
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
open import proof.Framework.Scott.StageCall pt fe pe
open import proof.Framework.Scott.Values pt fe pe
open import proof.Framework.Scott.Semantics pt fe pe
open import Semantics.Scott.Prim pt fe pe using (primD; out; prim-br₁; prim-br₂)

{- the call of a target closure, a pair cd of code and environment -}
call : (Fin 2 → ⟨ 𝔻 ⟩) → ⟨ 𝔻 ⟩ → ⟨ 𝔻 ⟩
call cd a = appᵈ · (appᵈ · cd zero · cd (suc zero)) · a

{- The relation, by stages --------------------------------------------------------}

Rf : (n : ℕ) → ⟨ 𝔻 ⟩ → ⟨ 𝓓 n ⟩ → 𝓤₁ ̇
MatchR : (n : ℕ) (t t' : Tag) → ⟨ obj (Payload t) 𝔻 ⟩ → ⟨ obj (Payload t') (𝓓 n) ⟩ → 𝓤₁ ̇
Call : (n : ℕ) → DCPO[ 𝔻 , 𝔻 ] → (Fin 2 → ⟨ 𝓓 n ⟩) → 𝓤₁ ̇

Rf zero d k = 𝟙
Rf (succ n) d k = (p : is-defined k) → Σ q ꞉ defined d ,
  MatchR n (pr₁ (view d q)) (pr₁ (value k p)) (pr₂ (view d q)) (pr₂ (value k p))

MatchR n (con B c) (con B' c') x y = (con B c ＝ con B' c') × 𝟙 {𝓤₁}
MatchR n (tup j) (tup j') xs ys = Σ e ꞉ j ＝ j' , ((i : Fin j) → Rf n (xs i) (ys (transport Fin e i)))
MatchR n left left x y = Rf n x y
MatchR n right right x y = Rf n x y
MatchR n fun pr s cd = Call n s cd
MatchR n (con B c) _ x y = 𝟘
MatchR n (tup j) _ xs ys = 𝟘
MatchR n left _ x y = 𝟘
MatchR n right _ x y = 𝟘
MatchR n fun _ s y = 𝟘
MatchR n pr _ x y = 𝟘

Call zero s cd = 𝟙
Call (succ zero) s cd = 𝟙
Call (succ (succ m)) s cd = (a : ⟨ 𝔻 ⟩) (v : ⟨ 𝓓 m ⟩) → Rf m a v → Rf m (strict · s · a) (callₛ m cd v)

Rf-prop : (n : ℕ) (d : ⟨ 𝔻 ⟩) (k : ⟨ 𝓓 n ⟩) → is-prop (Rf n d k)
MatchR-prop : (n : ℕ) (t t' : Tag) (x : ⟨ obj (Payload t) 𝔻 ⟩) (y : ⟨ obj (Payload t') (𝓓 n) ⟩) → is-prop (MatchR n t t' x y)
Call-prop : (n : ℕ) (s : DCPO[ 𝔻 , 𝔻 ]) (cd : Fin 2 → ⟨ 𝓓 n ⟩) → is-prop (Call n s cd)

Rf-prop zero d k = 𝟙-is-prop
Rf-prop (succ n) d k = Π-is-prop fe (λ p → Σ-is-prop (defined-is-prop d) (λ q →
  MatchR-prop n (pr₁ (view d q)) (pr₁ (value k p)) (pr₂ (view d q)) (pr₂ (value k p))))

MatchR-prop n (con B c) (con B' c') x y = ×-is-prop K-is-set 𝟙-is-prop
MatchR-prop n (tup j) (tup j') xs ys = Σ-is-prop K-is-set (λ e → Π-is-prop fe (λ i → Rf-prop n (xs i) (ys (transport Fin e i))))
MatchR-prop n left left x y = Rf-prop n x y
MatchR-prop n right right x y = Rf-prop n x y
MatchR-prop n fun pr s cd = Call-prop n s cd
MatchR-prop n (con B c) (tup k') x y = 𝟘-is-prop
MatchR-prop n (con B c) left x y = 𝟘-is-prop
MatchR-prop n (con B c) right x y = 𝟘-is-prop
MatchR-prop n (con B c) fun x y = 𝟘-is-prop
MatchR-prop n (con B c) pr x y = 𝟘-is-prop
MatchR-prop n (tup j) (con B' c') x y = 𝟘-is-prop
MatchR-prop n (tup j) left x y = 𝟘-is-prop
MatchR-prop n (tup j) right x y = 𝟘-is-prop
MatchR-prop n (tup j) fun x y = 𝟘-is-prop
MatchR-prop n (tup j) pr x y = 𝟘-is-prop
MatchR-prop n left (con B' c') x y = 𝟘-is-prop
MatchR-prop n left (tup k') x y = 𝟘-is-prop
MatchR-prop n left right x y = 𝟘-is-prop
MatchR-prop n left fun x y = 𝟘-is-prop
MatchR-prop n left pr x y = 𝟘-is-prop
MatchR-prop n right (con B' c') x y = 𝟘-is-prop
MatchR-prop n right (tup k') x y = 𝟘-is-prop
MatchR-prop n right left x y = 𝟘-is-prop
MatchR-prop n right fun x y = 𝟘-is-prop
MatchR-prop n right pr x y = 𝟘-is-prop
MatchR-prop n fun (con B' c') x y = 𝟘-is-prop
MatchR-prop n fun (tup k') x y = 𝟘-is-prop
MatchR-prop n fun left x y = 𝟘-is-prop
MatchR-prop n fun right x y = 𝟘-is-prop
MatchR-prop n fun fun x y = 𝟘-is-prop
MatchR-prop n pr t' x y = 𝟘-is-prop

Call-prop zero s cd = 𝟙-is-prop
Call-prop (succ zero) s cd = 𝟙-is-prop
Call-prop (succ (succ m)) s cd = Π-is-prop fe (λ a → Π-is-prop fe (λ v → Π-is-prop fe (λ _ → Rf-prop m (strict · s · a) (callₛ m cd v))))

{- Downward closed in the target -}

Rf-mono : (n : ℕ) (d : ⟨ 𝔻 ⟩) (k k' : ⟨ 𝓓 n ⟩) → k' ⊑⟨ 𝓓 n ⟩ k → Rf n d k → Rf n d k'
MatchR-mono : (n : ℕ) (t t' : Tag) (x : ⟨ obj (Payload t) 𝔻 ⟩) (y y' : ⟨ obj (Payload t') (𝓓 n) ⟩)
  → y' ⊑⟨ obj (Payload t') (𝓓 n) ⟩ y → MatchR n t t' x y → MatchR n t t' x y'
MatchR-mono-Σ : (n : ℕ) (t : Tag) (x : ⟨ obj (Payload t) 𝔻 ⟩) (v v' : ⟨ obj Val (𝓓 n) ⟩)
  → v' ⊑⟨ obj Val (𝓓 n) ⟩ v → MatchR n t (pr₁ v) x (pr₂ v) → MatchR n t (pr₁ v') x (pr₂ v')
Call-mono : (n : ℕ) (s : DCPO[ 𝔻 , 𝔻 ]) (cd cd' : Fin 2 → ⟨ 𝓓 n ⟩)
  → ((i : Fin 2) → cd' i ⊑⟨ 𝓓 n ⟩ cd i) → Call n s cd → Call n s cd'

Rf-mono zero d k k' le h = ⋆
Rf-mono (succ n) d k k' (f , g) h p' =
  pr₁ (h (f p')) ,
  MatchR-mono-Σ n (pr₁ (view d (pr₁ (h (f p'))))) (pr₂ (view d (pr₁ (h (f p'))))) (value k (f p')) (value k' p')
    (g p') (pr₂ (h (f p')))

MatchR-mono-Σ n t x (t' , y) (.t' , y') (refl , le) m = MatchR-mono n t t' x y y' le m

MatchR-mono n (con B c) (con B' c') x y y' le m = m
MatchR-mono n (tup j) (tup j') xs ys ys' le (e , m) = e , (λ i → Rf-mono n (xs i) (ys (transport Fin e i)) (ys' (transport Fin e i)) (le (transport Fin e i)) (m i))
MatchR-mono n left left x y y' le m = Rf-mono n x y y' le m
MatchR-mono n right right x y y' le m = Rf-mono n x y y' le m
MatchR-mono n fun pr s cd cd' le m = Call-mono n s cd cd' le m
MatchR-mono n (con B c) (tup k') x y y' le ()
MatchR-mono n (con B c) left x y y' le ()
MatchR-mono n (con B c) right x y y' le ()
MatchR-mono n (con B c) fun x y y' le ()
MatchR-mono n (con B c) pr x y y' le ()
MatchR-mono n (tup j) (con B' c') x y y' le ()
MatchR-mono n (tup j) left x y y' le ()
MatchR-mono n (tup j) right x y y' le ()
MatchR-mono n (tup j) fun x y y' le ()
MatchR-mono n (tup j) pr x y y' le ()
MatchR-mono n left (con B' c') x y y' le ()
MatchR-mono n left (tup k') x y y' le ()
MatchR-mono n left right x y y' le ()
MatchR-mono n left fun x y y' le ()
MatchR-mono n left pr x y y' le ()
MatchR-mono n right (con B' c') x y y' le ()
MatchR-mono n right (tup k') x y y' le ()
MatchR-mono n right left x y y' le ()
MatchR-mono n right fun x y y' le ()
MatchR-mono n right pr x y y' le ()
MatchR-mono n fun (con B' c') x y y' le ()
MatchR-mono n fun (tup k') x y y' le ()
MatchR-mono n fun left x y y' le ()
MatchR-mono n fun right x y y' le ()
MatchR-mono n fun fun x y y' le ()
MatchR-mono n pr t' x y y' le ()

Call-mono zero s cd cd' le h = ⋆
Call-mono (succ zero) s cd cd' le h = ⋆
Call-mono (succ (succ m)) s cd cd' le h a v r =
  Rf-mono m (strict · s · a) (callₛ m cd v) (callₛ m cd' v) (callₛ-mono m cd' cd v le) (h a v r)

{- Admissible: closed under directed sups in the target -}

Rf-sup : (n : ℕ) (d : ⟨ 𝔻 ⟩) {I : 𝓤₀ ̇ } (α : I → ⟨ 𝓓 n ⟩) (δ : is-Directed (𝓓 n) α)
  → ((i : I) → Rf n d (α i)) → Rf n d (∐ (𝓓 n) {I} {α} δ)
MatchR-sup : (n : ℕ) (t t' : Tag) (x : ⟨ obj (Payload t) 𝔻 ⟩) {I : 𝓤₀ ̇ } (β : I → ⟨ obj (Payload t') (𝓓 n) ⟩)
  (δ : is-Directed (obj (Payload t') (𝓓 n)) β) → ((i : I) → MatchR n t t' x (β i)) → MatchR n t t' x (∐ (obj (Payload t') (𝓓 n)) {I} {β} δ)
Call-sup : (n : ℕ) (s : DCPO[ 𝔻 , 𝔻 ]) {I : 𝓤₀ ̇ } (β : I → Fin 2 → ⟨ 𝓓 n ⟩) (δ : is-Directed (Pow (Fin 2) (𝓓 n)) β)
  → ((i : I) → Call n s (β i)) → Call n s (∐ (Pow (Fin 2) (𝓓 n)) {I} {β} δ)

Rf-sup zero d α δ h = ⋆
Rf-sup (succ n) d {I} α δ h = stage-sup-ind n α δ Q Q-sup h
 where
  M : defined d → (v : ⟨ obj Val (𝓓 n) ⟩) → 𝓤₁ ̇
  M q v = MatchR n (pr₁ (view d q)) (pr₁ v) (pr₂ (view d q)) (pr₂ v)
  Q : ⟨ obj Val (𝓓 n) ⟩ → 𝓤₁ ̇
  Q v = Σ q ꞉ defined d , M q v
  Q-prop : (v : ⟨ obj Val (𝓓 n) ⟩) → is-prop (Q v)
  Q-prop v = Σ-is-prop (defined-is-prop d) (λ q → MatchR-prop n (pr₁ (view d q)) (pr₁ v) (pr₂ (view d q)) (pr₂ v))
  Q-sup : {K : 𝓤₀ ̇ } (γ : K → ⟨ obj Val (𝓓 n) ⟩) (ε : is-Directed (obj Val (𝓓 n)) γ) → ((k : K) → Q (γ k))
        → Q (∐ (obj Val (𝓓 n)) {K} {γ} ε)
  Q-sup {K} γ ε hγ = ∥∥-rec (Q-prop (∐ (obj Val (𝓓 n)) {K} {γ} ε)) step (pr₁ ε)
   where
    step : K → Q (∐ (obj Val (𝓓 n)) {K} {γ} ε)
    step k = q , Σ-sup-ind Tag Tag-is-set (λ t → obj (Payload t) (𝓓 n))
                  (λ t' y → MatchR n (pr₁ (view d q)) t' (pr₂ (view d q)) y)
                  (λ t' β' δ' → MatchR-sup n (pr₁ (view d q)) t' (pr₂ (view d q)) β' δ')
                  γ ε
                  (λ k' → transport (λ q' → M q' (γ k')) (defined-is-prop d (pr₁ (hγ k')) q) (pr₂ (hγ k')))
     where
      q = pr₁ (hγ k)

MatchR-sup n (con B c) (con B' c') x β δ h = ∥∥-rec (MatchR-prop n (con B c) (con B' c') x (∐ (obj (Payload (con B' c')) (𝓓 n)) {_} {β} δ)) h (pr₁ δ)
MatchR-sup n (tup j) (tup j') xs β δ h =
  ∥∥-rec (MatchR-prop n (tup j) (tup j') xs (∐ (obj (Payload (tup j')) (𝓓 n)) {_} {β} δ))
    (λ i₀ → pr₁ (h i₀) , (λ idx → Rf-sup n (xs idx) (λ i → β i (transport Fin (pr₁ (h i₀)) idx))
       (component-is-directed (Fin j') (𝓓 n) β δ (transport Fin (pr₁ (h i₀)) idx))
       (λ i → transport (λ e → Rf n (xs idx) (β i (transport Fin e idx))) (K-is-set (pr₁ (h i)) (pr₁ (h i₀))) (pr₂ (h i) idx))))
    (pr₁ δ)
MatchR-sup n left left x β δ h = Rf-sup n x β δ h
MatchR-sup n right right x β δ h = Rf-sup n x β δ h
MatchR-sup n fun pr s β δ h = Call-sup n s β δ h
MatchR-sup n (con B c) (tup k') x β δ h = ∥∥-rec 𝟘-is-prop h (pr₁ δ)
MatchR-sup n (con B c) left x β δ h = ∥∥-rec 𝟘-is-prop h (pr₁ δ)
MatchR-sup n (con B c) right x β δ h = ∥∥-rec 𝟘-is-prop h (pr₁ δ)
MatchR-sup n (con B c) fun x β δ h = ∥∥-rec 𝟘-is-prop h (pr₁ δ)
MatchR-sup n (con B c) pr x β δ h = ∥∥-rec 𝟘-is-prop h (pr₁ δ)
MatchR-sup n (tup j) (con B' c') x β δ h = ∥∥-rec 𝟘-is-prop h (pr₁ δ)
MatchR-sup n (tup j) left x β δ h = ∥∥-rec 𝟘-is-prop h (pr₁ δ)
MatchR-sup n (tup j) right x β δ h = ∥∥-rec 𝟘-is-prop h (pr₁ δ)
MatchR-sup n (tup j) fun x β δ h = ∥∥-rec 𝟘-is-prop h (pr₁ δ)
MatchR-sup n (tup j) pr x β δ h = ∥∥-rec 𝟘-is-prop h (pr₁ δ)
MatchR-sup n left (con B' c') x β δ h = ∥∥-rec 𝟘-is-prop h (pr₁ δ)
MatchR-sup n left (tup k') x β δ h = ∥∥-rec 𝟘-is-prop h (pr₁ δ)
MatchR-sup n left right x β δ h = ∥∥-rec 𝟘-is-prop h (pr₁ δ)
MatchR-sup n left fun x β δ h = ∥∥-rec 𝟘-is-prop h (pr₁ δ)
MatchR-sup n left pr x β δ h = ∥∥-rec 𝟘-is-prop h (pr₁ δ)
MatchR-sup n right (con B' c') x β δ h = ∥∥-rec 𝟘-is-prop h (pr₁ δ)
MatchR-sup n right (tup k') x β δ h = ∥∥-rec 𝟘-is-prop h (pr₁ δ)
MatchR-sup n right left x β δ h = ∥∥-rec 𝟘-is-prop h (pr₁ δ)
MatchR-sup n right fun x β δ h = ∥∥-rec 𝟘-is-prop h (pr₁ δ)
MatchR-sup n right pr x β δ h = ∥∥-rec 𝟘-is-prop h (pr₁ δ)
MatchR-sup n fun (con B' c') x β δ h = ∥∥-rec 𝟘-is-prop h (pr₁ δ)
MatchR-sup n fun (tup k') x β δ h = ∥∥-rec 𝟘-is-prop h (pr₁ δ)
MatchR-sup n fun left x β δ h = ∥∥-rec 𝟘-is-prop h (pr₁ δ)
MatchR-sup n fun right x β δ h = ∥∥-rec 𝟘-is-prop h (pr₁ δ)
MatchR-sup n fun fun x β δ h = ∥∥-rec 𝟘-is-prop h (pr₁ δ)
MatchR-sup n pr t' x β δ h = ∥∥-rec 𝟘-is-prop h (pr₁ δ)

Call-sup zero s β δ h = ⋆
Call-sup (succ zero) s β δ h = ⋆
Call-sup (succ (succ m)) s {I} β δ h a v r =
  transport (λ - → Rf m (strict · s · a) -) (callᶜ-is m v (∐ (Pow (Fin 2) (𝓓 (succ (succ m)))) {I} {β} δ))
    (transport (λ - → Rf m (strict · s · a) -)
       (continuous-∐-＝ (Pow (Fin 2) (𝓓 (succ (succ m)))) (𝓓 m) (callᶜ m v) {I} {β} δ ⁻¹)
       (Rf-sup m (strict · s · a) (λ i → callᶜ m v · β i)
          (image-is-directed' (Pow (Fin 2) (𝓓 (succ (succ m)))) (𝓓 m) (callᶜ m v) {I} {β} δ)
          (λ i → transport (λ - → Rf m (strict · s · a) -) (callᶜ-is m v (β i) ⁻¹) (h i a v r))))

{- Moving between stages -}

Rf-π : (n : ℕ) (d : ⟨ 𝔻 ⟩) (k : ⟨ 𝓓 (succ n) ⟩) → Rf (succ n) d k → Rf n d (π n k)
Rf-ε : (n : ℕ) (d : ⟨ 𝔻 ⟩) (k : ⟨ 𝓓 n ⟩) → Rf n d k → Rf (succ n) d (ε n k)
MatchR-π : (n : ℕ) (t t' : Tag) (x : ⟨ obj (Payload t) 𝔻 ⟩) (y : ⟨ obj (Payload t') (𝓓 (succ n)) ⟩)
  → MatchR (succ n) t t' x y → MatchR n t t' x (fmap (Payload t') (𝓓 (succ n)) (𝓓 n) (π' n) (ε' n) y)
MatchR-ε : (n : ℕ) (t t' : Tag) (x : ⟨ obj (Payload t) 𝔻 ⟩) (y : ⟨ obj (Payload t') (𝓓 n) ⟩)
  → MatchR n t t' x y → MatchR (succ n) t t' x (fmap (Payload t') (𝓓 n) (𝓓 (succ n)) (ε' n) (π' n) y)
Call-π : (n : ℕ) (s : DCPO[ 𝔻 , 𝔻 ]) (cd : Fin 2 → ⟨ 𝓓 (succ n) ⟩) → Call (succ n) s cd → Call n s (λ i → π n (cd i))
Call-ε : (n : ℕ) (s : DCPO[ 𝔻 , 𝔻 ]) (cd : Fin 2 → ⟨ 𝓓 n ⟩) → Call n s cd → Call (succ n) s (λ i → ε n (cd i))

Rf-π zero d k h = ⋆
Rf-π (succ n) d k h = transport (λ - → Rf (succ n) d -) (π-succ n k ⁻¹) (λ p →
  pr₁ (h p) , MatchR-π n (pr₁ (view d (pr₁ (h p)))) (pr₁ (value k p)) (pr₂ (view d (pr₁ (h p)))) (pr₂ (value k p)) (pr₂ (h p)))

Rf-ε zero d k h p = 𝟘-elim (ε-zero-undefined k p)
Rf-ε (succ n) d k h = transport (λ - → Rf (succ (succ n)) d -) (ε-succ n k ⁻¹) (λ p →
  pr₁ (h p) , MatchR-ε n (pr₁ (view d (pr₁ (h p)))) (pr₁ (value k p)) (pr₂ (view d (pr₁ (h p)))) (pr₂ (value k p)) (pr₂ (h p)))

MatchR-π n (con B c) (con B' c') x y m = m
MatchR-π n (tup j) (tup j') xs ys (e , m) = e , (λ i → Rf-π n (xs i) (ys (transport Fin e i)) (m i))
MatchR-π n left left x y m = Rf-π n x y m
MatchR-π n right right x y m = Rf-π n x y m
MatchR-π n fun pr s cd m = Call-π n s cd m
MatchR-π n (con B c) (tup k') x y ()
MatchR-π n (con B c) left x y ()
MatchR-π n (con B c) right x y ()
MatchR-π n (con B c) fun x y ()
MatchR-π n (con B c) pr x y ()
MatchR-π n (tup j) (con B' c') x y ()
MatchR-π n (tup j) left x y ()
MatchR-π n (tup j) right x y ()
MatchR-π n (tup j) fun x y ()
MatchR-π n (tup j) pr x y ()
MatchR-π n left (con B' c') x y ()
MatchR-π n left (tup k') x y ()
MatchR-π n left right x y ()
MatchR-π n left fun x y ()
MatchR-π n left pr x y ()
MatchR-π n right (con B' c') x y ()
MatchR-π n right (tup k') x y ()
MatchR-π n right left x y ()
MatchR-π n right fun x y ()
MatchR-π n right pr x y ()
MatchR-π n fun (con B' c') x y ()
MatchR-π n fun (tup k') x y ()
MatchR-π n fun left x y ()
MatchR-π n fun right x y ()
MatchR-π n fun fun x y ()
MatchR-π n pr t' x y ()

MatchR-ε n (con B c) (con B' c') x y m = m
MatchR-ε n (tup j) (tup j') xs ys (e , m) = e , (λ i → Rf-ε n (xs i) (ys (transport Fin e i)) (m i))
MatchR-ε n left left x y m = Rf-ε n x y m
MatchR-ε n right right x y m = Rf-ε n x y m
MatchR-ε n fun pr s cd m = Call-ε n s cd m
MatchR-ε n (con B c) (tup k') x y ()
MatchR-ε n (con B c) left x y ()
MatchR-ε n (con B c) right x y ()
MatchR-ε n (con B c) fun x y ()
MatchR-ε n (con B c) pr x y ()
MatchR-ε n (tup j) (con B' c') x y ()
MatchR-ε n (tup j) left x y ()
MatchR-ε n (tup j) right x y ()
MatchR-ε n (tup j) fun x y ()
MatchR-ε n (tup j) pr x y ()
MatchR-ε n left (con B' c') x y ()
MatchR-ε n left (tup k') x y ()
MatchR-ε n left right x y ()
MatchR-ε n left fun x y ()
MatchR-ε n left pr x y ()
MatchR-ε n right (con B' c') x y ()
MatchR-ε n right (tup k') x y ()
MatchR-ε n right left x y ()
MatchR-ε n right fun x y ()
MatchR-ε n right pr x y ()
MatchR-ε n fun (con B' c') x y ()
MatchR-ε n fun (tup k') x y ()
MatchR-ε n fun left x y ()
MatchR-ε n fun right x y ()
MatchR-ε n fun fun x y ()
MatchR-ε n pr t' x y ()

Call-π zero s cd h = ⋆
Call-π (succ zero) s cd h = ⋆
Call-π (succ (succ m)) s cd h a v r =
  Rf-mono m (strict · s · a) (π m (callₛ (succ m) cd (ε m v))) (callₛ m (λ i → π (succ (succ m)) (cd i)) v)
    (callₛ-π m cd v) (Rf-π m (strict · s · a) (callₛ (succ m) cd (ε m v)) (h a (ε m v) (Rf-ε m a v r)))

Call-ε zero s cd h = ⋆
Call-ε (succ zero) s cd h a v r = ⋆
Call-ε (succ (succ m)) s cd h a w r =
  transport (λ - → Rf (succ m) (strict · s · a) -) (callₛ-ε m cd w ⁻¹)
    (Rf-ε m (strict · s · a) (callₛ m cd (π m w)) (h a (π m w) (Rf-π m a w r)))

Rf-πs : (k n : ℕ) (d : ⟨ 𝔻 ⟩) (x : ⟨ 𝓓 (k + n) ⟩) → Rf (k + n) d x → Rf n d (πs k n x)
Rf-πs zero n d x h = h
Rf-πs (succ k) n d x h = Rf-πs k n d (π (k + n) x) (Rf-π (k + n) d x h)

Rf-εs : (k n : ℕ) (d : ⟨ 𝔻 ⟩) (x : ⟨ 𝓓 n ⟩) → Rf n d x → Rf (k + n) d (εs k n x)
Rf-εs zero n d x h = h
Rf-εs (succ k) n d x h = Rf-ε (k + n) d (εs k n x) (Rf-εs k n d x h)

{- The relation between values: the source is related to every
   approximation of the target -}

Refl : ⟨ 𝔻 ⟩ → ⟨ 𝔻 ⟩ → 𝓤₁ ̇
Refl d d' = (n : ℕ) → Rf n d (π∞ n · d')

{- related to an approximation, related to its embedding -}
Refl-ε : (n : ℕ) (d : ⟨ 𝔻 ⟩) (x : ⟨ 𝓓 n ⟩) → Rf n d x → Refl d (ε∞ n · x)
Refl-ε n d x h m = go (split m n)
 where
  down : (k : ℕ) (n : ℕ) → n ＝ k + m → (x : ⟨ 𝓓 n ⟩) → Rf n d x → Rf m d (π∞ m · (ε∞ n · x))
  down k .(k + m) refl x h = transport (λ - → Rf m d -) (π∞-ε∞-down k m x ⁻¹) (Rf-πs k m d x h)
  up : (k : ℕ) (m : ℕ) → m ＝ k + n → Rf m d (π∞ m · (ε∞ n · x))
  up k .(k + n) refl = transport (λ - → Rf (k + n) d -) (π∞-ε∞-up k n x ⁻¹) (Rf-εs k n d x h)
  go : Split m n → Rf m d (π∞ m · (ε∞ n · x))
  go (lower k e) = down k n e x h
  go (higher k e) = up k m e

{- related to the target, related to its approximations -}
Refl-e : (n : ℕ) (d d' : ⟨ 𝔻 ⟩) → Refl d d' → Refl d (e n d')
Refl-e n d d' h = Refl-ε n d (π∞ n · d') (h n)

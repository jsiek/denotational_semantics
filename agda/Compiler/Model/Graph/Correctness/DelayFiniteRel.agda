{-

  A logical relation indexed by finite lists of observations from one side
  of the delay pass, generic in which side that is (see issue #1).

  R k V D relates a finite list V of values, from the side being simulated,
  to an arbitrary set D from the other side. It is defined by recursion on
  the depth of V, which we encode with fuel: R k V D only looks at the parts
  of V of depth < k, and R-irr shows that the fuel is irrelevant as long as
  it bounds the depth of V (Bnd k V).

  The parameters describe function application on each side:
  - Entry V U₀ w : V contains a function entry U₀ ↦ w,
  - D ⊚ E : application on the other side,
  - Good U : a side condition on the arguments (consistency, for reflect).

  From Entry we define, once for both sides, the batches of calls of V:
  Calls V U W says that each w in W is the result of a function entry
  U₀ ↦ w of V (with U₀ nonempty), and U is the union of those U₀. The
  function clause relates the arguments U of a batch to an argument set
  E on the other side, and the results W to the application D ⊚ E.

-}

open import SetsAsPredicates
open import Primitives
open import Compiler.Model.Graph.Domain.ISWIM.Domain
open import Compiler.Model.Graph.Correctness.DelayFiniteCommon

open import Data.Nat using (ℕ; zero; suc; _<_)
open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Membership.Propositional renaming (_∈_ to _⋵_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩ )
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit.Polymorphic using () renaming (tt to ptt; ⊤ to pTrue)
open import Relation.Binary.PropositionalEquality using (_≢_; refl)

module Compiler.Model.Graph.Correctness.DelayFiniteRel
  (Entry : List Value → List Value → Value → Set)
  (_⊚_ : 𝒫 Value → 𝒫 Value → 𝒫 Value)
  (Good : List Value → Set)
  (Entry-⊆ : ∀ {V₁ V₂ U₀ w} → mem V₁ ⊆ mem V₂ → Entry V₁ U₀ w → Entry V₂ U₀ w)
  (Entry-flat : ∀ {V U₀ w} → (∀ v → v ⋵ V → Flat v) → Entry V U₀ w → ⊥)
  (⊚-mono : ∀ {D₁ D₂ E} → D₁ ⊆ D₂ → (D₁ ⊚ E) ⊆ (D₂ ⊚ E))
  (Bnd-Entry : ∀ {k V U₀ w} → Bnd (suc k) V → Entry V U₀ w → Bnd k U₀ × depth w < k)
  where

{- Batches of calls of the functions in a finite list -------------------------}

{- Calls V U W: each w in W is the result of a function entry U₀ ↦ w of V,
   and U is the union of the (nonempty) arguments U₀ of those entries -}
infixr 5 _∷_
data Calls (V : List Value) : List Value → List Value → Set where
  [] : Calls V [] []
  _∷_ : ∀ {U₀ w U W} → Entry V U₀ w × U₀ ≢ [] → Calls V U W → Calls V (U₀ ++ U) (w ∷ W)

{- one call of a batch: w is the result of an entry U₀ ↦ w of V with U₀ ⊆ U -}
record Call (V U : List Value) (w : Value) : Set where
  constructor call
  field
    U₀ : List Value
    entry : Entry V U₀ w
    U₀≢[] : U₀ ≢ []
    U₀⊆ : mem U₀ ⊆ mem U

Calls-∈ : ∀ {V U W w} → Calls V U W → w ⋵ W → Call V U w
Calls-∈ (_∷_ {U₀ = U₀} ⟨ e , ne ⟩ cs) (here refl) = call U₀ e ne (λ d d∈ → ∈-++⁺ˡ d∈)
Calls-∈ (_∷_ {U₀ = U₀} _ cs) (there w∈) with Calls-∈ cs w∈
... | call U₁ e ne U₁⊆ = call U₁ e ne (λ d d∈ → ∈-++⁺ʳ U₀ (U₁⊆ d d∈))

Calls-⊆ : ∀ {V₁ V₂ U W} → mem V₁ ⊆ mem V₂ → Calls V₁ U W → Calls V₂ U W
Calls-⊆ s [] = []
Calls-⊆ s (⟨ e , ne ⟩ ∷ cs) = ⟨ Entry-⊆ s e , ne ⟩ ∷ Calls-⊆ s cs

{- a list without function entries makes no calls -}
Calls-none : ∀ {V U W} → (∀ {U₀ w} → Entry V U₀ w → ⊥) → Calls V U W → mem W ⊆ ∅
Calls-none no [] _ ()
Calls-none no (⟨ e , _ ⟩ ∷ _) _ _ = ⊥-elim (no e)

Calls-flat : ∀ {V U W} → (∀ v → v ⋵ V → Flat v) → Calls V U W → mem W ⊆ ∅
Calls-flat fl = Calls-none (Entry-flat fl)

Bnd-Calls-args : ∀ {k V U W} → Bnd (suc k) V → Calls V U W → Bnd k U
Bnd-Calls-args bV [] _ ()
Bnd-Calls-args bV (_∷_ {U₀ = U₀} ⟨ e , _ ⟩ cs) u u∈ with ∈-++⁻ U₀ u∈
... | inj₁ u∈U₀ = proj₁ (Bnd-Entry bV e) u u∈U₀
... | inj₂ u∈U = Bnd-Calls-args bV cs u u∈U

Bnd-Calls-apps : ∀ {k V U W} → Bnd (suc k) V → Calls V U W → Bnd k W
Bnd-Calls-apps bV [] _ ()
Bnd-Calls-apps bV (⟨ e , _ ⟩ ∷ cs) _ (here refl) = proj₂ (Bnd-Entry bV e)
Bnd-Calls-apps bV (_ ∷ cs) w (there w∈) = Bnd-Calls-apps bV cs w w∈

{- The relation ---------------------------------------------------------------}

record Obs (R : List Value → 𝒫 Value → Set₁) (V : List Value) (D : 𝒫 Value) : Set₁ where
  field
    const-obs : ∀ {B} (c : base-rep B) → const c ⋵ V → const c ∈ D
    ω-obs : ω ⋵ V → ω ∈ D
    nonempty-obs : V ≢ [] → nonempty D
    app-obs : ∀ {U W} → Calls V U W → ∀ E → Good U → R U E → R W (D ⊚ E)
    nth-obs : ∀ {n} (i : Fin n) W → mem W ⊆ Nths i V → R W (Nth i D)
    left-obs : ∀ W → mem W ⊆ Lefts' V → R W (Lefts D)
    right-obs : ∀ W → mem W ⊆ Rights' V → R W (Rights D)

R : ℕ → List Value → 𝒫 Value → Set₁
R zero V D = pTrue
R (suc k) V D = Obs (R k) V D

infix 4 _⊳ₑ_
_⊳ₑ_ : Env → Env → Set₁
ρ₁ ⊳ₑ ρ₂ = ∀ x V k → mem V ⊆ ρ₁ x → Bnd k V → R k V (ρ₂ x)

R-∅ : ∀ k {V D} → mem V ⊆ ∅ → R k V D
R-∅ zero _ = ptt
R-∅ (suc k) {V} V⊆∅ = record
  { const-obs = λ c c∈ → ⊥-elim (V⊆∅ _ c∈)
  ; ω-obs = λ ω∈ → ⊥-elim (V⊆∅ _ ω∈)
  ; nonempty-obs = λ ne → ⊥-elim (proj₂ (ne-mem ne V⊆∅))
  ; app-obs = λ cs E _ _ → R-∅ k (Calls-flat (λ v v∈ → ⊥-elim (V⊆∅ v v∈)) cs)
  ; nth-obs = λ i W W⊆ → R-∅ k (λ d d∈ → V⊆∅ _ (W⊆ d d∈))
  ; left-obs = λ W W⊆ → R-∅ k (λ d d∈ → V⊆∅ _ (W⊆ d d∈))
  ; right-obs = λ W W⊆ → R-∅ k (λ d d∈ → V⊆∅ _ (W⊆ d d∈))
  }

R-flat : ∀ k {V D} → mem V ⊆ D → (∀ v → v ⋵ V → Flat v) → R k V D
R-flat zero _ _ = ptt
R-flat (suc k) {V} V⊆ fl = record
  { const-obs = λ c c∈ → V⊆ _ c∈
  ; ω-obs = λ ω∈ → V⊆ ω ω∈
  ; nonempty-obs = λ ne → ne-mem ne V⊆
  ; app-obs = λ cs E _ _ → R-∅ k (Calls-flat fl cs)
  ; nth-obs = λ i W W⊆ → R-∅ k (λ d d∈ → flat-tup (fl _ (W⊆ d d∈)))
  ; left-obs = λ W W⊆ → R-∅ k (λ d d∈ → flat-left (fl _ (W⊆ d d∈)))
  ; right-obs = λ W W⊆ → R-∅ k (λ d d∈ → flat-right (fl _ (W⊆ d d∈)))
  }

{- antitone in the list of observations -}
R-⊆ : ∀ k {V₁ V₂ D} → mem V₁ ⊆ mem V₂ → R k V₂ D → R k V₁ D
R-⊆ zero _ _ = ptt
R-⊆ (suc k) {V₁}{V₂} V₁⊆V₂ r = record
  { const-obs = λ c c∈ → const-obs c (V₁⊆V₂ _ c∈)
  ; ω-obs = λ ω∈ → ω-obs (V₁⊆V₂ _ ω∈)
  ; nonempty-obs = λ ne → nonempty-obs (ne-⊆ V₁⊆V₂ ne)
  ; app-obs = λ cs → app-obs (Calls-⊆ V₁⊆V₂ cs)
  ; nth-obs = λ i W W⊆ → nth-obs i W (λ d d∈ → V₁⊆V₂ _ (W⊆ d d∈))
  ; left-obs = λ W W⊆ → left-obs W (λ d d∈ → V₁⊆V₂ _ (W⊆ d d∈))
  ; right-obs = λ W W⊆ → right-obs W (λ d d∈ → V₁⊆V₂ _ (W⊆ d d∈))
  }
  where open Obs r

{- monotone in the set on the other side -}
R-mono : ∀ k {V D₁ D₂} → D₁ ⊆ D₂ → R k V D₁ → R k V D₂
R-mono zero _ _ = ptt
R-mono (suc k) D⊆ r = record
  { const-obs = λ c c∈ → D⊆ _ (const-obs c c∈)
  ; ω-obs = λ ω∈ → D⊆ ω (ω-obs ω∈)
  ; nonempty-obs = λ ne → ⟨ proj₁ (nonempty-obs ne) , D⊆ _ (proj₂ (nonempty-obs ne)) ⟩
  ; app-obs = λ cs E gU rU → R-mono k (⊚-mono D⊆) (app-obs cs E gU rU)
  ; nth-obs = λ i W W⊆ → R-mono k (λ d → D⊆ (tup[ i ] d)) (nth-obs i W W⊆)
  ; left-obs = λ W W⊆ → R-mono k (λ d → D⊆ (left d)) (left-obs W W⊆)
  ; right-obs = λ W W⊆ → R-mono k (λ d → D⊆ (right d)) (right-obs W W⊆)
  }
  where open Obs r

{- the fuel is irrelevant once it bounds the depth of the observations -}
R-irr : ∀ k j {V D} → Bnd k V → Bnd j V → R k V D → R j V D
R-irr k zero _ _ _ = ptt
R-irr zero (suc j) bk _ _ = R-∅ (suc j) (λ v v∈ → <0 (bk v v∈))
R-irr (suc k) (suc j) bk bj r = record
  { const-obs = const-obs
  ; ω-obs = ω-obs
  ; nonempty-obs = nonempty-obs
  ; app-obs = λ cs E gU rU →
      R-irr k j (Bnd-Calls-apps bk cs) (Bnd-Calls-apps bj cs)
        (app-obs cs E gU (R-irr j k (Bnd-Calls-args bj cs) (Bnd-Calls-args bk cs) rU))
  ; nth-obs = λ i W W⊆ →
      R-irr k j (Bnd-Nths bk W⊆) (Bnd-Nths bj W⊆) (nth-obs i W W⊆)
  ; left-obs = λ W W⊆ →
      R-irr k j (Bnd-Lefts bk W⊆) (Bnd-Lefts bj W⊆) (left-obs W W⊆)
  ; right-obs = λ W W⊆ →
      R-irr k j (Bnd-Rights bk W⊆) (Bnd-Rights bj W⊆) (right-obs W W⊆)
  }
  where open Obs r

{- relating the initial environment of a closed program to itself -}
Init⊳Init : ρ₀ ⊳ₑ ρ₀
Init⊳Init x V k V⊆ bV = R-flat k V⊆ (λ v v∈ → Init-flat (V⊆ v v∈))

{-

  A logical relation indexed by finite lists of observations from one side
  of the delay pass, generic in which side that is (see issue #1).

  R k V D relates a finite list V of values, from the side being simulated,
  to an arbitrary set D from the other side. It is defined by recursion on
  the depth of V, which we encode with fuel: R k V D only looks at the parts
  of V of depth < k, and R-irr shows that the fuel is irrelevant as long as
  it bounds the depth of V (Bnd k V).

  The parameters describe function application on each side:
  - ArgsOf V : the arguments that the functions in V are prepared to accept,
  - AppsOf V U : the results of applying the functions in V to the list U,
  - D ⊚ E : application on the other side,
  - Good U : a side condition on the arguments (consistency, for reflect).

-}

open import SetsAsPredicates
open import Primitives
open import Compiler.Model.Graph.Domain.ISWIM.Domain
open import Compiler.Model.Graph.Correctness.DelayFiniteCommon

open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional renaming (_∈_ to _⋵_)
open import Data.Product using (proj₁; proj₂) renaming (_,_ to ⟨_,_⟩ )
open import Data.Empty using (⊥-elim)
open import Data.Unit.Polymorphic using () renaming (tt to ptt; ⊤ to pTrue)
open import Relation.Binary.PropositionalEquality using (_≢_)

module Compiler.Model.Graph.Correctness.DelayFiniteRel
  (ArgsOf : List Value → 𝒫 Value)
  (AppsOf : List Value → List Value → 𝒫 Value)
  (_⊚_ : 𝒫 Value → 𝒫 Value → 𝒫 Value)
  (Good : List Value → Set)
  (ArgsOf-⊆ : ∀ {V₁ V₂} → mem V₁ ⊆ mem V₂ → ArgsOf V₁ ⊆ ArgsOf V₂)
  (AppsOf-⊆ : ∀ {V₁ V₂ U} → mem V₁ ⊆ mem V₂ → AppsOf V₁ U ⊆ AppsOf V₂ U)
  (AppsOf-flat : ∀ {V U} → (∀ v → v ⋵ V → Flat v) → AppsOf V U ⊆ ∅)
  (⊚-mono : ∀ {D₁ D₂ E} → D₁ ⊆ D₂ → (D₁ ⊚ E) ⊆ (D₂ ⊚ E))
  (Bnd-ArgsOf : ∀ {k V U} → Bnd (suc k) V → mem U ⊆ ArgsOf V → Bnd k U)
  (Bnd-AppsOf : ∀ {k V U W} → Bnd (suc k) V → mem W ⊆ AppsOf V U → Bnd k W)
  where

record Obs (R : List Value → 𝒫 Value → Set₁) (V : List Value) (D : 𝒫 Value) : Set₁ where
  field
    const-obs : ∀ {B} (c : base-rep B) → const c ⋵ V → const c ∈ D
    ω-obs : ω ⋵ V → ω ∈ D
    nonempty-obs : V ≢ [] → nonempty D
    app-obs : ∀ U E → mem U ⊆ ArgsOf V → Good U → R U E
            → ∀ W → mem W ⊆ AppsOf V U → R W (D ⊚ E)
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
  ; app-obs = λ U E _ _ _ W W⊆ →
      R-∅ k (λ w w∈ → AppsOf-flat (λ v v∈ → ⊥-elim (V⊆∅ v v∈)) w (W⊆ w w∈))
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
  ; app-obs = λ U E _ _ _ W W⊆ → R-∅ k (λ w w∈ → AppsOf-flat fl w (W⊆ w w∈))
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
  ; app-obs = λ U E U⊆ gU rU W W⊆ →
      app-obs U E (λ u u∈ → ArgsOf-⊆ V₁⊆V₂ u (U⊆ u u∈)) gU rU W
              (λ w w∈ → AppsOf-⊆ V₁⊆V₂ w (W⊆ w w∈))
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
  ; app-obs = λ U E U⊆ gU rU W W⊆ →
      R-mono k (⊚-mono D⊆) (app-obs U E U⊆ gU rU W W⊆)
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
  ; app-obs = λ U E U⊆ gU rU W W⊆ →
      R-irr k j (Bnd-AppsOf bk W⊆) (Bnd-AppsOf bj W⊆)
        (app-obs U E U⊆ gU
           (R-irr j k (Bnd-ArgsOf bj U⊆) (Bnd-ArgsOf bk U⊆) rU) W W⊆)
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

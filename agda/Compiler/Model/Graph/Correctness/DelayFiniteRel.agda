{-

  The logical relation for the backward (reflect) direction of the delay
  pass, indexed by finite lists of target observations (see issue #1).

  R k V' D relates a finite list V' of target values to a source set D.
  It is defined by recursion on the depth of V', which we encode with
  fuel: R k V' D only looks at the parts of V' of depth < k, and R-irr
  shows that the fuel is irrelevant as long as it bounds the depth of V'
  (Bnd k V').

  A target closure is split into the car halves ⦅ FV ↦ (U₀ ↦ w) ∣ of its
  code and the cdr halves ∣ fv ⦆ of its environment. A call takes its
  code from car C and its free variables FV from cdr C separately, and FV
  is a finite set of observations, so a single target value says nothing
  about a call (this would be so even if pairs were single values). The function entries of V' (CarEntry)
  are the codes in the car halves of V' whose free variables FV are in
  the cdr halves of V'. Calls V' U W says that each w in W is the result
  of a function entry U₀ ↦ w of V' with U₀ ⊆ U, and that each u in U is
  an argument of a function entry of V' (so U is no deeper than V'). The
  function clause relates the arguments U of a batch to an argument set E
  of the source, and the results W to the source application D ● E.

-}

open import SetsAsPredicates
open import Primitives
open import Compiler.Model.Graph.Domain.ISWIM.Domain
open import Compiler.Model.Graph.Correctness.DelayFiniteCommon

open import Data.Nat using (ℕ; zero; suc; _<_; s≤s)
open import Data.Nat.Properties using (≤-trans; m≤m⊔n; m≤n⊔m; n≤1+n)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional renaming (_∈_ to _⋵_)
open import Data.Product using (_×_; proj₁; proj₂; Σ-syntax) renaming (_,_ to ⟨_,_⟩ )
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit.Polymorphic using () renaming (tt to ptt; ⊤ to pTrue)
open import Relation.Binary.PropositionalEquality using (_≢_)

module Compiler.Model.Graph.Correctness.DelayFiniteRel where

{- The function entries of a finite list of target values --------------------}

{- the free variables stored in the cdr halves of V' -}
Cdrs : List Value → 𝒫 Value
Cdrs V' = Cdr (mem V')

record CarEntry (V' U₀ : List Value) (w : Value) : Set where
  constructor car-entry
  field
    FV : List Value
    car∈ : ⦅ FV ↦ (U₀ ↦ w) ∣ ⋵ V'
    FV≢[] : FV ≢ []
    FV⊆ : mem FV ⊆ Cdrs V'

CarEntry-⊆ : ∀ {V₁ V₂ U₀ w} → mem V₁ ⊆ mem V₂ → CarEntry V₁ U₀ w → CarEntry V₂ U₀ w
CarEntry-⊆ s (car-entry FV e∈ neFV FV⊆) = car-entry FV (s _ e∈) neFV (λ d d∈ → s _ (FV⊆ d d∈))

Bnd-CarEntry : ∀ {k V' U₀ w} → Bnd (suc k) V' → CarEntry V' U₀ w → Bnd k U₀ × depth w < k
Bnd-CarEntry {U₀ = U₀}{w} bV (car-entry FV e∈ _ _) =
  ⟨ (λ u u∈ → <-shrink (s≤s (≤-trans (depth-⋵ u∈) (≤-trans (m≤m⊔n _ (depth w)) up))) (bV _ e∈))
  , <-shrink (s≤s (≤-trans (m≤n⊔m (depths U₀) _) up)) (bV _ e∈) ⟩
  where up = ≤-trans (n≤1+n _) (≤-trans (m≤n⊔m (depths FV) _) (n≤1+n _))

{- Batches of calls ------------------------------------------------------------}

{- U and W form a batch of calls of V: each w in W is the result of a
   function entry U₀ ↦ w of V with U₀ ⊆ U, and each u in U is an argument
   of a function entry of V -}
record Calls (V U W : List Value) : Set where
  field
    results : ∀ w → w ⋵ W → Σ[ U₀ ∈ List Value ] CarEntry V U₀ w × U₀ ≢ [] × mem U₀ ⊆ mem U
    args : ∀ u → u ⋵ U → Σ[ U₀ ∈ List Value ] Σ[ w ∈ Value ] CarEntry V U₀ w × u ⋵ U₀

Calls-⊆ : ∀ {V₁ V₂ U W} → mem V₁ ⊆ mem V₂ → Calls V₁ U W → Calls V₂ U W
Calls-⊆ s cs = record
  { results = λ w w∈ → let ⟨ U₀ , ⟨ e , r ⟩ ⟩ = Calls.results cs w w∈ in ⟨ U₀ , ⟨ CarEntry-⊆ s e , r ⟩ ⟩
  ; args = λ u u∈ → let ⟨ U₀ , ⟨ w , ⟨ e , r ⟩ ⟩ ⟩ = Calls.args cs u u∈ in ⟨ U₀ , ⟨ w , ⟨ CarEntry-⊆ s e , r ⟩ ⟩ ⟩
  }

{- a list without car halves makes no calls -}
Calls-none : ∀ {V U W} → (∀ u → ⦅ u ∣ ⋵ V → ⊥) → Calls V U W → mem W ⊆ ∅
Calls-none no cs w w∈ = no _ (CarEntry.car∈ (proj₁ (proj₂ (Calls.results cs w w∈))))

Bnd-Calls-args : ∀ {k V U W} → Bnd (suc k) V → Calls V U W → Bnd k U
Bnd-Calls-args bV cs u u∈ =
  let ⟨ _ , ⟨ _ , ⟨ e , u∈U₀ ⟩ ⟩ ⟩ = Calls.args cs u u∈ in proj₁ (Bnd-CarEntry bV e) u u∈U₀

Bnd-Calls-apps : ∀ {k V U W} → Bnd (suc k) V → Calls V U W → Bnd k W
Bnd-Calls-apps bV cs w w∈ = proj₂ (Bnd-CarEntry bV (proj₁ (proj₂ (Calls.results cs w w∈))))

{- The relation ---------------------------------------------------------------}

record Obs (R : List Value → 𝒫 Value → Set₁) (V : List Value) (D : 𝒫 Value) : Set₁ where
  field
    const-obs : ∀ {B} (c : base-rep B) → const c ⋵ V → const c ∈ D
    nonempty-obs : V ≢ [] → nonempty D
    app-obs : ∀ {U W} → Calls V U W → ∀ E → consis (mem U) → R U E → R W (D ● E)
    tag-obs : ∀ t W → mem W ⊆ Untag t (mem V) → R W (Untag t D)

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
  ; nonempty-obs = λ ne → ⊥-elim (proj₂ (ne-mem ne V⊆∅))
  ; app-obs = λ cs E _ _ → R-∅ k (Calls-none (λ u u∈ → V⊆∅ _ u∈) cs)
  ; tag-obs = λ t W W⊆ → R-∅ k (λ d d∈ → V⊆∅ _ (W⊆ d d∈))
  }

R-flat : ∀ k {V D} → mem V ⊆ D → (∀ v → v ⋵ V → Flat v) → R k V D
R-flat zero _ _ = ptt
R-flat (suc k) {V} V⊆ fl = record
  { const-obs = λ c c∈ → V⊆ _ c∈
  ; nonempty-obs = λ ne → ne-mem ne V⊆
  ; app-obs = λ cs E _ _ → R-∅ k (Calls-none (λ u u∈ → noflat (fl _ u∈)) cs)
  ; tag-obs = λ t W W⊆ → R-∅ k (λ d d∈ → flat-tag t (fl _ (W⊆ d d∈)))
  }
  where noflat : ∀ {u} → Flat ⦅ u ∣ → ⊥
        noflat ()

{- antitone in the list of observations -}
R-⊆ : ∀ k {V₁ V₂ D} → mem V₁ ⊆ mem V₂ → R k V₂ D → R k V₁ D
R-⊆ zero _ _ = ptt
R-⊆ (suc k) {V₁}{V₂} V₁⊆V₂ r = record
  { const-obs = λ c c∈ → const-obs c (V₁⊆V₂ _ c∈)
  ; nonempty-obs = λ ne → nonempty-obs (ne-⊆ V₁⊆V₂ ne)
  ; app-obs = λ cs → app-obs (Calls-⊆ V₁⊆V₂ cs)
  ; tag-obs = λ t W W⊆ → tag-obs t W (λ d d∈ → V₁⊆V₂ _ (W⊆ d d∈))
  }
  where open Obs r

{- monotone in the set on the other side -}
R-mono : ∀ k {V D₁ D₂} → D₁ ⊆ D₂ → R k V D₁ → R k V D₂
R-mono zero _ _ = ptt
R-mono (suc k) D⊆ r = record
  { const-obs = λ c c∈ → D⊆ _ (const-obs c c∈)
  ; nonempty-obs = λ ne → ⟨ proj₁ (nonempty-obs ne) , D⊆ _ (proj₂ (nonempty-obs ne)) ⟩
  ; app-obs = λ cs E gU rU → R-mono k (●-mono-l D⊆) (app-obs cs E gU rU)
  ; tag-obs = λ t W W⊆ → R-mono k (λ d → D⊆ (tag t d)) (tag-obs t W W⊆)
  }
  where open Obs r

{- the fuel is irrelevant once it bounds the depth of the observations -}
R-irr : ∀ k j {V D} → Bnd k V → Bnd j V → R k V D → R j V D
R-irr k zero _ _ _ = ptt
R-irr zero (suc j) bk _ _ = R-∅ (suc j) (λ v v∈ → <0 (bk v v∈))
  where <0 : ∀ {n} → n < 0 → ⊥
        <0 ()
R-irr (suc k) (suc j) bk bj r = record
  { const-obs = const-obs
  ; nonempty-obs = nonempty-obs
  ; app-obs = λ cs E gU rU →
      R-irr k j (Bnd-Calls-apps bk cs) (Bnd-Calls-apps bj cs)
        (app-obs cs E gU (R-irr j k (Bnd-Calls-args bj cs) (Bnd-Calls-args bk cs) rU))
  ; tag-obs = λ t W W⊆ →
      R-irr k j (Bnd-Untag t bk W⊆) (Bnd-Untag t bj W⊆) (tag-obs t W W⊆)
  }
  where open Obs r

{- relating the initial environment of a closed program to itself -}
Init⊳Init : ρ₀ ⊳ₑ ρ₀
Init⊳Init x V k V⊆ bV = R-flat k V⊆ (λ v v∈ → Init-flat (V⊆ v v∈))

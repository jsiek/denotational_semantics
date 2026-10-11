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
  of a function entry U₀ ↦ w of V', and U is the union of those U₀. The
  function clause relates the arguments U of a batch to an argument set E
  of the source, and the results W to the source application D ● E.

-}

open import SetsAsPredicates
open import Primitives
open import Compiler.Model.Graph.Domain.ISWIM.Domain
open import Compiler.Model.Graph.Domain.ISWIM.Ops
open import Compiler.Model.Graph.Correctness.DelayFiniteCommon

open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; s≤s)
open import Data.Nat.Properties using (≤-trans; m≤m⊔n; m≤n⊔m; n≤1+n)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Membership.Propositional renaming (_∈_ to _⋵_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩ )
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit.Polymorphic using () renaming (tt to ptt; ⊤ to pTrue)
open import Relation.Binary.PropositionalEquality using (_≢_; refl)

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

infixr 5 _∷_
data Calls (V : List Value) : List Value → List Value → Set where
  [] : Calls V [] []
  _∷_ : ∀ {U₀ w U W} → CarEntry V U₀ w × U₀ ≢ [] → Calls V U W → Calls V (U₀ ++ U) (w ∷ W)

{- one call of a batch: w is the result of an entry U₀ ↦ w of V with U₀ ⊆ U -}
record Call (V U : List Value) (w : Value) : Set where
  constructor call
  field
    U₀ : List Value
    entry : CarEntry V U₀ w
    U₀≢[] : U₀ ≢ []
    U₀⊆ : mem U₀ ⊆ mem U

Calls-∈ : ∀ {V U W w} → Calls V U W → w ⋵ W → Call V U w
Calls-∈ (_∷_ {U₀ = U₀} ⟨ e , ne ⟩ cs) (here refl) = call U₀ e ne (λ d d∈ → ∈-++⁺ˡ d∈)
Calls-∈ (_∷_ {U₀ = U₀} _ cs) (there w∈) with Calls-∈ cs w∈
... | call U₁ e ne U₁⊆ = call U₁ e ne (λ d d∈ → ∈-++⁺ʳ U₀ (U₁⊆ d d∈))

Calls-⊆ : ∀ {V₁ V₂ U W} → mem V₁ ⊆ mem V₂ → Calls V₁ U W → Calls V₂ U W
Calls-⊆ s [] = []
Calls-⊆ s (⟨ e , ne ⟩ ∷ cs) = ⟨ CarEntry-⊆ s e , ne ⟩ ∷ Calls-⊆ s cs

{- a list without car halves makes no calls -}
Calls-none : ∀ {V U W} → (∀ u → ⦅ u ∣ ⋵ V → ⊥) → Calls V U W → mem W ⊆ ∅
Calls-none no [] _ ()
Calls-none no (⟨ e , _ ⟩ ∷ _) _ _ = no _ (CarEntry.car∈ e)

Bnd-Calls-args : ∀ {k V U W} → Bnd (suc k) V → Calls V U W → Bnd k U
Bnd-Calls-args bV [] _ ()
Bnd-Calls-args bV (_∷_ {U₀ = U₀} ⟨ e , _ ⟩ cs) u u∈ with ∈-++⁻ U₀ u∈
... | inj₁ u∈U₀ = proj₁ (Bnd-CarEntry bV e) u u∈U₀
... | inj₂ u∈U = Bnd-Calls-args bV cs u u∈U

Bnd-Calls-apps : ∀ {k V U W} → Bnd (suc k) V → Calls V U W → Bnd k W
Bnd-Calls-apps bV [] _ ()
Bnd-Calls-apps bV (⟨ e , _ ⟩ ∷ cs) _ (here refl) = proj₂ (Bnd-CarEntry bV e)
Bnd-Calls-apps bV (_ ∷ cs) w (there w∈) = Bnd-Calls-apps bV cs w w∈

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

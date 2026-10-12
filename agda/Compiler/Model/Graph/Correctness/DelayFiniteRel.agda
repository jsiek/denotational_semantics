{-

  The logical relation for the backward (reflect) direction of the delay
  pass, indexed by finite lists of target observations (see issue #1).

  R V' D relates a finite list V' of target values to a source set D.
  It is defined by recursion on the depth of V'. Agda does not see this
  recursion as structural, so we encode it with fuel: R′ k V' D only looks
  at the parts of V' of depth < k, R V' D is R′ (1 + depth V') V' D, and
  R′-irr shows that the fuel is irrelevant as long as it bounds the depth
  of V' (Bnd k V'). The fuel stays private: unfold and fold show that
  R V' D holds exactly when the clauses Obs R V' D hold.

  A target closure denotes pairs ⦅ f , t ⦆ of a code entry f and an
  environment value t. A call takes its code entry FV ↦ (U₀ ↦ w) from
  car C and its free variables FV from cdr C separately, possibly from
  different pairs, and FV is a finite set of observations, so a single
  target value says nothing about a call. The function entries of V'
  (CarEntry) are the code entries in the cars of the pairs in V' whose
  free variables FV are in the cdrs of the pairs in V'. Calls V' U W says that each w in W is the result
  of a function entry U₀ ↦ w of V' with U₀ ⊆ U, and that each u in U is
  an argument of a function entry of V' (so U is no deeper than V'). The
  function clause relates the arguments U of a batch to an argument set E
  of the source, and the results W to the source application D ● E.

-}

open import SetsAsPredicates
open import Primitives
open import GraphModel.Domain
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

{- the free variables stored in the cdrs of the pairs in V' -}
Cdrs : List Value → 𝒫 Value
Cdrs V' = Cdr (mem V')

record CarEntry (V' U₀ : List Value) (w : Value) : Set where
  constructor car-entry
  field
    FV : List Value
    env : Value
    car∈ : ⦅ FV ↦ (U₀ ↦ w) , env ⦆ ⋵ V'
    FV≢[] : FV ≢ []
    FV⊆ : mem FV ⊆ Cdrs V'

CarEntry-⊆ : ∀ {V₁ V₂ U₀ w} → mem V₁ ⊆ mem V₂ → CarEntry V₁ U₀ w → CarEntry V₂ U₀ w
CarEntry-⊆ s (car-entry FV t e∈ neFV FV⊆) =
  car-entry FV t (s _ e∈) neFV (λ d d∈ → let ⟨ u , i ⟩ = FV⊆ d d∈ in ⟨ u , s _ i ⟩)

Bnd-CarEntry : ∀ {k V' U₀ w} → Bnd (suc k) V' → CarEntry V' U₀ w → Bnd k U₀ × depth w < k
Bnd-CarEntry {U₀ = U₀}{w} bV (car-entry FV t e∈ _ _) =
  ⟨ (λ u u∈ → <-shrink (s≤s (≤-trans (depth-⋵ u∈) (≤-trans (m≤m⊔n _ (depth w)) up))) (bV _ e∈))
  , <-shrink (s≤s (≤-trans (m≤n⊔m (depths U₀) _) up)) (bV _ e∈) ⟩
  where up = ≤-trans (n≤1+n _) (≤-trans (m≤n⊔m (depths FV) _) (≤-trans (n≤1+n _) (m≤m⊔n _ (depth t))))

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

{- a list without pairs makes no calls -}
Calls-none : ∀ {V U W} → (∀ u v → ⦅ u , v ⦆ ⋵ V → ⊥) → Calls V U W → mem W ⊆ ∅
Calls-none no cs w w∈ = no _ _ (CarEntry.car∈ (proj₁ (proj₂ (Calls.results cs w w∈))))

Bnd-Calls-args : ∀ {k V U W} → Bnd (suc k) V → Calls V U W → Bnd k U
Bnd-Calls-args bV cs u u∈ =
  let ⟨ _ , ⟨ _ , ⟨ e , u∈U₀ ⟩ ⟩ ⟩ = Calls.args cs u u∈ in proj₁ (Bnd-CarEntry bV e) u u∈U₀

Bnd-Calls-apps : ∀ {k V U W} → Bnd (suc k) V → Calls V U W → Bnd k W
Bnd-Calls-apps bV cs w w∈ = proj₂ (Bnd-CarEntry bV (proj₁ (proj₂ (Calls.results cs w w∈))))

{- The relation ---------------------------------------------------------------}

{- the clauses of the relation, for a relation Q on the smaller parts of V -}
record Obs (Q : List Value → 𝒫 Value → Set₁) (V : List Value) (D : 𝒫 Value) : Set₁ where
  field
    const-obs : ∀ {B} (c : base-rep B) → const c ⋵ V → const c ∈ D
    nonempty-obs : V ≢ [] → nonempty D
    app-obs : ∀ {U W} → Calls V U W → ∀ E → Con E → Con (mem U) → Q U E → Q W (D ● E)
    tag-obs : ∀ t W → mem W ⊆ Untag t (mem V) → Q W (Untag t D)

{- converting the clauses between relations that agree on lists of bounded depth -}
Obs-map : ∀ {k j Q₁ Q₂ V D} → Bnd (suc k) V → Bnd (suc j) V
  → (∀ {W E} → Bnd k W → Bnd j W → Q₁ W E → Q₂ W E)
  → (∀ {W E} → Bnd j W → Bnd k W → Q₂ W E → Q₁ W E)
  → Obs Q₁ V D → Obs Q₂ V D
Obs-map bk bj to from o = record
  { const-obs = const-obs
  ; nonempty-obs = nonempty-obs
  ; app-obs = λ cs E cE gU rU → to (Bnd-Calls-apps bk cs) (Bnd-Calls-apps bj cs)
      (app-obs cs E cE gU (from (Bnd-Calls-args bj cs) (Bnd-Calls-args bk cs) rU))
  ; tag-obs = λ t W W⊆ → to (Bnd-Untag t bk W⊆) (Bnd-Untag t bj W⊆) (tag-obs t W W⊆)
  }
  where open Obs o

{- the relation with fuel k: it only looks at the parts of V of depth < k -}
private
  R′ : ℕ → List Value → 𝒫 Value → Set₁
  R′ zero V D = pTrue
  R′ (suc k) V D = Obs (R′ k) V D

R : List Value → 𝒫 Value → Set₁
R V D = R′ (suc (depths V)) V D

infix 4 _⊳ₑ_
_⊳ₑ_ : Env → Env → Set₁
ρ₁ ⊳ₑ ρ₂ = ∀ x V → mem V ⊆ ρ₁ x → R V (ρ₂ x)

private
  R′-∅ : ∀ k {V D} → mem V ⊆ ∅ → R′ k V D
  R′-∅ zero _ = ptt
  R′-∅ (suc k) {V} V⊆∅ = record
    { const-obs = λ c c∈ → ⊥-elim (V⊆∅ _ c∈)
    ; nonempty-obs = λ ne → ⊥-elim (proj₂ (ne-mem ne V⊆∅))
    ; app-obs = λ cs E _ _ _ → R′-∅ k (Calls-none (λ u v uv∈ → V⊆∅ _ uv∈) cs)
    ; tag-obs = λ t W W⊆ → R′-∅ k (λ d d∈ → V⊆∅ _ (W⊆ d d∈))
    }

  R′-data : ∀ k {V D} → mem V ⊆ D → (∀ v → v ⋵ V → Data v) → R′ k V D
  R′-data zero _ _ = ptt
  R′-data (suc k) {V} V⊆ fl = record
    { const-obs = λ c c∈ → V⊆ _ c∈
    ; nonempty-obs = λ ne → ne-mem ne V⊆
    ; app-obs = λ cs E _ _ _ → R′-∅ k (Calls-none (λ u v uv∈ → noflat (fl _ uv∈)) cs)
    ; tag-obs = λ t W W⊆ →
        R′-data k (λ d d∈ → V⊆ _ (W⊆ d d∈)) (λ d d∈ → data-untag t (fl _ (W⊆ d d∈)))
    }
    where noflat : ∀ {u v} → Data ⦅ u , v ⦆ → ⊥
          noflat ()

  R′-mono : ∀ k {V D₁ D₂} → D₁ ⊆ D₂ → R′ k V D₁ → R′ k V D₂
  R′-mono zero _ _ = ptt
  R′-mono (suc k) D⊆ r = record
    { const-obs = λ c c∈ → D⊆ _ (const-obs c c∈)
    ; nonempty-obs = λ ne → ⟨ proj₁ (nonempty-obs ne) , D⊆ _ (proj₂ (nonempty-obs ne)) ⟩
    ; app-obs = λ cs E cE gU rU → R′-mono k (●-mono-l D⊆) (app-obs cs E cE gU rU)
    ; tag-obs = λ t W W⊆ → R′-mono k (λ d → D⊆ (tag t d)) (tag-obs t W W⊆)
    }
    where open Obs r

  {- the fuel is irrelevant once it bounds the depth of the observations -}
  R′-irr : ∀ k j {V D} → Bnd k V → Bnd j V → R′ k V D → R′ j V D
  R′-irr k zero _ _ _ = ptt
  R′-irr zero (suc j) bk _ _ = R′-∅ (suc j) (λ v v∈ → <0 (bk v v∈))
    where <0 : ∀ {n} → n < 0 → ⊥
          <0 ()
  R′-irr (suc k) (suc j) bk bj = Obs-map bk bj (R′-irr k j) (R′-irr j k)

{- R V D holds exactly when its clauses hold for R itself -}
unfold : ∀ {V D} → R V D → Obs R V D
unfold {V} = Obs-map bV bV (λ b _ → R′-irr _ _ b (Bnd-depths _)) (λ _ b → R′-irr _ _ (Bnd-depths _) b)
  where bV = Bnd-depths V

fold : ∀ {V D} → Obs R V D → R V D
fold {V} = Obs-map bV bV (λ _ b → R′-irr _ _ (Bnd-depths _) b) (λ b _ → R′-irr _ _ b (Bnd-depths _))
  where bV = Bnd-depths V

R-∅ : ∀ {V D} → mem V ⊆ ∅ → R V D
R-∅ = R′-∅ _

R-flat : ∀ {V D} → mem V ⊆ D → (∀ v → v ⋵ V → Flat v) → R V D
R-flat V⊆ fl = R′-data _ V⊆ (λ v v∈ → flat-data (fl v v∈))

R-data : ∀ {V D} → mem V ⊆ D → (∀ v → v ⋵ V → Data v) → R V D
R-data = R′-data _

{- monotone in the set on the other side -}
R-mono : ∀ {V D₁ D₂} → D₁ ⊆ D₂ → R V D₁ → R V D₂
R-mono = R′-mono _

{- antitone in the list of observations -}
R-⊆ : ∀ {V₁ V₂ D} → mem V₁ ⊆ mem V₂ → R V₂ D → R V₁ D
R-⊆ V₁⊆V₂ r = fold record
  { const-obs = λ c c∈ → const-obs c (V₁⊆V₂ _ c∈)
  ; nonempty-obs = λ ne → nonempty-obs (ne-⊆ V₁⊆V₂ ne)
  ; app-obs = λ cs → app-obs (Calls-⊆ V₁⊆V₂ cs)
  ; tag-obs = λ t W W⊆ → tag-obs t W (λ d d∈ → V₁⊆V₂ _ (W⊆ d d∈))
  }
  where open Obs (unfold r)

{- relating the initial environment of a closed program to itself -}
Init⊳Init : ρ₀ ⊳ₑ ρ₀
Init⊳Init x V V⊆ = R-flat V⊆ (λ v v∈ → Init-flat (V⊆ v v∈))

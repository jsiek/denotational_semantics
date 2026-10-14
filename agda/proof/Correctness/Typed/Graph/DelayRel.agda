{-

  The relation of the backward (reflect) direction of typed delay
  (Clos3ᵀ → Clos4ᵀ) in the graph model, as for untyped delay
  (proof/Correctness/Graph/DelayFiniteRel.agda): R V' D relates a finite
  list V' of target observations to a source set D, by recursion on the
  depth of V' (with fuel), since a target closure is a set of pairs whose
  calls combine the codes and environments of several pairs (Calls).
  The types add one clause, for project: a pair (a target closure) in V'
  is reflected by a source function (fun-obs).

-}

open import proof.Framework.GraphModel.SetsAsPredicates
open import Framework.Primitives
open import proof.Framework.GraphModel.Domain
open import proof.Framework.GraphModel.Ops using (⋆; car; cdr)
open import proof.Framework.GraphModel.DomainUtilBase
open import proof.Semantics.Graph.Prim using (out)
open import Semantics.Graph.Typed.Ops using (fun₂)
open import Language.Prim using (Out; int; bool)
open import Data.Bool using (true; false)

open import Data.Nat using (ℕ; zero; suc; _<_; s≤s)
open import Data.Nat.Properties using (≤-trans; m≤m⊔n; m≤n⊔m; n≤1+n)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional renaming (_∈_ to _⋵_)
open import Data.Product using (_×_; proj₁; proj₂; Σ-syntax) renaming (_,_ to ⟨_,_⟩ )
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit.Polymorphic using () renaming (tt to ptt; ⊤ to pTrue)
open import Relation.Binary.PropositionalEquality using (_≢_)

module proof.Correctness.Typed.Graph.DelayRel where

{- Shorthands -----------------------------------------------------------------}

_●_ : 𝒫 Value → 𝒫 Value → 𝒫 Value
D ● E = ⋆ ⟨ D , ⟨ E , ptt ⟩ ⟩

{- the call of the target closures D on E (callc) -}
_⊙_ : 𝒫 Value → 𝒫 Value → 𝒫 Value
D ⊙ E = (car ⟨ D , ptt ⟩ ● cdr ⟨ D , ptt ⟩) ● E

●-mono-l : ∀ {D₁ D₂ E} → D₁ ⊆ D₂ → (D₁ ● E) ⊆ (D₂ ● E)
●-mono-l D⊆ w ⟨ V , ⟨ V↦w∈ , ⟨ V⊆E , neV ⟩ ⟩ ⟩ = ⟨ V , ⟨ D⊆ _ V↦w∈ , ⟨ V⊆E , neV ⟩ ⟩ ⟩

out-data : ∀ (o : Out) → Data (out o)
out-data (int n) = flat-const
out-data (bool true) = flat-⟨⟩
out-data (bool false) = flat-⟨⟩

{- The function entries of a finite list of target values --------------------}

Cdrs : List Value → 𝒫 Value
Cdrs V' = cdr ⟨ mem V' , ptt ⟩

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

{- a batch of calls of V: each w in W is the result of a function entry
   U₀ ↦ w of V with U₀ ⊆ U, and each u in U is an argument of one -}
record Calls (V U W : List Value) : Set where
  field
    results : ∀ w → w ⋵ W → Σ[ U₀ ∈ List Value ] CarEntry V U₀ w × U₀ ≢ [] × mem U₀ ⊆ mem U
    args : ∀ u → u ⋵ U → Σ[ U₀ ∈ List Value ] Σ[ w ∈ Value ] CarEntry V U₀ w × u ⋵ U₀

Calls-⊆ : ∀ {V₁ V₂ U W} → mem V₁ ⊆ mem V₂ → Calls V₁ U W → Calls V₂ U W
Calls-⊆ s cs = record
  { results = λ w w∈ → let ⟨ U₀ , ⟨ e , r ⟩ ⟩ = Calls.results cs w w∈ in ⟨ U₀ , ⟨ CarEntry-⊆ s e , r ⟩ ⟩
  ; args = λ u u∈ → let ⟨ U₀ , ⟨ w , ⟨ e , r ⟩ ⟩ ⟩ = Calls.args cs u u∈ in ⟨ U₀ , ⟨ w , ⟨ CarEntry-⊆ s e , r ⟩ ⟩ ⟩
  }

Calls-none : ∀ {V U W} → (∀ u v → ⦅ u , v ⦆ ⋵ V → ⊥) → Calls V U W → mem W ⊆ ∅
Calls-none no cs w w∈ = no _ _ (CarEntry.car∈ (proj₁ (proj₂ (Calls.results cs w w∈))))

Bnd-Calls-args : ∀ {k V U W} → Bnd (suc k) V → Calls V U W → Bnd k U
Bnd-Calls-args bV cs u u∈ =
  let ⟨ _ , ⟨ _ , ⟨ e , u∈U₀ ⟩ ⟩ ⟩ = Calls.args cs u u∈ in proj₁ (Bnd-CarEntry bV e) u u∈U₀

Bnd-Calls-apps : ∀ {k V U W} → Bnd (suc k) V → Calls V U W → Bnd k W
Bnd-Calls-apps bV cs w w∈ = proj₂ (Bnd-CarEntry bV (proj₁ (proj₂ (Calls.results cs w w∈))))

{- The relation ---------------------------------------------------------------}

record Obs (Q : List Value → 𝒫 Value → Set₁) (V : List Value) (D : 𝒫 Value) : Set₁ where
  field
    const-obs : ∀ {B} (c : base-rep B) → const c ⋵ V → const c ∈ D
    nonempty-obs : V ≢ [] → nonempty D
    fun-obs : ∀ {u v} → ⦅ u , v ⦆ ⋵ V → Σ[ d ∈ Value ] d ∈ D × fun₂ d
    app-obs : ∀ {U W} → Calls V U W → ∀ E → Con E → Con (mem U) → Q U E → Q W (D ● E)
    tag-obs : ∀ t W → mem W ⊆ Untag t (mem V) → Q W (Untag t D)

Obs-map : ∀ {k j Q₁ Q₂ V D} → Bnd (suc k) V → Bnd (suc j) V
  → (∀ {W E} → Bnd k W → Bnd j W → Q₁ W E → Q₂ W E)
  → (∀ {W E} → Bnd j W → Bnd k W → Q₂ W E → Q₁ W E)
  → Obs Q₁ V D → Obs Q₂ V D
Obs-map bk bj to from o = record
  { const-obs = const-obs
  ; nonempty-obs = nonempty-obs
  ; fun-obs = fun-obs
  ; app-obs = λ cs E cE gU rU → to (Bnd-Calls-apps bk cs) (Bnd-Calls-apps bj cs)
      (app-obs cs E cE gU (from (Bnd-Calls-args bj cs) (Bnd-Calls-args bk cs) rU))
  ; tag-obs = λ t W W⊆ → to (Bnd-Untag t bk W⊆) (Bnd-Untag t bj W⊆) (tag-obs t W W⊆)
  }
  where open Obs o

private
  R′ : ℕ → List Value → 𝒫 Value → Set₁
  R′ zero V D = pTrue
  R′ (suc k) V D = Obs (R′ k) V D

R : List Value → 𝒫 Value → Set₁
R V D = R′ (suc (depths V)) V D

private
  R′-∅ : ∀ k {V D} → mem V ⊆ ∅ → R′ k V D
  R′-∅ zero _ = ptt
  R′-∅ (suc k) {V} V⊆∅ = record
    { const-obs = λ c c∈ → ⊥-elim (V⊆∅ _ c∈)
    ; nonempty-obs = λ ne → ⊥-elim (proj₂ (ne-mem ne V⊆∅))
    ; fun-obs = λ p∈ → ⊥-elim (V⊆∅ _ p∈)
    ; app-obs = λ cs E _ _ _ → R′-∅ k (Calls-none (λ u v uv∈ → V⊆∅ _ uv∈) cs)
    ; tag-obs = λ t W W⊆ → R′-∅ k (λ d d∈ → V⊆∅ _ (W⊆ d d∈))
    }

  R′-data : ∀ k {V D} → mem V ⊆ D → (∀ v → v ⋵ V → Data v) → R′ k V D
  R′-data zero _ _ = ptt
  R′-data (suc k) {V} V⊆ fl = record
    { const-obs = λ c c∈ → V⊆ _ c∈
    ; nonempty-obs = λ ne → ne-mem ne V⊆
    ; fun-obs = λ p∈ → ⊥-elim (noflat (fl _ p∈))
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
    ; fun-obs = λ p∈ → let ⟨ d , ⟨ d∈ , f ⟩ ⟩ = fun-obs p∈ in ⟨ d , ⟨ D⊆ d d∈ , f ⟩ ⟩
    ; app-obs = λ cs E cE gU rU → R′-mono k (●-mono-l D⊆) (app-obs cs E cE gU rU)
    ; tag-obs = λ t W W⊆ → R′-mono k (λ d → D⊆ (tag t d)) (tag-obs t W W⊆)
    }
    where open Obs r

  R′-irr : ∀ k j {V D} → Bnd k V → Bnd j V → R′ k V D → R′ j V D
  R′-irr k zero _ _ _ = ptt
  R′-irr zero (suc j) bk _ _ = R′-∅ (suc j) (λ v v∈ → <0 (bk v v∈))
    where <0 : ∀ {n} → n < 0 → ⊥
          <0 ()
  R′-irr (suc k) (suc j) bk bj = Obs-map bk bj (R′-irr k j) (R′-irr j k)

unfold : ∀ {V D} → R V D → Obs R V D
unfold {V} = Obs-map bV bV (λ b _ → R′-irr _ _ b (Bnd-depths _)) (λ _ b → R′-irr _ _ (Bnd-depths _) b)
  where bV = Bnd-depths V

fold : ∀ {V D} → Obs R V D → R V D
fold {V} = Obs-map bV bV (λ _ b → R′-irr _ _ (Bnd-depths _) b) (λ b _ → R′-irr _ _ b (Bnd-depths _))
  where bV = Bnd-depths V

R-∅ : ∀ {V D} → mem V ⊆ ∅ → R V D
R-∅ = R′-∅ _

R-data : ∀ {V D} → mem V ⊆ D → (∀ v → v ⋵ V → Data v) → R V D
R-data = R′-data _

R-flat : ∀ {V D} → mem V ⊆ D → (∀ v → v ⋵ V → Flat v) → R V D
R-flat V⊆ fl = R′-data _ V⊆ (λ v v∈ → flat-data (fl v v∈))

R-mono : ∀ {V D₁ D₂} → D₁ ⊆ D₂ → R V D₁ → R V D₂
R-mono = R′-mono _

R-⊆ : ∀ {V₁ V₂ D} → mem V₁ ⊆ mem V₂ → R V₂ D → R V₁ D
R-⊆ V₁⊆V₂ r = fold record
  { const-obs = λ c c∈ → const-obs c (V₁⊆V₂ _ c∈)
  ; nonempty-obs = λ ne → nonempty-obs (ne-⊆ V₁⊆V₂ ne)
  ; fun-obs = λ p∈ → fun-obs (V₁⊆V₂ _ p∈)
  ; app-obs = λ cs → app-obs (Calls-⊆ V₁⊆V₂ cs)
  ; tag-obs = λ t W W⊆ → tag-obs t W (λ d d∈ → V₁⊆V₂ _ (W⊆ d d∈))
  }
  where open Obs (unfold r)

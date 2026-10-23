{-

  The approximant logical relation, for the backward (reflect) direction
  of delay (EnvClosμ → FlatClosμ) in the graph model: that of typed delay
  (proof/Correctness/Graph/DelayRel.agda) without its clause for
  project (fun-obs), which ISWIMμ does not have.
  ApproxLR D V' relates an arbitrary source denotation D (a set of EnvClosμ
  values) to a finite target approximant V' (a list of FlatClosμ values), by
  recursion on the depth of V', since a target closure is a set of pairs
  whose calls combine the codes and environments of several pairs (Batch).
  ApproxLRLayer is one unfolding of the relation, with the recursive call
  left open (Q). The fuel index of ApproxLR≤ is only a termination
  device: ApproxLR-depth-irrelevant shows that any fuel bounding the
  depth gives the same relation (unfold, fold). Approx D D' says that D
  is related to every finite part of a target set D', the form of the
  fundamental lemma; Approx-fold proves it from the four clauses.

  The types of EnvClosμ cannot replace the depth as the measure. A
  relation by recursion on the type would define the relation at μ A
  as the one at its unfolding A [ μ A ] (fold and unfold are the
  identity on denotations), which is not smaller: at μX. X ⇒ Int,
  app-obs asks for the relation at the argument type, μX. X ⇒ Int
  itself. What decreases is the depth of the approximant: the arguments
  U and results W of Batch V U W are shallower than V (Bnd-Batch-args,
  Bnd-Batch-apps), which is what ApproxLR≤'s fuel counts. The values are
  untyped, and fold does not change them, so the depth needs no help
  from the type.

-}

open import proof.Framework.GraphModel.Prelude
open import Framework.Primitives
open import proof.Framework.GraphModel.Ops using (⋆; car; cdr)
open import proof.Framework.GraphModel.DomainUtilBase
open import proof.Semantics.Graph.Prim using (out)
open import Language.Prim using (Out; int; bool)
open import Data.Bool using (true; false)

open import Data.Nat using (ℕ; zero; suc; _<_; s≤s)
open import Data.Nat.Properties using (≤-trans; m≤m⊔n; m≤n⊔m; n≤1+n; n≮0)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Relation.Unary.Any using (here)
open import Data.List.Membership.Propositional renaming (_∈_ to _⋵_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺; ∈-map⁻; ∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻)
open import Data.Product using (_×_; proj₁; proj₂; Σ-syntax) renaming (_,_ to ⟨_,_⟩ )
import Data.Product as Prod
open import Data.Sum using ([_,_]′)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit.Polymorphic using () renaming (tt to ptt; ⊤ to pTrue)
open import Relation.Binary.PropositionalEquality using (_≢_; refl)

module Mu.proof.Correctness.GraphModel.DelayRel where

{- Shorthands -----------------------------------------------------------------}

_●_ : 𝒫 Value → 𝒫 Value → 𝒫 Value
D ● E = ⋆ ⟨ D , ⟨ E , ptt ⟩ ⟩

{- the call of the target closures D on E (callc) -}
_⊙_ : 𝒫 Value → 𝒫 Value → 𝒫 Value
D ⊙ E = (car ⟨ D , ptt ⟩ ● cdr ⟨ D , ptt ⟩) ● E

●-mono : ∀ {D₁ D₂ E₁ E₂} → D₁ ⊆ D₂ → E₁ ⊆ E₂ → (D₁ ● E₁) ⊆ (D₂ ● E₂)
●-mono D⊆ E⊆ w ⟨ V , ⟨ V↦w∈ , ⟨ V⊆E , neV ⟩ ⟩ ⟩ = ⟨ V , ⟨ D⊆ _ V↦w∈ , ⟨ (λ v v∈ → E⊆ v (V⊆E v v∈)) , neV ⟩ ⟩ ⟩

out-data : ∀ (o : Out) → Data (out o)
out-data (int n) = flat-const
out-data (bool true) = flat-⟨⟩
out-data (bool false) = flat-⟨⟩

{- The function entries of a finite list of target values --------------------}

Cdrs : List Value → 𝒫 Value
Cdrs V' = cdr ⟨ mem V' , ptt ⟩

{- the usable entries of V' (Figure 4 of the paper): UsableEntry V' U₀ w is
   an entry FV ↦ (U₀ ↦ w) of car(V') whose environments FV are among
   cdr(V') -}
record UsableEntry (V' U₀ : List Value) (w : Value) : Set where
  constructor usable-entry
  field
    FV : List Value
    env : Value
    car∈ : ⦅ FV ↦ (U₀ ↦ w) , env ⦆ ⋵ V'
    FV≢[] : FV ≢ []
    FV⊆ : mem FV ⊆ Cdrs V'

UsableEntry-⊆ : ∀ {V₁ V₂ U₀ w} → mem V₁ ⊆ mem V₂ → UsableEntry V₁ U₀ w → UsableEntry V₂ U₀ w
UsableEntry-⊆ s (usable-entry FV t e∈ neFV FV⊆) =
  usable-entry FV t (s _ e∈) neFV (λ d d∈ → let ⟨ u , i ⟩ = FV⊆ d d∈ in ⟨ u , s _ i ⟩)

Bnd-UsableEntry : ∀ {k V' U₀ w} → Bnd (suc k) V' → UsableEntry V' U₀ w → Bnd k U₀ × depth w < k
Bnd-UsableEntry {U₀ = U₀}{w} bV (usable-entry FV t e∈ _ _) =
  ⟨ (λ u u∈ → <-shrink (s≤s (≤-trans (depth-⋵ u∈) (≤-trans (m≤m⊔n _ (depth w)) up))) (bV _ e∈))
  , <-shrink (s≤s (≤-trans (m≤n⊔m (depths U₀) _) up)) (bV _ e∈) ⟩
  where up = ≤-trans (n≤1+n _) (≤-trans (m≤n⊔m (depths FV) _) (≤-trans (n≤1+n _) (m≤m⊔n _ (depth t))))

{- a batch of calls of V (Figure 4 of the paper): each w in W is the
   result of a usable entry U₀ ↦ w of V with U₀ ⊆ U, and each u in U is an argument of one -}
record Batch (V U W : List Value) : Set where
  field
    results : ∀ w → w ⋵ W → Σ[ U₀ ∈ List Value ] UsableEntry V U₀ w × U₀ ≢ [] × mem U₀ ⊆ mem U
    args : ∀ u → u ⋵ U → Σ[ U₀ ∈ List Value ] Σ[ w ∈ Value ] UsableEntry V U₀ w × u ⋵ U₀

Batch-⊆ : ∀ {V₁ V₂ U W} → mem V₁ ⊆ mem V₂ → Batch V₁ U W → Batch V₂ U W
Batch-⊆ s cs = record
  { results = λ w w∈ → let ⟨ U₀ , ⟨ e , r ⟩ ⟩ = Batch.results cs w w∈ in ⟨ U₀ , ⟨ UsableEntry-⊆ s e , r ⟩ ⟩
  ; args = λ u u∈ → let ⟨ U₀ , ⟨ w , ⟨ e , r ⟩ ⟩ ⟩ = Batch.args cs u u∈ in ⟨ U₀ , ⟨ w , ⟨ UsableEntry-⊆ s e , r ⟩ ⟩ ⟩
  }

{- two batches of calls of V are one -}
Batch-++ : ∀ {V U₁ U₂ W₁ W₂} → Batch V U₁ W₁ → Batch V U₂ W₂ → Batch V (U₁ ++ U₂) (W₁ ++ W₂)
Batch-++ {U₁ = U₁} {W₁ = W₁} c₁ c₂ = record
  { results = λ w w∈ → [ (λ i → Prod.map₂ (Prod.map₂ (Prod.map₂ λ ⊆U d d∈ → ∈-++⁺ˡ (⊆U d d∈))) (Batch.results c₁ w i))
                       , (λ i → Prod.map₂ (Prod.map₂ (Prod.map₂ λ ⊆U d d∈ → ∈-++⁺ʳ U₁ (⊆U d d∈))) (Batch.results c₂ w i)) ]′ (∈-++⁻ W₁ w∈)
  ; args = λ u u∈ → [ Batch.args c₁ u , Batch.args c₂ u ]′ (∈-++⁻ U₁ u∈)
  }

Batch-none : ∀ {V U W} → (∀ u v → ⦅ u , v ⦆ ⋵ V → ⊥) → Batch V U W → mem W ⊆ ∅
Batch-none no cs w w∈ = no _ _ (UsableEntry.car∈ (proj₁ (proj₂ (Batch.results cs w w∈))))

Bnd-Batch-args : ∀ {k V U W} → Bnd (suc k) V → Batch V U W → Bnd k U
Bnd-Batch-args bV cs u u∈ =
  let ⟨ _ , ⟨ _ , ⟨ e , u∈U₀ ⟩ ⟩ ⟩ = Batch.args cs u u∈ in proj₁ (Bnd-UsableEntry bV e) u u∈U₀

Bnd-Batch-apps : ∀ {k V U W} → Bnd (suc k) V → Batch V U W → Bnd k W
Bnd-Batch-apps bV cs w w∈ = proj₂ (Bnd-UsableEntry bV (proj₁ (proj₂ (Batch.results cs w w∈))))

{- The approximant logical relation -------------------------------------------}

record ApproxLRLayer (Q : 𝒫 Value → List Value → Set₁) (D : 𝒫 Value) (V : List Value) : Set₁ where
  field
    const-obs : ∀ {B} (c : base-rep B) → const c ⋵ V → const c ∈ D
    nonempty-obs : V ≢ [] → nonempty D
    app-obs : ∀ {U W} → Batch V U W → ∀ E → Con E → Con (mem U) → Q E U → Q (D ● E) W
    tag-obs : ∀ t W → mem W ⊆ Untag t (mem V) → Q (Untag t D) W

ApproxLRLayer-map : ∀ {k j Q₁ Q₂ D V} → Bnd (suc k) V → Bnd (suc j) V
  → (∀ {E W} → Bnd k W → Bnd j W → Q₁ E W → Q₂ E W)
  → (∀ {E W} → Bnd j W → Bnd k W → Q₂ E W → Q₁ E W)
  → ApproxLRLayer Q₁ D V → ApproxLRLayer Q₂ D V
ApproxLRLayer-map bk bj to from o = record
  { const-obs = const-obs
  ; nonempty-obs = nonempty-obs
  ; app-obs = λ cs E cE gU rU → to (Bnd-Batch-apps bk cs) (Bnd-Batch-apps bj cs)
      (app-obs cs E cE gU (from (Bnd-Batch-args bj cs) (Bnd-Batch-args bk cs) rU))
  ; tag-obs = λ t W W⊆ → to (Bnd-Untag t bk W⊆) (Bnd-Untag t bj W⊆) (tag-obs t W W⊆)
  }
  where open ApproxLRLayer o

private
  ApproxLR≤ : ℕ → 𝒫 Value → List Value → Set₁
  ApproxLR≤ zero D V = pTrue
  ApproxLR≤ (suc k) D V = ApproxLRLayer (ApproxLR≤ k) D V

ApproxLR : 𝒫 Value → List Value → Set₁
ApproxLR D V = ApproxLR≤ (suc (depths V)) D V

private
  {- a list of first-order data in D, the empty list among them -}
  ApproxLR≤-data : ∀ k {D V} → (∀ v → v ⋵ V → v ∈ D × Data v) → ApproxLR≤ k D V
  ApproxLR≤-data zero _ = ptt
  ApproxLR≤-data (suc k) dV = record
    { const-obs = λ c c∈ → proj₁ (dV _ c∈)
    ; nonempty-obs = λ ne → ne-mem ne (λ v v∈ → proj₁ (dV v v∈))
    ; app-obs = λ cs _ _ _ _ → ApproxLR≤-data k (λ w w∈ → ⊥-elim (Batch-none (λ u v uv∈ → noflat (proj₂ (dV _ uv∈))) cs w w∈))
    ; tag-obs = λ t W W⊆ → ApproxLR≤-data k (λ d d∈ → let ⟨ d∈D , dd ⟩ = dV _ (W⊆ d d∈) in ⟨ d∈D , data-untag t dd ⟩)
    }
    where noflat : ∀ {u v} → Data ⦅ u , v ⦆ → ⊥
          noflat ()

  ApproxLR≤-mono : ∀ k {D₁ D₂ V} → D₁ ⊆ D₂ → ApproxLR≤ k D₁ V → ApproxLR≤ k D₂ V
  ApproxLR≤-mono zero _ _ = ptt
  ApproxLR≤-mono (suc k) D⊆ r = record
    { const-obs = λ c c∈ → D⊆ _ (const-obs c c∈)
    ; nonempty-obs = λ ne → ⟨ proj₁ (nonempty-obs ne) , D⊆ _ (proj₂ (nonempty-obs ne)) ⟩
    ; app-obs = λ cs E cE gU rU → ApproxLR≤-mono k (●-mono D⊆ (λ _ e → e)) (app-obs cs E cE gU rU)
    ; tag-obs = λ t W W⊆ → ApproxLR≤-mono k (λ d → D⊆ (tag t d)) (tag-obs t W W⊆)
    }
    where open ApproxLRLayer r

  ApproxLR-depth-irrelevant : ∀ {k j D V} → Bnd k V → Bnd j V → ApproxLR≤ k D V → ApproxLR≤ j D V
  ApproxLR-depth-irrelevant {j = zero} _ _ _ = ptt
  ApproxLR-depth-irrelevant {zero} {suc j} bk _ _ = ApproxLR≤-data (suc j) (λ v v∈ → ⊥-elim (n≮0 (bk v v∈)))
  ApproxLR-depth-irrelevant {suc k} {suc j} bk bj = ApproxLRLayer-map bk bj ApproxLR-depth-irrelevant ApproxLR-depth-irrelevant

unfold : ∀ {D V} → ApproxLR D V → ApproxLRLayer ApproxLR D V
unfold {V = V} = ApproxLRLayer-map bV bV (λ b _ → ApproxLR-depth-irrelevant b (Bnd-depths _)) (λ _ → ApproxLR-depth-irrelevant (Bnd-depths _))
  where bV = Bnd-depths V

fold : ∀ {D V} → ApproxLRLayer ApproxLR D V → ApproxLR D V
fold {V = V} = ApproxLRLayer-map bV bV (λ _ → ApproxLR-depth-irrelevant (Bnd-depths _)) (λ b _ → ApproxLR-depth-irrelevant b (Bnd-depths _))
  where bV = Bnd-depths V

ApproxLR-data : ∀ {D V} → (∀ v → v ⋵ V → v ∈ D × Data v) → ApproxLR D V
ApproxLR-data = ApproxLR≤-data _

ApproxLR-∅ : ∀ {D V} → mem V ⊆ ∅ → ApproxLR D V
ApproxLR-∅ V⊆∅ = ApproxLR-data (λ v v∈ → ⊥-elim (V⊆∅ v v∈))

ApproxLR-mono : ∀ {D₁ D₂ V} → D₁ ⊆ D₂ → ApproxLR D₁ V → ApproxLR D₂ V
ApproxLR-mono = ApproxLR≤-mono _

ApproxLR-⊆ : ∀ {D V₁ V₂} → mem V₁ ⊆ mem V₂ → ApproxLR D V₂ → ApproxLR D V₁
ApproxLR-⊆ V₁⊆V₂ r = fold record
  { const-obs = λ c c∈ → const-obs c (V₁⊆V₂ _ c∈)
  ; nonempty-obs = λ ne → nonempty-obs (ne-⊆ V₁⊆V₂ ne)
  ; app-obs = λ cs → app-obs (Batch-⊆ V₁⊆V₂ cs)
  ; tag-obs = λ t W W⊆ → tag-obs t W (λ d d∈ → V₁⊆V₂ _ (W⊆ d d∈))
  }
  where open ApproxLRLayer (unfold r)

{- D approximates every finite part of a target set D' (the conclusion of
   the fundamental lemma); then D has the constants of D', is nonempty
   when D' is, and its projections approximate those of D' -}
Approx : 𝒫 Value → 𝒫 Value → Set₁
Approx D D' = ∀ V → mem V ⊆ D' → ApproxLR D V

Approx-const : ∀ {D D' B} {c : base-rep B} → Approx D D' → const c ∈ D' → const c ∈ D
Approx-const {c = c} r c∈ = ApproxLRLayer.const-obs (unfold (r (const c ∷ []) (single⊆ c∈))) c (here refl)

Approx-ne : ∀ {D D'} → Approx D D' → nonempty D' → nonempty D
Approx-ne r ⟨ v , v∈ ⟩ = ApproxLRLayer.nonempty-obs (unfold (r (v ∷ []) (single⊆ v∈))) (λ ())

Approx-untag : ∀ t {D D'} → Approx D D' → Approx (Untag t D) (Untag t D')
Approx-untag t r W W⊆ = ApproxLRLayer.tag-obs (unfold (r (map (tag t) W) tW⊆)) t W (λ d → ∈-map⁺ (tag t))
  where
  tW⊆ : mem (map (tag t) W) ⊆ _
  tW⊆ d d∈ with ∈-map⁻ (tag t) d∈
  ... | ⟨ x , ⟨ x∈ , refl ⟩ ⟩ = W⊆ x x∈

{- the four clauses, for every finite part of D' -}
AppObs : 𝒫 Value → 𝒫 Value → Set₁
AppObs D D' = ∀ {V U W} → mem V ⊆ D' → Batch V U W → ∀ E → Con E → Con (mem U) → ApproxLR E U → ApproxLR (D ● E) W

Approx-fold : ∀ {D D'} → (∀ {B} (c : base-rep B) → const c ∈ D' → const c ∈ D) → (nonempty D' → nonempty D)
  → AppObs D D' → (∀ t → Approx (Untag t D) (Untag t D')) → Approx D D'
Approx-fold cs ne app tg V V⊆ = fold record
  { const-obs = λ c c∈ → cs c (V⊆ _ c∈)
  ; nonempty-obs = λ neV → ne (ne-mem neV V⊆)
  ; app-obs = app V⊆
  ; tag-obs = λ t W W⊆ → tg t W (λ d d∈ → V⊆ _ (W⊆ d d∈))
  }

{- a target set without pairs has no calls -}
Approx-fold₀ : ∀ {D D'} → (∀ {B} (c : base-rep B) → const c ∈ D' → const c ∈ D) → (nonempty D' → nonempty D)
  → (∀ u v → ⦅ u , v ⦆ ∈ D' → ⊥) → (∀ t → Approx (Untag t D) (Untag t D')) → Approx D D'
Approx-fold₀ cs ne np = Approx-fold cs ne λ V⊆ calls _ _ _ _ → ApproxLR-∅ (Batch-none (λ u v uv∈ → np u v (V⊆ _ uv∈)) calls)

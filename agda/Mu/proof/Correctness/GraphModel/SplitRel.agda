{-

  The approximant logical relation, for the backward (reflect) direction
  of split (EnvClosμ → PairClosμ) in the graph model: that of typed split
  (proof/Correctness/Graph/SplitRel.agda) without its clause for
  project (fun-obs), which FPC does not have. The relation itself and
  Lemma 4.2 are in ApproxLR.agda (re-exported here); this module adds the
  call of a closure (_⊙_), the union of batches, and Approx, the form of
  the fundamental lemma.
  ApproxLR D V' relates an arbitrary source denotation D (a set of EnvClosμ
  values) to a finite target approximant V' (a list of PairClosμ values), by
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

module Mu.proof.Correctness.GraphModel.SplitRel where

open import Mu.proof.Correctness.GraphModel.ApproxLR public

{- Shorthands -----------------------------------------------------------------}

{- the call of the target closures D on E (callc) -}
_⊙_ : 𝒫 Value → 𝒫 Value → 𝒫 Value
D ⊙ E = (car ⟨ D , ptt ⟩ ● cdr ⟨ D , ptt ⟩) ● E

out-data : ∀ (o : Out) → Data (out o)
out-data (int n) = flat-const
out-data (bool true) = flat-⟨⟩
out-data (bool false) = flat-⟨⟩

{- two batches of calls of V are one -}
Batch-++ : ∀ {V U₁ U₂ W₁ W₂} → Batch V U₁ W₁ → Batch V U₂ W₂ → Batch V (U₁ ++ U₂) (W₁ ++ W₂)
Batch-++ {U₁ = U₁} {W₁ = W₁} c₁ c₂ = record
  { results = λ w w∈ → [ (λ i → Prod.map₂ (Prod.map₂ (Prod.map₂ λ ⊆U d d∈ → ∈-++⁺ˡ (⊆U d d∈))) (Batch.results c₁ w i))
                       , (λ i → Prod.map₂ (Prod.map₂ (Prod.map₂ λ ⊆U d d∈ → ∈-++⁺ʳ U₁ (⊆U d d∈))) (Batch.results c₂ w i)) ]′ (∈-++⁻ W₁ w∈)
  ; args = λ u u∈ → [ Batch.args c₁ u , Batch.args c₂ u ]′ (∈-++⁻ U₁ u∈)
  }

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

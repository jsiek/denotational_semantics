{-

  This module builds on the approximant logical relation for the
  backward (reflect) direction of split (EnvClosμ → PairClosμ) in the
  graph model. The relation is the one for typed split
  (ISWIM/proof/Correctness/Graph/SplitRel.agda) minus its clause for
  project (fun-obs), because FPC has no project construct.
  ApproxLR.agda defines the relation and proves Lemma 4.4 of the paper,
  and this module re-exports them. This module adds the call of a
  target closure (_⊙_), the union of two self-contained calls
  (SelfContainedMaps-++), and Approx, the form of the conclusion of the
  fundamental lemma.

  ApproxLR D V' relates an arbitrary source denotation D (a set of
  EnvClosμ values) to a finite target approximant V' (a list of
  PairClosμ values). A call of a target closure can combine the code
  of one pair with the environments of other pairs (SelfContainedMaps),
  so the target side is a finite list of pairs rather than a single
  one. The relation is defined by recursion on the depth of V'.
  ApproxLRLayer is one unfolding of the relation, with the recursive
  occurrence left as a parameter Q. The fuel index of ApproxLR≤ serves
  only for termination, because any fuel that bounds the depth gives
  the same relation (ApproxLR-depth-irrelevant, unfold, fold).
  Approx D D' says that D is related to every finite part of a target
  set D', and Approx-fold proves Approx D D' from the four clauses.

  The types of EnvClosμ cannot serve as the measure in place of the
  depth. Because fold and unfold mean the identity on denotations, a
  relation defined by recursion on types would define the relation at
  μ A as the relation at its unfolding A [ μ A ], which is not a smaller
  type. For example, at μX. X ⇒ Int, app-obs needs the relation at the
  argument type, which is μX. X ⇒ Int itself. The depth of the
  approximant decreases instead. The arguments U and the results W of
  SelfContainedMaps V U W are shallower than V
  (Bnd-SelfContainedMaps-args, Bnd-SelfContainedMaps-apps), and the
  fuel of ApproxLR≤ counts this depth. The values are untyped and fold
  leaves them unchanged, so the depth needs no help from the types.

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

module FPC.proof.Correctness.GraphModel.SplitRel where

open import FPC.proof.Correctness.GraphModel.ApproxLR public

{- Shorthands -----------------------------------------------------------------}

{- D ⊙ E calls the target closures in D on the arguments in E, as callc
   does. It applies the codes car D to the environments cdr D and then
   applies the results to E. -}
_⊙_ : 𝒫 Value → 𝒫 Value → 𝒫 Value
D ⊙ E = (car ⟨ D , ptt ⟩ ● cdr ⟨ D , ptt ⟩) ● E

out-data : ∀ (o : Out) → Data (out o)
out-data (int n) = flat-const
out-data (bool true) = flat-⟨⟩
out-data (bool false) = flat-⟨⟩

{- If V maps U₁ to W₁ and maps U₂ to W₂, then V maps U₁ ++ U₂ to
   W₁ ++ W₂. -}
SelfContainedMaps-++ : ∀ {V U₁ U₂ W₁ W₂} → SelfContainedMaps V U₁ W₁ → SelfContainedMaps V U₂ W₂ → SelfContainedMaps V (U₁ ++ U₂) (W₁ ++ W₂)
SelfContainedMaps-++ {U₁ = U₁} {W₁ = W₁} c₁ c₂ = record
  { results = λ w w∈ → [ (λ i → Prod.map₂ (Prod.map₂ (Prod.map₂ λ ⊆U d d∈ → ∈-++⁺ˡ (⊆U d d∈))) (SelfContainedMaps.results c₁ w i))
                       , (λ i → Prod.map₂ (Prod.map₂ (Prod.map₂ λ ⊆U d d∈ → ∈-++⁺ʳ U₁ (⊆U d d∈))) (SelfContainedMaps.results c₂ w i)) ]′ (∈-++⁻ W₁ w∈)
  ; args = λ u u∈ → [ SelfContainedMaps.args c₁ u , SelfContainedMaps.args c₂ u ]′ (∈-++⁻ U₁ u∈)
  }

{- Approx D D' says that D is related to every finite part of the target
   set D'. The fundamental lemma concludes Approx. If Approx D D' holds,
   then D contains every constant of D' (Approx-const), D is nonempty
   when D' is (Approx-ne), and the projections of D approximate the
   projections of D' (Approx-untag). -}
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

{- AppObs D D' is the third clause of the relation (app-obs), for every
   finite part of D'. -}
AppObs : 𝒫 Value → 𝒫 Value → Set₁
AppObs D D' = ∀ {V U W} → mem V ⊆ D' → SelfContainedMaps V U W → ∀ E → Con E → Con (mem U) → ApproxLR E U → ApproxLR (D ● E) W

{- Approx-fold proves Approx D D' from the four clauses, stated for the
   sets D and D' as a whole. -}
Approx-fold : ∀ {D D'} → (∀ {B} (c : base-rep B) → const c ∈ D' → const c ∈ D) → (nonempty D' → nonempty D)
  → AppObs D D' → (∀ t → Approx (Untag t D) (Untag t D')) → Approx D D'
Approx-fold cs ne app tg V V⊆ = fold record
  { const-obs = λ c c∈ → cs c (V⊆ _ c∈)
  ; nonempty-obs = λ neV → ne (ne-mem neV V⊆)
  ; app-obs = app V⊆
  ; tag-obs = λ t W W⊆ → tg t W (λ d d∈ → V⊆ _ (W⊆ d d∈))
  }

{- If D' contains no pair, then D' has no calls, so Approx-fold₀ needs
   only the other three clauses. -}
Approx-fold₀ : ∀ {D D'} → (∀ {B} (c : base-rep B) → const c ∈ D' → const c ∈ D) → (nonempty D' → nonempty D)
  → (∀ u v → ⦅ u , v ⦆ ∈ D' → ⊥) → (∀ t → Approx (Untag t D) (Untag t D')) → Approx D D'
Approx-fold₀ cs ne np = Approx-fold cs ne λ V⊆ calls _ _ _ _ → ApproxLR-∅ (SelfContainedMaps-none (λ u v uv∈ → np u v (V⊆ _ uv∈)) calls)

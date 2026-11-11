{-

  This module is a design experiment for the reflection half of split
  (EnvClosμ → PairClosμ) in the graph model, separate from the size
  totals of the proofs. It replaces the finite target list V of the
  approximant logical relation of SplitRel.agda with a target set T of
  bounded depth, which may be infinite. The paper discusses this
  alternative in Section 4.2 ("Design alternatives: which sides to
  relate", fourth bullet).

  ApproxLRSet≤ k D T consists of the four clauses of ApproxLRLayer and
  is defined by recursion on the bound k. It is meant for a set T whose
  elements all have depth less than k, although the definition makes
  sense for every T. The finite parts of a call stay lists, because
  they are parts of one graph value. These parts are the arguments U₀
  and the environments FV of a code entry FV ↦ (U₀ ↦ w). The
  self-contained calls become sets (SelfContainedMapsS T U W), because
  the arguments U and the results W of the calls of T may be infinite.
  If T is bounded by k + 1, then U and W are bounded by k. The
  projection clause relates Untag t D to the whole set Untag t T, so it
  needs no quantifier over subsets.

  ApproxLRSet⇒ and ApproxLRSet⇐, together ApproxLRSet⇔, prove by one
  induction on k that, on a set T bounded by k, the set relation agrees
  with the relation on each finite sublist of T (Approx D T of
  SplitRel.agda):

    Bnd𝒫 k T → (ApproxLRSet≤ k D T ⇔ ∀ V → mem V ⊆ T → ApproxLR D V)

  Each direction of the induction step uses the other direction at k on
  the arguments of the calls, because the arguments occur in negative
  position. The direction (⇒) passes a finite self-contained call of
  V ⊆ T to the set clause as the sets mem U and mem W. The direction
  (⇐) cuts an infinite call into finite pieces. A finite W₀ ⊆ W comes
  from finitely many code entries of T. Their pairs, together with the
  pairs that supply their environments (cdr-witness), form a finite
  V ⊆ T, and their arguments form a finite U₁ ⊆ U (collectS). The
  relation of E to U gives the relation of E to U₁, and the consistency
  of U gives the consistency of U₁. The clause of the finite relation at
  V then relates D ● E to W₀.

-}

open import proof.Framework.GraphModel.Prelude
open import Framework.Primitives
open import proof.Framework.GraphModel.Ops using (cdr)
open import proof.Framework.GraphModel.DomainUtilBase
open import proof.Framework.GraphModel.DomainUtil using (cdr-witness)
open import FPC.proof.Correctness.GraphModel.SplitRel

open import Data.Nat using (ℕ; zero; suc; _<_; s≤s)
open import Data.Nat.Properties using (n≮0; ≤-refl)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Membership.Propositional renaming (_∈_ to _⋵_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻)
open import Data.Product using (_×_; proj₁; proj₂; Σ-syntax) renaming (_,_ to ⟨_,_⟩ )
open import Data.Sum using ([_,_]′)
open import Data.Empty using (⊥-elim)
open import Data.Unit.Polymorphic using () renaming (tt to ptt; ⊤ to pTrue)
open import Relation.Binary.PropositionalEquality using (_≢_; refl)

module FPC.proof.Correctness.GraphModel.SplitDesignBoundedSets where

{- Bounded sets ---------------------------------------------------------------}

Bnd𝒫 : ℕ → 𝒫 Value → Set
Bnd𝒫 k T = ∀ v → v ∈ T → depth v < k

Bnd𝒫-mem : ∀ {k V T} → Bnd𝒫 k T → mem V ⊆ T → Bnd k V
Bnd𝒫-mem bT V⊆ v v∈ = bT v (V⊆ v v∈)

Bnd𝒫-Untag : ∀ {k T} t → Bnd𝒫 (suc k) T → Bnd𝒫 k (Untag t T)
Bnd𝒫-Untag (tupT i) bT d d∈ = <-shrink ≤-refl (bT _ d∈)
Bnd𝒫-Untag leftT bT d d∈ = <-shrink ≤-refl (bT _ d∈)
Bnd𝒫-Untag rightT bT d d∈ = <-shrink ≤-refl (bT _ d∈)

{- Usable entries and self-contained calls of a target set -------------------}

{- UsableEntryS is UsableEntry for a target set T in place of a list. -}
record UsableEntryS (T : 𝒫 Value) (U₀ : List Value) (w : Value) : Set where
  constructor usable-entryS
  field
    FV : List Value
    env : Value
    car∈ : ⦅ FV ↦ (U₀ ↦ w) , env ⦆ ∈ T
    FV≢[] : FV ≢ []
    FV⊆ : mem FV ⊆ cdr ⟨ T , ptt ⟩

{- SelfContainedMapsS T U W says that T maps U to W, as in
   SelfContainedMaps, where the arguments U and the results W are
   sets. -}
record SelfContainedMapsS (T U W : 𝒫 Value) : Set where
  field
    results : ∀ w → w ∈ W → Σ[ U₀ ∈ List Value ] UsableEntryS T U₀ w × U₀ ≢ [] × mem U₀ ⊆ U
    args : ∀ u → u ∈ U → Σ[ U₀ ∈ List Value ] Σ[ w ∈ Value ] UsableEntryS T U₀ w × u ⋵ U₀

{- If V ⊆ T, then every usable entry of the list V is a usable entry of
   the set T. -}
UsableEntry→S : ∀ {V T U₀ w} → mem V ⊆ T → UsableEntry V U₀ w → UsableEntryS T U₀ w
UsableEntry→S V⊆ (usable-entry FV t e∈ neFV FV⊆) =
  usable-entryS FV t (V⊆ _ e∈) neFV (λ d d∈ → let ⟨ u , i ⟩ = FV⊆ d d∈ in ⟨ u , V⊆ _ i ⟩)

SelfContainedMaps→S : ∀ {V T U W} → mem V ⊆ T → SelfContainedMaps V U W → SelfContainedMapsS T (mem U) (mem W)
SelfContainedMaps→S V⊆ cs = record
  { results = λ w w∈ → let ⟨ U₀ , ⟨ e , r ⟩ ⟩ = SelfContainedMaps.results cs w w∈ in ⟨ U₀ , ⟨ UsableEntry→S V⊆ e , r ⟩ ⟩
  ; args = λ u u∈ → let ⟨ U₀ , ⟨ w , ⟨ e , r ⟩ ⟩ ⟩ = SelfContainedMaps.args cs u u∈ in ⟨ U₀ , ⟨ w , ⟨ UsableEntry→S V⊆ e , r ⟩ ⟩ ⟩
  }

{- Every usable entry of T is a usable entry of some finite V ⊆ T. The
   list V consists of the entry's pair and the pairs that supply its
   environments. -}
S→UsableEntry : ∀ {T U₀ w} → UsableEntryS T U₀ w → Σ[ V ∈ List Value ] mem V ⊆ T × UsableEntry V U₀ w
S→UsableEntry {T} {U₀} {w} (usable-entryS FV t e∈ neFV FV⊆) with cdr-witness FV FV⊆
... | ⟨ P , ⟨ P⊆T , FV⊆P ⟩ ⟩ =
  ⟨ e ∷ P , ⟨ (λ { _ (here refl) → e∈ ; d (there d∈) → P⊆T d d∈ })
  , usable-entry FV t (here refl) neFV (λ d d∈ → let ⟨ u , i ⟩ = FV⊆P d d∈ in ⟨ u , there i ⟩) ⟩ ⟩
  where e = ⦅ FV ↦ (U₀ ↦ w) , t ⦆

Bnd-UsableEntryS : ∀ {k T U₀ w} → Bnd𝒫 (suc k) T → UsableEntryS T U₀ w → Bnd k U₀ × depth w < k
Bnd-UsableEntryS bT e = let ⟨ V , ⟨ V⊆ , e' ⟩ ⟩ = S→UsableEntry e in Bnd-UsableEntry (Bnd𝒫-mem bT V⊆) e'

Bnd-SelfContainedMapsS-args : ∀ {k T U W} → Bnd𝒫 (suc k) T → SelfContainedMapsS T U W → Bnd𝒫 k U
Bnd-SelfContainedMapsS-args bT cs u u∈ =
  let ⟨ _ , ⟨ _ , ⟨ e , u∈U₀ ⟩ ⟩ ⟩ = SelfContainedMapsS.args cs u u∈ in proj₁ (Bnd-UsableEntryS bT e) u u∈U₀

Bnd-SelfContainedMapsS-apps : ∀ {k T U W} → Bnd𝒫 (suc k) T → SelfContainedMapsS T U W → Bnd𝒫 k W
Bnd-SelfContainedMapsS-apps bT cs w w∈ = proj₂ (Bnd-UsableEntryS bT (proj₁ (proj₂ (SelfContainedMapsS.results cs w w∈))))

{- If T maps U to W and W₀ is a finite part of W, then some finite
   V ⊆ T maps some finite U₁ ⊆ U to W₀. -}
collectS : ∀ {T U W} → SelfContainedMapsS T U W → ∀ W₀ → mem W₀ ⊆ W
  → Σ[ V ∈ List Value ] Σ[ U₁ ∈ List Value ] mem V ⊆ T × mem U₁ ⊆ U × SelfContainedMaps V U₁ W₀
collectS cs [] _ = ⟨ [] , ⟨ [] , ⟨ (λ _ ()) , ⟨ (λ _ ()) , record { results = λ _ () ; args = λ _ () } ⟩ ⟩ ⟩ ⟩
collectS cs (w ∷ W₀) W₀⊆
    with SelfContainedMapsS.results cs w (W₀⊆ w (here refl)) | collectS cs W₀ (λ d d∈ → W₀⊆ d (there d∈))
... | ⟨ U₀ , ⟨ e , ⟨ neU₀ , U₀⊆U ⟩ ⟩ ⟩ | ⟨ V , ⟨ U₁ , ⟨ V⊆ , ⟨ U₁⊆ , cs' ⟩ ⟩ ⟩ ⟩
    with S→UsableEntry e
... | ⟨ P , ⟨ P⊆ , ent ⟩ ⟩ =
  ⟨ P ++ V , ⟨ U₀ ++ U₁ , ⟨ ++⊆ P⊆ V⊆ , ⟨ ++⊆ U₀⊆U U₁⊆
  , SelfContainedMaps-++ (SelfContainedMaps-⊆ (λ d d∈ → ∈-++⁺ˡ d∈)
                (record { results = λ { _ (here refl) → ⟨ U₀ , ⟨ ent , ⟨ neU₀ , (λ _ d∈ → d∈) ⟩ ⟩ ⟩ ; _ (there ()) }
                        ; args = λ u u∈ → ⟨ U₀ , ⟨ w , ⟨ ent , u∈ ⟩ ⟩ ⟩ }))
             (SelfContainedMaps-⊆ (λ d d∈ → ∈-++⁺ʳ P d∈) cs') ⟩ ⟩ ⟩ ⟩
  where
  ++⊆ : ∀ {A B : List Value} {D} → mem A ⊆ D → mem B ⊆ D → mem (A ++ B) ⊆ D
  ++⊆ {A} A⊆ B⊆ d d∈ = [ A⊆ d , B⊆ d ]′ (∈-++⁻ A d∈)

{- The relation on bounded target sets ----------------------------------------}

record ApproxLRSetLayer (Q : 𝒫 Value → 𝒫 Value → Set₁) (D T : 𝒫 Value) : Set₁ where
  field
    const-obs : ∀ {B} (c : base-rep B) → const c ∈ T → const c ∈ D
    nonempty-obs : nonempty T → nonempty D
    app-obs : ∀ {U W} → SelfContainedMapsS T U W → ∀ E → Con E → Con U → Q E U → Q (D ● E) W
    tag-obs : ∀ t → Q (Untag t D) (Untag t T)

ApproxLRSet≤ : ℕ → 𝒫 Value → 𝒫 Value → Set₁
ApproxLRSet≤ zero D T = pTrue
ApproxLRSet≤ (suc k) D T = ApproxLRSetLayer (ApproxLRSet≤ k) D T

{- Agreement of the set relation with the list relation ----------------------}

ApproxLRSet⇒ : ∀ k {D T} → Bnd𝒫 k T → ApproxLRSet≤ k D T → Approx D T
ApproxLRSet⇐ : ∀ k {D T} → Bnd𝒫 k T → Approx D T → ApproxLRSet≤ k D T

ApproxLRSet⇒ zero bT _ V V⊆ = ApproxLR-∅ (λ v v∈ → ⊥-elim (n≮0 (bT v (V⊆ v v∈))))
ApproxLRSet⇒ (suc k) {D} {T} bT r V V⊆ = fold record
  { const-obs = λ c c∈ → const-obs c (V⊆ _ c∈)
  ; nonempty-obs = λ neV → nonempty-obs (ne-mem neV V⊆)
  ; app-obs = λ {U} {W} cs E cE cU rU →
      ApproxLRSet⇒ k (Bnd𝒫-mem-inv (Bnd-SelfContainedMaps-apps bV cs))
        (app-obs (SelfContainedMaps→S V⊆ cs) E cE cU
           (ApproxLRSet⇐ k (Bnd𝒫-mem-inv (Bnd-SelfContainedMaps-args bV cs)) (λ U' U'⊆ → ApproxLR-⊆ U'⊆ rU)))
        W (λ _ d∈ → d∈)
  ; tag-obs = λ t W W⊆ →
      ApproxLRSet⇒ k (Bnd𝒫-Untag t bT) (tag-obs t) W (λ d d∈ → V⊆ _ (W⊆ d d∈))
  }
  where
  open ApproxLRSetLayer r
  bV = Bnd𝒫-mem bT V⊆
  Bnd𝒫-mem-inv : ∀ {j} {X : List Value} → Bnd j X → Bnd𝒫 j (mem X)
  Bnd𝒫-mem-inv b = b

ApproxLRSet⇐ zero _ _ = ptt
ApproxLRSet⇐ (suc k) {D} {T} bT r = record
  { const-obs = λ c c∈ → Approx-const r c∈
  ; nonempty-obs = Approx-ne r
  ; app-obs = λ {U} {W} cs E cE cU rU →
      ApproxLRSet⇐ k (Bnd-SelfContainedMapsS-apps bT cs) λ W₀ W₀⊆ →
        let ⟨ V , ⟨ U₁ , ⟨ V⊆ , ⟨ U₁⊆ , cs₀ ⟩ ⟩ ⟩ ⟩ = collectS cs W₀ W₀⊆ in
        ApproxLRLayer.app-obs (unfold (r V V⊆)) cs₀ E cE (Con-⊆ cU U₁⊆)
          (ApproxLRSet⇒ k (Bnd-SelfContainedMapsS-args bT cs) rU U₁ U₁⊆)
  ; tag-obs = λ t → ApproxLRSet⇐ k (Bnd𝒫-Untag t bT) (Approx-untag t r)
  }

ApproxLRSet⇔ : ∀ k {D T} → Bnd𝒫 k T → (ApproxLRSet≤ k D T → Approx D T) × (Approx D T → ApproxLRSet≤ k D T)
ApproxLRSet⇔ k bT = ⟨ ApproxLRSet⇒ k bT , ApproxLRSet⇐ k bT ⟩

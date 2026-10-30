{-

  A design experiment for the reflection half of delay (EnvClosμ → PairClosμ)
  in the graph model, in no proof's total: the approximant logical
  relation of DelayRel with a target *set* T of bounded depth, possibly
  infinite, in place of the finite target list V (the paper, §4.2,
  "Which sides to relate", fourth bullet).

  ApproxLRSet≤ k D T has the four clauses of ApproxLRLayer, by recursion
  on the bound k, for T whose elements all have depth < k (the
  definition itself is total). The finite parts of a call stay lists,
  since they are parts of one graph value: the arguments U₀ and the
  environments FV of a code entry FV ↦ (U₀ ↦ w). The batches of calls
  become sets (BatchS T U W): the arguments U and the results W of the
  calls of T may be infinite, and they are bounded by k when T is
  bounded by k + 1. The projection clause relates Untag t D to the whole
  set Untag t T, so it needs no quantifier over its subsets.

  ApproxLRSet⇒ and ApproxLRSet⇐ (together ApproxLRSet⇔) prove, by one
  induction on k, that the set relation on a set bounded by k is the
  relation on each of its finite sublists, Approx D T of DelayRel:

    Bnd𝒫 k T → (ApproxLRSet≤ k D T ⇔ ∀ V → mem V ⊆ T → ApproxLR D V)

  Each direction of the step uses the other direction at k, on the
  arguments of the calls, which are in negative position. (⇒) passes a
  finite batch of calls of V ⊆ T to the set clause as the sets mem U and
  mem W. (⇐) cuts an infinite batch into finite pieces: a finite W₀ ⊆ W
  comes from finitely many code entries of T, whose pairs and the pairs
  that supply their environments (cdr-witness) form a finite V ⊆ T, and
  whose arguments form a finite U₁ ⊆ U (collectS); the relation of E to
  U gives the one to U₁, the consistency of U that of U₁, and the
  clause of the finite relation at V gives D ● E related to W₀.

-}

open import proof.Framework.GraphModel.Prelude
open import Framework.Primitives
open import proof.Framework.GraphModel.Ops using (cdr)
open import proof.Framework.GraphModel.DomainUtilBase
open import proof.Framework.GraphModel.DomainUtil using (cdr-witness)
open import Mu.proof.Correctness.GraphModel.DelayRel

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

module Mu.proof.Correctness.GraphModel.DelayDesignBoundedSets where

{- Bounded sets ------------------------------------------------------------------}

Bnd𝒫 : ℕ → 𝒫 Value → Set
Bnd𝒫 k T = ∀ v → v ∈ T → depth v < k

Bnd𝒫-mem : ∀ {k V T} → Bnd𝒫 k T → mem V ⊆ T → Bnd k V
Bnd𝒫-mem bT V⊆ v v∈ = bT v (V⊆ v v∈)

Bnd𝒫-Untag : ∀ {k T} t → Bnd𝒫 (suc k) T → Bnd𝒫 k (Untag t T)
Bnd𝒫-Untag (tupT i) bT d d∈ = <-shrink ≤-refl (bT _ d∈)
Bnd𝒫-Untag leftT bT d d∈ = <-shrink ≤-refl (bT _ d∈)
Bnd𝒫-Untag rightT bT d d∈ = <-shrink ≤-refl (bT _ d∈)

{- The function entries of a target set, and batches of its calls --------------}

record UsableEntryS (T : 𝒫 Value) (U₀ : List Value) (w : Value) : Set where
  constructor usable-entryS
  field
    FV : List Value
    env : Value
    car∈ : ⦅ FV ↦ (U₀ ↦ w) , env ⦆ ∈ T
    FV≢[] : FV ≢ []
    FV⊆ : mem FV ⊆ cdr ⟨ T , ptt ⟩

{- a batch of calls of T, as in Batch, with sets of arguments U and results W -}
record BatchS (T U W : 𝒫 Value) : Set where
  field
    results : ∀ w → w ∈ W → Σ[ U₀ ∈ List Value ] UsableEntryS T U₀ w × U₀ ≢ [] × mem U₀ ⊆ U
    args : ∀ u → u ∈ U → Σ[ U₀ ∈ List Value ] Σ[ w ∈ Value ] UsableEntryS T U₀ w × u ⋵ U₀

{- an entry of a finite V ⊆ T is one of T -}
UsableEntry→S : ∀ {V T U₀ w} → mem V ⊆ T → UsableEntry V U₀ w → UsableEntryS T U₀ w
UsableEntry→S V⊆ (usable-entry FV t e∈ neFV FV⊆) =
  usable-entryS FV t (V⊆ _ e∈) neFV (λ d d∈ → let ⟨ u , i ⟩ = FV⊆ d d∈ in ⟨ u , V⊆ _ i ⟩)

Batch→S : ∀ {V T U W} → mem V ⊆ T → Batch V U W → BatchS T (mem U) (mem W)
Batch→S V⊆ cs = record
  { results = λ w w∈ → let ⟨ U₀ , ⟨ e , r ⟩ ⟩ = Batch.results cs w w∈ in ⟨ U₀ , ⟨ UsableEntry→S V⊆ e , r ⟩ ⟩
  ; args = λ u u∈ → let ⟨ U₀ , ⟨ w , ⟨ e , r ⟩ ⟩ ⟩ = Batch.args cs u u∈ in ⟨ U₀ , ⟨ w , ⟨ UsableEntry→S V⊆ e , r ⟩ ⟩ ⟩
  }

{- an entry of T is one of a finite V ⊆ T: its pair and the pairs that
   supply its environments -}
S→UsableEntry : ∀ {T U₀ w} → UsableEntryS T U₀ w → Σ[ V ∈ List Value ] mem V ⊆ T × UsableEntry V U₀ w
S→UsableEntry {T} {U₀} {w} (usable-entryS FV t e∈ neFV FV⊆) with cdr-witness FV FV⊆
... | ⟨ P , ⟨ P⊆T , FV⊆P ⟩ ⟩ =
  ⟨ e ∷ P , ⟨ (λ { _ (here refl) → e∈ ; d (there d∈) → P⊆T d d∈ })
  , usable-entry FV t (here refl) neFV (λ d d∈ → let ⟨ u , i ⟩ = FV⊆P d d∈ in ⟨ u , there i ⟩) ⟩ ⟩
  where e = ⦅ FV ↦ (U₀ ↦ w) , t ⦆

Bnd-UsableEntryS : ∀ {k T U₀ w} → Bnd𝒫 (suc k) T → UsableEntryS T U₀ w → Bnd k U₀ × depth w < k
Bnd-UsableEntryS bT e = let ⟨ V , ⟨ V⊆ , e' ⟩ ⟩ = S→UsableEntry e in Bnd-UsableEntry (Bnd𝒫-mem bT V⊆) e'

Bnd-BatchS-args : ∀ {k T U W} → Bnd𝒫 (suc k) T → BatchS T U W → Bnd𝒫 k U
Bnd-BatchS-args bT cs u u∈ =
  let ⟨ _ , ⟨ _ , ⟨ e , u∈U₀ ⟩ ⟩ ⟩ = BatchS.args cs u u∈ in proj₁ (Bnd-UsableEntryS bT e) u u∈U₀

Bnd-BatchS-apps : ∀ {k T U W} → Bnd𝒫 (suc k) T → BatchS T U W → Bnd𝒫 k W
Bnd-BatchS-apps bT cs w w∈ = proj₂ (Bnd-UsableEntryS bT (proj₁ (proj₂ (BatchS.results cs w w∈))))

{- the results W₀ ⊆ W, finitely many, of a batch of calls of T come from a
   batch of calls of a finite V ⊆ T on finitely many arguments U₁ ⊆ U -}
collectS : ∀ {T U W} → BatchS T U W → ∀ W₀ → mem W₀ ⊆ W
  → Σ[ V ∈ List Value ] Σ[ U₁ ∈ List Value ] mem V ⊆ T × mem U₁ ⊆ U × Batch V U₁ W₀
collectS cs [] _ = ⟨ [] , ⟨ [] , ⟨ (λ _ ()) , ⟨ (λ _ ()) , record { results = λ _ () ; args = λ _ () } ⟩ ⟩ ⟩ ⟩
collectS cs (w ∷ W₀) W₀⊆
    with BatchS.results cs w (W₀⊆ w (here refl)) | collectS cs W₀ (λ d d∈ → W₀⊆ d (there d∈))
... | ⟨ U₀ , ⟨ e , ⟨ neU₀ , U₀⊆U ⟩ ⟩ ⟩ | ⟨ V , ⟨ U₁ , ⟨ V⊆ , ⟨ U₁⊆ , cs' ⟩ ⟩ ⟩ ⟩
    with S→UsableEntry e
... | ⟨ P , ⟨ P⊆ , ent ⟩ ⟩ =
  ⟨ P ++ V , ⟨ U₀ ++ U₁ , ⟨ ++⊆ P⊆ V⊆ , ⟨ ++⊆ U₀⊆U U₁⊆
  , Batch-++ (Batch-⊆ (λ d d∈ → ∈-++⁺ˡ d∈)
                (record { results = λ { _ (here refl) → ⟨ U₀ , ⟨ ent , ⟨ neU₀ , (λ _ d∈ → d∈) ⟩ ⟩ ⟩ ; _ (there ()) }
                        ; args = λ u u∈ → ⟨ U₀ , ⟨ w , ⟨ ent , u∈ ⟩ ⟩ ⟩ }))
             (Batch-⊆ (λ d d∈ → ∈-++⁺ʳ P d∈) cs') ⟩ ⟩ ⟩ ⟩
  where
  ++⊆ : ∀ {A B : List Value} {D} → mem A ⊆ D → mem B ⊆ D → mem (A ++ B) ⊆ D
  ++⊆ {A} A⊆ B⊆ d d∈ = [ A⊆ d , B⊆ d ]′ (∈-++⁻ A d∈)

{- The relation on bounded target sets -----------------------------------------}

record ApproxLRSetLayer (Q : 𝒫 Value → 𝒫 Value → Set₁) (D T : 𝒫 Value) : Set₁ where
  field
    const-obs : ∀ {B} (c : base-rep B) → const c ∈ T → const c ∈ D
    nonempty-obs : nonempty T → nonempty D
    app-obs : ∀ {U W} → BatchS T U W → ∀ E → Con E → Con U → Q E U → Q (D ● E) W
    tag-obs : ∀ t → Q (Untag t D) (Untag t T)

ApproxLRSet≤ : ℕ → 𝒫 Value → 𝒫 Value → Set₁
ApproxLRSet≤ zero D T = pTrue
ApproxLRSet≤ (suc k) D T = ApproxLRSetLayer (ApproxLRSet≤ k) D T

{- The relation on a bounded set is the relation on its finite sublists ---------}

ApproxLRSet⇒ : ∀ k {D T} → Bnd𝒫 k T → ApproxLRSet≤ k D T → Approx D T
ApproxLRSet⇐ : ∀ k {D T} → Bnd𝒫 k T → Approx D T → ApproxLRSet≤ k D T

ApproxLRSet⇒ zero bT _ V V⊆ = ApproxLR-∅ (λ v v∈ → ⊥-elim (n≮0 (bT v (V⊆ v v∈))))
ApproxLRSet⇒ (suc k) {D} {T} bT r V V⊆ = fold record
  { const-obs = λ c c∈ → const-obs c (V⊆ _ c∈)
  ; nonempty-obs = λ neV → nonempty-obs (ne-mem neV V⊆)
  ; app-obs = λ {U} {W} cs E cE cU rU →
      ApproxLRSet⇒ k (Bnd𝒫-mem-inv (Bnd-Batch-apps bV cs))
        (app-obs (Batch→S V⊆ cs) E cE cU
           (ApproxLRSet⇐ k (Bnd𝒫-mem-inv (Bnd-Batch-args bV cs)) (λ U' U'⊆ → ApproxLR-⊆ U'⊆ rU)))
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
      ApproxLRSet⇐ k (Bnd-BatchS-apps bT cs) λ W₀ W₀⊆ →
        let ⟨ V , ⟨ U₁ , ⟨ V⊆ , ⟨ U₁⊆ , cs₀ ⟩ ⟩ ⟩ ⟩ = collectS cs W₀ W₀⊆ in
        ApproxLRLayer.app-obs (unfold (r V V⊆)) cs₀ E cE (Con-⊆ cU U₁⊆)
          (ApproxLRSet⇒ k (Bnd-BatchS-args bT cs) rU U₁ U₁⊆)
  ; tag-obs = λ t → ApproxLRSet⇐ k (Bnd𝒫-Untag t bT) (Approx-untag t r)
  }

ApproxLRSet⇔ : ∀ k {D T} → Bnd𝒫 k T → (ApproxLRSet≤ k D T → Approx D T) × (Approx D T → ApproxLRSet≤ k D T)
ApproxLRSet⇔ k bT = ⟨ ApproxLRSet⇒ k bT , ApproxLRSet⇐ k bT ⟩

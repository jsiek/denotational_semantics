{-

  The relation of the backward (reflect) direction of the correctness of
  typed delay (Clos3ᵀ → Clos4ᵀ) in the graph model with errors, as in
  Untyped/proof/Correctness/GraphErr/DelayRel.agda: indexed by finite lists of
  target observations (by their depth), since a target closure is a set
  of pairs whose calls combine the codes and environments of several
  pairs (Calls). A value of type Any may be a closure, so the relation
  cannot be by recursion on types: Any makes the types recursive.

  What the types remove: the source application has no check of its
  operator, and the target call no late check, so a target closure is
  related only by its applications (app-obs); kinds (kind-obs, where a
  closure has the kind of a function, kind₄) matter only to project, the one check (R-checkₗ,
  bad-reflect, R-restrict).

-}

open import proof.Framework.GraphModel.ErrorPrelude
open import Framework.Primitives
open import proof.Framework.GraphModel.DomainUtilBase
open import proof.Semantics.GraphErr.Prim using (out)
open import Language.Prim using (int; bool)
open import Semantics.GraphErr.Typed.Clos4 using (kind₄)
open import Semantics.GraphErr.Typed.Ops using (checkedᵠ; hit; keep; kindᶠ)
open import Language.Typed.Type using (ttup; tfun; tsum; tint; flat)
open import Data.Bool using (true; false)

open import Data.Nat using (ℕ; zero; suc; _<_; s≤s)
open import Data.Nat.Properties using (≤-trans; m≤m⊔n; m≤n⊔m; n≤1+n)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Membership.Propositional renaming (_∈_ to _⋵_)
open import Data.Product using (_×_; proj₁; proj₂; Σ-syntax) renaming (_,_ to ⟨_,_⟩ )
open import Data.Sum using (inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (tt; ⊤)
open import Data.Unit.Polymorphic using () renaming (tt to ptt; ⊤ to pTrue)
open import Level using (lift; lower)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong)

module proof.Correctness.GraphErr.DelayRel where

{- the kernel of a source application, once its operator is bound -}
_●_ : 𝒫 Value → 𝒫 Value → 𝒫 Value
D ● E = E ≫= λ X → ⋆ ⟨ D , ⟨ X , ptt ⟩ ⟩

●-mono-e : ∀ {D₁ D₂ E} → (∀ V w → (V ↦ w) ∈ D₁ → (V ↦ w) ∈ D₂) → (D₁ ● E) ⊆ (D₂ ● E)
●-mono-e {D₁} {D₂} f = ≫=-mono {F = λ X → ⋆ ⟨ D₁ , ⟨ X , ptt ⟩ ⟩} {F' = λ X → ⋆ ⟨ D₂ , ⟨ X , ptt ⟩ ⟩} (λ d z → z)
  λ X⊆ → λ { w ⟨ V , ⟨ e∈ , ⟨ V⊆ , ne ⟩ ⟩ ⟩ → ⟨ V , ⟨ f V w e∈ , ⟨ (λ d d∈ → X⊆ d (V⊆ d d∈)) , ne ⟩ ⟩ ⟩ }

●-mono-l : ∀ {D₁ D₂ E} → D₁ ⊆ D₂ → (D₁ ● E) ⊆ (D₂ ● E)
●-mono-l {D₁} {D₂} D⊆ = ●-mono-e {D₁} {D₂} (λ V w → D⊆ (V ↦ w))

{- Kinds ----------------------------------------------------------------------}

{- data have their kind in Clos4ᵀ -}
data-kind : ∀ d → Data d → kind d ≡ kind₄ (kind d)
data-kind (const k) _ = refl
data-kind ⟨⟩ _ = refl
data-kind (left x) _ = refl
data-kind (right x) _ = refl
data-kind ω _ = refl

out-data : ∀ o → Data (out o)
out-data (int n) = flat-const
out-data (bool true) = flat-⟨⟩
out-data (bool false) = flat-⟨⟩

{- the list without its ω -}
dropω : List Value → List Value
dropω [] = []
dropω (v ∷ V) with ω? v
... | inj₁ _ = dropω V
... | inj₂ _ = v ∷ dropω V

dropω-⊆ : ∀ V → mem (dropω V) ⊆ mem V
dropω-⊆ (v ∷ V) d d∈ with ω? v
... | inj₁ _ = there (dropω-⊆ V d d∈)
dropω-⊆ (v ∷ V) d (here refl) | inj₂ _ = here refl
dropω-⊆ (v ∷ V) d (there d∈) | inj₂ _ = there (dropω-⊆ V d d∈)

dropω-keep : ∀ V w → w ⋵ V → w ≢ ω → w ⋵ dropω V
dropω-keep (v ∷ V) w w∈ w≢ with ω? v
dropω-keep (v ∷ V) .v (here refl) w≢ | inj₁ eq = ⊥-elim (w≢ eq)
dropω-keep (v ∷ V) w (there w∈) w≢ | inj₁ _ = dropω-keep V w w∈ w≢
dropω-keep (v ∷ V) .v (here refl) w≢ | inj₂ _ = here refl
dropω-keep (v ∷ V) w (there w∈) w≢ | inj₂ _ = there (dropω-keep V w w∈ w≢)

dropω-noω : ∀ V w → w ⋵ dropω V → w ≢ ω
dropω-noω (v ∷ V) w w∈ with ω? v
... | inj₁ _ = dropω-noω V w w∈
dropω-noω (v ∷ V) .v (here refl) | inj₂ v≢ = v≢
dropω-noω (v ∷ V) w (there w∈) | inj₂ _ = dropω-noω V w w∈

tag≢ω : ∀ t {d} → tag t d ≢ ω
tag≢ω (tupT i) ()
tag≢ω leftT ()
tag≢ω rightT ()

{- The function entries of a finite list of target values --------------------}

Cdrs : List Value → 𝒫 Value
Cdrs V' v = Σ[ u ∈ Value ] ⦅ u , v ⦆ ⋵ V'

record CarEntry (V' U₀ : List Value) (w : Value) : Set where
  constructor car-entry
  field
    FV : List Value
    env : Value
    car∈ : ⦅ FV ↦ (U₀ ↦ w) , env ⦆ ⋵ V'
    FV≢[] : FV ≢ []
    FV⊆ : mem FV ⊆ Cdrs V'

{- the pairs of one list are in another -}
Pairs⊆ : List Value → List Value → Set
Pairs⊆ V₁ V₂ = ∀ u v → ⦅ u , v ⦆ ⋵ V₁ → ⦅ u , v ⦆ ⋵ V₂

CarEntry-⊆ : ∀ {V₁ V₂ U₀ w} → Pairs⊆ V₁ V₂ → CarEntry V₁ U₀ w → CarEntry V₂ U₀ w
CarEntry-⊆ s (car-entry FV t e∈ neFV FV⊆) =
  car-entry FV t (s _ _ e∈) neFV (λ d d∈ → let ⟨ u , i ⟩ = FV⊆ d d∈ in ⟨ u , s _ _ i ⟩)

Bnd-CarEntry : ∀ {k V' U₀ w} → Bnd (suc k) V' → CarEntry V' U₀ w → Bnd k U₀ × depth w < k
Bnd-CarEntry {U₀ = U₀}{w} bV (car-entry FV t e∈ _ _) =
  ⟨ (λ u u∈ → <-shrink (s≤s (≤-trans (depth-⋵ u∈) (≤-trans (m≤m⊔n _ (depth w)) up))) (bV _ e∈))
  , <-shrink (s≤s (≤-trans (m≤n⊔m (depths U₀) _) up)) (bV _ e∈) ⟩
  where up = ≤-trans (n≤1+n _) (≤-trans (m≤n⊔m (depths FV) _) (≤-trans (n≤1+n _) (m≤m⊔n _ (depth t))))

{- Batches of calls ------------------------------------------------------------}

record Calls (V U W : List Value) : Set where
  field
    results : ∀ w → w ⋵ W → Σ[ U₀ ∈ List Value ] CarEntry V U₀ w × U₀ ≢ [] × mem U₀ ⊆ mem U
    args : ∀ u → u ⋵ U → Σ[ U₀ ∈ List Value ] Σ[ w ∈ Value ] CarEntry V U₀ w × u ⋵ U₀
    noerr : NoErr U

Calls-⊆ : ∀ {V₁ V₂ U W} → Pairs⊆ V₁ V₂ → Calls V₁ U W → Calls V₂ U W
Calls-⊆ s cs = record
  { results = λ w w∈ → let ⟨ U₀ , ⟨ e , r ⟩ ⟩ = Calls.results cs w w∈ in ⟨ U₀ , ⟨ CarEntry-⊆ s e , r ⟩ ⟩
  ; args = λ u u∈ → let ⟨ U₀ , ⟨ w , ⟨ e , r ⟩ ⟩ ⟩ = Calls.args cs u u∈ in ⟨ U₀ , ⟨ w , ⟨ CarEntry-⊆ s e , r ⟩ ⟩ ⟩
  ; noerr = Calls.noerr cs
  }

Calls-none : ∀ {V U W} → (∀ u v → ⦅ u , v ⦆ ⋵ V → ⊥) → Calls V U W → mem W ⊆ ∅
Calls-none nop cs w w∈ = nop _ _ (CarEntry.car∈ (proj₁ (proj₂ (Calls.results cs w w∈))))

Bnd-Calls-args : ∀ {k V U W} → Bnd (suc k) V → Calls V U W → Bnd k U
Bnd-Calls-args bV cs u u∈ =
  let ⟨ _ , ⟨ _ , ⟨ e , u∈U₀ ⟩ ⟩ ⟩ = Calls.args cs u u∈ in proj₁ (Bnd-CarEntry bV e) u u∈U₀

Bnd-Calls-apps : ∀ {k V U W} → Bnd (suc k) V → Calls V U W → Bnd k W
Bnd-Calls-apps bV cs w w∈ = proj₂ (Bnd-CarEntry bV (proj₁ (proj₂ (Calls.results cs w w∈))))

{- The relation ---------------------------------------------------------------}

record Obs (Q : List Value → 𝒫 Value → Set₁) (V : List Value) (D : 𝒫 Value) : Set₁ where
  field
    err-obs : ω ⋵ V → ω ∈ D
    const-obs : ∀ {B} (c : base-rep B) → const c ⋵ V → const c ∈ D
    kind-obs : ∀ d → d ⋵ V → d ≢ ω → Σ[ s ∈ Value ] s ∈ ⌊ D ⌋ × kind s ≡ kind₄ (kind d)
    app-obs : ∀ {U W} → Calls V U W → ∀ E → Con E → Con (mem U) → Q U E → Q W (D ● E)
    tag-obs : ∀ t W → mem W ⊆ Untag t (mem V) → Q W (Untag t D)

Obs-map : ∀ {k j Q₁ Q₂ V D} → Bnd (suc k) V → Bnd (suc j) V
  → (∀ {W E} → Bnd k W → Bnd j W → Q₁ W E → Q₂ W E)
  → (∀ {W E} → Bnd j W → Bnd k W → Q₂ W E → Q₁ W E)
  → Obs Q₁ V D → Obs Q₂ V D
Obs-map bk bj to from o = record
  { err-obs = err-obs ; const-obs = const-obs ; kind-obs = kind-obs
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
    { err-obs = λ ω∈ → ⊥-elim (V⊆∅ _ ω∈)
    ; const-obs = λ c c∈ → ⊥-elim (V⊆∅ _ c∈)
    ; kind-obs = λ d d∈ _ → ⊥-elim (V⊆∅ _ d∈)
    ; app-obs = λ cs E _ _ _ → R′-∅ k (Calls-none (λ u v uv∈ → V⊆∅ _ uv∈) cs)
    ; tag-obs = λ t W W⊆ → R′-∅ k (λ d d∈ → V⊆∅ _ (W⊆ d d∈))
    }

  R′-data : ∀ k {V D} → mem V ⊆ D → (∀ v → v ⋵ V → Data v) → R′ k V D
  R′-data zero _ _ = ptt
  R′-data (suc k) {V} V⊆ fl = record
    { err-obs = λ ω∈ → V⊆ _ ω∈
    ; const-obs = λ c c∈ → V⊆ _ c∈
    ; kind-obs = λ d d∈ d≢ → ⟨ d , ⟨ ⟨ V⊆ d d∈ , d≢ ⟩ , data-kind d (fl d d∈) ⟩ ⟩
    ; app-obs = λ cs E _ _ _ → R′-∅ k (Calls-none (λ u v uv∈ → noflat (fl _ uv∈)) cs)
    ; tag-obs = λ t W W⊆ →
        R′-data k (λ d d∈ → V⊆ _ (W⊆ d d∈)) (λ d d∈ → data-untag t (fl _ (W⊆ d d∈)))
    }
    where noflat : ∀ {u v} → Data ⦅ u , v ⦆ → ⊥
          noflat ()

  R′-mono : ∀ k {V D₁ D₂} → D₁ ⊆ D₂ → R′ k V D₁ → R′ k V D₂
  R′-mono zero _ _ = ptt
  R′-mono (suc k) D⊆ r = record
    { err-obs = λ ω∈ → D⊆ _ (err-obs ω∈)
    ; const-obs = λ c c∈ → D⊆ _ (const-obs c c∈)
    ; kind-obs = λ d d∈ d≢ → let ⟨ s , ⟨ s∈ , k ⟩ ⟩ = kind-obs d d∈ d≢ in ⟨ s , ⟨ ⌊⌋-mono D⊆ s s∈ , k ⟩ ⟩
   
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

R-mono : ∀ {V D₁ D₂} → D₁ ⊆ D₂ → R V D₁ → R V D₂
R-mono = R′-mono _

{- the values of V₂ are in V₁, and its ω is in D -}
R-sub : ∀ {V₁ V₂ D} → (∀ w → w ⋵ V₂ → w ≢ ω → w ⋵ V₁) → (ω ⋵ V₂ → ω ∈ D) → R V₁ D → R V₂ D
R-sub {V₁} {V₂} sub err r = fold record
  { err-obs = err
  ; const-obs = λ c c∈ → const-obs c (sub _ c∈ (λ ()))
  ; kind-obs = λ d d∈ d≢ → kind-obs d (sub d d∈ d≢) d≢
  ; app-obs = λ cs → app-obs (Calls-⊆ (λ u v uv∈ → sub _ uv∈ (λ ())) cs)
  ; tag-obs = λ t W W⊆ → tag-obs t W (λ d d∈ → sub _ (W⊆ d d∈) (tag≢ω t))
  }
  where open Obs (unfold r)

R-⊆ : ∀ {V₁ V₂ D} → mem V₁ ⊆ mem V₂ → R V₂ D → R V₁ D
R-⊆ s r = R-sub (λ w w∈ _ → s w w∈) (λ ω∈ → Obs.err-obs (unfold r) (s ω ω∈)) r

{- what a relation gives, for one target value -}
R-err : ∀ {D} → R (ω ∷ []) D → ω ∈ D
R-err r = Obs.err-obs (unfold r) (here refl)

R-conv : ∀ {d D} → R (d ∷ []) D → d ≢ ω → Conv D
R-conv r d≢ = let ⟨ s , ⟨ s∈ , _ ⟩ ⟩ = Obs.kind-obs (unfold r) _ (here refl) d≢ in ⟨ s , s∈ ⟩

{- Reflecting errors through the monad -------------------------------------------}

{- the values of V are in A, and its ω in D -}
R-cases : ∀ {V A D} → (∀ w → w ⋵ V → w ≢ ω → w ∈ A) → (ω ⋵ V → ω ∈ D)
  → (∀ W → mem W ⊆ A → R W D) → R V D
R-cases {V} vA err h =
  R-sub (dropω-keep V) err (h (dropω V) (λ w w∈ → vA w (dropω-⊆ V w w∈) (dropω-noω V w w∈)))

{- the target lists of A' are related to B -}
Rel : 𝒫 Value → 𝒫 Value → Set₁
Rel A' B = ∀ W → mem W ⊆ A' → R W B

{- a target bind is related to D when its errors are errors of D and its
   continuation, on the values of its operand, is related to D -}
R-bindₗ : ∀ {A' F' D} → (ω ∈ A' → ω ∈ D) → (Conv A' → Rel (F' ⌊ A' ⌋) D) → Rel (A' ≫= F') D
R-bindₗ {A'} {F'} {D} err hF V V⊆ = R-cases {A = λ w → Conv A' × w ∈ F' ⌊ A' ⌋} vals errs go
  where
  vals : ∀ w → w ⋵ V → w ≢ ω → Conv A' × w ∈ F' ⌊ A' ⌋
  vals w w∈ w≢ with V⊆ w w∈
  ... | inj₁ ⟨ refl , _ ⟩ = ⊥-elim (w≢ refl)
  ... | inj₂ r = r
  errs : ω ⋵ V → ω ∈ D
  errs ω∈ with V⊆ ω ω∈
  ... | inj₁ ⟨ _ , ω∈' ⟩ = err ω∈'
  ... | inj₂ ⟨ c , ω∈F ⟩ = R-err (hF c (ω ∷ []) (single⊆ ω∈F))
  go : ∀ W → mem W ⊆ (λ w → Conv A' × w ∈ F' ⌊ A' ⌋) → R W D
  go [] _ = R-∅ (λ _ ())
  go (w ∷ W) W⊆ = hF (proj₁ (W⊆ w (here refl))) (w ∷ W) (λ x x∈ → proj₂ (W⊆ x x∈))

{- a target bind reflects to a source bind: the operand A' to A, and the
   continuation F' to F on their values -}
R-bind : ∀ {A' A F' F} → Con A → Rel A' A
  → (Conv A' → Conv A → Rel ⌊ A' ⌋ ⌊ A ⌋ → Rel (F' ⌊ A' ⌋) (F ⌊ A ⌋))
  → Rel (A' ≫= F') (A ≫= F)
R-bind {A'} {A} {F'} {F} cA hA hF =
  R-bindₗ {A'} {F'} {A ≫= F} (λ ω∈ → inj₁ ⟨ refl , R-err (hA (ω ∷ []) (single⊆ ω∈)) ⟩)
          (λ c W W⊆ → R-mono (λ x x∈ → inj₂ ⟨ cv c , x∈ ⟩) (hF c (cv c) (hX c) W W⊆))
  where
  cv : Conv A' → Conv A
  cv ⟨ d , ⟨ d∈ , d≢ ⟩ ⟩ = R-conv (hA (d ∷ []) (single⊆ d∈)) d≢
  hX : ∀ c → Rel ⌊ A' ⌋ ⌊ A ⌋
  hX c W W⊆ = R-mono (⌊⌋-clean (con-clean cA (cv c))) (hA W (λ w w∈ → proj₁ (W⊆ w w∈)))

{- Project ---------------------------------------------------------------------}

{- a target check is related to D when its failure is an error of D -}
R-checkₗ : ∀ {k' X' A' D} → (Σ[ d ∈ Value ] d ∈ X' × kind₄ (kind d) ≢ k' → ω ∈ D) → Rel A' D → Rel (checkedᵠ kind₄ k' X' A') D
R-checkₗ {k'} {X'} {A'} {D} bad hA V V⊆ = R-cases {A = A'} vals err hA
  where
  vals : ∀ w → w ⋵ V → w ≢ ω → w ∈ A'
  vals w w∈ w≢ with V⊆ w w∈
  ... | inj₁ ⟨ refl , _ ⟩ = ⊥-elim (w≢ refl)
  ... | inj₂ r = r
  err : ω ⋵ V → ω ∈ D
  err ω∈ with V⊆ ω ω∈
  ... | inj₂ ω∈A' = R-err (hA _ (single⊆ ω∈A'))
  ... | inj₁ ⟨ _ , b ⟩ = bad b

{- a target value of the wrong kind gives a source value of the wrong kind -}
bad-reflect : ∀ {k X' X} → Clean X' → Rel X' X → Σ[ d ∈ Value ] d ∈ X' × kind₄ (kind d) ≢ k → Bad k X
bad-reflect clX hX ⟨ d , ⟨ d∈ , dk ⟩ ⟩ with Obs.kind-obs (unfold (hX _ (single⊆ d∈))) _ (here refl) (clX d d∈)
... | ⟨ s , ⟨ s∈ , sk ⟩ ⟩ = ⟨ s , ⟨ proj₁ s∈ , (λ eq → dk (trans (sym sk) eq)) ⟩ ⟩

tag-kind : ∀ t {a b} → kind (tag t a) ≡ kind₄ (kind (tag t b))
tag-kind (tupT i) = refl
tag-kind leftT = refl
tag-kind rightT = refl

{- a target tuple entry for a component gives a source one -}
hit-reflect : ∀ t {X' X} → Rel X' X → hit t X' → hit t X
hit-reflect (ttup n i) h ⟨ e , e∈ ⟩ with ω? e
... | inj₁ refl = ⟨ ω , R-err (Obs.tag-obs (unfold (h _ (single⊆ e∈))) (tupT i) (ω ∷ []) (λ { _ (here refl) → here refl })) ⟩
... | inj₂ e≢ = let ⟨ s , s∈ ⟩ = R-conv (Obs.tag-obs (unfold (h _ (single⊆ e∈))) (tupT i) (e ∷ []) (λ { _ (here refl) → here refl })) e≢
                in ⟨ s , proj₁ s∈ ⟩
hit-reflect tfun h _ = tt
hit-reflect tsum h _ = tt
hit-reflect tint h _ = tt

{- the target values that project keeps are related to the source ones -}
R-restrict : ∀ t {X' X} → Rel X' X → Rel (keep kind₄ t X') (keep (λ k → k) t X)
R-restrict t {X'} {X} h W W⊆ = fold record
  { err-obs = λ ω∈ → ⟨ err-obs ω∈ , ⟨ hitX ω∈ , proj₂ (proj₂ (W⊆ ω ω∈)) ⟩ ⟩
  ; const-obs = λ c c∈ → ⟨ const-obs c c∈ , ⟨ hitX c∈ , proj₂ (proj₂ (W⊆ _ c∈)) ⟩ ⟩
  ; kind-obs = λ d d∈ d≢ → let ⟨ s , ⟨ s∈ , e ⟩ ⟩ = kind-obs d d∈ d≢ in
      ⟨ s , ⟨ ⟨ ⟨ proj₁ s∈ , ⟨ hitX d∈ , trans e (proj₂ (proj₂ (W⊆ d d∈))) ⟩ ⟩ , proj₂ s∈ ⟩ , e ⟩ ⟩
  ; app-obs = app
  ; tag-obs = tg }
  where
  open Obs (unfold (h W (λ d d∈ → proj₁ (W⊆ d d∈))))
  k = kindᶠ (flat t)
  hitX : ∀ {d} → d ⋵ W → hit t X
  hitX d∈ = hit-reflect t h (proj₁ (proj₂ (W⊆ _ d∈)))
  app : ∀ {U W₂} → Calls W U W₂ → ∀ E → Con E → Con (mem U) → R U E → R W₂ (keep (λ k → k) t X ● E)
  app {W₂ = []} _ _ _ _ _ = R-∅ (λ _ ())
  app {W₂ = w ∷ W₂} cs E cE cU rU =
    R-mono (●-mono-e {X} {keep (λ k → k) t X} (λ V x e∈ → ⟨ e∈ , ⟨ hitX c∈ , proj₂ (proj₂ (W⊆ _ c∈)) ⟩ ⟩))
      (app-obs cs E cE cU rU)
    where c∈ = CarEntry.car∈ (proj₁ (proj₂ (Calls.results cs w (here refl))))
  tg : ∀ t' W' → mem W' ⊆ Untag t' (mem W) → R W' (Untag t' (keep (λ k → k) t X))
  tg t' [] _ = R-∅ (λ _ ())
  tg t' (w ∷ W') W'⊆ =
    R-mono (λ d d∈ → ⟨ d∈ , ⟨ hitX (W'⊆ w (here refl)) , trans (tag-kind t') (proj₂ (proj₂ (W⊆ _ (W'⊆ w (here refl))))) ⟩ ⟩) (tag-obs t' (w ∷ W') W'⊆)

{- the initial environment of a closed program -}
Init-R : ∀ {V} → mem V ⊆ ⌈ ω ⌉ → R V ⌈ ω ⌉
Init-R V⊆ = R-data V⊆ (λ v v∈ → flat-data (Init-flat (V⊆ v v∈)))

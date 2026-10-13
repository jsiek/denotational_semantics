{-

  Definitions for the delay pass (Clos3 → Clos4) in the graph model with
  errors: the application of a target closure (⊙), how a target value
  corresponds to a source value (Corr), and the logical relation of the
  backward (reflect) direction, indexed by finite lists of target
  observations, as in proof/Correctness/Graph/DelayFiniteRel.agda.

  What is new with errors:

  * ω is a target observation: ω in the list means ω in the source set
    (err-obs);
  * every other target value has a corresponding source value of the
    same kind (shape-obs, Corr): a constant itself, a tuple of the same
    size, an injection on the same side, a function for a pair (a target
    closure). This replaces the constant and nonemptiness clauses, and
    gives the source errors of the wrong kind from the target's;
  * the car of a target pair is a function (car-obs), so the late code
    check of a Clos4 call never fails on a closure delay built;
  * the arguments of a batch of calls hold no ω, as binders bind no ω.

-}

open import proof.Framework.GraphModel.SetsAsPredicates
open import Framework.Primitives
open import proof.Framework.GraphModel.Domain
open import proof.Framework.GraphModel.OpsBase
open import proof.Framework.GraphModel.ErrorOps
open import proof.Framework.GraphModel.DomainUtilBase
open import proof.Semantics.GraphErr.Prim using (IsInt; out)
open import Language.Prim using (int; bool)
open import Data.Bool using (true; false)
import proof.Framework.GraphModel.Env

open import Data.Nat using (ℕ; zero; suc; _<_; s≤s)
open import Data.Nat.Properties using (≤-trans; m≤m⊔n; m≤n⊔m; n≤1+n)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Membership.Propositional renaming (_∈_ to _⋵_)
open import Data.Product using (_×_; proj₁; proj₂; Σ-syntax) renaming (_,_ to ⟨_,_⟩ )
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (tt)
open import Data.Unit.Polymorphic using () renaming (tt to ptt; ⊤ to pTrue)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary using (¬_; Dec; yes; no)

module proof.Correctness.GraphErr.DelayRel where

{- Shorthands ----------------------------------------------------------------}

Env : Set₁
Env = proof.Framework.GraphModel.Env.Env Value

{- source application -}
_●_ : 𝒫 Value → 𝒫 Value → 𝒫 Value
D ● E = ⋆ᵉ ⟨ D , ⟨ E , ptt ⟩ ⟩

{- application of a target closure: its code, its environment, and E -}
_⊙_ : 𝒫 Value → 𝒫 Value → 𝒫 Value
D ⊙ E = callᵉ ⟨ carᵉ ⟨ D , ptt ⟩ , ⟨ cdrᵉ ⟨ D , ptt ⟩ , ⟨ E , ptt ⟩ ⟩ ⟩

●-mono-l : ∀ {D₁ D₂ E} → D₁ ⊆ D₂ → (D₁ ● E) ⊆ (D₂ ● E)
●-mono-l {D₁}{D₂}{E} D⊆ = lower (⋆ᵉ-mono ⟨ D₁ , ⟨ E , ptt ⟩ ⟩ ⟨ D₂ , ⟨ E , ptt ⟩ ⟩ ⟨ lift D⊆ , ⟨ lift (λ d z → z) , ptt ⟩ ⟩)
  where open import Level using (lift; lower)

⊙-mono-l : ∀ {D₁ D₂ E} → D₁ ⊆ D₂ → (D₁ ⊙ E) ⊆ (D₂ ⊙ E)
⊙-mono-l {D₁}{D₂}{E} D⊆ =
  lower (callᵉ-mono _ _ ⟨ carᵉ-mono ⟨ D₁ , ptt ⟩ ⟨ D₂ , ptt ⟩ ⟨ lift D⊆ , ptt ⟩
                        , ⟨ cdrᵉ-mono ⟨ D₁ , ptt ⟩ ⟨ D₂ , ptt ⟩ ⟨ lift D⊆ , ptt ⟩ , ⟨ lift (λ d z → z) , ptt ⟩ ⟩ ⟩)
  where open import Level using (lift; lower)

is-ω? : ∀ v → Dec (v ≡ ω)
is-ω? ω = yes refl
is-ω? (const k) = no (λ ())
is-ω? (V ↦ w) = no (λ ())
is-ω? ν = no (λ ())
is-ω? ⦅ u , v ⦆ = no (λ ())
is-ω? (tup[ i ] d) = no (λ ())
is-ω? (left d) = no (λ ())
is-ω? (right d) = no (λ ())
is-ω? ⟨⟩ = no (λ ())

tag≢ω : ∀ t {d} → tag t d ≢ ω
tag≢ω (tupT i) ()
tag≢ω leftT ()
tag≢ω rightT ()

{- the list without its ω -}
dropω : List Value → List Value
dropω [] = []
dropω (v ∷ V) with is-ω? v
... | yes _ = dropω V
... | no _ = v ∷ dropω V

dropω-⊆ : ∀ V → mem (dropω V) ⊆ mem V
dropω-⊆ (v ∷ V) d d∈ with is-ω? v
... | yes _ = there (dropω-⊆ V d d∈)
dropω-⊆ (v ∷ V) d (here refl) | no _ = here refl
dropω-⊆ (v ∷ V) d (there d∈) | no _ = there (dropω-⊆ V d d∈)

dropω-keep : ∀ V w → w ⋵ V → w ≢ ω → w ⋵ dropω V
dropω-keep (v ∷ V) w w∈ w≢ with is-ω? v
dropω-keep (v ∷ V) .v (here refl) w≢ | yes eq = ⊥-elim (w≢ eq)
dropω-keep (v ∷ V) w (there w∈) w≢ | yes _ = dropω-keep V w w∈ w≢
dropω-keep (v ∷ V) .v (here refl) w≢ | no _ = here refl
dropω-keep (v ∷ V) w (there w∈) w≢ | no _ = there (dropω-keep V w w∈ w≢)

dropω-noω : ∀ V w → w ⋵ dropω V → w ≢ ω
dropω-noω (v ∷ V) w w∈ with is-ω? v
... | yes _ = dropω-noω V w w∈
dropω-noω (v ∷ V) .v (here refl) | no v≢ = v≢
dropω-noω (v ∷ V) w (there w∈) | no _ = dropω-noω V w w∈

{- Corresponding values ---------------------------------------------------------}

{- the source value s corresponds to the target value d: a constant to
   itself, a tuple, an injection to one of the same kind, a target
   closure (a pair) to a function; a bare target function to nothing, as
   delay builds none -}
Corr : Value → Value → Set
Corr (const k) s = s ≡ const k
Corr ⟨⟩ s = s ≡ ⟨⟩
Corr (tup[_]_ {m} i x) s = Σ[ y ∈ Value ] s ≡ tup[_]_ {m} i y
Corr (left x) s = Σ[ y ∈ Value ] s ≡ left y
Corr (right x) s = Σ[ y ∈ Value ] s ≡ right y
Corr ⦅ u , t ⦆ s = IsFun s
Corr _ s = ⊥

corr-fun : ∀ d s → Corr d s → IsFun s → IsPair d
corr-fun ⦅ u , t ⦆ s c f = tt
corr-fun (const k) .(const k) refl ()
corr-fun ⟨⟩ .⟨⟩ refl ()
corr-fun (tup[ i ] x) .(tup[ i ] y) ⟨ y , refl ⟩ ()
corr-fun (left x) .(left y) ⟨ y , refl ⟩ ()
corr-fun (right x) .(right y) ⟨ y , refl ⟩ ()

corr-tup : ∀ {n} d s → Corr d s → IsTup n s → IsTup n d
corr-tup (const k) .(const k) refl ()
corr-tup ⟨⟩ .⟨⟩ refl t = t
corr-tup (tup[ i ] x) .(tup[ i ] y) ⟨ y , refl ⟩ t = t
corr-tup (left x) .(left y) ⟨ y , refl ⟩ ()
corr-tup (right x) .(right y) ⟨ y , refl ⟩ ()
corr-tup ⦅ u , t ⦆ (V ↦ w) c ()
corr-tup ⦅ u , t ⦆ ν c ()

corr-inj : ∀ d s → Corr d s → IsInj s → IsInj d
corr-inj (const k) .(const k) refl ()
corr-inj ⟨⟩ .⟨⟩ refl ()
corr-inj (tup[ i ] x) .(tup[ i ] y) ⟨ y , refl ⟩ ()
corr-inj (left x) .(left y) ⟨ y , refl ⟩ t = tt
corr-inj (right x) .(right y) ⟨ y , refl ⟩ t = tt
corr-inj ⦅ u , t ⦆ (V ↦ w) c ()
corr-inj ⦅ u , t ⦆ ν c ()

corr-int : ∀ d s → Corr d s → IsInt s → IsInt d
corr-int (const k) .(const k) refl i = i
corr-int ⟨⟩ .⟨⟩ refl ()
corr-int (tup[ i ] x) .(tup[ i ] y) ⟨ y , refl ⟩ ()
corr-int (left x) .(left y) ⟨ y , refl ⟩ ()
corr-int (right x) .(right y) ⟨ y , refl ⟩ ()
corr-int ⦅ u , t ⦆ (V ↦ w) c ()
corr-int ⦅ u , t ⦆ ν c ()

{- the results of the primitives are first-order data -}
out-data : ∀ o → Data (out o)
out-data (int n) = flat-const
out-data (bool true) = flat-⟨⟩
out-data (bool false) = flat-⟨⟩

{- data correspond to themselves -}
corr-data : ∀ d → Data d → d ≢ ω → Corr d d
corr-data (const k) _ _ = refl
corr-data ⟨⟩ _ _ = refl
corr-data (left x) _ _ = ⟨ x , refl ⟩
corr-data (right x) _ _ = ⟨ x , refl ⟩
corr-data ω _ ne = ⊥-elim (ne refl)

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
    shape-obs : ∀ d → d ⋵ V → d ≢ ω → Σ[ s ∈ Value ] s ∈ D × s ≢ ω × Corr d s
    pair-obs : ∀ c t → ⦅ c , t ⦆ ⋵ V → IsFun c × t ≢ ω
    app-obs : ∀ {U W} → Calls V U W → ∀ E → Con E → Con (mem U) → Q U E → Q W (D ● E)
    tag-obs : ∀ t W → mem W ⊆ Untag t (mem V) → Q W (Untag t D)

Obs-map : ∀ {k j Q₁ Q₂ V D} → Bnd (suc k) V → Bnd (suc j) V
  → (∀ {W E} → Bnd k W → Bnd j W → Q₁ W E → Q₂ W E)
  → (∀ {W E} → Bnd j W → Bnd k W → Q₂ W E → Q₁ W E)
  → Obs Q₁ V D → Obs Q₂ V D
Obs-map bk bj to from o = record
  { err-obs = err-obs
  ; shape-obs = shape-obs
  ; pair-obs = pair-obs
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

infix 4 _⊳ₑ_
_⊳ₑ_ : Env → Env → Set₁
ρ₁ ⊳ₑ ρ₂ = ∀ x V → mem V ⊆ ρ₁ x → R V (ρ₂ x)

private
  R′-∅ : ∀ k {V D} → mem V ⊆ ∅ → R′ k V D
  R′-∅ zero _ = ptt
  R′-∅ (suc k) {V} V⊆∅ = record
    { err-obs = λ ω∈ → ⊥-elim (V⊆∅ _ ω∈)
    ; shape-obs = λ d d∈ _ → ⊥-elim (V⊆∅ _ d∈)
    ; pair-obs = λ c t ct∈ → ⊥-elim (V⊆∅ _ ct∈)
    ; app-obs = λ cs E _ _ _ → R′-∅ k (Calls-none (λ u v uv∈ → V⊆∅ _ uv∈) cs)
    ; tag-obs = λ t W W⊆ → R′-∅ k (λ d d∈ → V⊆∅ _ (W⊆ d d∈))
    }

  R′-data : ∀ k {V D} → mem V ⊆ D → (∀ v → v ⋵ V → Data v) → R′ k V D
  R′-data zero _ _ = ptt
  R′-data (suc k) {V} V⊆ fl = record
    { err-obs = λ ω∈ → V⊆ _ ω∈
    ; shape-obs = λ d d∈ d≢ → ⟨ d , ⟨ V⊆ d d∈ , ⟨ d≢ , corr-data d (fl d d∈) d≢ ⟩ ⟩ ⟩
    ; pair-obs = λ c t ct∈ → ⊥-elim (noflat (fl _ ct∈))
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
    ; shape-obs = λ d d∈ d≢ → let ⟨ s , ⟨ s∈ , rest ⟩ ⟩ = shape-obs d d∈ d≢ in ⟨ s , ⟨ D⊆ s s∈ , rest ⟩ ⟩
    ; pair-obs = pair-obs
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

{- the values of V₂ other than ω are in V₁, and its ω is in D -}
R-sub : ∀ {V₁ V₂ D} → (∀ w → w ⋵ V₂ → w ≢ ω → w ⋵ V₁) → (ω ⋵ V₂ → ω ∈ D) → R V₁ D → R V₂ D
R-sub {V₁} {V₂} sub err r = fold record
  { err-obs = err
  ; shape-obs = λ d d∈ d≢ → shape-obs d (sub d d∈ d≢) d≢
  ; pair-obs = λ c t ct∈ → pair-obs c t (sub _ ct∈ (λ ()))
  ; app-obs = λ cs → app-obs (Calls-⊆ (λ u v uv∈ → sub _ uv∈ (λ ())) cs)
  ; tag-obs = λ t W W⊆ → tag-obs t W (λ d d∈ → sub _ (W⊆ d d∈) (tag≢ω t))
  }
  where open Obs (unfold r)

R-⊆ : ∀ {V₁ V₂ D} → mem V₁ ⊆ mem V₂ → R V₂ D → R V₁ D
R-⊆ {V₁} {V₂} {D} s r = R-sub (λ w w∈ _ → s w w∈) (λ ω∈ → Obs.err-obs (unfold r) (s ω ω∈)) r

{- what a relation gives -}
R-val : ∀ {V D} → R V D → ∀ v → v ⋵ V → v ≢ ω → val∈ D
R-val r v v∈ v≢ = let ⟨ s , ⟨ s∈ , ⟨ s≢ , _ ⟩ ⟩ ⟩ = Obs.shape-obs (unfold r) v v∈ v≢ in ⟨ s , ⟨ s∈ , s≢ ⟩ ⟩

R-err : ∀ {V D} → R V D → ω ⋵ V → ω ∈ D
R-err r = Obs.err-obs (unfold r)

{- a target value of the wrong kind gives a source value of the wrong kind -}
wrong-reflect : ∀ {V D} {P P' : Value → Set} → (∀ d s → Corr d s → P s → P' d)
  → R V D → ∀ d → d ⋵ V → d ≢ ω → ¬ P' d → wrong P D
wrong-reflect {P = P} corr r d d∈ d≢ np with Obs.shape-obs (unfold r) d d∈ d≢
... | ⟨ s , ⟨ s∈ , ⟨ s≢ , c ⟩ ⟩ ⟩ = ⟨ s , ⟨ s∈ , ⟨ s≢ , (λ p → np (corr d s c p)) ⟩ ⟩ ⟩

{- relating the initial environment of a closed program to itself -}
Init⊳Init : ρ₀ ⊳ₑ ρ₀
Init⊳Init x V V⊆ = R-data V⊆ (λ v v∈ → flat-data (Init-flat (V⊆ v v∈)))

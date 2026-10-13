{-

  Definitions for the delay pass (Clos3 → Clos4) in the graph model with errors: the application of a target closure (⊙), the kind
  a source value has for a target value of a kind (tgt), and the logical
  relation of the backward (reflect) direction, indexed by finite lists
  of target observations, as in proof/Correctness/Graph/DelayFiniteRel.agda.

  With errors, ω is a target observation (err-obs), and every other
  target value has a source value whose kind corresponds (kind-obs): a
  target closure (a pair) a function, any other value its own kind.

  The errors of the operators are reflected once, through the monad:
  R-bind reflects a bind (an error of the operand, or of the
  continuation on its values), R-check the check of a kernel (a target
  value of the wrong kind gives a source value of the wrong kind), and
  R-cases splits the errors of a set from its values.

-}

open import proof.Framework.GraphModel.SetsAsPredicates
open import Framework.Primitives
open import proof.Framework.GraphModel.Domain
open import proof.Framework.GraphModel.OpsBase
open import proof.Framework.GraphModel.ErrorMonad
open import proof.Framework.GraphModel.ContinuityBase using (mono)
open import proof.Framework.GraphModel.DomainUtilBase
open import proof.Semantics.GraphErr.Prim using (out)
open import Language.Prim using (int; bool)
open import Data.Bool using (true; false)
import proof.Framework.GraphModel.Env

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

{- Shorthands ----------------------------------------------------------------}

Env : Set₁
Env = proof.Framework.GraphModel.Env.Env Value

{- source application, and the application of a target closure: its code,
   its environment, and E -}
_●_ : 𝒫 Value → 𝒫 Value → 𝒫 Value
D ● E = ⋆ᵐ ⟨ D , ⟨ E , ptt ⟩ ⟩

_⊙_ : 𝒫 Value → 𝒫 Value → 𝒫 Value
D ⊙ E = callᵐ ⟨ carᵐ ⟨ D , ptt ⟩ , ⟨ cdrᵐ ⟨ D , ptt ⟩ , ⟨ E , ptt ⟩ ⟩ ⟩

●-mono-l : ∀ {D₁ D₂ E} → D₁ ⊆ D₂ → (D₁ ● E) ⊆ (D₂ ● E)
●-mono-l D⊆ = lower (mono (⋆ᵐ-good {⊤}) _ _ ⟨ lift D⊆ , ⟨ lift (λ d z → z) , ptt ⟩ ⟩)

⊙-mono-l : ∀ {D₁ D₂ E} → D₁ ⊆ D₂ → (D₁ ⊙ E) ⊆ (D₂ ⊙ E)
⊙-mono-l D⊆ = lower (mono (callᵐ-good {⊤}) _ _
  ⟨ mono (carᵐ-good {⊤}) _ _ ⟨ lift D⊆ , ptt ⟩ , ⟨ mono (cdrᵐ-good {⊤}) _ _ ⟨ lift D⊆ , ptt ⟩ , ⟨ lift (λ d z → z) , ptt ⟩ ⟩ ⟩)

{- the kind of a target value for a source value of kind k: a function
   is a closure, a pair; other kinds are kept -}
tgt : Kind → Kind
tgt fun = prod
tgt k = k

tgt-inj : ∀ x k → x ≢ prod → k ≢ prod → tgt x ≡ tgt k → x ≡ k
tgt-inj fun fun _ _ _ = refl
tgt-inj fun prod _ np _ = ⊥-elim (np refl)
tgt-inj prod k np _ _ = ⊥-elim (np refl)
tgt-inj inj inj _ _ _ = refl
tgt-inj error error _ _ _ = refl
tgt-inj (tup m) (tup n) _ _ refl = refl
tgt-inj (base B) (base C) _ _ refl = refl

{- data correspond to themselves -}
data-tgt : ∀ d → Data d → tgt (kind d) ≡ kind d
data-tgt (const k) _ = refl
data-tgt ⟨⟩ _ = refl
data-tgt (left x) _ = refl
data-tgt (right x) _ = refl
data-tgt ω _ = refl

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
    kind-obs : ∀ d → d ⋵ V → d ≢ ω → Σ[ s ∈ Value ] s ∈ ⌊ D ⌋ × tgt (kind s) ≡ kind d
    pair-obs : ∀ c t → ⦅ c , t ⦆ ⋵ V → kind c ≡ fun × t ≢ ω
    app-obs : ∀ {U W} → Calls V U W → ∀ E → Con E → Con (mem U) → Q U E → Q W (D ● E)
    tag-obs : ∀ t W → mem W ⊆ Untag t (mem V) → Q W (Untag t D)

Obs-map : ∀ {k j Q₁ Q₂ V D} → Bnd (suc k) V → Bnd (suc j) V
  → (∀ {W E} → Bnd k W → Bnd j W → Q₁ W E → Q₂ W E)
  → (∀ {W E} → Bnd j W → Bnd k W → Q₂ W E → Q₁ W E)
  → Obs Q₁ V D → Obs Q₂ V D
Obs-map bk bj to from o = record
  { err-obs = err-obs ; const-obs = const-obs ; kind-obs = kind-obs ; pair-obs = pair-obs
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
    ; const-obs = λ c c∈ → ⊥-elim (V⊆∅ _ c∈)
    ; kind-obs = λ d d∈ _ → ⊥-elim (V⊆∅ _ d∈)
    ; pair-obs = λ c t ct∈ → ⊥-elim (V⊆∅ _ ct∈)
    ; app-obs = λ cs E _ _ _ → R′-∅ k (Calls-none (λ u v uv∈ → V⊆∅ _ uv∈) cs)
    ; tag-obs = λ t W W⊆ → R′-∅ k (λ d d∈ → V⊆∅ _ (W⊆ d d∈))
    }

  R′-data : ∀ k {V D} → mem V ⊆ D → (∀ v → v ⋵ V → Data v) → R′ k V D
  R′-data zero _ _ = ptt
  R′-data (suc k) {V} V⊆ fl = record
    { err-obs = λ ω∈ → V⊆ _ ω∈
    ; const-obs = λ c c∈ → V⊆ _ c∈
    ; kind-obs = λ d d∈ d≢ → ⟨ d , ⟨ ⟨ V⊆ d d∈ , d≢ ⟩ , data-tgt d (fl d d∈) ⟩ ⟩
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
    ; const-obs = λ c c∈ → D⊆ _ (const-obs c c∈)
    ; kind-obs = λ d d∈ d≢ → let ⟨ s , ⟨ s∈ , k ⟩ ⟩ = kind-obs d d∈ d≢ in ⟨ s , ⟨ ⌊⌋-mono D⊆ s s∈ , k ⟩ ⟩
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

{- the values of V₂ are in V₁, and its ω is in D -}
R-sub : ∀ {V₁ V₂ D} → (∀ w → w ⋵ V₂ → w ≢ ω → w ⋵ V₁) → (ω ⋵ V₂ → ω ∈ D) → R V₁ D → R V₂ D
R-sub {V₁} {V₂} sub err r = fold record
  { err-obs = err
  ; const-obs = λ c c∈ → const-obs c (sub _ c∈ (λ ()))
  ; kind-obs = λ d d∈ d≢ → kind-obs d (sub d d∈ d≢) d≢
  ; pair-obs = λ c t ct∈ → pair-obs c t (sub _ ct∈ (λ ()))
  ; app-obs = λ cs → app-obs (Calls-⊆ (λ u v uv∈ → sub _ uv∈ (λ ())) cs)
  ; tag-obs = λ t W W⊆ → tag-obs t W (λ d d∈ → sub _ (W⊆ d d∈) (tag≢ω t))
  }
  where open Obs (unfold r)

R-⊆ : ∀ {V₁ V₂ D} → mem V₁ ⊆ mem V₂ → R V₂ D → R V₁ D
R-⊆ s r = R-sub (λ w w∈ _ → s w w∈) (λ ω∈ → Obs.err-obs (unfold r) (s ω ω∈)) r

{- what a relation gives, for one target value -}
R-err : ∀ {D} → R (ω ∷ []) D → ω ∈ D
R-err r = Obs.err-obs (unfold r) (here refl)

R-kind : ∀ {d D} → R (d ∷ []) D → d ≢ ω → Σ[ s ∈ Value ] s ∈ ⌊ D ⌋ × tgt (kind s) ≡ kind d
R-kind r d≢ = Obs.kind-obs (unfold r) _ (here refl) d≢

R-conv : ∀ {d D} → R (d ∷ []) D → d ≢ ω → Conv D
R-conv r d≢ = let ⟨ s , ⟨ s∈ , _ ⟩ ⟩ = R-kind r d≢ in ⟨ s , s∈ ⟩

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

{- a target check is related to D when its failure is an error of D -}
R-checkₗ : ∀ {k' X' A' D} → (Bad k' X' → ω ∈ D) → Rel A' D → Rel (checked k' X' A') D
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
bad-reflect : ∀ {k X' X} → Clean X' → Rel X' X → Bad (tgt k) X' → Bad k X
bad-reflect clX hX ⟨ d , ⟨ d∈ , dk ⟩ ⟩ with R-kind (hX _ (single⊆ d∈)) (clX d d∈)
... | ⟨ s , ⟨ s∈ , sk ⟩ ⟩ = ⟨ s , ⟨ proj₁ s∈ , (λ eq → dk (trans (sym sk) (cong tgt eq))) ⟩ ⟩

{- the check of a target kernel reflects to the check of the source one -}
R-check : ∀ {k X' X A' A} → Clean X' → Rel X' X → Rel A' A → Rel (checked (tgt k) X' A') (checked k X A)
R-check {k} {X'} {X} {A'} {A} clX hX hA = R-checkₗ {tgt k} {X'} {A'} {checked k X A} (λ b → inj₁ ⟨ refl , bad-reflect clX hX b ⟩) (λ W W⊆ → R-mono (λ x x∈ → inj₂ x∈) (hA W W⊆))

{- relating the initial environment of a closed program to itself -}
Init⊳Init : ρ₀ ⊳ₑ ρ₀
Init⊳Init x V V⊆ = R-data V⊆ (λ v v∈ → flat-data (Init-flat (V⊆ v v∈)))

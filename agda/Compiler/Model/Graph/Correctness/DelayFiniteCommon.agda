{-

  Definitions shared by the proofs for the delay pass (DelayPreserve,
  DelayFiniteRel, DelayReflectFinite) and the other passes: operator
  shorthands, environments, the depth of values, and small lemmas about
  finite lists of values.

-}

open import SetsAsPredicates
open import Primitives
open import Compiler.Model.Graph.Domain.ISWIM.Domain
open import Compiler.Model.Graph.Domain.ISWIM.Ops
import NewEnv

open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; s≤s; _⊔_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; m≤m⊔n; m≤n⊔m)
open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Membership.Propositional renaming (_∈_ to _⋵_)
open import Data.Product using (_×_; Σ-syntax)
  renaming (_,_ to ⟨_,_⟩ )
open import Data.Empty using (⊥-elim)
open import Data.Unit using (tt)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Relation.Binary.PropositionalEquality using (_≢_; refl)
open import Data.Bool using (true; false)
open import Compiler.Lang.Prim using (int; bool)

module Compiler.Model.Graph.Correctness.DelayFiniteCommon where

{- Shorthands ----------------------------------------------------------------}

Env : Set₁
Env = NewEnv.Env Value

_●_ : 𝒫 Value → 𝒫 Value → 𝒫 Value
D ● E = ⋆ ⟨ D , ⟨ E , ptt ⟩ ⟩

Car : 𝒫 Value → 𝒫 Value
Car D = car ⟨ D , ptt ⟩

Cdr : 𝒫 Value → 𝒫 Value
Cdr D = cdr ⟨ D , ptt ⟩

{- application of a target closure: (car D ⋆ cdr D) ⋆ E -}
_⊙_ : 𝒫 Value → 𝒫 Value → 𝒫 Value
D ⊙ E = (Car D ● Cdr D) ● E

{- the projections of the values with a given tag: proj i, left, right -}
data Tag : Set where
  tupT : ∀ {n} → Fin n → Tag
  leftT rightT : Tag

tag : Tag → Value → Value
tag (tupT i) d = tup[ i ] d
tag leftT d = left d
tag rightT d = right d

Untag : Tag → 𝒫 Value → 𝒫 Value
Untag t D d = tag t d ∈ D

Nth : ∀ {n} → Fin n → 𝒫 Value → 𝒫 Value
Nth i = Untag (tupT i)

Lefts : 𝒫 Value → 𝒫 Value
Lefts = Untag leftT

Rights : 𝒫 Value → 𝒫 Value
Rights = Untag rightT

{- the untagged part of a consistent set is consistent -}
Untag-con : ∀ s {D} → (∀ {a b} → tag s a ~ tag s b → a ~ b) → Con D → Con (Untag s D)
Untag-con s s~ cD a b a∈ b∈ = s~ (cD _ _ a∈ b∈)

Init : 𝒫 Value
Init = ⌈ ω ⌉

{- the environment of a closed program -}
ρ₀ : Env
ρ₀ = λ _ → Init

{- Depth ----------------------------------------------------------------------}

depth : Value → ℕ
depths : List Value → ℕ
depth (const k) = 0
depth (V ↦ w) = suc (depths V ⊔ depth w)
depth ν = 0
depth ω = 0
depth ⦅ u , v ⦆ = suc (depth u ⊔ depth v)
depth (tup[ i ] d) = suc (depth d)
depth (left d) = suc (depth d)
depth (right d) = suc (depth d)
depth ⟨⟩ = 0
depths [] = 0
depths (v ∷ V) = depth v ⊔ depths V

depth-⋵ : ∀ {v V} → v ⋵ V → depth v ≤ depths V
depth-⋵ {v} {.v ∷ V} (here refl) = m≤m⊔n (depth v) (depths V)
depth-⋵ {v} {u ∷ V} (there v∈) = ≤-trans (depth-⋵ v∈) (m≤n⊔m (depth u) (depths V))

{- Bnd k V says that every element of V has depth less than k -}
Bnd : ℕ → List Value → Set
Bnd k V = ∀ v → v ⋵ V → depth v < k

Bnd-depths : ∀ V → Bnd (suc (depths V)) V
Bnd-depths V v v∈ = s≤s (depth-⋵ v∈)

<-shrink : ∀ {a b k} → suc a ≤ b → b < suc k → a < k
<-shrink sa≤b (s≤s b≤k) = ≤-trans sa≤b b≤k

Bnd-Untag : ∀ {k V W} t → Bnd (suc k) V → mem W ⊆ Untag t (mem V) → Bnd k W
Bnd-Untag (tupT i) bV W⊆ d d∈ = <-shrink ≤-refl (bV _ (W⊆ d d∈))
Bnd-Untag leftT bV W⊆ d d∈ = <-shrink ≤-refl (bV _ (W⊆ d d∈))
Bnd-Untag rightT bV W⊆ d d∈ = <-shrink ≤-refl (bV _ (W⊆ d d∈))

{- List helpers ---------------------------------------------------------------}

ne-mem : ∀ {V : List Value}{D : 𝒫 Value} → V ≢ [] → mem V ⊆ D → nonempty D
ne-mem {[]} ne _ = ⊥-elim (ne refl)
ne-mem {v ∷ V} _ V⊆ = ⟨ v , V⊆ v (here refl) ⟩

ne-⊆ : ∀ {V₁ V₂ : List Value} → mem V₁ ⊆ mem V₂ → V₁ ≢ [] → V₂ ≢ []
ne-⊆ {[]} _ ne = ⊥-elim (ne refl)
ne-⊆ {x ∷ V₁} {[]} s _ with s x (here refl)
... | ()
ne-⊆ {x ∷ V₁} {y ∷ V₂} s _ = λ ()

single⊆ : ∀ {v : Value}{D : 𝒫 Value} → v ∈ D → mem (v ∷ []) ⊆ D
single⊆ v∈ _ (here refl) = v∈

●-mono-l : ∀ {D₁ D₂ E} → D₁ ⊆ D₂ → (D₁ ● E) ⊆ (D₂ ● E)
●-mono-l D⊆ w ⟨ V , ⟨ V↦w∈ , ⟨ V⊆E , neV ⟩ ⟩ ⟩ = ⟨ V , ⟨ D⊆ _ V↦w∈ , ⟨ V⊆E , neV ⟩ ⟩ ⟩

Cdr-mono : ∀ {D₁ D₂} → D₁ ⊆ D₂ → Cdr D₁ ⊆ Cdr D₂
Cdr-mono D⊆ v ⟨ u , uv∈ ⟩ = ⟨ u , D⊆ _ uv∈ ⟩

{- finitely many elements of L whose cdrs cover the list FV -}
cdr-witness : ∀ {L} FV → mem FV ⊆ Cdr L
  → Σ[ P ∈ List Value ] mem P ⊆ L × mem FV ⊆ Cdr (mem P)
cdr-witness [] _ = ⟨ [] , ⟨ (λ _ ()) , (λ _ ()) ⟩ ⟩
cdr-witness (fv ∷ FV) FV⊆ with FV⊆ fv (here refl) | cdr-witness FV (λ d d∈ → FV⊆ d (there d∈))
... | ⟨ u , u∈ ⟩ | ⟨ P , ⟨ P⊆ , FV⊆P ⟩ ⟩ = ⟨ ⦅ u , fv ⦆ ∷ P , ⟨ P⊆′ , FV⊆′ ⟩ ⟩
  where
  P⊆′ : mem (⦅ u , fv ⦆ ∷ P) ⊆ _
  P⊆′ _ (here refl) = u∈
  P⊆′ d (there d∈) = P⊆ d d∈
  FV⊆′ : mem (fv ∷ FV) ⊆ Cdr (mem (⦅ u , fv ⦆ ∷ P))
  FV⊆′ _ (here refl) = ⟨ u , here refl ⟩
  FV⊆′ d (there d∈) = let ⟨ u′ , i ⟩ = FV⊆P d d∈ in ⟨ u′ , there i ⟩

⊙-mono-l : ∀ {D₁ D₂ E} → D₁ ⊆ D₂ → (D₁ ⊙ E) ⊆ (D₂ ⊙ E)
⊙-mono-l D⊆ w ⟨ U , ⟨ ⟨ FV , ⟨ ⟨ t , f∈ ⟩ , ⟨ FV⊆ , neFV ⟩ ⟩ ⟩ , ⟨ U⊆ , neU ⟩ ⟩ ⟩ =
  ⟨ U , ⟨ ⟨ FV , ⟨ ⟨ t , D⊆ _ f∈ ⟩ , ⟨ (λ d d∈ → Cdr-mono D⊆ d (FV⊆ d d∈)) , neFV ⟩ ⟩ ⟩
        , ⟨ U⊆ , neU ⟩ ⟩ ⟩

{- Values that have no observations besides themselves ------------------------}

data Flat : Value → Set where
  flat-const : ∀ {B} {c : base-rep B} → Flat (const c)
  flat-ω : Flat ω
  flat-⟨⟩ : Flat ⟨⟩

{- first-order data: flat values under left and right, such as the
   results of the primitives -}
Data : Value → Set
Data (left d) = Data d
Data (right d) = Data d
Data v = Flat v

flat-data : ∀ {v} → Flat v → Data v
flat-data flat-const = flat-const
flat-data flat-ω = flat-ω
flat-data flat-⟨⟩ = flat-⟨⟩

data-untag : ∀ t {d} → Data (tag t d) → Data d
data-untag (tupT i) ()
data-untag leftT dd = dd
data-untag rightT dd = dd

out-data : ∀ o → Data (out o)
out-data (int n) = flat-const
out-data (bool true) = flat-⟨⟩
out-data (bool false) = flat-⟨⟩

{- the empty tuple has only the observation ⟨⟩, whatever its operands -}
𝒯0-flat : ∀ {Ds Es} v → v ∈ 𝒯 0 Ds → v ∈ 𝒯 0 Es × Flat v
𝒯0-flat ⟨⟩ tt = ⟨ tt , flat-⟨⟩ ⟩

Init-flat : ∀ {v} → v ∈ Init → Flat v
Init-flat refl = flat-ω

ℬ-flat : ∀ {B} {c : base-rep B} v → v ∈ ℬ B c ptt → Flat v
ℬ-flat (const k) _ = flat-const

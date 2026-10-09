{-

  Definitions shared by the finite-observation logical relations for the
  delay pass (see DelayFiniteRel, DelayReflectFinite, DelayPreserveFinite):
  operator shorthands, the depth of values, and small lemmas about
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
open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax)
  renaming (_,_ to ⟨_,_⟩ )
open import Data.Empty using (⊥-elim) renaming (⊥ to False)
open import Data.Unit using (tt)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

module Compiler.Model.Graph.Correctness.DelayFiniteCommon where

{- Shorthands ----------------------------------------------------------------}

Env : Set₁
Env = NewEnv.Env Value

consis : 𝒫 Value → Set
consis D = ∀ u v → u ∈ D → v ∈ D → u ~ v

_●_ : 𝒫 Value → 𝒫 Value → 𝒫 Value
D ● E = ⋆ ⟨ D , ⟨ E , ptt ⟩ ⟩

Car : 𝒫 Value → 𝒫 Value
Car D = car ⟨ D , ptt ⟩

Cdr : 𝒫 Value → 𝒫 Value
Cdr D = cdr ⟨ D , ptt ⟩

{- application of a target closure: (car D ⋆ cdr D) ⋆ E -}
_⊙_ : 𝒫 Value → 𝒫 Value → 𝒫 Value
D ⊙ E = (Car D ● Cdr D) ● E

Nth : ∀ {n} → Fin n → 𝒫 Value → 𝒫 Value
Nth i D = proj i ⟨ D , ptt ⟩

Lefts : 𝒫 Value → 𝒫 Value
Lefts D d = left d ∈ D

Rights : 𝒫 Value → 𝒫 Value
Rights D d = right d ∈ D

Init : 𝒫 Value
Init = ⌈ ω ⌉

{- the environment of a closed program -}
ρ₀ : Env
ρ₀ = λ _ → Init

{- projections of a finite list of values -}

Nths : ∀ {n} → Fin n → List Value → 𝒫 Value
Nths i V d = tup[ i ] d ⋵ V

Lefts' : List Value → 𝒫 Value
Lefts' V d = left d ⋵ V

Rights' : List Value → 𝒫 Value
Rights' V d = right d ⋵ V

{- Depth ----------------------------------------------------------------------}

depth : Value → ℕ
depths : List Value → ℕ
depth (const k) = 0
depth (V ↦ w) = suc (depths V ⊔ depth w)
depth ν = 0
depth ω = 0
depth ⦅ u ∣ = suc (depth u)
depth ∣ V ⦆ = suc (depths V)
depth (tup[ i ] d) = suc (depth d)
depth (left d) = suc (depth d)
depth (right d) = suc (depth d)
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

Bnd-single : ∀ v → Bnd (suc (depth v)) (v ∷ [])
Bnd-single v .v (here refl) = ≤-refl

Bnd-⊆ : ∀ {k V W} → mem W ⊆ mem V → Bnd k V → Bnd k W
Bnd-⊆ W⊆V bV w w∈ = bV w (W⊆V w w∈)

<-shrink : ∀ {a b k} → suc a ≤ b → b < suc k → a < k
<-shrink sa≤b (s≤s b≤k) = ≤-trans sa≤b b≤k

<0 : ∀ {n} → n < 0 → False
<0 ()

Bnd-Nths : ∀ {k V W n} {i : Fin n} → Bnd (suc k) V → mem W ⊆ Nths i V → Bnd k W
Bnd-Nths bV W⊆ d d∈ = <-shrink ≤-refl (bV _ (W⊆ d d∈))

Bnd-Lefts : ∀ {k V W} → Bnd (suc k) V → mem W ⊆ Lefts' V → Bnd k W
Bnd-Lefts bV W⊆ d d∈ = <-shrink ≤-refl (bV _ (W⊆ d d∈))

Bnd-Rights : ∀ {k V W} → Bnd (suc k) V → mem W ⊆ Rights' V → Bnd k W
Bnd-Rights bV W⊆ d d∈ = <-shrink ≤-refl (bV _ (W⊆ d d∈))

{- List helpers ---------------------------------------------------------------}

ne-mem : ∀ {V : List Value}{D : 𝒫 Value} → V ≢ [] → mem V ⊆ D → nonempty D
ne-mem {[]} ne _ = ⊥-elim (ne refl)
ne-mem {v ∷ V} _ V⊆ = ⟨ v , V⊆ v (here refl) ⟩

ne-head : ∀ {V : List Value} → V ≢ [] → Σ[ v ∈ Value ] v ⋵ V
ne-head {[]} ne = ⊥-elim (ne refl)
ne-head {v ∷ V} _ = ⟨ v , here refl ⟩

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
Cdr-mono D⊆ d ⟨ FVs , ⟨ ∣FVs⦆∈ , d∈FVs ⟩ ⟩ = ⟨ FVs , ⟨ D⊆ _ ∣FVs⦆∈ , d∈FVs ⟩ ⟩

⊙-mono-l : ∀ {D₁ D₂ E} → D₁ ⊆ D₂ → (D₁ ⊙ E) ⊆ (D₂ ⊙ E)
⊙-mono-l {D₁}{D₂} D⊆ w ⟨ U , ⟨ ⟨ FV , ⟨ f∈ , ⟨ FV⊆ , neFV ⟩ ⟩ ⟩ , ⟨ U⊆ , neU ⟩ ⟩ ⟩ =
  ⟨ U , ⟨ ⟨ FV , ⟨ D⊆ _ f∈ , ⟨ (λ d d∈ → Cdr-mono {D₁}{D₂} D⊆ d (FV⊆ d d∈)) , neFV ⟩ ⟩ ⟩
        , ⟨ U⊆ , neU ⟩ ⟩ ⟩

{- Values that have no observations besides themselves ------------------------}

data Flat : Value → Set where
  flat-const : ∀ {B} {c : base-rep B} → Flat (const c)
  flat-ω : Flat ω

flat-car : ∀ {u} → Flat ⦅ u ∣ → False
flat-car ()

flat-fun : ∀ {V w} → Flat (V ↦ w) → False
flat-fun ()

flat-tup : ∀ {n} {i : Fin n} {d} → Flat (tup[ i ] d) → False
flat-tup ()

flat-left : ∀ {d} → Flat (left d) → False
flat-left ()

flat-right : ∀ {d} → Flat (right d) → False
flat-right ()

Init-flat : ∀ {v} → v ∈ Init → Flat v
Init-flat refl = flat-ω

Init-consis : consis Init
Init-consis .ω .ω refl refl = tt

{- Inversion lemmas -----------------------------------------------------------}

pair-ne : ∀ {A B : 𝒫 Value} v → v ∈ pair ⟨ A , ⟨ B , ptt ⟩ ⟩ → nonempty B
pair-ne ⦅ f ∣ ⟨ FV , ⟨ _ , ⟨ FV⊆ , ne ⟩ ⟩ ⟩ = ne-mem ne FV⊆
pair-ne ∣ FV ⦆ ⟨ f , ⟨ _ , ⟨ FV⊆ , ne ⟩ ⟩ ⟩ = ne-mem ne FV⊆
pair-ne (const k) ()
pair-ne (V ↦ w) ()
pair-ne ν ()
pair-ne ω ()
pair-ne (tup[ i ] d) ()
pair-ne (left d) ()
pair-ne (right d) ()

cdr-pair : ∀ {A B : 𝒫 Value}{FV} → ∣ FV ⦆ ∈ pair ⟨ A , ⟨ B , ptt ⟩ ⟩ → mem FV ⊆ B
cdr-pair ⟨ f , ⟨ _ , ⟨ FV⊆ , _ ⟩ ⟩ ⟩ = FV⊆

ℒ-inv : ∀ {D : 𝒫 Value} v → v ∈ ℒ ⟨ D , ptt ⟩ → Σ[ d ∈ Value ] v ≡ left d × d ∈ D
ℒ-inv (left d) d∈ = ⟨ d , ⟨ refl , d∈ ⟩ ⟩
ℒ-inv (const k) ()
ℒ-inv (V ↦ w) ()
ℒ-inv ν ()
ℒ-inv ω ()
ℒ-inv ⦅ u ∣ ()
ℒ-inv ∣ V ⦆ ()
ℒ-inv (tup[ i ] d) ()
ℒ-inv (right d) ()

ℛ-inv : ∀ {D : 𝒫 Value} v → v ∈ ℛ ⟨ D , ptt ⟩ → Σ[ d ∈ Value ] v ≡ right d × d ∈ D
ℛ-inv (right d) d∈ = ⟨ d , ⟨ refl , d∈ ⟩ ⟩
ℛ-inv (const k) ()
ℛ-inv (V ↦ w) ()
ℛ-inv ν ()
ℛ-inv ω ()
ℛ-inv ⦅ u ∣ ()
ℛ-inv ∣ V ⦆ ()
ℛ-inv (tup[ i ] d) ()
ℛ-inv (left d) ()

ℬ-flat : ∀ {B} {c : base-rep B} v → v ∈ ℬ B c ptt → Flat v
ℬ-flat (const k) _ = flat-const
ℬ-flat (V ↦ w) ()
ℬ-flat ν ()
ℬ-flat ω ()
ℬ-flat ⦅ u ∣ ()
ℬ-flat ∣ V ⦆ ()
ℬ-flat (tup[ i ] d) ()
ℬ-flat (left d) ()
ℬ-flat (right d) ()

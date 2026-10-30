{-

  A design-space fact about the relation for the reflect half of delay
  (EnvClosμ → PairClosμ) in the graph model (DelayRel, DelayReflect): its
  source side must be a whole, possibly infinite, source set, not a
  single element or a finite list. Two examples show it: one whose
  source sets differ only by duplicate inputs (1, 2), and one with no
  duplicate inputs (3). Not part of the proof of the compiler, and in
  no size count.

  1. Disjoint related arguments. The target list U = [u₁], where u₁ is
     the target closure of λx.1 with the code entry [⟨⟩] ↦ ([1] ↦ 1),
     is related (ApproxLR) to each source set E n = {[1,…,1] ↦ 1}
     (n+1 ones). The E n are consistent, nonempty and pairwise
     disjoint (E-con, E-ne, E-disjoint, E-related). They are parts of
     the source denotation of λx.1, and U is a finite part of its
     target denotation (E⊆λ1, U⊆λ1').

  2. A finite source side fails clause 3 (app-obs). For the identity
     closure idC = clos (` Z) [] (λy.y), the target list V = [v-id],
     with the code entry [⟨⟩] ↦ (U ↦ u₁), calls on U with results
     W = [u₁] (calls). The fundamental lemma (delay-reflect) gives
     ApproxLR (D ● E n) W for every n, with D the whole source
     denotation of idC (whole-source). But for every finite list D₀ of
     values (whether or not in D) there is an n with D₀ ● E n empty
     (finite-empty), so ¬ ApproxLR (mem D₀ ● E n) W (finite-source).
     The reason is the one of the paper: an entry X ↦ w of D₀ with
     X ⊆ E n has e n as the first element of X, and the finitely many
     entries of D₀ name finitely many n. More generally, no relation R
     between finite source lists and finite target lists that relates
     each [e n] to U and has nonempty-obs can satisfy clause 3 with a
     finite D₀ (no-finite-source, an instance of no-finite-sourceBy);
     ApproxLR on lists is one such R (no-finite-source-ApproxLR).

  3. The same without duplicate inputs. The E n of 1 differ only by
     duplicates in their input lists, which one might hope to rule out.
     The second example has none, and its source sets look well typed.
     The target closure g = ⦅ ν , ⟨⟩ ⦆, whose code ν is the function
     with no entries, has no usable code entry, so every nonempty
     source set is related to [g] (g-related): there are no constants,
     no calls and no projections to match. In particular [g] is related
     to each E′ n = {[n] ↦ n}, a consistent, nonempty singleton of a
     function Nat → Nat, and the E′ n are pairwise disjoint (E′-con,
     E′-ne, E′-disjoint, E′-related). Both sides come from the identity
     λx.x on Nat: the E′ n are parts of its source denotation and g is
     in its target denotation (E′⊆idN, g∈idN'). For idC, the target
     list V′ = [v′] with the code entry [⟨⟩] ↦ ([g] ↦ g), in the target
     denotation of idC (V′⊆idC'), calls on U′ = [g] with results
     W′ = [g] (calls′). Then ApproxLR (D ● E′ n) W′ for every n by the
     fundamental lemma (whole-source′), while every finite D₀ has an n,
     past the largest first input constant of its entries, with
     D₀ ● E′ n empty (finite-empty′), so ¬ ApproxLR (mem D₀ ● E′ n) W′
     (finite-source′, finite-source-clause3′, and the generic form
     no-finite-source-ApproxLR′).

-}

open import proof.Framework.GraphModel.Prelude hiding (ρ₀)
open import Mu.Semantics.GraphModel.Closed using (ρ₀)
open import Framework.Primitives
open import proof.Framework.GraphModel.DomainUtilBase
open import Mu.Language.Type using (Type; base; _⇒_; tup; Z)
open import Mu.Language.EnvClos
import Mu.proof.Semantics.GraphModel.EnvClos as S3
import Mu.proof.Semantics.GraphModel.PairClos as S4
open S3 using (⟦_⟧)
open S4 using () renaming (⟦_⟧ to ⟦_⟧')
open import Mu.Framework.AllUtil using ([])
open import Mu.Compiler.Delay using (delay-program)
open import Mu.proof.Correctness.GraphModel.DelayRel renaming (fold to foldᴬ; unfold to unfoldᴬ)
open import Mu.proof.Correctness.GraphModel.DelayReflect using (delay-reflect; Envs₀)

open import Data.Nat using (ℕ; zero; suc; _+_; _≤_)
open import Data.Nat.Properties using (suc-injective; ≤-trans; m≤m+n; m≤n+m; 1+n≰n; ≤-reflexive; n≤1+n)
open import Data.List using (List; []; _∷_; length; replicate)
open import Data.List.Properties using (length-replicate)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Membership.Propositional renaming (_∈_ to _⋵_)
open import Data.Product using (_×_; proj₁; proj₂; Σ-syntax) renaming (_,_ to ⟨_,_⟩ )
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (tt)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; trans; sym)
open import Relation.Nullary using (¬_)

module Mu.proof.Correctness.GraphModel.DelayDesignFiniteSource where

{- The values -----------------------------------------------------------------}

one : Value
one = const {Nat} 1

{- the target closure of λx.1: code entry [⟨⟩] ↦ ([1] ↦ 1), environment ⟨⟩ -}
u₁ : Value
u₁ = ⦅ (⟨⟩ ∷ []) ↦ ((one ∷ []) ↦ one) , ⟨⟩ ⦆

U : List Value
U = u₁ ∷ []

{- the source entries [1,…,1] ↦ 1, with n+1 ones -}
e : ℕ → Value
e n = replicate (suc n) one ↦ one

E : ℕ → 𝒫 Value
E n = mem (e n ∷ [])

{- Lemmas ---------------------------------------------------------------------}

∈-replicate : ∀ {x v : Value} k → x ⋵ replicate k v → x ≡ v
∈-replicate (suc k) (here refl) = refl
∈-replicate (suc k) (there x∈) = ∈-replicate k x∈

≈-ones : ∀ k j → replicate k one ≈ replicate j one
≈-ones zero j = tt
≈-ones (suc k) j = ⟨ all j , ≈-ones k j ⟩
  where
  all : ∀ j → All (one ~_) (replicate j one)
  all zero = []
  all (suc j) = ~-refl one ∷ all j

Con-single : ∀ v → Con (mem (v ∷ []))
Con-single v = ≈⇒Con ≈-single

untag-U : ∀ t {w} → tag t w ⋵ U → ⊥
untag-U (tupT i) (here ())
untag-U leftT (here ())
untag-U rightT (here ())
untag-U _ (there ())

{- 1. Disjoint related arguments ----------------------------------------------}

E-con : ∀ n → Con (E n)
E-con n = Con-single (e n)

E-ne : ∀ n → nonempty (E n)
E-ne n = ⟨ e n , here refl ⟩

E-disjoint : ∀ {n m v} → v ∈ E n → v ∈ E m → n ≡ m
E-disjoint {n} {m} (here refl) (here eq) =
  suc-injective (trans (sym (length-replicate (suc n))) (trans (cong inputs eq) (length-replicate (suc m))))
  where
  inputs : Value → ℕ
  inputs (X ↦ _) = length X
  inputs _ = 0

{- every result of a call of U is 1, and 1 is among the arguments -}
calls-U : ∀ {U' W w} → Batch U U' W → w ⋵ W → w ≡ one × one ⋵ U'
calls-U cs w∈ with Batch.results cs _ w∈
... | ⟨ _ , ⟨ usable-entry _ _ (here refl) _ _ , ⟨ _ , U₀⊆ ⟩ ⟩ ⟩ = ⟨ refl , U₀⊆ one (here refl) ⟩
... | ⟨ _ , ⟨ usable-entry _ _ (there ()) _ _ , _ ⟩ ⟩

E-related : ∀ n → ApproxLR (E n) U
E-related n = foldᴬ record
  { const-obs = λ { c (here ()) ; c (there ()) }
  ; nonempty-obs = λ _ → E-ne n
  ; app-obs = app-E
  ; tag-obs = λ t W W⊆ → ApproxLR-∅ (λ w w∈ → untag-U t (W⊆ w w∈))
  }
  where
  app-E : ∀ {U' W} → Batch U U' W → ∀ E' → Con E' → Con (mem U') → ApproxLR E' U' → ApproxLR (E n ● E') W
  app-E cs E' _ _ rE = ApproxLR-data res
    where
    one∈E' : ∀ {w} → w ⋵ _ → one ∈ E'
    one∈E' w∈ = ApproxLRLayer.const-obs (unfoldᴬ rE) 1 (proj₂ (calls-U cs w∈))
    res : ∀ w → w ⋵ _ → w ∈ (E n ● E') × Data w
    res w w∈ with calls-U cs w∈
    ... | ⟨ refl , _ ⟩ =
      ⟨ ⟨ replicate (suc n) one , ⟨ here refl , ⟨ (λ x x∈ → subst∈ (∈-replicate (suc n) x∈)) , (λ ()) ⟩ ⟩ ⟩ , flat-const ⟩
      where
      subst∈ : ∀ {x} → x ≡ one → x ∈ E'
      subst∈ refl = one∈E' w∈

{- the E n are parts of the source denotation of λx.1, and U is a finite
   part of its target denotation -}
λ1 : Tm [] (base Nat ⇒ base Nat)
λ1 = clos {Δ = []} (lit Nat 1) []

E⊆λ1 : ∀ n → E n ⊆ ⟦ λ1 ⟧ ρ₀
E⊆λ1 n _ (here refl) =
  ⟨ ⟨⟩ ∷ [] , ⟨ ⟨ ⟨ ⟨ refl , refl ⟩ , ⟨ (λ ()) , ≈-ones (suc n) (suc n) ⟩ ⟩ , ⟨ (λ ()) , ≈-single ⟩ ⟩
            , ⟨ (λ { _ (here refl) → tt }) , (λ ()) ⟩ ⟩ ⟩

U⊆λ1' : mem U ⊆ ⟦ delay-program λ1 ⟧' ρ₀
U⊆λ1' _ (here refl) = ⟨ ⟨ ⟨ ⟨ refl , refl ⟩ , ⟨ (λ ()) , ≈-single ⟩ ⟩ , ⟨ (λ ()) , ≈-single ⟩ ⟩ , tt ⟩

{- 2. A finite source side fails clause 3 -------------------------------------}

{- the identity closure λy.y, of type A ⇒ A with A = Nat ⇒ Nat -}
idC : Tm [] ((base Nat ⇒ base Nat) ⇒ (base Nat ⇒ base Nat))
idC = clos {Δ = []} (` Z) []

{- its whole source denotation -}
D : 𝒫 Value
D = ⟦ idC ⟧ ρ₀

{- the target closure of λy.y with the code entry [⟨⟩] ↦ (U ↦ u₁) -}
v-id : Value
v-id = ⦅ (⟨⟩ ∷ []) ↦ (U ↦ u₁) , ⟨⟩ ⦆

V : List Value
V = v-id ∷ []

W : List Value
W = u₁ ∷ []

V⊆idC' : mem V ⊆ ⟦ delay-program idC ⟧' ρ₀
V⊆idC' _ (here refl) = ⟨ ⟨ ⟨ here refl , ⟨ (λ ()) , ≈-single ⟩ ⟩ , ⟨ (λ ()) , ≈-single ⟩ ⟩ , tt ⟩

calls : Batch V U W
calls = record
  { results = λ { _ (here refl) → ⟨ U , ⟨ ent , ⟨ (λ ()) , (λ _ d∈ → d∈) ⟩ ⟩ ⟩ ; _ (there ()) }
  ; args = λ { _ (here refl) → ⟨ U , ⟨ u₁ , ⟨ ent , here refl ⟩ ⟩ ⟩ ; _ (there ()) }
  }
  where
  ent : UsableEntry V U u₁
  ent = usable-entry (⟨⟩ ∷ []) ⟨⟩ (here refl) (λ ()) (λ { _ (here refl) → ⟨ _ , here refl ⟩ ; _ (there ()) })

{- the whole source denotation satisfies clause 3, by the fundamental lemma -}
whole-source : ∀ n → ApproxLR (D ● E n) W
whole-source n =
  ApproxLRLayer.app-obs (unfoldᴬ (delay-reflect idC {r = λ ()} (Envs₀ (λ ())) V V⊆idC'))
    calls (E n) (E-con n) (Con-single u₁) (E-related n)

{- a finite list of values names finitely many n: the width of an entry
   X ↦ w is the size of the first element of X, which for the entries
   e n is the length of its input list -}
widthBy : (Value → ℕ) → Value → ℕ
widthBy size ((x ∷ _) ↦ _) = size x
widthBy size _ = 0

boundBy : (Value → ℕ) → List Value → ℕ
boundBy size [] = 0
boundBy size (d ∷ D₀) = widthBy size d + boundBy size D₀

width≤boundBy : ∀ size {d} D₀ → d ⋵ D₀ → widthBy size d ≤ boundBy size D₀
width≤boundBy size (d ∷ D₀) (here refl) = m≤m+n (widthBy size d) (boundBy size D₀)
width≤boundBy size (d ∷ D₀) (there d∈) =
  ≤-trans (width≤boundBy size D₀ d∈) (m≤n+m (boundBy size D₀) (widthBy size d))

{- if the n-th entry has size at least n, then a finite list D₀ applied
   to the singleton of the entry past its bound gives nothing -}
finite-emptyBy : ∀ (size : Value → ℕ) (s : ℕ → Value) → (∀ n → n ≤ size (s n))
  → ∀ D₀ w → ¬ (w ∈ (mem D₀ ● mem (s (suc (boundBy size D₀)) ∷ [])))
finite-emptyBy size s big D₀ w ⟨ [] , ⟨ _ , ⟨ _ , neX ⟩ ⟩ ⟩ = neX refl
finite-emptyBy size s big D₀ w ⟨ x ∷ X , ⟨ X↦w∈ , ⟨ X⊆ , _ ⟩ ⟩ ⟩ with X⊆ x (here refl)
... | here refl = 1+n≰n (≤-trans (big (suc (boundBy size D₀))) (width≤boundBy size D₀ X↦w∈))
... | there ()

inputs : Value → ℕ
inputs (X ↦ _) = length X
inputs _ = 0

bound : List Value → ℕ
bound = boundBy inputs

e-big : ∀ n → n ≤ inputs (e n)
e-big n = ≤-trans (n≤1+n n) (≤-reflexive (sym (length-replicate (suc n))))

finite-empty : ∀ D₀ w → ¬ (w ∈ (mem D₀ ● E (suc (bound D₀))))
finite-empty = finite-emptyBy inputs e e-big

finite-source : ∀ (D₀ : List Value) → Σ[ n ∈ ℕ ] ¬ ApproxLR (mem D₀ ● E n) W
finite-source D₀ = ⟨ suc (bound D₀) , (λ r → let ⟨ w , w∈ ⟩ = ApproxLRLayer.nonempty-obs (unfoldᴬ r) (λ ()) in finite-empty D₀ w w∈) ⟩

{- so no finite list satisfies clause 3 for V's batch of calls on U, which
   the whole source denotation satisfies -}
finite-source-clause3 : ∀ (D₀ : List Value) → ¬ (∀ n → ApproxLR (mem D₀ ● E n) W)
finite-source-clause3 D₀ all = proj₂ (finite-source D₀) (all (proj₁ (finite-source D₀)))

{- The same for any relation between finite source lists and finite target
   lists that relates each [s n] to U and has nonempty-obs: clause 3 for
   the source list D₀ and a batch of calls on U with results W, with the
   result of the call any finite part S of D₀ ● E₀ -}
FinClause3 : (List Value → List Value → Set₁) → List Value → List Value → List Value → Set₁
FinClause3 R U W D₀ = ∀ E₀ → R E₀ U → Σ[ S ∈ List Value ] mem S ⊆ (mem D₀ ● mem E₀) × R S W

no-finite-sourceBy : ∀ (R : List Value → List Value → Set₁) {U W}
  → (∀ {S V'} → R S V' → V' ≢ [] → S ≢ [])
  → W ≢ []
  → ∀ (size : Value → ℕ) (s : ℕ → Value) → (∀ n → n ≤ size (s n))
  → (∀ n → R (s n ∷ []) U)
  → ∀ D₀ → ¬ FinClause3 R U W D₀
no-finite-sourceBy R ne neW size s big rel D₀ c3 with c3 (s (suc (boundBy size D₀)) ∷ []) (rel _)
... | ⟨ [] , ⟨ _ , rS ⟩ ⟩ = ne rS neW refl
... | ⟨ x ∷ _ , ⟨ S⊆ , _ ⟩ ⟩ = finite-emptyBy size s big D₀ x (S⊆ x (here refl))

ne-ApproxLR : ∀ {S V'} → ApproxLR (mem S) V' → V' ≢ [] → S ≢ []
ne-ApproxLR r neV refl with ApproxLRLayer.nonempty-obs (unfoldᴬ r) neV
... | ⟨ _ , () ⟩

no-finite-source : ∀ (R : List Value → List Value → Set₁)
  → (∀ {S V'} → R S V' → V' ≢ [] → S ≢ [])
  → (∀ n → R (e n ∷ []) U)
  → ∀ D₀ → ¬ FinClause3 R U W D₀
no-finite-source R ne = no-finite-sourceBy R ne (λ ()) inputs e e-big

no-finite-source-ApproxLR : ∀ D₀ → ¬ FinClause3 (λ S V' → ApproxLR (mem S) V') U W D₀
no-finite-source-ApproxLR = no-finite-source _ ne-ApproxLR E-related

{- 3. Without duplicate inputs ------------------------------------------------}

{- the target closure g = ⦅ ν , ⟨⟩ ⦆, whose code ν is the function with no
   entries: g has no usable code entry, so no calls -}
g : Value
g = ⦅ ν , ⟨⟩ ⦆

{- the source entries [n] ↦ n -}
nat : ℕ → Value
nat n = const {Nat} n

e′ : ℕ → Value
e′ n = (nat n ∷ []) ↦ nat n

E′ : ℕ → 𝒫 Value
E′ n = mem (e′ n ∷ [])

E′-con : ∀ n → Con (E′ n)
E′-con n = Con-single (e′ n)

E′-ne : ∀ n → nonempty (E′ n)
E′-ne n = ⟨ e′ n , here refl ⟩

E′-disjoint : ∀ {n m v} → v ∈ E′ n → v ∈ E′ m → n ≡ m
E′-disjoint (here refl) (here refl) = refl

no-car-g : ∀ {U₀ w} → UsableEntry (g ∷ []) U₀ w → ⊥
no-car-g (usable-entry _ _ (here ()) _ _)
no-car-g (usable-entry _ _ (there ()) _ _)

untag-g : ∀ t {w} → tag t w ⋵ (g ∷ []) → ⊥
untag-g (tupT i) (here ())
untag-g leftT (here ())
untag-g rightT (here ())
untag-g _ (there ())

{- every nonempty source set is related to [g]: there are no constants,
   calls or projections to match -}
g-related : ∀ {E₁} → nonempty E₁ → ApproxLR E₁ (g ∷ [])
g-related neE = foldᴬ record
  { const-obs = λ { c (here ()) ; c (there ()) }
  ; nonempty-obs = λ _ → neE
  ; app-obs = λ cs _ _ _ _ → ApproxLR-∅ (λ w w∈ → no-car-g (proj₁ (proj₂ (Batch.results cs w w∈))))
  ; tag-obs = λ t W W⊆ → ApproxLR-∅ (λ w w∈ → untag-g t (W⊆ w w∈))
  }

E′-related : ∀ n → ApproxLR (E′ n) (g ∷ [])
E′-related n = g-related (E′-ne n)

{- the E′ n are parts of the source denotation of the identity λx.x on
   Nat, and g is in its target denotation -}
idN : Tm [] (base Nat ⇒ base Nat)
idN = clos {Δ = []} (` Z) []

E′⊆idN : ∀ n → E′ n ⊆ ⟦ idN ⟧ ρ₀
E′⊆idN n _ (here refl) =
  ⟨ ⟨⟩ ∷ [] , ⟨ ⟨ ⟨ here refl , ⟨ (λ ()) , ≈-single ⟩ ⟩ , ⟨ (λ ()) , ≈-single ⟩ ⟩
            , ⟨ (λ { _ (here refl) → tt }) , (λ ()) ⟩ ⟩ ⟩

g∈idN' : g ∈ ⟦ delay-program idN ⟧' ρ₀
g∈idN' = ⟨ tt , tt ⟩

{- the identity closure idC on such closures, with the target closure
   v′ whose code entry is [⟨⟩] ↦ ([g] ↦ g) -}
v′ : Value
v′ = ⦅ (⟨⟩ ∷ []) ↦ ((g ∷ []) ↦ g) , ⟨⟩ ⦆

V′ : List Value
V′ = v′ ∷ []

U′ : List Value
U′ = g ∷ []

W′ : List Value
W′ = g ∷ []

V′⊆idC' : mem V′ ⊆ ⟦ delay-program idC ⟧' ρ₀
V′⊆idC' _ (here refl) = ⟨ ⟨ ⟨ here refl , ⟨ (λ ()) , ≈-single ⟩ ⟩ , ⟨ (λ ()) , ≈-single ⟩ ⟩ , tt ⟩

calls′ : Batch V′ U′ W′
calls′ = record
  { results = λ { _ (here refl) → ⟨ U′ , ⟨ ent , ⟨ (λ ()) , (λ _ d∈ → d∈) ⟩ ⟩ ⟩ ; _ (there ()) }
  ; args = λ { _ (here refl) → ⟨ U′ , ⟨ g , ⟨ ent , here refl ⟩ ⟩ ⟩ ; _ (there ()) }
  }
  where
  ent : UsableEntry V′ U′ g
  ent = usable-entry (⟨⟩ ∷ []) ⟨⟩ (here refl) (λ ()) (λ { _ (here refl) → ⟨ _ , here refl ⟩ ; _ (there ()) })

{- the whole source denotation satisfies clause 3, by the fundamental lemma -}
whole-source′ : ∀ n → ApproxLR (D ● E′ n) W′
whole-source′ n =
  ApproxLRLayer.app-obs (unfoldᴬ (delay-reflect idC {r = λ ()} (Envs₀ (λ ())) V′ V′⊆idC'))
    calls′ (E′ n) (E′-con n) (Con-single g) (E′-related n)

{- the size of an entry [k, …] ↦ w is k, so the size of e′ n is n -}
arg : Value → ℕ
arg ((const {Nat} k ∷ _) ↦ _) = k
arg _ = 0

e′-big : ∀ n → n ≤ arg (e′ n)
e′-big n = ≤-reflexive refl

finite-empty′ : ∀ D₀ w → ¬ (w ∈ (mem D₀ ● E′ (suc (boundBy arg D₀))))
finite-empty′ = finite-emptyBy arg e′ e′-big

finite-source′ : ∀ (D₀ : List Value) → Σ[ n ∈ ℕ ] ¬ ApproxLR (mem D₀ ● E′ n) W′
finite-source′ D₀ = ⟨ suc (boundBy arg D₀) , (λ r → let ⟨ w , w∈ ⟩ = ApproxLRLayer.nonempty-obs (unfoldᴬ r) (λ ()) in finite-empty′ D₀ w w∈) ⟩

finite-source-clause3′ : ∀ (D₀ : List Value) → ¬ (∀ n → ApproxLR (mem D₀ ● E′ n) W′)
finite-source-clause3′ D₀ all = proj₂ (finite-source′ D₀) (all (proj₁ (finite-source′ D₀)))

no-finite-source-ApproxLR′ : ∀ D₀ → ¬ FinClause3 (λ S V' → ApproxLR (mem S) V') U′ W′ D₀
no-finite-source-ApproxLR′ = no-finite-sourceBy _ ne-ApproxLR (λ ()) arg e′ e′-big E′-related

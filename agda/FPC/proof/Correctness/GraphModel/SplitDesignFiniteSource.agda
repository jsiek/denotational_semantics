{-

  This module establishes a fact about the design of the relation for
  the reflection half of split (EnvClosμ → PairClosμ) in the graph
  model (SplitRel.agda, SplitReflect.agda). The source side of the
  relation must be a whole source set, which may be infinite, rather
  than a single element or a finite list. Two examples show this. In
  the first example (parts 1 and 2), the source sets differ only by
  duplicate inputs. The second example (part 3) has no duplicate
  inputs. This module is a design experiment, separate from the proof
  of the compiler and from the size counts.

  1. Disjoint related arguments. Let u₁ be a pair of the target closure
     of λx.1, with the code entry [⟨⟩] ↦ ([1] ↦ 1), and let U = [u₁].
     For each n, let E n be the source set {[1,…,1] ↦ 1} with n+1 ones.
     Then U is related (ApproxLR) to every E n, and the sets E n are
     consistent, nonempty, and pairwise disjoint (E-con, E-ne,
     E-disjoint, E-related). Each E n is part of the source denotation
     of λx.1, and U is a finite part of its target denotation (E⊆λ1,
     U⊆λ1').

  2. A finite source side fails clause 3 (app-obs). Consider the
     identity closure idC = clos (` Z) [] (λy.y) and the target list
     V = [v-id], whose code entry is [⟨⟩] ↦ (U ↦ u₁). Then V maps U to
     W = [u₁] (calls). Let D be the whole source denotation of idC. The
     fundamental lemma (split-reflect) gives ApproxLR (D ● E n) W for
     every n (whole-source). In contrast, for every finite list D₀ of
     values, whether or not they belong to D, there is an n such that
     D₀ ● E n is empty (finite-empty). Therefore
     ¬ ApproxLR (mem D₀ ● E n) W (finite-source). The paper gives the
     reason. If an entry X ↦ w of D₀ applies to E n, then every element
     of X is e n, so the first element of X determines n. The finitely
     many entries of D₀ therefore name only finitely many n. More
     generally, let R be any relation between finite source lists and
     finite target lists that relates each [e n] to U and satisfies
     nonempty-obs. Then no finite D₀ satisfies clause 3 for R
     (no-finite-source, an instance of no-finite-sourceBy). ApproxLR on
     lists is one such R (no-finite-source-ApproxLR).

  3. The same without duplicate inputs. The sets E n of part 1 differ
     only by duplicates in their input lists, and one might hope to
     rule such duplicates out. The second example has no duplicates,
     and its source sets look well typed. Let g = ⦅ ν , ⟨⟩ ⦆ be a target
     closure whose code ν is the function with no entries, so g has no
     usable code entry. Because [g] offers no constants, calls, or
     projections to match, every nonempty source set is related to [g]
     (g-related). In particular, [g] is related to each
     E′ n = {[n] ↦ n}, a consistent, nonempty singleton of a function
     Nat → Nat, and the sets E′ n are pairwise disjoint (E′-con,
     E′-ne, E′-disjoint, E′-related). Both sides come from the identity
     λx.x on Nat. Each E′ n is part of its source denotation, and g is
     in its target denotation (E′⊆idN, g∈idN'). For idC, the target
     list V′ = [v′], whose code entry is [⟨⟩] ↦ ([g] ↦ g), lies in the
     target denotation of idC (V′⊆idC'), and V′ maps U′ = [g] to
     W′ = [g] (calls′). The fundamental lemma then gives
     ApproxLR (D ● E′ n) W′ for every n (whole-source′). In contrast,
     every finite D₀ has an n such that D₀ ● E′ n is empty, namely any
     n larger than the sum of the sizes (arg) of the first arguments of
     the entries of D₀ (finite-empty′). Therefore
     ¬ ApproxLR (mem D₀ ● E′ n) W′ (finite-source′,
     finite-source-clause3′, and the generic form
     no-finite-source-ApproxLR′).

-}

open import proof.Framework.GraphModel.Prelude hiding (ρ₀)
open import FPC.Semantics.GraphModel.Closed using (ρ₀)
open import Framework.Primitives
open import proof.Framework.GraphModel.DomainUtilBase
open import FPC.Language.Type using (Type; base; _⇒_; tup; Z)
open import FPC.Language.EnvClos
import FPC.proof.Semantics.GraphModel.EnvClos as S3
import FPC.proof.Semantics.GraphModel.PairClos as S4
open S3 using (⟦_⟧)
open S4 using () renaming (⟦_⟧ to ⟦_⟧')
open import FPC.Framework.AllUtil using ([])
open import FPC.Compiler.Split using (split-program)
open import FPC.proof.Correctness.GraphModel.SplitRel renaming (fold to foldᴬ; unfold to unfoldᴬ)
open import FPC.proof.Correctness.GraphModel.SplitReflect using (split-reflect; Envs₀)

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

module FPC.proof.Correctness.GraphModel.SplitDesignFiniteSource where

{- The values -----------------------------------------------------------------}

one : Value
one = const {Nat} 1

{- u₁ is a pair of the target closure of λx.1. Its code entry is
   [⟨⟩] ↦ ([1] ↦ 1), and its environment is ⟨⟩. -}
u₁ : Value
u₁ = ⦅ (⟨⟩ ∷ []) ↦ ((one ∷ []) ↦ one) , ⟨⟩ ⦆

U : List Value
U = u₁ ∷ []

{- e n is the source entry [1,…,1] ↦ 1 with n+1 ones. -}
e : ℕ → Value
e n = replicate (suc n) one ↦ one

E : ℕ → 𝒫 Value
E n = mem (e n ∷ [])

{- Lemmas ---------------------------------------------------------------------}

∈-replicate : ∀ {x v : Value} k
  → x ⋵ replicate k v
  → x ≡ v
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

untag-U : ∀ t {w}
  → tag t w ⋵ U
  → ⊥
untag-U (tupT i) (here ())
untag-U leftT (here ())
untag-U rightT (here ())
untag-U _ (there ())

{- 1. Disjoint related arguments ----------------------------------------------}

E-con : ∀ n → Con (E n)
E-con n = Con-single (e n)

E-ne : ∀ n → nonempty (E n)
E-ne n = ⟨ e n , here refl ⟩

E-disjoint : ∀ {n m v}
  → v ∈ E n
  → v ∈ E m
  → n ≡ m
E-disjoint {n} {m} (here refl) (here eq) =
  suc-injective (trans (sym (length-replicate (suc n))) (trans (cong inputs eq) (length-replicate (suc m))))
  where
  inputs : Value → ℕ
  inputs (X ↦ _) = length X
  inputs _ = 0

{- If U maps U' to W, then every result in W is 1, and 1 is among the
   arguments U'. -}
calls-U : ∀ {U' W w} → SelfContainedMaps U U' W → w ⋵ W → w ≡ one × one ⋵ U'
calls-U cs w∈ with SelfContainedMaps.results cs _ w∈
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
  app-E : ∀ {U' W}
    → SelfContainedMaps U U' W
    → ∀ E'
    → Con E'
    → Con (mem U')
    → ApproxLR E' U'
    → ApproxLR (E n ● E') W
  app-E cs E' _ _ rE = ApproxLR-data res
    where
    one∈E' : ∀ {w}
      → w ⋵ _
      → one ∈ E'
    one∈E' w∈ = ApproxLRLayer.const-obs (unfoldᴬ rE) 1 (proj₂ (calls-U cs w∈))
    res : ∀ w
      → w ⋵ _
      → w ∈ (E n ● E') × Data w
    res w w∈ with calls-U cs w∈
    ... | ⟨ refl , _ ⟩ =
      ⟨ ⟨ replicate (suc n) one , ⟨ here refl , ⟨ (λ x x∈ → subst∈ (∈-replicate (suc n) x∈)) , (λ ()) ⟩ ⟩ ⟩ , flat-const ⟩
      where
      subst∈ : ∀ {x}
        → x ≡ one
        → x ∈ E'
      subst∈ refl = one∈E' w∈

{- Each E n is part of the source denotation of λx.1, and U is a finite
   part of its target denotation. -}
λ1 : Tm [] (base Nat ⇒ base Nat)
λ1 = clos {Δ = []} (lit Nat 1) []

E⊆λ1 : ∀ n → E n ⊆ ⟦ λ1 ⟧ ρ₀
E⊆λ1 n _ (here refl) =
  ⟨ ⟨⟩ ∷ [] , ⟨ ⟨ ⟨ ⟨ refl , refl ⟩ , ⟨ (λ ()) , ≈-ones (suc n) (suc n) ⟩ ⟩ , ⟨ (λ ()) , ≈-single ⟩ ⟩
            , ⟨ (λ { _ (here refl) → tt }) , (λ ()) ⟩ ⟩ ⟩

U⊆λ1' : mem U ⊆ ⟦ split-program λ1 ⟧' ρ₀
U⊆λ1' _ (here refl) = ⟨ ⟨ ⟨ ⟨ refl , refl ⟩ , ⟨ (λ ()) , ≈-single ⟩ ⟩ , ⟨ (λ ()) , ≈-single ⟩ ⟩ , tt ⟩

{- 2. A finite source side fails clause 3 -------------------------------------}

{- idC is the identity closure λy.y at type A ⇒ A, where
   A = Nat ⇒ Nat. -}
idC : Tm [] ((base Nat ⇒ base Nat) ⇒ (base Nat ⇒ base Nat))
idC = clos {Δ = []} (` Z) []

{- D is the whole source denotation of idC. -}
D : 𝒫 Value
D = ⟦ idC ⟧ ρ₀

{- v-id is a pair of the target closure of λy.y, with the code entry
   [⟨⟩] ↦ (U ↦ u₁). -}
v-id : Value
v-id = ⦅ (⟨⟩ ∷ []) ↦ (U ↦ u₁) , ⟨⟩ ⦆

V : List Value
V = v-id ∷ []

W : List Value
W = u₁ ∷ []

V⊆idC' : mem V ⊆ ⟦ split-program idC ⟧' ρ₀
V⊆idC' _ (here refl) = ⟨ ⟨ ⟨ here refl , ⟨ (λ ()) , ≈-single ⟩ ⟩ , ⟨ (λ ()) , ≈-single ⟩ ⟩ , tt ⟩

calls : SelfContainedMaps V U W
calls = record
  { results = λ { _ (here refl) → ⟨ U , ⟨ ent , ⟨ (λ ()) , (λ _ d∈ → d∈) ⟩ ⟩ ⟩ ; _ (there ()) }
  ; args = λ { _ (here refl) → ⟨ U , ⟨ u₁ , ⟨ ent , here refl ⟩ ⟩ ⟩ ; _ (there ()) }
  }
  where
  ent : UsableEntry V U u₁
  ent = usable-entry (⟨⟩ ∷ []) ⟨⟩ (here refl) (λ ()) (λ { _ (here refl) → ⟨ _ , here refl ⟩ ; _ (there ()) })

{- The whole source denotation D satisfies clause 3, by the fundamental
   lemma. -}
whole-source : ∀ n → ApproxLR (D ● E n) W
whole-source n =
  ApproxLRLayer.app-obs (unfoldᴬ (split-reflect idC Envs₀ V V⊆idC'))
    calls (E n) (E-con n) (Con-single u₁) (E-related n)

{- A finite list of values names only finitely many n. The width of an
   entry X ↦ w is the size of the first element of X, and the bound of
   a list is the sum of the widths of its elements. With the size
   inputs, an entry whose first argument is e n has width n + 1, the
   length of the input list of e n. -}
widthBy : (Value → ℕ) → Value → ℕ
widthBy size ((x ∷ _) ↦ _) = size x
widthBy size _ = 0

boundBy : (Value → ℕ) → List Value → ℕ
boundBy size [] = 0
boundBy size (d ∷ D₀) = widthBy size d + boundBy size D₀

width≤boundBy : ∀ size {d} D₀
  → d ⋵ D₀
  → widthBy size d ≤ boundBy size D₀
width≤boundBy size (d ∷ D₀) (here refl) = m≤m+n (widthBy size d) (boundBy size D₀)
width≤boundBy size (d ∷ D₀) (there d∈) =
  ≤-trans (width≤boundBy size D₀ d∈) (m≤n+m (boundBy size D₀) (widthBy size d))

{- Suppose the size of s n is at least n for every n, and let b be the
   bound of a finite list D₀. Then applying D₀ to the singleton set of
   s (b + 1) gives the empty set. -}
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

{- Therefore no finite list D₀ satisfies clause 3 for the call in which
   V maps U to W, although the whole source denotation D satisfies it
   (whole-source). -}
finite-source-clause3 : ∀ (D₀ : List Value) → ¬ (∀ n → ApproxLR (mem D₀ ● E n) W)
finite-source-clause3 D₀ all = proj₂ (finite-source D₀) (all (proj₁ (finite-source D₀)))

{- The same failure holds for any relation R between finite source
   lists and finite target lists that relates each [s n] to U and
   satisfies nonempty-obs (no-finite-sourceBy). FinClause3 R U W D₀ is
   clause 3 for R at the finite source list D₀ and a self-contained
   call that maps U to W. It says that for every source list E₀ related
   to U, some finite part S of D₀ ● E₀ is related to W. -}
FinClause3 : (List Value → List Value → Set₁) → List Value → List Value → List Value → Set₁
FinClause3 R U W D₀ = ∀ E₀ → R E₀ U → Σ[ S ∈ List Value ] mem S ⊆ (mem D₀ ● mem E₀) × R S W

no-finite-sourceBy : ∀ (R : List Value → List Value → Set₁) {U W}
  → (∀ {S V'} → R S V' → V' ≢ [] → S ≢ [])
  → W ≢ []
  → ∀ (size : Value → ℕ) (s : ℕ → Value)
  → (∀ n → n ≤ size (s n))
  → (∀ n → R (s n ∷ []) U)
  → ∀ D₀
  → ¬ FinClause3 R U W D₀
no-finite-sourceBy R ne neW size s big rel D₀ c3 with c3 (s (suc (boundBy size D₀)) ∷ []) (rel _)
... | ⟨ [] , ⟨ _ , rS ⟩ ⟩ = ne rS neW refl
... | ⟨ x ∷ _ , ⟨ S⊆ , _ ⟩ ⟩ = finite-emptyBy size s big D₀ x (S⊆ x (here refl))

ne-ApproxLR : ∀ {S V'}
  → ApproxLR (mem S) V'
  → V' ≢ []
  → S ≢ []
ne-ApproxLR r neV refl with ApproxLRLayer.nonempty-obs (unfoldᴬ r) neV
... | ⟨ _ , () ⟩

no-finite-source : ∀ (R : List Value → List Value → Set₁)
  → (∀ {S V'} → R S V' → V' ≢ [] → S ≢ [])
  → (∀ n → R (e n ∷ []) U)
  → ∀ D₀
  → ¬ FinClause3 R U W D₀
no-finite-source R ne = no-finite-sourceBy R ne (λ ()) inputs e e-big

no-finite-source-ApproxLR : ∀ D₀ → ¬ FinClause3 (λ S V' → ApproxLR (mem S) V') U W D₀
no-finite-source-ApproxLR = no-finite-source _ ne-ApproxLR E-related

{- 3. Without duplicate inputs ------------------------------------------------}

{- g = ⦅ ν , ⟨⟩ ⦆ is a target closure whose code ν is the function with
   no entries. Because g has no usable code entry, it has no calls. -}
g : Value
g = ⦅ ν , ⟨⟩ ⦆

{- e′ n is the source entry [n] ↦ n. -}
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

E′-disjoint : ∀ {n m v}
  → v ∈ E′ n
  → v ∈ E′ m
  → n ≡ m
E′-disjoint (here refl) (here refl) = refl

no-car-g : ∀ {U₀ w}
  → UsableEntry (g ∷ []) U₀ w
  → ⊥
no-car-g (usable-entry _ _ (here ()) _ _)
no-car-g (usable-entry _ _ (there ()) _ _)

untag-g : ∀ t {w}
  → tag t w ⋵ (g ∷ [])
  → ⊥
untag-g (tupT i) (here ())
untag-g leftT (here ())
untag-g rightT (here ())
untag-g _ (there ())

{- Every nonempty source set is related to [g], because [g] offers no
   constants, calls, or projections to match. -}
g-related : ∀ {E₁} → nonempty E₁ → ApproxLR E₁ (g ∷ [])
g-related neE = foldᴬ record
  { const-obs = λ { c (here ()) ; c (there ()) }
  ; nonempty-obs = λ _ → neE
  ; app-obs = λ cs _ _ _ _ → ApproxLR-∅ (λ w w∈ → no-car-g (proj₁ (proj₂ (SelfContainedMaps.results cs w w∈))))
  ; tag-obs = λ t W W⊆ → ApproxLR-∅ (λ w w∈ → untag-g t (W⊆ w w∈))
  }

E′-related : ∀ n → ApproxLR (E′ n) (g ∷ [])
E′-related n = g-related (E′-ne n)

{- Each E′ n is part of the source denotation of the identity λx.x on
   Nat, and g is in its target denotation. -}
idN : Tm [] (base Nat ⇒ base Nat)
idN = clos {Δ = []} (` Z) []

E′⊆idN : ∀ n → E′ n ⊆ ⟦ idN ⟧ ρ₀
E′⊆idN n _ (here refl) =
  ⟨ ⟨⟩ ∷ [] , ⟨ ⟨ ⟨ here refl , ⟨ (λ ()) , ≈-single ⟩ ⟩ , ⟨ (λ ()) , ≈-single ⟩ ⟩
            , ⟨ (λ { _ (here refl) → tt }) , (λ ()) ⟩ ⟩ ⟩

g∈idN' : g ∈ ⟦ split-program idN ⟧' ρ₀
g∈idN' = ⟨ tt , tt ⟩

{- For the identity closure idC on such closures, v′ is a pair of its
   target denotation with the code entry [⟨⟩] ↦ ([g] ↦ g). -}
v′ : Value
v′ = ⦅ (⟨⟩ ∷ []) ↦ ((g ∷ []) ↦ g) , ⟨⟩ ⦆

V′ : List Value
V′ = v′ ∷ []

U′ : List Value
U′ = g ∷ []

W′ : List Value
W′ = g ∷ []

V′⊆idC' : mem V′ ⊆ ⟦ split-program idC ⟧' ρ₀
V′⊆idC' _ (here refl) = ⟨ ⟨ ⟨ here refl , ⟨ (λ ()) , ≈-single ⟩ ⟩ , ⟨ (λ ()) , ≈-single ⟩ ⟩ , tt ⟩

calls′ : SelfContainedMaps V′ U′ W′
calls′ = record
  { results = λ { _ (here refl) → ⟨ U′ , ⟨ ent , ⟨ (λ ()) , (λ _ d∈ → d∈) ⟩ ⟩ ⟩ ; _ (there ()) }
  ; args = λ { _ (here refl) → ⟨ U′ , ⟨ g , ⟨ ent , here refl ⟩ ⟩ ⟩ ; _ (there ()) }
  }
  where
  ent : UsableEntry V′ U′ g
  ent = usable-entry (⟨⟩ ∷ []) ⟨⟩ (here refl) (λ ()) (λ { _ (here refl) → ⟨ _ , here refl ⟩ ; _ (there ()) })

{- The whole source denotation D satisfies clause 3, by the fundamental
   lemma. -}
whole-source′ : ∀ n → ApproxLR (D ● E′ n) W′
whole-source′ n =
  ApproxLRLayer.app-obs (unfoldᴬ (split-reflect idC Envs₀ V′ V′⊆idC'))
    calls′ (E′ n) (E′-con n) (Con-single g) (E′-related n)

{- The size arg of an entry [k, …] ↦ w is k, so the size of e′ n is
   n. -}
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

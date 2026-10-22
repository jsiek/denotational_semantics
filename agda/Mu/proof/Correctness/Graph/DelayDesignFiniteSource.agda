{-

  A design-space fact about the relation for the reflect half of delay
  (Clos3μ → Clos4μ) in the graph model (DelayRel, DelayReflect): its
  source side must be a whole, possibly infinite, source set, not a
  single element or a finite list. Not part of the proof of the
  compiler, and in no size count.

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
     finite D₀ (no-finite-source); ApproxLR on lists is one such R
     (no-finite-source-ApproxLR).

-}

open import proof.Framework.GraphModel.Prelude hiding (ρ₀)
open import Mu.Semantics.Graph.Closed using (ρ₀)
open import Framework.Primitives
open import proof.Framework.GraphModel.DomainUtilBase
open import Mu.Language.Type using (Type; base; _⇒_; tup; Z)
open import Mu.Language.Clos3
import Mu.proof.Semantics.Graph.Clos3 as S3
import Mu.proof.Semantics.Graph.Clos4 as S4
open S3 using (⟦_⟧)
open S4 using () renaming (⟦_⟧ to ⟦_⟧')
open import Mu.Framework.AllUtil using ([])
open import Mu.Compiler.Delay using (delay-program)
open import Mu.proof.Correctness.Graph.DelayRel renaming (fold to foldᴬ; unfold to unfoldᴬ)
open import Mu.proof.Correctness.Graph.DelayReflect using (delay-reflect; Envs₀)

open import Data.Nat using (ℕ; zero; suc; _+_; _≤_)
open import Data.Nat.Properties using (suc-injective; ≤-trans; m≤m+n; m≤n+m; 1+n≰n; ≤-reflexive)
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

module Mu.proof.Correctness.Graph.DelayDesignFiniteSource where

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
calls-U : ∀ {U' W w} → Calls U U' W → w ⋵ W → w ≡ one × one ⋵ U'
calls-U cs w∈ with Calls.results cs _ w∈
... | ⟨ _ , ⟨ car-entry _ _ (here refl) _ _ , ⟨ _ , U₀⊆ ⟩ ⟩ ⟩ = ⟨ refl , U₀⊆ one (here refl) ⟩
... | ⟨ _ , ⟨ car-entry _ _ (there ()) _ _ , _ ⟩ ⟩

E-related : ∀ n → ApproxLR (E n) U
E-related n = foldᴬ record
  { const-obs = λ { c (here ()) ; c (there ()) }
  ; nonempty-obs = λ _ → E-ne n
  ; app-obs = app-E
  ; tag-obs = λ t W W⊆ → ApproxLR-∅ (λ w w∈ → untag-U t (W⊆ w w∈))
  }
  where
  app-E : ∀ {U' W} → Calls U U' W → ∀ E' → Con E' → Con (mem U') → ApproxLR E' U' → ApproxLR (E n ● E') W
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

calls : Calls V U W
calls = record
  { results = λ { _ (here refl) → ⟨ U , ⟨ ent , ⟨ (λ ()) , (λ _ d∈ → d∈) ⟩ ⟩ ⟩ ; _ (there ()) }
  ; args = λ { _ (here refl) → ⟨ U , ⟨ u₁ , ⟨ ent , here refl ⟩ ⟩ ⟩ ; _ (there ()) }
  }
  where
  ent : CarEntry V U u₁
  ent = car-entry (⟨⟩ ∷ []) ⟨⟩ (here refl) (λ ()) (λ { _ (here refl) → ⟨ _ , here refl ⟩ ; _ (there ()) })

{- the whole source denotation satisfies clause 3, by the fundamental lemma -}
whole-source : ∀ n → ApproxLR (D ● E n) W
whole-source n =
  ApproxLRLayer.app-obs (unfoldᴬ (delay-reflect idC {r = λ ()} (Envs₀ (λ ())) V V⊆idC'))
    calls (E n) (E-con n) (Con-single u₁) (E-related n)

{- a finite list of values names finitely many n: the width of an entry
   X ↦ w is the length of the input list of the first element of X -}
width : Value → ℕ
width ((x ∷ _) ↦ _) = inputs x
  where
  inputs : Value → ℕ
  inputs (X ↦ _) = length X
  inputs _ = 0
width _ = 0

bound : List Value → ℕ
bound [] = 0
bound (d ∷ D₀) = width d + bound D₀

width≤bound : ∀ {d} D₀ → d ⋵ D₀ → width d ≤ bound D₀
width≤bound (d ∷ D₀) (here refl) = m≤m+n (width d) (bound D₀)
width≤bound (d ∷ D₀) (there d∈) = ≤-trans (width≤bound D₀ d∈) (m≤n+m (bound D₀) (width d))

finite-empty : ∀ D₀ w → ¬ (w ∈ (mem D₀ ● E (bound D₀)))
finite-empty D₀ w ⟨ [] , ⟨ _ , ⟨ _ , neX ⟩ ⟩ ⟩ = neX refl
finite-empty D₀ w ⟨ x ∷ X , ⟨ X↦w∈ , ⟨ X⊆ , _ ⟩ ⟩ ⟩ with X⊆ x (here refl)
... | here refl = 1+n≰n (≤-trans (≤-reflexive (sym (length-replicate (suc (bound D₀))))) (width≤bound D₀ X↦w∈))
... | there ()

finite-source : ∀ (D₀ : List Value) → Σ[ n ∈ ℕ ] ¬ ApproxLR (mem D₀ ● E n) W
finite-source D₀ = ⟨ bound D₀ , (λ r → let ⟨ w , w∈ ⟩ = ApproxLRLayer.nonempty-obs (unfoldᴬ r) (λ ()) in finite-empty D₀ w w∈) ⟩

{- so no finite list satisfies clause 3 for V's batch of calls on U, which
   the whole source denotation satisfies -}
finite-source-clause3 : ∀ (D₀ : List Value) → ¬ (∀ n → ApproxLR (mem D₀ ● E n) W)
finite-source-clause3 D₀ all = proj₂ (finite-source D₀) (all (proj₁ (finite-source D₀)))

{- The same for any relation between finite source lists and finite target
   lists that relates each [e n] to U and has nonempty-obs: clause 3 for
   the source list D₀ and V's batch of calls, with the result of the call
   any finite part S of D₀ ● E₀ -}
FinClause3 : (List Value → List Value → Set₁) → List Value → Set₁
FinClause3 R D₀ = ∀ E₀ → R E₀ U → Σ[ S ∈ List Value ] mem S ⊆ (mem D₀ ● mem E₀) × R S W

no-finite-source : ∀ (R : List Value → List Value → Set₁)
  → (∀ {S V'} → R S V' → V' ≢ [] → S ≢ [])
  → (∀ n → R (e n ∷ []) U)
  → ∀ D₀ → ¬ FinClause3 R D₀
no-finite-source R ne rel D₀ c3 with c3 (e (bound D₀) ∷ []) (rel (bound D₀))
... | ⟨ [] , ⟨ _ , rS ⟩ ⟩ = ne rS (λ ()) refl
... | ⟨ s ∷ _ , ⟨ S⊆ , _ ⟩ ⟩ = finite-empty D₀ s (S⊆ s (here refl))

no-finite-source-ApproxLR : ∀ D₀ → ¬ FinClause3 (λ S V' → ApproxLR (mem S) V') D₀
no-finite-source-ApproxLR = no-finite-source _ ne E-related
  where
  ne : ∀ {S V'} → ApproxLR (mem S) V' → V' ≢ [] → S ≢ []
  ne r neV refl with ApproxLRLayer.nonempty-obs (unfoldᴬ r) neV
  ... | ⟨ _ , () ⟩

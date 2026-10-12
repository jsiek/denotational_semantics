{-

  The values of the Clos5 machine (Operational/Machine/Clos5.agda), which
  the X86 machine shares, in the graph model; shared by the adequacy
  proofs for Clos5 (Adequacy/Clos5.agda) and X86 (Adequacy/X86.agda).

  * Den T: for soundness, the denotation 𝒱 v of a machine value, where a
    code pointer code k denotes the entry T k of a table whose entries
    all hold ν and are consistent; every value denotes a nonempty,
    consistent set with an element of the shape of its observation.

  * Rel Run: for adequacy, the logical relation 𝕍 d v between
    denotational and machine values. A code pointer is related to the
    entries Λ X. Λ Y. … of code: X ↦ (Y ↦ w) is related to code k when
    Run k e a (𝕍 w) for all e and a related to all of X and Y, where
    Run k e a P says that the machine runs definition k on e and a to a
    value with P (Clos5LogRel.agda, X86LogRel.agda).

-}

module proof.Compiler.Operational.Adequacy.Values where

open import Framework.Primitives using (Int)
open import Compiler.Lang.Prim using (int; bool; δ)
open import Framework.GraphModel.SetsAsPredicates
open import Framework.GraphModel.Domain
  using (Value; _↦_; ν; ⦅_,_⦆; tup[_]_; left; right; ⟨⟩; Con)
  renaming (const to dconst)
open import Framework.GraphModel.Ops using (ℬ; inl; inr; pair-consis; ℬ-consis; inl-consis; inr-consis)
  renaming (pair to dpair)
open import Compiler.Model.Graph.Prim using (primD) renaming (out to dout)
open import Compiler.Model.Graph.Sem.Clos5Iswim using (Table)
open import Compiler.Observation
open import Framework.ListUtil using (proj; has-length)
open import Compiler.Operational.Machine.Clos5 using (Val; code; pair; const; tup; obs; obs-list; out)
import Compiler.Operational.Machine.Clos5 as T using (inl; inr)
open import proof.Compiler.Operational.Adequacy.Common
  using (ShapeOf; ShapeAt; has-length→length; length→has-length; δ?-inv)
open import proof.Compiler.Operational.Adequacy.Soundness using (At; AllNE; 𝒯L; AllCon; 𝒯L-con)

open import Data.Bool using (true; false)
open import Data.Empty using (⊥)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_; length)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (just)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (Σ-syntax; _×_) renaming (_,_ to ⟨_,_⟩)
open import Data.Unit using (⊤; tt)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Level using (lift; lower)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong; subst)

length-obs-list : ∀ vs → length (obs-list vs) ≡ length vs
length-obs-list [] = refl
length-obs-list (v ∷ vs) = cong suc (length-obs-list vs)

{- Denotations of values (soundness) --------------------------------------------}

module Den (T⁺ : Table) (T⁺-ν : ∀ k → ν ∈ T⁺ k) (T⁺-con : ∀ k → Con (T⁺ k)) where

  𝒱 : Val → 𝒫 Value
  𝒱s : List Val → List (𝒫 Value)

  𝒱 (code k) = T⁺ k
  𝒱 (pair v w) = dpair ⟨ 𝒱 v , ⟨ 𝒱 w , ptt ⟩ ⟩
  𝒱 (const B k) = ℬ B k ptt
  𝒱 (tup vs) = 𝒯L (𝒱s vs)
  𝒱 (T.inl v) = inl ⟨ 𝒱 v , ptt ⟩
  𝒱 (T.inr v) = inr ⟨ 𝒱 v , ptt ⟩

  𝒱s [] = []
  𝒱s (v ∷ vs) = 𝒱 v ∷ 𝒱s vs

  length-𝒱s : ∀ vs → length (𝒱s vs) ≡ length vs
  length-𝒱s [] = refl
  length-𝒱s (v ∷ vs) = cong suc (length-𝒱s vs)

  {- every value denotes a nonempty set -}
  𝒱-nonempty : ∀ v → nonempty (𝒱 v)
  𝒱s-nonempty : ∀ vs → AllNE (𝒱s vs)

  𝒱-nonempty (code k) = ⟨ ν , T⁺-ν k ⟩
  𝒱-nonempty (pair v w) with 𝒱-nonempty v | 𝒱-nonempty w
  ... | ⟨ d , d∈ ⟩ | ⟨ e , e∈ ⟩ = ⟨ ⦅ d , e ⦆ , ⟨ d∈ , e∈ ⟩ ⟩
  𝒱-nonempty (const B k) = ⟨ dconst k , ⟨ refl , refl ⟩ ⟩
  𝒱-nonempty (tup []) = ⟨ ⟨⟩ , tt ⟩
  𝒱-nonempty (tup (v ∷ vs)) with 𝒱-nonempty v
  ... | ⟨ d , d∈ ⟩ =
    ⟨ tup[_]_ {suc (length vs)} zero d , ⟨ ⟨ length-𝒱s vs , d∈ ⟩ , ⟨ ⟨ d , d∈ ⟩ , 𝒱s-nonempty vs ⟩ ⟩ ⟩
  𝒱-nonempty (T.inl v) with 𝒱-nonempty v
  ... | ⟨ d , d∈ ⟩ = ⟨ left d , d∈ ⟩
  𝒱-nonempty (T.inr v) with 𝒱-nonempty v
  ... | ⟨ d , d∈ ⟩ = ⟨ right d , d∈ ⟩

  𝒱s-nonempty [] = tt
  𝒱s-nonempty (v ∷ vs) = ⟨ 𝒱-nonempty v , 𝒱s-nonempty vs ⟩

  {- every value denotes a consistent set -}
  𝒱-con : ∀ v → Con (𝒱 v)
  𝒱s-con : ∀ vs → AllCon (𝒱s vs)
  𝒱-con (code k) = T⁺-con k
  𝒱-con (pair v w) = lower (pair-consis _ _ ⟨ lift (𝒱-con v) , ⟨ lift (𝒱-con w) , ptt ⟩ ⟩)
  𝒱-con (const B k) = lower (ℬ-consis B k ptt ptt ptt)
  𝒱-con (tup vs) = 𝒯L-con (𝒱s vs) (𝒱s-con vs)
  𝒱-con (T.inl v) = lower (inl-consis _ _ ⟨ lift (𝒱-con v) , ptt ⟩)
  𝒱-con (T.inr v) = lower (inr-consis _ _ ⟨ lift (𝒱-con v) , ptt ⟩)
  𝒱s-con [] = tt
  𝒱s-con (v ∷ vs) = ⟨ 𝒱-con v , 𝒱s-con vs ⟩

  {- a component of a tuple -}
  proj-𝒱s : ∀ {n} (i : Fin n) vs {v} → proj i vs ≡ just v → ∀ d → d ∈ 𝒱 v → At i (𝒱s vs) d
  proj-𝒱s {suc n} zero (v ∷ vs) eq d d∈ with has-length n vs in h
  proj-𝒱s {suc n} zero (v ∷ vs) refl d d∈ | true =
    ⟨ subst (λ m → length (𝒱s vs) ≡ m) (has-length→length n vs h) (length-𝒱s vs) , d∈ ⟩
  proj-𝒱s {suc n} zero (v ∷ vs) () d d∈ | false
  proj-𝒱s (suc i) (v ∷ vs) eq d d∈ = proj-𝒱s i vs eq d d∈

  {- primitives -}
  int-in : ∀ v {n} → obs v ≡ o-const Int n → dconst {Int} n ∈ 𝒱 v
  int-in (const B k) refl = ⟨ refl , refl ⟩

  𝒱-out : ∀ r d → d ∈ 𝒱 (out r) → d ≡ dout r
  𝒱-out (int k) (dconst k') ⟨ refl , refl ⟩ = refl
  𝒱-out (bool true) (left ⟨⟩) tt = refl
  𝒱-out (bool false) (right ⟨⟩) tt = refl
  𝒱-out (bool true) (left (tup[ zero ] d)) ⟨ () , _ ⟩
  𝒱-out (bool true) (left (tup[ suc i ] d)) ⟨ () , _ ⟩
  𝒱-out (bool false) (right (tup[ zero ] d)) ⟨ () , _ ⟩
  𝒱-out (bool false) (right (tup[ suc i ] d)) ⟨ () , _ ⟩

  prim-⊆ : ∀ p v w r → δ? p (obs v) (obs w) ≡ just r → 𝒱 (out r) ⊆ primD p ⟨ 𝒱 v , ⟨ 𝒱 w , ptt ⟩ ⟩
  prim-⊆ p v w r e d d∈ with δ?-inv p (obs v) (obs w) e
  ... | ⟨ n , ⟨ m , ⟨ ov , ⟨ ow , refl ⟩ ⟩ ⟩ ⟩ =
    ⟨ n , ⟨ m , ⟨ int-in v ov , ⟨ int-in w ow , 𝒱-out (δ p n m) d d∈ ⟩ ⟩ ⟩ ⟩

  {- the denotation of a value has an element of the shape of its observation -}
  𝒱-shape : ∀ v → Σ[ d ∈ Value ] d ∈ 𝒱 v × ShapeOf (obs v) d
  𝒱-shape (code k) = ⟨ ν , ⟨ T⁺-ν k , tt ⟩ ⟩
  𝒱-shape (pair v w) with 𝒱-nonempty v | 𝒱-nonempty w
  ... | ⟨ d , d∈ ⟩ | ⟨ e , e∈ ⟩ = ⟨ ⦅ d , e ⦆ , ⟨ ⟨ d∈ , e∈ ⟩ , tt ⟩ ⟩
  𝒱-shape (const B k) = ⟨ dconst k , ⟨ ⟨ refl , refl ⟩ , refl ⟩ ⟩
  𝒱-shape (tup []) = ⟨ ⟨⟩ , ⟨ tt , refl ⟩ ⟩
  𝒱-shape (tup (v ∷ vs)) with 𝒱-shape v
  ... | ⟨ d , ⟨ d∈ , sh ⟩ ⟩ =
    ⟨ tup[_]_ {suc (length vs)} zero d
    , ⟨ ⟨ ⟨ length-𝒱s vs , d∈ ⟩ , 𝒱s-nonempty (v ∷ vs) ⟩ , ⟨ length-obs-list vs , sh ⟩ ⟩ ⟩
  𝒱-shape (T.inl v) with 𝒱-shape v
  ... | ⟨ d , ⟨ d∈ , sh ⟩ ⟩ = ⟨ left d , ⟨ d∈ , sh ⟩ ⟩
  𝒱-shape (T.inr v) with 𝒱-shape v
  ... | ⟨ d , ⟨ d∈ , sh ⟩ ⟩ = ⟨ right d , ⟨ d∈ , sh ⟩ ⟩

{- The logical relation (adequacy) ------------------------------------------------}

module Rel (Run : ℕ → Val → Val → (Val → Set) → Set) where

  𝕍 : Value → Val → Set
  𝕍code : List Value → Value → ℕ → Set
  𝕍s : List Value → Val → Set
  𝕍At : ∀ {n} → Fin n → Value → List Val → Set

  𝕍 (dconst {B} k) v = v ≡ const B k
  𝕍 ν (code k) = ⊤
  𝕍 (X ↦ w) (code k) = 𝕍code X w k
  𝕍 ⦅ u₁ , u₂ ⦆ (pair v w) = 𝕍 u₁ v × 𝕍 u₂ w
  𝕍 ⟨⟩ (tup vs) = vs ≡ []
  𝕍 (tup[ i ] d) (tup vs) = 𝕍At i d vs
  𝕍 (left d) (T.inl v) = 𝕍 d v
  𝕍 (right d) (T.inr v) = 𝕍 d v
  𝕍 _ _ = ⊥

  {- the entries of code, Λ X. Λ Y. N -}
  𝕍code X ν k = ⊤
  𝕍code X (Y ↦ w) k = ∀ e → 𝕍s X e → ∀ v → 𝕍s Y v → Run k e v (𝕍 w)
  𝕍code X _ k = ⊥

  𝕍s [] v = ⊤
  𝕍s (d ∷ V) v = 𝕍 d v × 𝕍s V v

  𝕍At {suc n} zero d (v ∷ vs) = length vs ≡ n × 𝕍 d v
  𝕍At (suc i) d (v ∷ vs) = 𝕍At i d vs
  𝕍At _ d [] = ⊥

  𝕍s-∈ : ∀ V {v d} → 𝕍s V v → d ∈ mem V → 𝕍 d v
  𝕍s-∈ (d ∷ V) ⟨ r , _ ⟩ (here refl) = r
  𝕍s-∈ (d ∷ V) ⟨ _ , rs ⟩ (there d∈) = 𝕍s-∈ V rs d∈

  all→𝕍s : ∀ V {v} → (∀ d → d ∈ mem V → 𝕍 d v) → 𝕍s V v
  all→𝕍s [] all = tt
  all→𝕍s (d ∷ V) all = ⟨ all d (here refl) , all→𝕍s V (λ d' d'∈ → all d' (there d'∈)) ⟩

  𝕍At-proj : ∀ {n} (i : Fin n) d vs → 𝕍At i d vs → Σ[ v ∈ Val ] proj i vs ≡ just v × 𝕍 d v
  𝕍At-proj {suc n} zero d (v ∷ vs) ⟨ len , r ⟩ rewrite length→has-length n vs len = ⟨ v , ⟨ refl , r ⟩ ⟩
  𝕍At-proj (suc i) d (v ∷ vs) r = 𝕍At-proj i d vs r

  𝕍-out : ∀ r → 𝕍 (dout r) (out r)
  𝕍-out (int k) = refl
  𝕍-out (bool true) = refl
  𝕍-out (bool false) = refl

  {- related values are observed in the shape of the denotational value -}
  𝕍-shape : ∀ d v → 𝕍 d v → ShapeOf (obs v) d
  𝕍At-shape : ∀ {n} (i : Fin n) d vs → 𝕍At i d vs → ShapeAt i (obs-list vs) d
  𝕍-shape (dconst k) (const B k) refl = refl
  𝕍-shape ν (code k) r = tt
  𝕍-shape (X ↦ w) (code k) r = tt
  𝕍-shape ⦅ u₁ , u₂ ⦆ (pair v w) r = tt
  𝕍-shape ⟨⟩ (tup []) refl = refl
  𝕍-shape (tup[ i ] d) (tup vs) r = 𝕍At-shape i d vs r
  𝕍-shape (left d) (T.inl v) r = 𝕍-shape d v r
  𝕍-shape (right d) (T.inr v) r = 𝕍-shape d v r
  𝕍At-shape {suc n} zero d (v ∷ vs) ⟨ len , r ⟩ = ⟨ trans (length-obs-list vs) len , 𝕍-shape d v r ⟩
  𝕍At-shape (suc i) d (v ∷ vs) r = 𝕍At-shape i d vs r

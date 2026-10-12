{-

  Adequacy of the graph model for the Clos5 machine: every element of the
  denotation of a well-formed program is witnessed by a run of the
  machine, for the table ds of its global definitions.

  As for ISWIM (Adequacy/LogRel.agda), a logical relation 𝕍 d v, by
  recursion on the denotational value d, relates d to machine values v,
  and the fundamental lemma (adequate) is by induction on the term. What
  differs:

  * Functions are code pointers, applied to an environment and then an
    argument at once (app L M N). The code of a definition denotes
    Λ X. Λ Y. ⟦ N ⟧ (Y • X • init), whose entries are ν, X ↦ ν and
    X ↦ (Y ↦ w); the last is related to code k when the machine finds a
    definition at k that, run on values related to all of X and Y,
    returns a value related to w.

  * A pair is related to the entries ⦅ u , v ⦆ whose components are
    related to its components.

  * The meaning of a reference is the table entry, so the fundamental
    lemma assumes that the table is related to the code pointers (𝕋),
    and the table of the program is (tab), by induction on the
    definitions: the code of each one is related, by the fundamental
    lemma for the older ones.

  * Environments are related on the variables in scope (𝔾 k, for a term
    with WS k): the code of a definition is run with exactly two values,
    and an unbound variable denotes {ω}, while the machine goes wrong.

-}

open import Data.List using (List; []; _∷_; length; replicate; reverse)
open import Compiler.Lang.Clos5 using (AST)

module Compiler.Operational.Adequacy.Clos5LogRel (ds : List AST) where

open import SetsAsPredicates
open import GraphModel.Domain
  using (Value; _↦_; ν; ω; ⦅_,_⦆; tup[_]_; left; right; ⟨⟩)
  renaming (const to dconst)
open import GraphModel.Ops using (nthD)
open import Compiler.Model.Graph.Prim using () renaming (out to dout)
open import Compiler.Lang.Prim using (int; bool; δ)
open import Primitives using (Int)
open import Data.Bool using (true; false)
open import Compiler.Lang.Clos5 hiding (AST)
open import Compiler.Model.Graph.Sem.Clos5Iswim
  using (Table; ⟦_⟧[_]; ⟦_⟧₊[_]; table; init)
import NewEnv
open import NewSyntaxUtil using (_,,_; ⟩_,,_)
open import ListUtil
open import Compiler.Operational.Machine.Clos5
open import Compiler.Compile.GlobalizeTable using (_⊑_; ∷-⊑; global-⊑)
open import Compiler.Operational.Adequacy.Common using (ShapeOf; ShapeAt; length→has-length)
open import Compiler.Operational.Adequacy.Clos5WF using (WS; WS-args; DefsWF)
open import Compiler.Operational.Adequacy.Clos5Common ds

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin; zero; suc)
open import Data.List.Base using (reverseAcc)
open import Data.List.Properties using (reverse-involutive)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_)
open import Data.Maybe using (just)
open import Data.Nat using (ℕ; zero; suc; _<_; _≟_; s≤s)
open import Data.Product using (_×_; Σ-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong; subst)
open import Relation.Nullary using (yes; no)

VEnv : Set₁
VEnv = NewEnv.Env Value

{- Evaluation -------------------------------------------------------------------}

infix 4 _⊢_⇓_
_⊢_⇓_ : Env → AST → Val → Set
γ ⊢ M ⇓ v = ∀ κ → eval M γ κ ↠ ret v κ

⇓-det : ∀ {γ M v₁ v₂} → γ ⊢ M ⇓ v₁ → γ ⊢ M ⇓ v₂ → v₁ ≡ v₂
⇓-det {v₁ = v₁} {v₂} e₁ e₂ with ↠-final-det (e₁ halt) (e₂ halt) refl refl
... | refl = refl

{- The logical relation ----------------------------------------------------------}

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
𝕍 (left d) (inl v) = 𝕍 d v
𝕍 (right d) (inr v) = 𝕍 d v
𝕍 _ _ = ⊥

{- the entries of code, Λ X. Λ Y. N -}
𝕍code X ν k = ⊤
𝕍code X (Y ↦ w) k =
  ∀ e → 𝕍s X e → ∀ v → 𝕍s Y v
  → Σ[ N ∈ AST ] global ds k ≡ just N × Σ[ v' ∈ Val ] (v ∷ e ∷ []) ⊢ N ⇓ v' × 𝕍 w v'
𝕍code X _ k = ⊥

𝕍s [] v = ⊤
𝕍s (d ∷ V) v = 𝕍 d v × 𝕍s V v

𝕍At {suc n} zero d (v ∷ vs) = length vs ≡ n × 𝕍 d v
𝕍At (suc i) d (v ∷ vs) = 𝕍At i d vs
𝕍At _ d [] = ⊥

𝕍s-∈ : ∀ V {v d} → 𝕍s V v → d ∈ mem V → 𝕍 d v
𝕍s-∈ (d ∷ V) ⟨ r , _ ⟩ (here refl) = r
𝕍s-∈ (d ∷ V) ⟨ _ , rs ⟩ (there d∈) = 𝕍s-∈ V rs d∈

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
𝕍-shape (left d) (inl v) r = 𝕍-shape d v r
𝕍-shape (right d) (inr v) r = 𝕍-shape d v r
𝕍At-shape {suc n} zero d (v ∷ vs) ⟨ len , r ⟩ = ⟨ trans (length-obs-list vs) len , 𝕍-shape d v r ⟩
𝕍At-shape (suc i) d (v ∷ vs) r = 𝕍At-shape i d vs r

{- Related environments and tables -----------------------------------------------}

{- on the k variables in scope -}
𝔾 : ℕ → VEnv → Env → Set
𝔾 k ρ γ = ∀ x → x < k → ∀ d → d ∈ ρ x → Σ[ v ∈ Val ] γ ‼ x ≡ just v × 𝕍 d v

𝔾-ext : ∀ {k ρ γ} V v → 𝔾 k ρ γ → 𝕍s V v → 𝔾 (suc k) (mem V • ρ) (v ∷ γ)
𝔾-ext V v G Vv zero _ d d∈ = ⟨ v , ⟨ refl , 𝕍s-∈ V Vv d∈ ⟩ ⟩
𝔾-ext V v G Vv (suc x) (s≤s x<) d d∈ = G x x< d d∈

{- every entry of the table is related to the code pointer -}
𝕋 : Table → Set
𝕋 T = ∀ k d → d ∈ T k → 𝕍 d (code k)

{- Lemmas about runs -------------------------------------------------------------}

collect : ∀ {γ M v} (P : Value → Val → Set) V
  → (∀ d → d ∈ mem V → Σ[ v' ∈ Val ] γ ⊢ M ⇓ v' × P d v') → γ ⊢ M ⇓ v
  → ∀ d → d ∈ mem V → P d v
collect P V all e d d∈ with all d d∈
... | ⟨ v' , ⟨ e' , r ⟩ ⟩ with ⇓-det e e'
... | refl = r

all→𝕍s : ∀ V {v} → (∀ d → d ∈ mem V → 𝕍 d v) → 𝕍s V v
all→𝕍s [] all = tt
all→𝕍s (d ∷ V) all = ⟨ all d (here refl) , all→𝕍s V (λ d' d'∈ → all d' (there d'∈)) ⟩

Evals : Env → List AST → List Val → Set
Evals γ = Pointwise (λ M v → γ ⊢ M ⇓ v)

tuple-run : ∀ {γ κ} acc Ms vs → Evals γ Ms vs
  → tuple-next acc Ms γ κ ↠ ret (tup (reverse (reverseAcc acc vs))) κ
tuple-run acc [] [] [] = done
tuple-run {γ} {κ} acc (M ∷ Ms) (v ∷ vs) (e ∷ es) =
  e (tupK acc Ms γ κ) ++↠ (refl ∷↠ tuple-run (v ∷ acc) Ms vs es)

{- The fundamental lemma ----------------------------------------------------------}

adequate : ∀ M {T k ρ γ d} → 𝕋 T → WS k M → 𝔾 k ρ γ → d ∈ ⟦ M ⟧[ T ] ρ
  → Σ[ v ∈ Val ] γ ⊢ M ⇓ v × 𝕍 d v
adequate-args : ∀ {n} (args : Args (replicate n ■)) {T k ρ γ} → 𝕋 T → WS-args k args
  → 𝔾 k ρ γ → (∀ j → nonempty (nthD (⟦ args ⟧₊[ T ] ρ) j))
  → Σ[ vs ∈ List Val ] Evals γ (args→list args) vs × length vs ≡ n
      × (∀ j d → d ∈ nthD (⟦ args ⟧₊[ T ] ρ) j → 𝕍At j d vs)

adequate (` x) tt' w G d∈ with G x w _ d∈
... | ⟨ v , ⟨ look , r ⟩ ⟩ = ⟨ v , ⟨ (λ κ → cong (λ m → ret? m κ) look ∷↠ done) , r ⟩ ⟩

adequate (fun-ref k ⦅ Nil ⦆) {d = d} 𝕋T w G d∈ =
  ⟨ code k , ⟨ (λ κ → refl ∷↠ done) , 𝕋T k d d∈ ⟩ ⟩

adequate (app ⦅ L ,, M ,, N ,, Nil ⦆) 𝕋T w G ⟨ [] , ⟨ _ , ⟨ _ , ne ⟩ ⟩ ⟩ = ⊥-elim (ne refl)
adequate (app ⦅ L ,, M ,, N ,, Nil ⦆) 𝕋T w G ⟨ _ ∷ _ , ⟨ ⟨ [] , ⟨ _ , ⟨ _ , ne ⟩ ⟩ ⟩ , _ ⟩ ⟩ =
  ⊥-elim (ne refl)
adequate (app ⦅ L ,, M ,, N ,, Nil ⦆) {T} {k} {ρ} {γ} {d} 𝕋T ⟨ wL , ⟨ wM , ⟨ wN , _ ⟩ ⟩ ⟩ G
    ⟨ v₀ ∷ V , ⟨ ⟨ u₀ ∷ U , ⟨ f∈ , ⟨ U⊆ , _ ⟩ ⟩ ⟩ , ⟨ V⊆ , _ ⟩ ⟩ ⟩
    with adequate L 𝕋T wL G f∈ | adequate M 𝕋T wM G (U⊆ u₀ (here refl))
       | adequate N 𝕋T wN G (V⊆ v₀ (here refl))
... | ⟨ code j , ⟨ eL , rL ⟩ ⟩ | ⟨ e , ⟨ eM , _ ⟩ ⟩ | ⟨ a , ⟨ eN , _ ⟩ ⟩
    with rL e (all→𝕍s (u₀ ∷ U) (collect 𝕍 (u₀ ∷ U) (λ d' d'∈ → adequate M 𝕋T wM G (U⊆ d' d'∈)) eM))
            a (all→𝕍s (v₀ ∷ V) (collect 𝕍 (v₀ ∷ V) (λ d' d'∈ → adequate N 𝕋T wN G (V⊆ d' d'∈)) eN))
... | ⟨ B , ⟨ g , ⟨ v , ⟨ eB , r ⟩ ⟩ ⟩ ⟩ =
  ⟨ v , ⟨ (λ κ → refl ∷↠ eL (appF M N γ κ) ++↠ refl ∷↠ eM (appE (code j) N γ κ)
                  ++↠ refl ∷↠ eN (appA (code j) e κ) ++↠ cong (λ m → call m a e κ) g ∷↠ eB κ)
        , r ⟩ ⟩

adequate (lit B k ⦅ Nil ⦆) {d = dconst k'} 𝕋T w G ⟨ refl , refl ⟩ =
  ⟨ const B k , ⟨ (λ κ → refl ∷↠ done) , refl ⟩ ⟩
adequate (lit B k ⦅ Nil ⦆) {d = V ↦ w'} 𝕋T w G ()
adequate (lit B k ⦅ Nil ⦆) {d = ν} 𝕋T w G ()
adequate (lit B k ⦅ Nil ⦆) {d = ω} 𝕋T w G ()
adequate (lit B k ⦅ Nil ⦆) {d = ⦅ u , v ⦆} 𝕋T w G ()
adequate (lit B k ⦅ Nil ⦆) {d = tup[ i ] d} 𝕋T w G ()
adequate (lit B k ⦅ Nil ⦆) {d = left d} 𝕋T w G ()
adequate (lit B k ⦅ Nil ⦆) {d = right d} 𝕋T w G ()
adequate (lit B k ⦅ Nil ⦆) {d = ⟨⟩} 𝕋T w G ()

adequate (pair-op ⦅ L ,, M ,, Nil ⦆) {γ = γ} {d = ⦅ u₁ , u₂ ⦆} 𝕋T ⟨ wL , ⟨ wM , _ ⟩ ⟩ G ⟨ u₁∈ , u₂∈ ⟩
    with adequate L 𝕋T wL G u₁∈ | adequate M 𝕋T wM G u₂∈
... | ⟨ v₁ , ⟨ e₁ , r₁ ⟩ ⟩ | ⟨ v₂ , ⟨ e₂ , r₂ ⟩ ⟩ =
  ⟨ pair v₁ v₂ , ⟨ (λ κ → refl ∷↠ e₁ (pairL M γ κ) ++↠ refl ∷↠ e₂ (pairR v₁ κ) ++↠ refl ∷↠ done)
               , ⟨ r₁ , r₂ ⟩ ⟩ ⟩
adequate (pair-op ⦅ L ,, M ,, Nil ⦆) {d = dconst k} 𝕋T w G ()
adequate (pair-op ⦅ L ,, M ,, Nil ⦆) {d = V ↦ w'} 𝕋T w G ()
adequate (pair-op ⦅ L ,, M ,, Nil ⦆) {d = ν} 𝕋T w G ()
adequate (pair-op ⦅ L ,, M ,, Nil ⦆) {d = ω} 𝕋T w G ()
adequate (pair-op ⦅ L ,, M ,, Nil ⦆) {d = tup[ i ] d} 𝕋T w G ()
adequate (pair-op ⦅ L ,, M ,, Nil ⦆) {d = left d} 𝕋T w G ()
adequate (pair-op ⦅ L ,, M ,, Nil ⦆) {d = right d} 𝕋T w G ()
adequate (pair-op ⦅ L ,, M ,, Nil ⦆) {d = ⟨⟩} 𝕋T w G ()

adequate (fst-op ⦅ M ,, Nil ⦆) {γ = γ} 𝕋T ⟨ wM , _ ⟩ G ⟨ _ , d∈ ⟩ with adequate M 𝕋T wM G d∈
... | ⟨ pair v₁ v₂ , ⟨ e , ⟨ r , _ ⟩ ⟩ ⟩ = ⟨ v₁ , ⟨ (λ κ → refl ∷↠ e (fstK κ) ++↠ refl ∷↠ done) , r ⟩ ⟩

adequate (snd-op ⦅ M ,, Nil ⦆) {γ = γ} 𝕋T ⟨ wM , _ ⟩ G ⟨ _ , d∈ ⟩ with adequate M 𝕋T wM G d∈
... | ⟨ pair v₁ v₂ , ⟨ e , ⟨ _ , r ⟩ ⟩ ⟩ = ⟨ v₂ , ⟨ (λ κ → refl ∷↠ e (sndK κ) ++↠ refl ∷↠ done) , r ⟩ ⟩

adequate (tuple zero ⦅ Nil ⦆) {d = ⟨⟩} 𝕋T w G tt = ⟨ tup [] , ⟨ (λ κ → refl ∷↠ done) , refl ⟩ ⟩
adequate (tuple (suc n) ⦅ args ⦆) {γ = γ} {d = tup[ i ] d} 𝕋T w G ⟨ refl , ⟨ d∈ , ne ⟩ ⟩
    with adequate-args args 𝕋T w G ne
... | ⟨ vs , ⟨ es , ⟨ len , rs ⟩ ⟩ ⟩ =
  ⟨ tup vs
  , ⟨ (λ κ → refl ∷↠ subst (λ ws → tuple-next [] (args→list args) γ κ ↠ ret (tup ws) κ)
                            (reverse-involutive vs) (tuple-run [] (args→list args) vs es))
    , rs i d d∈ ⟩ ⟩
adequate (tuple zero ⦅ Nil ⦆) {d = tup[ i ] d} 𝕋T w G ()
adequate (tuple zero ⦅ Nil ⦆) {d = dconst k} 𝕋T w G ()
adequate (tuple (suc n) ⦅ args ⦆) {d = dconst k} 𝕋T w G ()
adequate (tuple zero ⦅ Nil ⦆) {d = V ↦ w'} 𝕋T w G ()
adequate (tuple (suc n) ⦅ args ⦆) {d = V ↦ w'} 𝕋T w G ()
adequate (tuple zero ⦅ Nil ⦆) {d = ν} 𝕋T w G ()
adequate (tuple (suc n) ⦅ args ⦆) {d = ν} 𝕋T w G ()
adequate (tuple zero ⦅ Nil ⦆) {d = ω} 𝕋T w G ()
adequate (tuple (suc n) ⦅ args ⦆) {d = ω} 𝕋T w G ()
adequate (tuple zero ⦅ Nil ⦆) {d = ⦅ u , v ⦆} 𝕋T w G ()
adequate (tuple (suc n) ⦅ args ⦆) {d = ⦅ u , v ⦆} 𝕋T w G ()
adequate (tuple zero ⦅ Nil ⦆) {d = left d} 𝕋T w G ()
adequate (tuple (suc n) ⦅ args ⦆) {d = left d} 𝕋T w G ()
adequate (tuple zero ⦅ Nil ⦆) {d = right d} 𝕋T w G ()
adequate (tuple (suc n) ⦅ args ⦆) {d = right d} 𝕋T w G ()
adequate (tuple (suc n) ⦅ args ⦆) {d = ⟨⟩} 𝕋T w G ()

adequate (get i ⦅ M ,, Nil ⦆) {γ = γ} 𝕋T ⟨ wM , _ ⟩ G d∈ with adequate M 𝕋T wM G d∈
... | ⟨ tup vs , ⟨ e , r ⟩ ⟩ with 𝕍At-proj i _ vs r
... | ⟨ v , ⟨ p , r' ⟩ ⟩ =
  ⟨ v , ⟨ (λ κ → refl ∷↠ e (getK i κ) ++↠ cong (λ m → ret? m κ) p ∷↠ done) , r' ⟩ ⟩

adequate (inl-op ⦅ M ,, Nil ⦆) {γ = γ} {d = left d} 𝕋T ⟨ wM , _ ⟩ G d∈ with adequate M 𝕋T wM G d∈
... | ⟨ v , ⟨ e , r ⟩ ⟩ = ⟨ inl v , ⟨ (λ κ → refl ∷↠ e (inlK κ) ++↠ refl ∷↠ done) , r ⟩ ⟩
adequate (inl-op ⦅ M ,, Nil ⦆) {d = dconst k} 𝕋T w G ()
adequate (inl-op ⦅ M ,, Nil ⦆) {d = V ↦ w'} 𝕋T w G ()
adequate (inl-op ⦅ M ,, Nil ⦆) {d = ν} 𝕋T w G ()
adequate (inl-op ⦅ M ,, Nil ⦆) {d = ω} 𝕋T w G ()
adequate (inl-op ⦅ M ,, Nil ⦆) {d = ⦅ u , v ⦆} 𝕋T w G ()
adequate (inl-op ⦅ M ,, Nil ⦆) {d = tup[ i ] d} 𝕋T w G ()
adequate (inl-op ⦅ M ,, Nil ⦆) {d = right d} 𝕋T w G ()
adequate (inl-op ⦅ M ,, Nil ⦆) {d = ⟨⟩} 𝕋T w G ()

adequate (inr-op ⦅ M ,, Nil ⦆) {γ = γ} {d = right d} 𝕋T ⟨ wM , _ ⟩ G d∈ with adequate M 𝕋T wM G d∈
... | ⟨ v , ⟨ e , r ⟩ ⟩ = ⟨ inr v , ⟨ (λ κ → refl ∷↠ e (inrK κ) ++↠ refl ∷↠ done) , r ⟩ ⟩
adequate (inr-op ⦅ M ,, Nil ⦆) {d = dconst k} 𝕋T w G ()
adequate (inr-op ⦅ M ,, Nil ⦆) {d = V ↦ w'} 𝕋T w G ()
adequate (inr-op ⦅ M ,, Nil ⦆) {d = ν} 𝕋T w G ()
adequate (inr-op ⦅ M ,, Nil ⦆) {d = ω} 𝕋T w G ()
adequate (inr-op ⦅ M ,, Nil ⦆) {d = ⦅ u , v ⦆} 𝕋T w G ()
adequate (inr-op ⦅ M ,, Nil ⦆) {d = tup[ i ] d} 𝕋T w G ()
adequate (inr-op ⦅ M ,, Nil ⦆) {d = left d} 𝕋T w G ()
adequate (inr-op ⦅ M ,, Nil ⦆) {d = ⟨⟩} 𝕋T w G ()

adequate (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) {γ = γ} 𝕋T ⟨ wL , ⟨ wM , ⟨ wN , _ ⟩ ⟩ ⟩ G
    (inj₁ ⟨ u , ⟨ U , ⟨ allL , ⟨ w∈ , _ ⟩ ⟩ ⟩ ⟩)
    with adequate L 𝕋T wL G (allL u (here refl))
... | ⟨ inl a , ⟨ eL , _ ⟩ ⟩
    with adequate M 𝕋T wM (𝔾-ext (u ∷ U) a G
           (all→𝕍s (u ∷ U) (collect (λ d v → 𝕍 (left d) v) (u ∷ U)
              (λ d d∈ → adequate L 𝕋T wL G (allL d d∈)) eL))) w∈
... | ⟨ v , ⟨ eM , r ⟩ ⟩ =
  ⟨ v , ⟨ (λ κ → refl ∷↠ eL (caseK M N γ κ) ++↠ refl ∷↠ eM κ) , r ⟩ ⟩
adequate (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) {γ = γ} 𝕋T ⟨ wL , ⟨ wM , ⟨ wN , _ ⟩ ⟩ ⟩ G
    (inj₂ ⟨ u , ⟨ U , ⟨ allR , ⟨ w∈ , _ ⟩ ⟩ ⟩ ⟩)
    with adequate L 𝕋T wL G (allR u (here refl))
... | ⟨ inr a , ⟨ eL , _ ⟩ ⟩
    with adequate N 𝕋T wN (𝔾-ext (u ∷ U) a G
           (all→𝕍s (u ∷ U) (collect (λ d v → 𝕍 (right d) v) (u ∷ U)
              (λ d d∈ → adequate L 𝕋T wL G (allR d d∈)) eL))) w∈
... | ⟨ v , ⟨ eN , r ⟩ ⟩ =
  ⟨ v , ⟨ (λ κ → refl ∷↠ eL (caseK M N γ κ) ++↠ refl ∷↠ eN κ) , r ⟩ ⟩

adequate (let-op ⦅ M ,, ⟩ N ,, Nil ⦆) 𝕋T w G ⟨ [] , ⟨ _ , ⟨ _ , ne ⟩ ⟩ ⟩ = ⊥-elim (ne refl)
adequate (let-op ⦅ M ,, ⟩ N ,, Nil ⦆) {γ = γ} 𝕋T ⟨ wM , ⟨ wN , _ ⟩ ⟩ G
    ⟨ u ∷ U , ⟨ ⟨ d∈ , _ ⟩ , ⟨ U⊆ , _ ⟩ ⟩ ⟩
    with adequate M 𝕋T wM G (U⊆ u (here refl))
... | ⟨ a , ⟨ eM , _ ⟩ ⟩
    with adequate N 𝕋T wN (𝔾-ext (u ∷ U) a G
           (all→𝕍s (u ∷ U) (collect 𝕍 (u ∷ U) (λ d' d'∈ → adequate M 𝕋T wM G (U⊆ d' d'∈)) eM))) d∈
... | ⟨ v , ⟨ eN , r ⟩ ⟩ =
  ⟨ v , ⟨ (λ κ → refl ∷↠ eM (letK N γ κ) ++↠ refl ∷↠ eN κ) , r ⟩ ⟩

adequate (prim p ⦅ L ,, M ,, Nil ⦆) {γ = γ} 𝕋T ⟨ wL , ⟨ wM , _ ⟩ ⟩ G ⟨ n , ⟨ m , ⟨ n∈ , ⟨ m∈ , refl ⟩ ⟩ ⟩ ⟩
    with adequate L 𝕋T wL G n∈ | adequate M 𝕋T wM G m∈
... | ⟨ _ , ⟨ eL , refl ⟩ ⟩ | ⟨ _ , ⟨ eM , refl ⟩ ⟩ =
  ⟨ out (δ p n m)
  , ⟨ (λ κ → refl ∷↠ eL (primL p M γ κ) ++↠ refl ∷↠ eM (primR p (const Int n) κ) ++↠ refl ∷↠ done)
    , 𝕍-out (δ p n m) ⟩ ⟩

adequate-args {zero} Nil 𝕋T w G ne = ⟨ [] , ⟨ [] , ⟨ refl , (λ ()) ⟩ ⟩ ⟩
adequate-args {suc n} (M ,, args) 𝕋T ⟨ wM , ws ⟩ G ne
    with adequate M 𝕋T wM G (proj₂ (ne zero))
       | adequate-args args 𝕋T ws G (λ j → ne (suc j))
... | ⟨ v , ⟨ e , _ ⟩ ⟩ | ⟨ vs , ⟨ es , ⟨ len , rs ⟩ ⟩ ⟩ =
  ⟨ v ∷ vs , ⟨ e ∷ es , ⟨ cong suc len , R ⟩ ⟩ ⟩
  where
  R : ∀ j d → d ∈ nthD (⟦ M ,, args ⟧₊[ _ ] _) j → 𝕍At j d (v ∷ vs)
  R zero d d∈ = ⟨ len , collect 𝕍 (d ∷ []) (λ { d' (here refl) → adequate M 𝕋T wM G d∈ }) e d (here refl) ⟩
  R (suc j) d d∈ = rs j d d∈

{- The table of the program --------------------------------------------------------}

tab : ∀ Ns → Ns ⊑ ds → DefsWF Ns → 𝕋 (table Ns)
tab (N ∷ Ns) p wf k d d∈ with k ≟ length Ns
tab (N ∷ Ns) p wf k d d∈ | no _ = tab Ns (∷-⊑ p) (proj₂ wf) k d d∈
tab (N ∷ Ns) p wf .(length Ns) ν d∈ | yes refl = tt
tab (N ∷ Ns) p wf .(length Ns) (X ↦ ν) d∈ | yes refl = tt
tab (N ∷ Ns) p wf .(length Ns) (X ↦ (Y ↦ w)) ⟨ ⟨ w∈ , _ ⟩ , _ ⟩ | yes refl = rel
  where
  rel : 𝕍 (X ↦ (Y ↦ w)) (code (length Ns))
  rel e Xe v Yv =
    ⟨ N , ⟨ global-⊑ p , adequate N (tab Ns (∷-⊑ p) (proj₂ wf)) (proj₂ (proj₁ wf)) G w∈ ⟩ ⟩
    where
    G : 𝔾 2 (mem Y • mem X • (λ _ → init)) (v ∷ e ∷ [])
    G zero _ d d∈ = ⟨ v , ⟨ refl , 𝕍s-∈ Y Yv d∈ ⟩ ⟩
    G (suc zero) _ d d∈ = ⟨ e , ⟨ refl , 𝕍s-∈ X Xe d∈ ⟩ ⟩
    G (suc (suc x)) (s≤s (s≤s ())) d d∈

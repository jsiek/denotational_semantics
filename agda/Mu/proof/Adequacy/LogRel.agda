{-

  Adequacy of the graph model for the ISWIMμ machine: every element of
  the denotation of a closed program is witnessed by a run of the
  machine.

  As for ISWIM (proof/Adequacy/LogRel.agda): a logical relation 𝕍 d v,
  by recursion on the denotational value d (and on the folds of v: a
  value of a recursive type is related as the value it folds, since
  fold is the identity on denotations), relates a constant to itself, a
  function entry V ↦ w to closures that, run on a value related to
  every element of V, return a value related to w, and so on.
  Evaluation (γ ⊢ M ⇓ v) is "eval M γ κ runs to ret v κ, for every κ".
  The fundamental lemma (adequate) is by induction on the term, with
  related environments (𝔾). An application needs one argument value
  related to all of the (finitely many) elements of V: the value of the
  argument, since the machine is deterministic (⇓-det, through halt,
  which is a continuation of every type). Typed values have the shape
  of their type, so no case for a value of the wrong kind is needed.

-}

module Mu.proof.Adequacy.LogRel where

open import Framework.Primitives using (Base; base-rep; Int)
open import Language.Prim using (sub; eq; δ)
open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.Domain renaming (const to dconst)
open import proof.Framework.GraphModel.Ops using (nthD)
open import proof.Semantics.Graph.Prim using () renaming (out to dout)
import proof.Framework.GraphModel.Env as E
open import proof.Framework.Runs using (module Runs)
open import Mu.Language.Type
open import Mu.Language.ISWIM
open import Mu.Semantics.Graph.ISWIM using (⟦_⟧; ⟦_⟧s)
open import Mu.Framework.AllUtil using (All; []; _∷_; lookup; pos; All₂; _<><ᵃ_)
open import Mu.Semantics.CEK.ISWIM
open import Semantics.Observation using (o-const; Answer)

open import Data.Bool using (true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin; zero; suc)
open import Data.Integer using () renaming (_≟_ to _≟ℤ_)
open import Data.List using (List; []; _∷_; length)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; Σ-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (does)

open Runs step public

{- Evaluation -------------------------------------------------------------------}

infix 4 _⊢_⇓_
_⊢_⇓_ : ∀ {Γ A} → Env Γ → Tm Γ A → Val A → Set
γ ⊢ M ⇓ v = ∀ κ → eval M γ κ ↠ ret v κ

⇓-det : ∀ {Γ A} {γ : Env Γ} {M : Tm Γ A} {v₁ v₂} → γ ⊢ M ⇓ v₁ → γ ⊢ M ⇓ v₂ → v₁ ≡ v₂
⇓-det e₁ e₂ with ↠-final-det (e₁ halt) (e₂ halt) refl refl
... | refl = refl

{- The logical relation ----------------------------------------------------------}

𝕍 : ∀ {A} → Value → Val A → Set
𝕍s : ∀ {A} → List Value → Val A → Set
𝕍At : ∀ {n Δ} → Fin n → Value → All Val Δ → Set

𝕍 d (fold v) = 𝕍 d v
𝕍 (dconst k) (const k') = dconst k ≡ dconst k'
𝕍 (V ↦ w) (clo {B = B} N γ) = ∀ v → 𝕍s V v → Σ[ v' ∈ Val B ] (v ∷ γ) ⊢ N ⇓ v' × 𝕍 w v'
𝕍 ν (clo N γ) = ⊤
𝕍 ⟨⟩ (tup []) = ⊤
𝕍 (tup[ i ] d) (tup vs) = 𝕍At i d vs
𝕍 (left d) (inl v) = 𝕍 d v
𝕍 (right d) (inr v) = 𝕍 d v
𝕍 _ _ = ⊥

𝕍s [] v = ⊤
𝕍s (d ∷ V) v = 𝕍 d v × 𝕍s V v

𝕍At {ℕ.suc n} {_ ∷ Δ} zero d (v ∷ vs) = length Δ ≡ n × 𝕍 d v
𝕍At (suc i) d (v ∷ vs) = 𝕍At i d vs
𝕍At _ d _ = ⊥

𝕍s-∈ : ∀ {A} V {v : Val A} {d} → 𝕍s V v → d ∈ mem V → 𝕍 d v
𝕍s-∈ (d ∷ V) ⟨ r , _ ⟩ (here refl) = r
𝕍s-∈ (d ∷ V) ⟨ _ , rs ⟩ (there d∈) = 𝕍s-∈ V rs d∈

all→𝕍s : ∀ {A} V {v : Val A} → (∀ d → d ∈ mem V → 𝕍 d v) → 𝕍s V v
all→𝕍s [] all = tt
all→𝕍s (d ∷ V) all = ⟨ all d (here refl) , all→𝕍s V (λ d' d'∈ → all d' (there d'∈)) ⟩

𝕍At-lookup : ∀ {Δ A} (i : Δ ∋ A) d (vs : All Val Δ) → 𝕍At (pos i) d vs → 𝕍 d (lookup vs i)
𝕍At-lookup Z d (v ∷ vs) ⟨ _ , r ⟩ = r
𝕍At-lookup (S i) d (v ∷ vs) r = 𝕍At-lookup i d vs r

𝕍-δ : ∀ p n m → 𝕍 (dout (δ p n m)) (δᵀ p n m)
𝕍-δ sub n m = refl
𝕍-δ eq n m with does (n ≟ℤ m)
... | true = tt
... | false = tt

{- the observation of a value related to a constant is that constant -}
𝕍-const : ∀ {A B} {k : base-rep B} (v : Val A) → 𝕍 (dconst k) v → obs v ≡ o-const B k
𝕍-const (fold v) r = 𝕍-const v r
𝕍-const (const k) refl = refl

{- the machine observes no value as an error -}
obs-answer : ∀ {A} (v : Val A) → Answer (obs v)
obs-answer (clo N γ) ()
obs-answer (const k) ()
obs-answer (tup vs) ()
obs-answer (inl v) ()
obs-answer (inr v) ()
obs-answer (fold v) = obs-answer v

{- Related environments ---------------------------------------------------------}

𝔾 : ∀ {Γ} → E.Env Value → Env Γ → Set
𝔾 {Γ} ρ γ = ∀ {A} (x : Γ ∋ A) d → d ∈ ρ (idx x) → 𝕍 d (lookup γ x)

𝔾-ext : ∀ {Γ A ρ} {γ : Env Γ} V (v : Val A) → 𝔾 ρ γ → 𝕍s V v → 𝔾 (mem V • ρ) (v ∷ γ)
𝔾-ext V v G Vv Z d d∈ = 𝕍s-∈ V Vv d∈
𝔾-ext V v G Vv (S x) = G x

{- Lemmas about runs -------------------------------------------------------------}

{- one value related to all elements of V, all of which M produces -}
collect : ∀ {Γ A} {γ : Env Γ} {M : Tm Γ A} {v} (P : Value → Val A → Set) V
  → (∀ d → d ∈ mem V → Σ[ v' ∈ Val A ] γ ⊢ M ⇓ v' × P d v') → γ ⊢ M ⇓ v
  → ∀ d → d ∈ mem V → P d v
collect P V all e d d∈ with all d d∈
... | ⟨ v' , ⟨ e' , r ⟩ ⟩ with ⇓-det e e'
... | refl = r

Evals : ∀ {Γ Δ} → Env Γ → All (Tm Γ) Δ → All Val Δ → Set
Evals γ = All₂ (λ M v → γ ⊢ M ⇓ v)

tuple-run : ∀ {Γ Δ' Δ} {γ : Env Γ} (acc : All Val Δ') (Ms : All (Tm Γ) Δ) {vs} → Evals γ Ms vs
  → ∀ κ → tuple-next acc Ms γ κ ↠ ret (tup (acc <><ᵃ vs)) κ
tuple-run acc [] All₂.[] κ = done
tuple-run {γ = γ} acc (M ∷ Ms) (e All₂.∷ es) κ = e (tupK acc Ms γ κ) ++↠ (refl ∷↠ tuple-run (_ ∷ acc) Ms es κ)

{- The fundamental lemma ----------------------------------------------------------}

adequate : ∀ {Γ A} (M : Tm Γ A) {ρ} {γ : Env Γ} {d} → 𝔾 ρ γ → d ∈ ⟦ M ⟧ ρ
  → Σ[ v ∈ Val A ] γ ⊢ M ⇓ v × 𝕍 d v
adequate-args : ∀ {Γ Δ} (Ms : All (Tm Γ) Δ) {ρ} {γ : Env Γ} → 𝔾 ρ γ
  → (∀ j → nonempty (nthD (⟦ Ms ⟧s ρ) j))
  → Σ[ vs ∈ All Val Δ ] Evals γ Ms vs × (∀ j d → d ∈ nthD (⟦ Ms ⟧s ρ) j → 𝕍At j d vs)

adequate (` x) G d∈ = ⟨ _ , ⟨ (λ κ → refl ∷↠ done) , G x _ d∈ ⟩ ⟩
adequate (lam N) {γ = γ} {d = ν} G d∈ = ⟨ clo N γ , ⟨ (λ κ → refl ∷↠ done) , tt ⟩ ⟩
adequate (lam N) {γ = γ} {d = V ↦ w} G ⟨ w∈ , _ ⟩ =
  ⟨ clo N γ , ⟨ (λ κ → refl ∷↠ done) , (λ v Vv → adequate N (𝔾-ext V v G Vv) w∈) ⟩ ⟩
adequate (app L M) G ⟨ [] , ⟨ _ , ⟨ _ , ne ⟩ ⟩ ⟩ = ⊥-elim (ne refl)
adequate (app L M) {γ = γ} G ⟨ u ∷ U , ⟨ f∈ , ⟨ V⊆ , _ ⟩ ⟩ ⟩
    with adequate L G f∈ | adequate M G (V⊆ u (here refl))
... | ⟨ clo N γ' , ⟨ eL , rL ⟩ ⟩ | ⟨ vM , ⟨ eM , _ ⟩ ⟩
    with rL vM (all→𝕍s (u ∷ U) (collect 𝕍 (u ∷ U) (λ d' d'∈ → adequate M G (V⊆ d' d'∈)) eM))
... | ⟨ v , ⟨ eN , r ⟩ ⟩ =
  ⟨ v , ⟨ (λ κ → refl ∷↠ eL (appL M γ κ) ++↠ refl ∷↠ eM (appR (clo N γ') κ) ++↠ refl ∷↠ eN κ) , r ⟩ ⟩
adequate (lit B c) {d = dconst k} G ⟨ refl , refl ⟩ = ⟨ const c , ⟨ (λ κ → refl ∷↠ done) , refl ⟩ ⟩
adequate (tuple []) {d = ⟨⟩} G tt = ⟨ tup [] , ⟨ (λ κ → refl ∷↠ done) , tt ⟩ ⟩
adequate (tuple (M ∷ Ms)) {γ = γ} {d = tup[ i ] u} G ⟨ refl , ⟨ u∈ , ne ⟩ ⟩ with adequate-args (M ∷ Ms) G ne
... | ⟨ vs , ⟨ evs , rs ⟩ ⟩ = ⟨ tup vs , ⟨ (λ κ → refl ∷↠ tuple-run [] (M ∷ Ms) evs κ) , rs i u u∈ ⟩ ⟩
adequate (get i M) {γ = γ} G d∈ with adequate M G d∈
... | ⟨ tup vs , ⟨ e , r ⟩ ⟩ =
  ⟨ lookup vs i , ⟨ (λ κ → refl ∷↠ e (getK i κ) ++↠ refl ∷↠ done) , 𝕍At-lookup i _ vs r ⟩ ⟩
adequate (inl M) {d = left u} G u∈ with adequate M G u∈
... | ⟨ v , ⟨ e , r ⟩ ⟩ = ⟨ inl v , ⟨ (λ κ → refl ∷↠ e (inlK κ) ++↠ refl ∷↠ done) , r ⟩ ⟩
adequate (inr M) {d = right u} G u∈ with adequate M G u∈
... | ⟨ v , ⟨ e , r ⟩ ⟩ = ⟨ inr v , ⟨ (λ κ → refl ∷↠ e (inrK κ) ++↠ refl ∷↠ done) , r ⟩ ⟩
adequate (case L M N) {γ = γ} G (inj₁ ⟨ u , ⟨ U , ⟨ allL , ⟨ w∈ , _ ⟩ ⟩ ⟩ ⟩) with adequate L G (allL u (here refl))
... | ⟨ inr a , ⟨ _ , () ⟩ ⟩
... | ⟨ inl a , ⟨ eL , _ ⟩ ⟩
    with adequate M (𝔾-ext (u ∷ U) a G (all→𝕍s (u ∷ U)
           (collect (λ d v → 𝕍 (left d) v) (u ∷ U) (λ d d∈ → adequate L G (allL d d∈)) eL))) w∈
... | ⟨ v , ⟨ eM , r ⟩ ⟩ = ⟨ v , ⟨ (λ κ → refl ∷↠ eL (caseK M N γ κ) ++↠ refl ∷↠ eM κ) , r ⟩ ⟩
adequate (case L M N) {γ = γ} G (inj₂ ⟨ u , ⟨ U , ⟨ allR , ⟨ w∈ , _ ⟩ ⟩ ⟩ ⟩) with adequate L G (allR u (here refl))
... | ⟨ inl a , ⟨ _ , () ⟩ ⟩
... | ⟨ inr a , ⟨ eL , _ ⟩ ⟩
    with adequate N (𝔾-ext (u ∷ U) a G (all→𝕍s (u ∷ U)
           (collect (λ d v → 𝕍 (right d) v) (u ∷ U) (λ d d∈ → adequate L G (allR d d∈)) eL))) w∈
... | ⟨ v , ⟨ eN , r ⟩ ⟩ = ⟨ v , ⟨ (λ κ → refl ∷↠ eL (caseK M N γ κ) ++↠ refl ∷↠ eN κ) , r ⟩ ⟩
adequate (prim p L M) {γ = γ} G ⟨ n , ⟨ m , ⟨ n∈ , ⟨ m∈ , refl ⟩ ⟩ ⟩ ⟩
    with adequate L G n∈ | adequate M G m∈
... | ⟨ const _ , ⟨ eL , refl ⟩ ⟩ | ⟨ const _ , ⟨ eM , refl ⟩ ⟩ =
  ⟨ δᵀ p n m
  , ⟨ (λ κ → refl ∷↠ eL (primL p M γ κ) ++↠ refl ∷↠ eM (primR p n κ) ++↠ refl ∷↠ done) , 𝕍-δ p n m ⟩ ⟩
adequate (let′ M N) G ⟨ [] , ⟨ _ , ⟨ _ , ne ⟩ ⟩ ⟩ = ⊥-elim (ne refl)
adequate (let′ M N) {γ = γ} G ⟨ u ∷ U , ⟨ ⟨ w∈ , _ ⟩ , ⟨ V⊆ , _ ⟩ ⟩ ⟩
    with adequate M G (V⊆ u (here refl))
... | ⟨ a , ⟨ eM , _ ⟩ ⟩
    with adequate N (𝔾-ext (u ∷ U) a G (all→𝕍s (u ∷ U)
           (collect 𝕍 (u ∷ U) (λ d d∈ → adequate M G (V⊆ d d∈)) eM))) w∈
... | ⟨ v , ⟨ eN , r ⟩ ⟩ = ⟨ v , ⟨ (λ κ → refl ∷↠ eM (letK N γ κ) ++↠ refl ∷↠ eN κ) , r ⟩ ⟩
adequate (fold M) G d∈ with adequate M G d∈
... | ⟨ v , ⟨ e , r ⟩ ⟩ = ⟨ fold v , ⟨ (λ κ → refl ∷↠ e (foldK κ) ++↠ refl ∷↠ done) , r ⟩ ⟩
adequate (unfold M) G d∈ with adequate M G d∈
... | ⟨ fold v , ⟨ e , r ⟩ ⟩ = ⟨ v , ⟨ (λ κ → refl ∷↠ e (unfoldK κ) ++↠ refl ∷↠ done) , r ⟩ ⟩

adequate-args [] G ne = ⟨ [] , ⟨ All₂.[] , (λ ()) ⟩ ⟩
adequate-args (M ∷ Ms) G ne with adequate M G (proj₂ (ne zero)) | adequate-args Ms G (λ j → ne (suc j))
... | ⟨ v , ⟨ e , _ ⟩ ⟩ | ⟨ vs , ⟨ evs , rs ⟩ ⟩ = ⟨ v ∷ vs , ⟨ e All₂.∷ evs , R ⟩ ⟩
  where
  R : ∀ j d → d ∈ nthD (⟦ M ∷ Ms ⟧s _) j → 𝕍At j d (v ∷ vs)
  R zero d d∈ = ⟨ refl , collect 𝕍 (d ∷ []) (λ { d' (here refl) → adequate M G d∈ }) e d (here refl) ⟩
  R (suc j) d d∈ = rs j d d∈

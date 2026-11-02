{-

  Adequacy of the graph model for the clocked interpreter of FPC:
  every element of the denotation of a closed program is witnessed by
  the value the interpreter returns from some clock on.

  As for the FPC machine (Mu/proof/Adequacy/AbstractMachines/LogRel.agda): a logical
  relation 𝕍 d v, by recursion on the denotational value d (and on the
  folds of v), relates a constant to itself, a function entry V ↦ w to
  closures that, run on a value related to every element of V, return a
  value related to w, and so on. Evaluation (γ ⊢ M ⇓ v) is "eval returns
  v from some clock on" (Stable, proof/Framework/Clocked.agda), so the
  results of subterms compose by st-bind (at the largest of their
  clocks), with no lemma about the interpreter's monotonicity, and the
  interpreter is deterministic by stable-unique. The fundamental lemma
  (adequate) is by induction on the term, with related environments
  (𝔾); an application needs one argument value related to all of the
  (finitely many) elements of V: the value of the argument (collect).

-}

module Mu.proof.Adequacy.LogRel where

open import Framework.Primitives using (Base; base-rep; Int)
open import Language.Prim using (sub; eq) renaming (δ to δᴾ)
open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.Domain renaming (const to dconst)
open import proof.Framework.GraphModel.Ops using (nthD)
open import proof.Semantics.Graph.Prim using () renaming (out to dout)
import proof.Framework.GraphModel.Env as E
open import proof.Semantics.Interp.Clock using (Result; ret; Stable; st-now; st-bind; stable-unique)
open import Mu.Language.Type
open import Mu.Language.FPC
open import Mu.Semantics.GraphModel.FPC using (⟦_⟧; ⟦_⟧s)
open import Mu.Framework.AllUtil using (All; []; _∷_; lookup; pos; All₂)
open import Mu.Semantics.ClockedInterpreters.FPC
open import Semantics.Observation using (o-const)

open import Data.Bool using (true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin; zero; suc)
open import Data.Integer using () renaming (_≟_ to _≟ℤ_)
open import Data.List using (List; []; _∷_; length)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (ℕ; zero; suc; s≤s)
open import Data.Product using (_×_; Σ-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (does)

{- Evaluation -------------------------------------------------------------------}

infix 4 _⊢_⇓_
_⊢_⇓_ : ∀ {Γ A} → Env Γ → Tm Γ A → Val A → Set
γ ⊢ M ⇓ v = Stable (λ ck → eval ck γ M) (ret v)

⇓-det : ∀ {Γ A} (γ : Env Γ) (M : Tm Γ A) {v₁ v₂} → γ ⊢ M ⇓ v₁ → γ ⊢ M ⇓ v₂ → v₁ ≡ v₂
⇓-det γ M e₁ e₂ with stable-unique e₁ e₂
... | refl = refl

{- a value, at every clock -}
now : ∀ {B} {f : ℕ → Result B} {v} → (∀ ck → f ck ≡ ret v) → Stable f (ret v)
now = st-now

{- a call of a closure whose body returns v from clock c on returns v from c + 1 on -}
st-call : ∀ {Δ A B} {N : Tm (A ∷ Δ) B} {γ : Env Δ} {w v} → (w ∷ γ) ⊢ N ⇓ v
  → Stable (λ ck → call ck (pack (code N) (tup γ)) w) (ret v)
st-call ⟨ c , e ⟩ = ⟨ suc c , (λ { (suc ck) (s≤s le) → e ck le }) ⟩

{- The logical relation ----------------------------------------------------------}

𝕍 : ∀ {A} → Value → Val A → Set
𝕍s : ∀ {A} → List Value → Val A → Set
𝕍At : ∀ {n Δ} → Fin n → Value → All Val Δ → Set

𝕍 d (fold v) = 𝕍 d v
𝕍 (dconst k) (const k') = dconst k ≡ dconst k'
𝕍 (V ↦ w) (pack {B = B} (code N) (tup γ)) = ∀ v → 𝕍s V v → Σ[ v' ∈ Val B ] (v ∷ γ) ⊢ N ⇓ v' × 𝕍 w v'
𝕍 ν (pack c e) = ⊤
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

𝕍-δ : ∀ p n m → 𝕍 (dout (δᴾ p n m)) (δ p (const n) (const m))
𝕍-δ sub n m = refl
𝕍-δ eq n m with does (n ≟ℤ m)
... | true = tt
... | false = tt

{- the observation of a value related to a constant is that constant -}
𝕍-const : ∀ {A B} {k : base-rep B} (v : Val A) → 𝕍 (dconst k) v → obs v ≡ o-const B k
𝕍-const (fold v) r = 𝕍-const v r
𝕍-const (const k) refl = refl

{- Related environments ---------------------------------------------------------}

𝔾 : ∀ {Γ} → E.Env Value → Env Γ → Set
𝔾 {Γ} ρ γ = ∀ {A} (x : Γ ∋ A) d → d ∈ ρ (idx x) → 𝕍 d (lookup γ x)

𝔾-ext : ∀ {Γ A ρ} {γ : Env Γ} V (v : Val A) → 𝔾 ρ γ → 𝕍s V v → 𝔾 (mem V • ρ) (v ∷ γ)
𝔾-ext V v G Vv Z d d∈ = 𝕍s-∈ V Vv d∈
𝔾-ext V v G Vv (S x) = G x

{- one value related to all elements of V, all of which M produces -}
collect : ∀ {Γ A} (γ : Env Γ) (M : Tm Γ A) {v} (P : Value → Val A → Set) V
  → (∀ d → d ∈ mem V → Σ[ v' ∈ Val A ] γ ⊢ M ⇓ v' × P d v') → γ ⊢ M ⇓ v
  → ∀ d → d ∈ mem V → P d v
collect γ M P V all e d d∈ with all d d∈
... | ⟨ v' , ⟨ e' , r ⟩ ⟩ with ⇓-det γ M e e'
... | refl = r

Evals : ∀ {Γ Δ} → Env Γ → All (Tm Γ) Δ → All Val Δ → Set
Evals γ = All₂ (λ M v → γ ⊢ M ⇓ v)

evals-st : ∀ {Γ Δ} {γ : Env Γ} (Ms : All (Tm Γ) Δ) {vs} → Evals γ Ms vs → Stable (λ ck → evals ck γ Ms) (ret vs)
evals-st [] All₂.[] = now (λ _ → refl)
evals-st (M ∷ Ms) (e All₂.∷ es) = st-bind e (st-bind (evals-st Ms es) (now (λ _ → refl)))

{- The fundamental lemma ----------------------------------------------------------}

adequate : ∀ {Γ A} (M : Tm Γ A) {ρ} {γ : Env Γ} {d} → 𝔾 ρ γ → d ∈ ⟦ M ⟧ ρ
  → Σ[ v ∈ Val A ] γ ⊢ M ⇓ v × 𝕍 d v
adequate-args : ∀ {Γ Δ} (Ms : All (Tm Γ) Δ) {ρ} {γ : Env Γ} → 𝔾 ρ γ
  → (∀ j → nonempty (nthD (⟦ Ms ⟧s ρ) j))
  → Σ[ vs ∈ All Val Δ ] Evals γ Ms vs × (∀ j d → d ∈ nthD (⟦ Ms ⟧s ρ) j → 𝕍At j d vs)

adequate (` x) G d∈ = ⟨ _ , ⟨ now (λ _ → refl) , G x _ d∈ ⟩ ⟩
adequate (lam N) {γ = γ} {d = ν} G d∈ = ⟨ pack (code N) (tup γ) , ⟨ now (λ _ → refl) , tt ⟩ ⟩
adequate (lam N) {γ = γ} {d = V ↦ w} G ⟨ w∈ , _ ⟩ =
  ⟨ pack (code N) (tup γ) , ⟨ now (λ _ → refl) , (λ v Vv → adequate N (𝔾-ext V v G Vv) w∈) ⟩ ⟩
adequate (app L M) G ⟨ [] , ⟨ _ , ⟨ _ , ne ⟩ ⟩ ⟩ = ⊥-elim (ne refl)
adequate (app L M) {γ = γ} G ⟨ u ∷ U , ⟨ f∈ , ⟨ V⊆ , _ ⟩ ⟩ ⟩
    with adequate L G f∈ | adequate M G (V⊆ u (here refl))
... | ⟨ pack (code N) (tup γ') , ⟨ eL , rL ⟩ ⟩ | ⟨ vM , ⟨ eM , _ ⟩ ⟩
    with rL vM (all→𝕍s (u ∷ U) (collect γ M 𝕍 (u ∷ U) (λ d' d'∈ → adequate M G (V⊆ d' d'∈)) eM))
... | ⟨ v , ⟨ eN , r ⟩ ⟩ = ⟨ v , ⟨ st-bind eL (st-bind eM (st-call eN)) , r ⟩ ⟩
adequate (lit B c) {d = dconst k} G ⟨ refl , refl ⟩ = ⟨ const c , ⟨ now (λ _ → refl) , refl ⟩ ⟩
adequate (tuple []) {d = ⟨⟩} G tt = ⟨ tup [] , ⟨ now (λ _ → refl) , tt ⟩ ⟩
adequate (tuple (M ∷ Ms)) {d = tup[ i ] u} G ⟨ refl , ⟨ u∈ , ne ⟩ ⟩ with adequate-args (M ∷ Ms) G ne
... | ⟨ vs , ⟨ evs , rs ⟩ ⟩ = ⟨ tup vs , ⟨ st-bind (evals-st (M ∷ Ms) evs) (now (λ _ → refl)) , rs i u u∈ ⟩ ⟩
adequate (get i M) G d∈ with adequate M G d∈
... | ⟨ tup vs , ⟨ e , r ⟩ ⟩ = ⟨ lookup vs i , ⟨ st-bind e (now (λ _ → refl)) , 𝕍At-lookup i _ vs r ⟩ ⟩
adequate (inl M) {d = left u} G u∈ with adequate M G u∈
... | ⟨ v , ⟨ e , r ⟩ ⟩ = ⟨ inl v , ⟨ st-bind e (now (λ _ → refl)) , r ⟩ ⟩
adequate (inr M) {d = right u} G u∈ with adequate M G u∈
... | ⟨ v , ⟨ e , r ⟩ ⟩ = ⟨ inr v , ⟨ st-bind e (now (λ _ → refl)) , r ⟩ ⟩
adequate (case L M N) {γ = γ} G (inj₁ ⟨ u , ⟨ U , ⟨ allL , ⟨ w∈ , _ ⟩ ⟩ ⟩ ⟩) with adequate L G (allL u (here refl))
... | ⟨ inr a , ⟨ _ , () ⟩ ⟩
... | ⟨ inl a , ⟨ eL , _ ⟩ ⟩
    with adequate M (𝔾-ext (u ∷ U) a G (all→𝕍s (u ∷ U)
           (collect γ L (λ d v → 𝕍 (left d) v) (u ∷ U) (λ d d∈ → adequate L G (allL d d∈)) eL))) w∈
... | ⟨ v , ⟨ eM , r ⟩ ⟩ = ⟨ v , ⟨ st-bind eL eM , r ⟩ ⟩
adequate (case L M N) {γ = γ} G (inj₂ ⟨ u , ⟨ U , ⟨ allR , ⟨ w∈ , _ ⟩ ⟩ ⟩ ⟩) with adequate L G (allR u (here refl))
... | ⟨ inl a , ⟨ _ , () ⟩ ⟩
... | ⟨ inr a , ⟨ eL , _ ⟩ ⟩
    with adequate N (𝔾-ext (u ∷ U) a G (all→𝕍s (u ∷ U)
           (collect γ L (λ d v → 𝕍 (right d) v) (u ∷ U) (λ d d∈ → adequate L G (allR d d∈)) eL))) w∈
... | ⟨ v , ⟨ eN , r ⟩ ⟩ = ⟨ v , ⟨ st-bind eL eN , r ⟩ ⟩
adequate (prim p L M) G ⟨ n , ⟨ m , ⟨ n∈ , ⟨ m∈ , refl ⟩ ⟩ ⟩ ⟩
    with adequate L G n∈ | adequate M G m∈
... | ⟨ const _ , ⟨ eL , refl ⟩ ⟩ | ⟨ const _ , ⟨ eM , refl ⟩ ⟩ =
  ⟨ δ p (const n) (const m) , ⟨ st-bind eL (st-bind eM (now (λ _ → refl))) , 𝕍-δ p n m ⟩ ⟩
adequate (let′ M N) G ⟨ [] , ⟨ _ , ⟨ _ , ne ⟩ ⟩ ⟩ = ⊥-elim (ne refl)
adequate (let′ M N) {γ = γ} G ⟨ u ∷ U , ⟨ ⟨ w∈ , _ ⟩ , ⟨ V⊆ , _ ⟩ ⟩ ⟩
    with adequate M G (V⊆ u (here refl))
... | ⟨ a , ⟨ eM , _ ⟩ ⟩
    with adequate N (𝔾-ext (u ∷ U) a G (all→𝕍s (u ∷ U)
           (collect γ M 𝕍 (u ∷ U) (λ d d∈ → adequate M G (V⊆ d d∈)) eM))) w∈
... | ⟨ v , ⟨ eN , r ⟩ ⟩ = ⟨ v , ⟨ st-bind eM eN , r ⟩ ⟩
adequate (fold M) G d∈ with adequate M G d∈
... | ⟨ v , ⟨ e , r ⟩ ⟩ = ⟨ fold v , ⟨ st-bind e (now (λ _ → refl)) , r ⟩ ⟩
adequate (unfold M) G d∈ with adequate M G d∈
... | ⟨ fold v , ⟨ e , r ⟩ ⟩ = ⟨ v , ⟨ st-bind e (now (λ _ → refl)) , r ⟩ ⟩

adequate-args [] G ne = ⟨ [] , ⟨ All₂.[] , (λ ()) ⟩ ⟩
adequate-args (M ∷ Ms) {γ = γ} G ne with adequate M G (proj₂ (ne zero)) | adequate-args Ms G (λ j → ne (suc j))
... | ⟨ v , ⟨ e , _ ⟩ ⟩ | ⟨ vs , ⟨ evs , rs ⟩ ⟩ = ⟨ v ∷ vs , ⟨ e All₂.∷ evs , R ⟩ ⟩
  where
  R : ∀ j d → d ∈ nthD (⟦ M ∷ Ms ⟧s _) j → 𝕍At j d (v ∷ vs)
  R zero d d∈ = ⟨ refl , collect γ M 𝕍 (d ∷ []) (λ { d' (here refl) → adequate M G d∈ }) e d (here refl) ⟩
  R (suc j) d d∈ = rs j d d∈

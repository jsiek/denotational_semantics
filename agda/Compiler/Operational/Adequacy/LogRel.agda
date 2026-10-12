{-

  Adequacy of the graph model for the ISWIM machine: every element of the
  denotation of a closed program is witnessed by a run of the machine.

  A logical relation 𝕍 d v, by recursion on the denotational value d,
  relates d to machine values v: a constant to itself, a function entry
  V ↦ w to closures that, run on a value related to every element of V,
  return a value related to w; a tuple entry tup[ i ] d to tuples of the
  right size whose component i is related to d; and so on. Evaluation
  (γ ⊢ M ⇓ v) is "eval M γ κ runs to ret v κ, for every κ".

  The fundamental lemma (adequate) is by induction on M: if the
  environments are related on the variables that M uses (𝔾), then each
  d ∈ ⟦ M ⟧ ρ is related to the value of M. An application needs one
  argument value related to all of the (finitely many) elements of V; it
  is the unique value of the argument, since the machine is
  deterministic.

-}

module Compiler.Operational.Adequacy.LogRel where

open import Primitives using (Base; base-rep; Int)
open import SetsAsPredicates
open import Compiler.Model.Graph.Domain.ISWIM.Domain
  using (Value; _↦_; ν; ω; ⦅_,_⦆; tup[_]_; left; right; ⟨⟩)
  renaming (const to dconst)
open import Compiler.Model.Graph.Domain.ISWIM.Ops using (nthD) renaming (out to dout)
open import Compiler.Lang.Prim using (int; bool; δ)
open import Compiler.Lang.ISWIM
open import Compiler.Lang.Uses Op sig
open import Compiler.Model.Graph.Sem.ISWIM using (⟦_⟧; ⟦_⟧₊)
import NewEnv
open import NewSyntaxUtil using (_,,_; Nil; ⟩_,,_)
open import Compiler.Lang.ListUtil
open import Compiler.Operational.Machine.ISWIM
open import Compiler.Operational.Smallstep using (next; stop)
open import Compiler.Operational.Adequacy.Common

open import Data.Bool using (true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_; length; replicate; reverse)
open import Data.List.Base using (reverseAcc)
open import Data.List.Properties using (reverse-involutive)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; Σ-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)

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
𝕍s : List Value → Val → Set
𝕍At : ∀ {n} → Fin n → Value → List Val → Set

𝕍 (dconst {B} k) v = v ≡ const B k
𝕍 (V ↦ w) (clo N γ) = ∀ v → 𝕍s V v → Σ[ v' ∈ Val ] (v ∷ γ) ⊢ N ⇓ v' × 𝕍 w v'
𝕍 ν (clo N γ) = ⊤
𝕍 ⟨⟩ (tup vs) = vs ≡ []
𝕍 (tup[ i ] d) (tup vs) = 𝕍At i d vs
𝕍 (left d) (inl v) = 𝕍 d v
𝕍 (right d) (inr v) = 𝕍 d v
𝕍 _ _ = ⊥

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
𝕍-shape (V ↦ w) (clo N γ) r = tt
𝕍-shape ν (clo N γ) r = tt
𝕍-shape ⟨⟩ (tup []) refl = refl
𝕍-shape (tup[ i ] d) (tup vs) r = 𝕍At-shape i d vs r
𝕍-shape (left d) (inl v) r = 𝕍-shape d v r
𝕍-shape (right d) (inr v) r = 𝕍-shape d v r
𝕍At-shape {suc n} zero d (v ∷ vs) ⟨ len , r ⟩ = ⟨ trans (length-obs-list vs) len , 𝕍-shape d v r ⟩
𝕍At-shape (suc i) d (v ∷ vs) r = 𝕍At-shape i d vs r

{- Related environments, on the variables a term uses ---------------------------}

𝔾 : (Var → Set) → VEnv → Env → Set
𝔾 P ρ γ = ∀ x → P x → ∀ d → d ∈ ρ x → Σ[ v ∈ Val ] γ ‼ x ≡ just v × 𝕍 d v

𝔾-ext : ∀ {P ρ γ} V v → 𝔾 (λ x → P (suc x)) ρ γ → 𝕍s V v → 𝔾 P (mem V • ρ) (v ∷ γ)
𝔾-ext V v G Vv zero _ d d∈ = ⟨ v , ⟨ refl , 𝕍s-∈ V Vv d∈ ⟩ ⟩
𝔾-ext V v G Vv (suc x) u d d∈ = G x u d d∈

{- Lemmas about runs -------------------------------------------------------------}

{- one value related to all elements of V, all of which M produces -}
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

UsesP : AST → Var → Set
UsesP M x = Uses x M

adequate : ∀ M {ρ γ d} → 𝔾 (UsesP M) ρ γ → d ∈ ⟦ M ⟧ ρ
  → Σ[ v ∈ Val ] γ ⊢ M ⇓ v × 𝕍 d v
adequate-args : ∀ {n} (args : Args (replicate n ■)) {ρ γ}
  → 𝔾 (λ x → UsesArgs x args) ρ γ → (∀ j → nonempty (nthD (⟦ args ⟧₊ ρ) j))
  → Σ[ vs ∈ List Val ] Evals γ (args→list args) vs × length vs ≡ n
      × (∀ j d → d ∈ nthD (⟦ args ⟧₊ ρ) j → 𝕍At j d vs)

adequate (` x) {γ = γ} G d∈ with G x refl _ d∈
... | ⟨ v , ⟨ look , r ⟩ ⟩ = ⟨ v , ⟨ (λ κ → cong (λ m → ret? m κ) look ∷↠ done) , r ⟩ ⟩

adequate (lam ⦅ ⟩ N ,, Nil ⦆) {γ = γ} {d = ν} G d∈ = ⟨ clo N γ , ⟨ (λ κ → refl ∷↠ done) , tt ⟩ ⟩
adequate (lam ⦅ ⟩ N ,, Nil ⦆) {γ = γ} {d = V ↦ w} G ⟨ w∈ , _ ⟩ =
  ⟨ clo N γ , ⟨ (λ κ → refl ∷↠ done)
  , (λ v Vv → adequate N (𝔾-ext V v (λ x u → G x (inj₁ u)) Vv) w∈) ⟩ ⟩
adequate (lam ⦅ ⟩ N ,, Nil ⦆) {d = dconst k} G ()
adequate (lam ⦅ ⟩ N ,, Nil ⦆) {d = ω} G ()
adequate (lam ⦅ ⟩ N ,, Nil ⦆) {d = ⦅ u , v ⦆} G ()
adequate (lam ⦅ ⟩ N ,, Nil ⦆) {d = tup[ i ] d} G ()
adequate (lam ⦅ ⟩ N ,, Nil ⦆) {d = left d} G ()
adequate (lam ⦅ ⟩ N ,, Nil ⦆) {d = right d} G ()
adequate (lam ⦅ ⟩ N ,, Nil ⦆) {d = ⟨⟩} G ()

adequate (app ⦅ L ,, M ,, Nil ⦆) G ⟨ [] , ⟨ _ , ⟨ _ , ne ⟩ ⟩ ⟩ = ⊥-elim (ne refl)
adequate (app ⦅ L ,, M ,, Nil ⦆) {ρ} {γ} {d} G ⟨ u ∷ U , ⟨ f∈ , ⟨ V⊆ , _ ⟩ ⟩ ⟩
    with adequate L (λ x p → G x (inj₁ p)) f∈
       | adequate M GM (V⊆ u (here refl))
  where GM = λ x p → G x (inj₂ (inj₁ p))
... | ⟨ clo N γ' , ⟨ eL , rL ⟩ ⟩ | ⟨ vM , ⟨ eM , _ ⟩ ⟩
    with rL vM (all→𝕍s (u ∷ U)
                  (collect 𝕍 (u ∷ U) (λ d' d'∈ → adequate M (λ x p → G x (inj₂ (inj₁ p))) (V⊆ d' d'∈)) eM))
... | ⟨ v , ⟨ eN , r ⟩ ⟩ =
  ⟨ v , ⟨ (λ κ → refl ∷↠ eL (appL M γ κ) ++↠ refl ∷↠ eM (appR (clo N γ') κ) ++↠ refl ∷↠ eN κ) , r ⟩ ⟩

adequate (lit B k ⦅ Nil ⦆) {d = dconst k'} G ⟨ refl , refl ⟩ =
  ⟨ const B k , ⟨ (λ κ → refl ∷↠ done) , refl ⟩ ⟩
adequate (lit B k ⦅ Nil ⦆) {d = V ↦ w} G ()
adequate (lit B k ⦅ Nil ⦆) {d = ν} G ()
adequate (lit B k ⦅ Nil ⦆) {d = ω} G ()
adequate (lit B k ⦅ Nil ⦆) {d = ⦅ u , v ⦆} G ()
adequate (lit B k ⦅ Nil ⦆) {d = tup[ i ] d} G ()
adequate (lit B k ⦅ Nil ⦆) {d = left d} G ()
adequate (lit B k ⦅ Nil ⦆) {d = right d} G ()
adequate (lit B k ⦅ Nil ⦆) {d = ⟨⟩} G ()

adequate (tuple zero ⦅ Nil ⦆) {d = ⟨⟩} G tt = ⟨ tup [] , ⟨ (λ κ → refl ∷↠ done) , refl ⟩ ⟩
adequate (tuple (suc n) ⦅ args ⦆) {ρ} {γ} {d = tup[ i ] d} G ⟨ refl , ⟨ d∈ , ne ⟩ ⟩
    with adequate-args args G ne
... | ⟨ vs , ⟨ es , ⟨ len , rs ⟩ ⟩ ⟩ =
  ⟨ tup vs
  , ⟨ (λ κ → refl ∷↠ subst (λ ws → tuple-next [] (args→list args) γ κ ↠ ret (tup ws) κ)
                            (reverse-involutive vs) (tuple-run [] (args→list args) vs es))
    , rs i d d∈ ⟩ ⟩
adequate (tuple zero ⦅ Nil ⦆) {d = tup[ i ] d} G ()
adequate (tuple zero ⦅ Nil ⦆) {d = dconst k} G ()
adequate (tuple (suc n) ⦅ args ⦆) {d = dconst k} G ()
adequate (tuple zero ⦅ Nil ⦆) {d = V ↦ w} G ()
adequate (tuple (suc n) ⦅ args ⦆) {d = V ↦ w} G ()
adequate (tuple zero ⦅ Nil ⦆) {d = ν} G ()
adequate (tuple (suc n) ⦅ args ⦆) {d = ν} G ()
adequate (tuple zero ⦅ Nil ⦆) {d = ω} G ()
adequate (tuple (suc n) ⦅ args ⦆) {d = ω} G ()
adequate (tuple zero ⦅ Nil ⦆) {d = ⦅ u , v ⦆} G ()
adequate (tuple (suc n) ⦅ args ⦆) {d = ⦅ u , v ⦆} G ()
adequate (tuple zero ⦅ Nil ⦆) {d = left d} G ()
adequate (tuple (suc n) ⦅ args ⦆) {d = left d} G ()
adequate (tuple zero ⦅ Nil ⦆) {d = right d} G ()
adequate (tuple (suc n) ⦅ args ⦆) {d = right d} G ()
adequate (tuple (suc n) ⦅ args ⦆) {d = ⟨⟩} G ()

adequate (get i ⦅ M ,, Nil ⦆) {γ = γ} G d∈ with adequate M (λ x p → G x (inj₁ p)) d∈
... | ⟨ tup vs , ⟨ e , r ⟩ ⟩ with 𝕍At-proj i _ vs r
... | ⟨ v , ⟨ p , r' ⟩ ⟩ =
  ⟨ v , ⟨ (λ κ → refl ∷↠ e (getK i κ) ++↠ cong (λ m → ret? m κ) p ∷↠ done) , r' ⟩ ⟩

adequate (inl-op ⦅ M ,, Nil ⦆) {γ = γ} {d = left d} G d∈ with adequate M (λ x p → G x (inj₁ p)) d∈
... | ⟨ v , ⟨ e , r ⟩ ⟩ = ⟨ inl v , ⟨ (λ κ → refl ∷↠ e (inlK κ) ++↠ refl ∷↠ done) , r ⟩ ⟩
adequate (inl-op ⦅ M ,, Nil ⦆) {d = dconst k} G ()
adequate (inl-op ⦅ M ,, Nil ⦆) {d = V ↦ w} G ()
adequate (inl-op ⦅ M ,, Nil ⦆) {d = ν} G ()
adequate (inl-op ⦅ M ,, Nil ⦆) {d = ω} G ()
adequate (inl-op ⦅ M ,, Nil ⦆) {d = ⦅ u , v ⦆} G ()
adequate (inl-op ⦅ M ,, Nil ⦆) {d = tup[ i ] d} G ()
adequate (inl-op ⦅ M ,, Nil ⦆) {d = right d} G ()
adequate (inl-op ⦅ M ,, Nil ⦆) {d = ⟨⟩} G ()

adequate (inr-op ⦅ M ,, Nil ⦆) {γ = γ} {d = right d} G d∈ with adequate M (λ x p → G x (inj₁ p)) d∈
... | ⟨ v , ⟨ e , r ⟩ ⟩ = ⟨ inr v , ⟨ (λ κ → refl ∷↠ e (inrK κ) ++↠ refl ∷↠ done) , r ⟩ ⟩
adequate (inr-op ⦅ M ,, Nil ⦆) {d = dconst k} G ()
adequate (inr-op ⦅ M ,, Nil ⦆) {d = V ↦ w} G ()
adequate (inr-op ⦅ M ,, Nil ⦆) {d = ν} G ()
adequate (inr-op ⦅ M ,, Nil ⦆) {d = ω} G ()
adequate (inr-op ⦅ M ,, Nil ⦆) {d = ⦅ u , v ⦆} G ()
adequate (inr-op ⦅ M ,, Nil ⦆) {d = tup[ i ] d} G ()
adequate (inr-op ⦅ M ,, Nil ⦆) {d = left d} G ()
adequate (inr-op ⦅ M ,, Nil ⦆) {d = ⟨⟩} G ()

adequate (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) {ρ} {γ} G (inj₁ ⟨ u , ⟨ U , ⟨ allL , ⟨ w∈ , _ ⟩ ⟩ ⟩ ⟩)
    with adequate L GL (allL u (here refl))
  where GL = λ x p → G x (inj₁ p)
... | ⟨ inl w , ⟨ eL , _ ⟩ ⟩
    with adequate M (𝔾-ext (u ∷ U) w (λ x p → G x (inj₂ (inj₁ p)))
           (all→𝕍s (u ∷ U) (collect (λ d v → 𝕍 (left d) v) (u ∷ U)
              (λ d d∈ → adequate L (λ x p → G x (inj₁ p)) (allL d d∈)) eL))) w∈
... | ⟨ v , ⟨ eM , r ⟩ ⟩ =
  ⟨ v , ⟨ (λ κ → refl ∷↠ eL (caseK M N γ κ) ++↠ refl ∷↠ eM κ) , r ⟩ ⟩
adequate (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) {ρ} {γ} G (inj₂ ⟨ u , ⟨ U , ⟨ allR , ⟨ w∈ , _ ⟩ ⟩ ⟩ ⟩)
    with adequate L GL (allR u (here refl))
  where GL = λ x p → G x (inj₁ p)
... | ⟨ inr w , ⟨ eL , _ ⟩ ⟩
    with adequate N (𝔾-ext (u ∷ U) w (λ x p → G x (inj₂ (inj₂ (inj₁ p))))
           (all→𝕍s (u ∷ U) (collect (λ d v → 𝕍 (right d) v) (u ∷ U)
              (λ d d∈ → adequate L (λ x p → G x (inj₁ p)) (allR d d∈)) eL))) w∈
... | ⟨ v , ⟨ eN , r ⟩ ⟩ =
  ⟨ v , ⟨ (λ κ → refl ∷↠ eL (caseK M N γ κ) ++↠ refl ∷↠ eN κ) , r ⟩ ⟩

adequate (prim p ⦅ L ,, M ,, Nil ⦆) {γ = γ} G ⟨ n , ⟨ m , ⟨ n∈ , ⟨ m∈ , refl ⟩ ⟩ ⟩ ⟩
    with adequate L (λ x q → G x (inj₁ q)) n∈ | adequate M (λ x q → G x (inj₂ (inj₁ q))) m∈
... | ⟨ _ , ⟨ eL , refl ⟩ ⟩ | ⟨ _ , ⟨ eM , refl ⟩ ⟩ =
  ⟨ out (δ p n m)
  , ⟨ (λ κ → refl ∷↠ eL (primL p M γ κ) ++↠ refl ∷↠ eM (primR p (const Int n) κ) ++↠ refl ∷↠ done)
    , 𝕍-out (δ p n m) ⟩ ⟩

adequate-args {zero} Nil G ne = ⟨ [] , ⟨ [] , ⟨ refl , (λ ()) ⟩ ⟩ ⟩
adequate-args {suc n} (M ,, args) G ne
    with adequate M (λ x p → G x (inj₁ p)) (proj₂ (ne zero))
       | adequate-args args (λ x p → G x (inj₂ p)) (λ j → ne (suc j))
... | ⟨ v , ⟨ e , _ ⟩ ⟩ | ⟨ vs , ⟨ es , ⟨ len , rs ⟩ ⟩ ⟩ =
  ⟨ v ∷ vs , ⟨ e ∷ es , ⟨ cong suc len , R ⟩ ⟩ ⟩
  where
  R : ∀ j d → d ∈ nthD (⟦ M ,, args ⟧₊ _) j → 𝕍At j d (v ∷ vs)
  R zero d d∈ = ⟨ len , collect 𝕍 (d ∷ []) (λ { d' (here refl) → adequate M (λ x p → G x (inj₁ p)) d∈ }) e d (here refl) ⟩
  R (suc j) d d∈ = rs j d d∈

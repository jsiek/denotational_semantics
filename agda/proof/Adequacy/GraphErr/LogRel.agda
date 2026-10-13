{-

  Adequacy of the graph model with errors for the ISWIM machine: every
  element of the denotation of a closed program is witnessed by a run of
  the machine, and ω by a run that stops with an error.

  As in proof/Adequacy/LogRel.agda, a logical relation 𝕍 d v relates
  denotational values to machine values, by recursion on d; what is new
  is the relation of a denotational value to a term (ℝ d γ M): ω is
  related to a term that stops with an error (γ ⊢ M ⇓err), and any other
  value to a term that evaluates to a related value. A function entry
  V ↦ w relates to closures whose body, on a value related to V, is
  related to w, so it may stop with an error. The fundamental lemma
  (adequate) has a case for each error of each operator, following the
  machine's evaluation order: e.g. an application is an error when its
  operator is, when its operator is a value that is not a function (its
  argument is never run), or when its operator is a function and its
  argument is an error.

  A term cannot both stop with an error and evaluate to a value (⇓-⇓err),
  as the machine is deterministic; so an element of a successful tuple,
  application or case is never ω (collectℝ).

-}

module proof.Adequacy.GraphErr.LogRel where

open import Framework.Primitives using (Base; base-rep; Int; Nat; 𝔹; Unit; Void; Blame)
open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.Domain
  using (Value; _↦_; ν; ω; ⦅_,_⦆; tup[_]_; left; right; ⟨⟩)
  renaming (const to dconst)
open import proof.Framework.GraphModel.OpsBase using (nthD)
open import proof.Framework.GraphModel.ErrorOps
  using (val∈; wrong; errs; vals; IsFun; IsInj; IsTup; NoErr; inlᵉ-inv; inrᵉ-inv; Λᵉ-fun)
open import proof.Semantics.GraphErr.Prim using (IsInt) renaming (out to dout)
open import Language.Prim using (int; bool; δ)
open import Language.ISWIM
open import proof.Framework.Syntax.Uses Op sig
open import proof.Semantics.GraphErr.ISWIM using (⟦_⟧; ⟦_⟧₊)
import proof.Framework.GraphModel.Env
open import Framework.Syntax.SyntaxUtil using (_,,_; Nil; ⟩_,,_)
open import proof.Framework.ListUtil
open import Semantics.Observation
open import Semantics.CEK.ISWIM
open import proof.Semantics.CEK.Smallstep using (next; stop)
open import proof.Adequacy.Common

open import Data.Bool using (true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin; zero; suc)
open import Data.Integer using (ℤ)
open import Data.List using (List; []; _∷_; length; replicate; reverse)
open import Data.List.Base using (reverseAcc)
open import Data.List.Properties using (reverse-involutive)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing; map)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; Σ-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (¬_)

VEnv : Set₁
VEnv = proof.Framework.GraphModel.Env.Env Value

{- Evaluation, and errors ---------------------------------------------------------}

infix 4 _⊢_⇓_
_⊢_⇓_ : Env → AST → Val → Set
γ ⊢ M ⇓ v = ∀ κ → eval M γ κ ↠ ret v κ

{- a run from s to a state that stops with an error -}
Err : State → Set
Err s = Σ[ t ∈ State ] s ↠ t × step t ≡ stop o-error

infix 4 _⊢_⇓err
_⊢_⇓err : Env → AST → Set
γ ⊢ M ⇓err = ∀ κ → Err (eval M γ κ)

{- an error after a run -}
_⟫_ : ∀ {s s'} → s ↠ s' → Err s' → Err s
σ ⟫ ⟨ t , ⟨ τ , st ⟩ ⟩ = ⟨ t , ⟨ σ ++↠ τ , st ⟩ ⟩
infixr 4 _⟫_

{- a state that stops with an error right away -}
here! : ∀ {s} → step s ≡ stop o-error → Err s
here! {s} st = ⟨ s , ⟨ done , st ⟩ ⟩

⇓-det : ∀ {γ M v₁ v₂} → γ ⊢ M ⇓ v₁ → γ ⊢ M ⇓ v₂ → v₁ ≡ v₂
⇓-det {v₁ = v₁} {v₂} e₁ e₂ with ↠-final-det (e₁ halt) (e₂ halt) refl refl
... | refl = refl

obs-ok : ∀ v → stop {S = State} (obs v) ≡ stop o-error → ⊥
obs-ok (clo N γ) ()
obs-ok (const B k) ()
obs-ok (tup vs) ()
obs-ok (inl v) ()
obs-ok (inr v) ()

{- a term does not both evaluate to a value and stop with an error -}
⇓-⇓err : ∀ {γ M v} → γ ⊢ M ⇓ v → γ ⊢ M ⇓err → ⊥
⇓-⇓err {v = v} e err with err halt
... | ⟨ t , ⟨ τ , st ⟩ ⟩ with ↠-final-det (e halt) τ refl st
... | refl = obs-ok v st

{- The logical relation ----------------------------------------------------------}

𝕍 : Value → Val → Set
𝕍s : List Value → Val → Set
𝕍At : ∀ {n} → Fin n → Value → List Val → Set
ℝ : Value → Env → AST → Set

𝕍 (dconst {B} k) v = v ≡ const B k
𝕍 (V ↦ w) (clo N γ) = ∀ v → 𝕍s V v → ℝ w (v ∷ γ) N
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

{- ω means an error, any other value a related value -}
ℝ d γ M = (d ≡ ω × γ ⊢ M ⇓err) ⊎ (Σ[ v ∈ Val ] γ ⊢ M ⇓ v × 𝕍 d v)

𝕍-ω : ∀ {v} → 𝕍 ω v → ⊥
𝕍-ω {clo N γ} ()
𝕍-ω {const B k} ()
𝕍-ω {tup vs} ()
𝕍-ω {inl v} ()
𝕍-ω {inr v} ()

{- a value other than ω evaluates -}
conv : ∀ {d γ M} → ℝ d γ M → d ≢ ω → Σ[ v ∈ Val ] γ ⊢ M ⇓ v × 𝕍 d v
conv (inj₁ ⟨ refl , _ ⟩) d≢ = ⊥-elim (d≢ refl)
conv (inj₂ r) d≢ = r

{- ω is an error -}
err : ∀ {γ M} → ℝ ω γ M → γ ⊢ M ⇓err
err (inj₁ ⟨ _ , e ⟩) = e
err (inj₂ ⟨ v , ⟨ _ , r ⟩ ⟩) = ⊥-elim (𝕍-ω {v} r)

{- the value of a term that evaluates is related to every element -}
collectℝ : ∀ {γ M v d} → γ ⊢ M ⇓ v → ℝ d γ M → 𝕍 d v
collectℝ e (inj₁ ⟨ _ , er ⟩) = ⊥-elim (⇓-⇓err e er)
collectℝ e (inj₂ ⟨ v' , ⟨ e' , r ⟩ ⟩) with ⇓-det e e'
... | refl = r

𝕍s-∈ : ∀ V {v d} → 𝕍s V v → d ∈ mem V → 𝕍 d v
𝕍s-∈ (d ∷ V) ⟨ r , _ ⟩ (here refl) = r
𝕍s-∈ (d ∷ V) ⟨ _ , rs ⟩ (there d∈) = 𝕍s-∈ V rs d∈

all→𝕍s : ∀ V {v} → (∀ d → d ∈ mem V → 𝕍 d v) → 𝕍s V v
all→𝕍s [] all = tt
all→𝕍s (d ∷ V) all = ⟨ all d (here refl) , all→𝕍s V (λ d' d'∈ → all d' (there d'∈)) ⟩

𝕍At-proj : ∀ {n} (i : Fin n) d vs → 𝕍At i d vs → Σ[ v ∈ Val ] proj i vs ≡ just v × 𝕍 d v
𝕍At-proj {suc n} zero d (v ∷ vs) ⟨ len , r ⟩ rewrite length→has-length n vs len = ⟨ v , ⟨ refl , r ⟩ ⟩
𝕍At-proj (suc i) d (v ∷ vs) r = 𝕍At-proj i d vs r

𝕍At-length : ∀ {n} (i : Fin n) d vs → 𝕍At i d vs → length vs ≡ n
𝕍At-length {suc n} zero d (v ∷ vs) ⟨ len , _ ⟩ = cong suc len
𝕍At-length (suc i) d (v ∷ vs) r = cong suc (𝕍At-length i d vs r)

proj-just-length : ∀ {n} (i : Fin n) (vs : List Val) {v} → proj i vs ≡ just v → length vs ≡ n
proj-just-length {suc n} zero (v ∷ vs) eq with has-length n vs in h
proj-just-length {suc n} zero (v ∷ vs) refl | true = cong suc (has-length→length n vs h)
proj-just-length {suc n} zero (v ∷ vs) () | false
proj-just-length (suc i) (v ∷ vs) eq = cong suc (proj-just-length i vs eq)

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

{- The machine's checks fail on related values of the wrong kind ----------------}

{- a value related to a function is a closure -}
fun-clo : ∀ f v → 𝕍 f v → IsFun f → Σ[ N ∈ AST ] Σ[ γ ∈ Env ] v ≡ clo N γ
fun-clo (V ↦ w) (clo N γ) _ _ = ⟨ N , ⟨ γ , refl ⟩ ⟩
fun-clo ν (clo N γ) _ _ = ⟨ N , ⟨ γ , refl ⟩ ⟩

{- applying a value related to a non-function is an error -}
notfun-stop : ∀ d v → 𝕍 d v → ¬ IsFun d → ∀ M γ κ → step (ret v (appL M γ κ)) ≡ stop o-error
notfun-stop (V ↦ w) (clo N γ') r nf M γ κ = ⊥-elim (nf tt)
notfun-stop ν (clo N γ') r nf M γ κ = ⊥-elim (nf tt)
notfun-stop d (const B k) r nf M γ κ = refl
notfun-stop d (tup vs) r nf M γ κ = refl
notfun-stop d (inl v) r nf M γ κ = refl
notfun-stop d (inr v) r nf M γ κ = refl

{- a projection from a value related to a non-tuple of n components is an
   error -}
proj-nothing-[] : ∀ {n} (i : Fin n) → proj {A = Val} i [] ≡ nothing
proj-nothing-[] zero = refl
proj-nothing-[] (suc i) = refl

nottup-stop : ∀ {n} (i : Fin n) d v → 𝕍 d v → ¬ IsTup n d → ∀ κ → step (ret v (getK i κ)) ≡ stop o-error
nottup-stop i ⟨⟩ (tup []) refl nt κ = cong (λ m → ret? m κ) (proj-nothing-[] i)
nottup-stop {n} i (tup[_]_ {m} j d) (tup vs) r nt κ with proj i vs in p
... | just v = ⊥-elim (nt (trans (sym (𝕍At-length j d vs r)) (proj-just-length i vs p)))
... | nothing = refl
nottup-stop i d (clo N γ) r nt κ = refl
nottup-stop i d (const B k) r nt κ = refl
nottup-stop i d (inl v) r nt κ = refl
nottup-stop i d (inr v) r nt κ = refl

{- a case on a value related to a non-injection is an error -}
notinj-stop : ∀ d v → 𝕍 d v → ¬ IsInj d → ∀ M N γ κ → step (ret v (caseK M N γ κ)) ≡ stop o-error
notinj-stop (left d) (inl v) r ni M N γ κ = ⊥-elim (ni tt)
notinj-stop (right d) (inr v) r ni M N γ κ = ⊥-elim (ni tt)
notinj-stop d (clo N' γ') r ni M N γ κ = refl
notinj-stop d (const B k) r ni M N γ κ = refl
notinj-stop d (tup vs) r ni M N γ κ = refl

{- a value related to a non-integer is not observed as an integer -}
notint-obs : ∀ d v → 𝕍 d v → ¬ IsInt d → ∀ n → obs v ≢ o-const Int n
notint-obs (dconst k) (const B k) refl ni n refl = ni tt
notint-obs d (clo N γ) r ni n ()
notint-obs d (tup vs) r ni n ()
notint-obs d (inl v) r ni n ()
notint-obs d (inr v) r ni n ()

δ?-nothing₁ : ∀ p o₁ o₂ → (∀ n → o₁ ≢ o-const Int n) → δ? p o₁ o₂ ≡ nothing
δ?-nothing₁ p (o-const Int n) o₂ f = ⊥-elim (f n refl)
δ?-nothing₁ p (o-const Nat k) o₂ f = refl
δ?-nothing₁ p (o-const 𝔹 k) o₂ f = refl
δ?-nothing₁ p (o-const Unit k) o₂ f = refl
δ?-nothing₁ p (o-const Void k) o₂ f = refl
δ?-nothing₁ p (o-const Blame k) o₂ f = refl
δ?-nothing₁ p o-fun o₂ f = refl
δ?-nothing₁ p (o-tuple os) o₂ f = refl
δ?-nothing₁ p (o-inl o) o₂ f = refl
δ?-nothing₁ p (o-inr o) o₂ f = refl
δ?-nothing₁ p o-error o₂ f = refl

δ?-nothing₂ : ∀ p o₁ o₂ → (∀ m → o₂ ≢ o-const Int m) → δ? p o₁ o₂ ≡ nothing
δ?-nothing₂ p (o-const Int n) (o-const Int m) f = ⊥-elim (f m refl)
δ?-nothing₂ p (o-const Int n) (o-const Nat k) f = refl
δ?-nothing₂ p (o-const Int n) (o-const 𝔹 k) f = refl
δ?-nothing₂ p (o-const Int n) (o-const Unit k) f = refl
δ?-nothing₂ p (o-const Int n) (o-const Void k) f = refl
δ?-nothing₂ p (o-const Int n) (o-const Blame k) f = refl
δ?-nothing₂ p (o-const Int n) o-fun f = refl
δ?-nothing₂ p (o-const Int n) (o-tuple os) f = refl
δ?-nothing₂ p (o-const Int n) (o-inl o) f = refl
δ?-nothing₂ p (o-const Int n) (o-inr o) f = refl
δ?-nothing₂ p (o-const Int n) o-error f = refl
δ?-nothing₂ p (o-const Nat k) o₂ f = refl
δ?-nothing₂ p (o-const 𝔹 k) o₂ f = refl
δ?-nothing₂ p (o-const Unit k) o₂ f = refl
δ?-nothing₂ p (o-const Void k) o₂ f = refl
δ?-nothing₂ p (o-const Blame k) o₂ f = refl
δ?-nothing₂ p o-fun o₂ f = refl
δ?-nothing₂ p (o-tuple os) o₂ f = refl
δ?-nothing₂ p (o-inl o) o₂ f = refl
δ?-nothing₂ p (o-inr o) o₂ f = refl
δ?-nothing₂ p o-error o₂ f = refl

{- Related environments, on the variables a term uses ---------------------------}

𝔾 : (Var → Set) → VEnv → Env → Set
𝔾 P ρ γ = ∀ x → P x → ∀ d → d ∈ ρ x → Σ[ v ∈ Val ] γ ‼ x ≡ just v × 𝕍 d v

𝔾-ext : ∀ {P ρ γ} V v → 𝔾 (λ x → P (suc x)) ρ γ → 𝕍s V v → 𝔾 P (mem V • ρ) (v ∷ γ)
𝔾-ext V v G Vv zero _ d d∈ = ⟨ v , ⟨ refl , 𝕍s-∈ V Vv d∈ ⟩ ⟩
𝔾-ext V v G Vv (suc x) u d d∈ = G x u d d∈

Evals : Env → List AST → List Val → Set
Evals γ = Pointwise (λ M v → γ ⊢ M ⇓ v)

tuple-run : ∀ {γ κ} acc Ms vs → Evals γ Ms vs
  → tuple-next acc Ms γ κ ↠ ret (tup (reverse (reverseAcc acc vs))) κ
tuple-run acc [] [] [] = done
tuple-run {γ} {κ} acc (M ∷ Ms) (v ∷ vs) (e ∷ es) =
  e (tupK acc Ms γ κ) ++↠ (refl ∷↠ tuple-run (v ∷ acc) Ms vs es)

{- the head of a list without ω is not ω -}
head≢ω : ∀ {u U} → NoErr (u ∷ U) → u ≢ ω
head≢ω {u} {U} noe e = noe (subst (λ z → z ∈ mem (u ∷ U)) e (here refl))

{- The fundamental lemma ----------------------------------------------------------}

UsesP : AST → Var → Set
UsesP M x = Uses x M

adequate : ∀ M {ρ γ d} → 𝔾 (UsesP M) ρ γ → d ∈ ⟦ M ⟧ ρ → ℝ d γ M
adequate-args : ∀ {n} (args : Args (replicate n ■)) {ρ γ}
  → 𝔾 (λ x → UsesArgs x args) ρ γ → vals n (⟦ args ⟧₊ ρ)
  → Σ[ vs ∈ List Val ] Evals γ (args→list args) vs × length vs ≡ n
      × (∀ j d → d ∈ nthD (⟦ args ⟧₊ ρ) j → 𝕍At j d vs)
tuple-err : ∀ {n} (args : Args (replicate n ■)) {ρ γ}
  → 𝔾 (λ x → UsesArgs x args) ρ γ → errs n (⟦ args ⟧₊ ρ)
  → ∀ acc κ → Err (tuple-next acc (args→list args) γ κ)

adequate (` x) {γ = γ} G d∈ with G x refl _ d∈
... | ⟨ v , ⟨ look , r ⟩ ⟩ = inj₂ ⟨ v , ⟨ (λ κ → cong (λ m → ret? m κ) look ∷↠ done) , r ⟩ ⟩

adequate (lam ⦅ ⟩ N ,, Nil ⦆) {γ = γ} {d = ν} G d∈ = inj₂ ⟨ clo N γ , ⟨ (λ κ → refl ∷↠ done) , tt ⟩ ⟩
adequate (lam ⦅ ⟩ N ,, Nil ⦆) {γ = γ} {d = V ↦ w} G ⟨ w∈ , _ ⟩ =
  inj₂ ⟨ clo N γ , ⟨ (λ κ → refl ∷↠ done)
       , (λ v Vv → adequate N (𝔾-ext V v (λ x u → G x (inj₁ u)) Vv) w∈) ⟩ ⟩

adequate (app ⦅ L ,, M ,, Nil ⦆) G (inj₁ ⟨ [] , ⟨ _ , ⟨ _ , ⟨ ne , _ ⟩ ⟩ ⟩ ⟩) = ⊥-elim (ne refl)
adequate (app ⦅ L ,, M ,, Nil ⦆) {ρ} {γ} {d} G (inj₁ ⟨ u ∷ U , ⟨ f∈ , ⟨ V⊆ , ⟨ _ , noe ⟩ ⟩ ⟩ ⟩)
    with conv (adequate L (λ x p → G x (inj₁ p)) f∈) (λ ())
... | ⟨ clo N γ' , ⟨ eL , rL ⟩ ⟩
    with conv (adequate M (λ x p → G x (inj₂ (inj₁ p))) (V⊆ u (here refl))) (head≢ω noe)
... | ⟨ vM , ⟨ eM , _ ⟩ ⟩
    with rL vM (all→𝕍s (u ∷ U) (λ d' d'∈ → collectℝ eM (adequate M (λ x p → G x (inj₂ (inj₁ p))) (V⊆ d' d'∈))))
... | inj₁ ⟨ refl , eN ⟩ =
  inj₁ ⟨ refl , (λ κ → (refl ∷↠ eL (appL M γ κ) ++↠ refl ∷↠ eM (appR (clo N γ') κ) ++↠ refl ∷↠ done) ⟫ eN κ) ⟩
... | inj₂ ⟨ v , ⟨ eN , r ⟩ ⟩ =
  inj₂ ⟨ v , ⟨ (λ κ → refl ∷↠ eL (appL M γ κ) ++↠ refl ∷↠ eM (appR (clo N γ') κ) ++↠ refl ∷↠ eN κ) , r ⟩ ⟩
adequate (app ⦅ L ,, M ,, Nil ⦆) {γ = γ} G (inj₂ ⟨ refl , inj₁ ω∈ ⟩) =
  inj₁ ⟨ refl , (λ κ → (refl ∷↠ done) ⟫ err (adequate L (λ x p → G x (inj₁ p)) ω∈) (appL M γ κ)) ⟩
adequate (app ⦅ L ,, M ,, Nil ⦆) {γ = γ} G (inj₂ ⟨ refl , inj₂ (inj₁ ⟨ d' , ⟨ d'∈ , ⟨ d'≢ , nf ⟩ ⟩ ⟩) ⟩)
    with conv (adequate L (λ x p → G x (inj₁ p)) d'∈) d'≢
... | ⟨ v , ⟨ eL , r ⟩ ⟩ =
  inj₁ ⟨ refl , (λ κ → (refl ∷↠ eL (appL M γ κ)) ⟫ here! (notfun-stop d' v r nf M γ κ)) ⟩
adequate (app ⦅ L ,, M ,, Nil ⦆) {γ = γ} G (inj₂ ⟨ refl , inj₂ (inj₂ ⟨ ⟨ f , ⟨ f∈ , isf ⟩ ⟩ , ω∈ ⟩) ⟩)
    with conv (adequate L (λ x p → G x (inj₁ p)) f∈) (λ e → subst IsFun e isf)
... | ⟨ v , ⟨ eL , r ⟩ ⟩ with fun-clo f v r isf
... | ⟨ N , ⟨ γ' , refl ⟩ ⟩ =
  inj₁ ⟨ refl , (λ κ → (refl ∷↠ eL (appL M γ κ) ++↠ refl ∷↠ done)
                        ⟫ err (adequate M (λ x p → G x (inj₂ (inj₁ p))) ω∈) (appR (clo N γ') κ)) ⟩

adequate (lit B k ⦅ Nil ⦆) {d = dconst k'} G ⟨ refl , refl ⟩ =
  inj₂ ⟨ const B k , ⟨ (λ κ → refl ∷↠ done) , refl ⟩ ⟩

adequate (tuple n ⦅ args ⦆) {d = ω} G e = inj₁ ⟨ refl , (λ κ → (refl ∷↠ done) ⟫ tuple-err args G e [] κ) ⟩
adequate (tuple zero ⦅ Nil ⦆) {d = ⟨⟩} G tt = inj₂ ⟨ tup [] , ⟨ (λ κ → refl ∷↠ done) , refl ⟩ ⟩
adequate (tuple (suc n) ⦅ args ⦆) {ρ} {γ} {d = tup[ i ] d} G ⟨ refl , ⟨ d∈ , vs ⟩ ⟩
    with adequate-args args G vs
... | ⟨ ws , ⟨ es , ⟨ len , rs ⟩ ⟩ ⟩ =
  inj₂ ⟨ tup ws
       , ⟨ (λ κ → refl ∷↠ subst (λ us → tuple-next [] (args→list args) γ κ ↠ ret (tup us) κ)
                                 (reverse-involutive ws) (tuple-run [] (args→list args) ws es))
         , rs i d d∈ ⟩ ⟩

adequate (get i ⦅ M ,, Nil ⦆) {γ = γ} G (inj₁ t∈) with conv (adequate M (λ x p → G x (inj₁ p)) t∈) (λ ())
... | ⟨ tup vs , ⟨ e , r ⟩ ⟩ with 𝕍At-proj i _ vs r
... | ⟨ v , ⟨ p , r' ⟩ ⟩ =
  inj₂ ⟨ v , ⟨ (λ κ → refl ∷↠ e (getK i κ) ++↠ cong (λ m → ret? m κ) p ∷↠ done) , r' ⟩ ⟩
adequate (get i ⦅ M ,, Nil ⦆) {γ = γ} G (inj₂ ⟨ refl , inj₁ ω∈ ⟩) =
  inj₁ ⟨ refl , (λ κ → (refl ∷↠ done) ⟫ err (adequate M (λ x p → G x (inj₁ p)) ω∈) (getK i κ)) ⟩
adequate (get i ⦅ M ,, Nil ⦆) {γ = γ} G (inj₂ ⟨ refl , inj₂ ⟨ e , ⟨ e∈ , ⟨ e≢ , nt ⟩ ⟩ ⟩ ⟩)
    with conv (adequate M (λ x p → G x (inj₁ p)) e∈) e≢
... | ⟨ v , ⟨ eM , r ⟩ ⟩ =
  inj₁ ⟨ refl , (λ κ → (refl ∷↠ eM (getK i κ)) ⟫ here! (nottup-stop i e v r nt κ)) ⟩

adequate (inl-op ⦅ M ,, Nil ⦆) {γ = γ} {d} G d∈ with inlᵉ-inv d d∈
... | inj₁ ⟨ v' , ⟨ refl , ⟨ v'∈ , v'≢ ⟩ ⟩ ⟩ with conv (adequate M (λ x p → G x (inj₁ p)) v'∈) v'≢
...   | ⟨ v , ⟨ e , r ⟩ ⟩ = inj₂ ⟨ inl v , ⟨ (λ κ → refl ∷↠ e (inlK κ) ++↠ refl ∷↠ done) , r ⟩ ⟩
adequate (inl-op ⦅ M ,, Nil ⦆) {γ = γ} {d} G d∈ | inj₂ ⟨ refl , ω∈ ⟩ =
  inj₁ ⟨ refl , (λ κ → (refl ∷↠ done) ⟫ err (adequate M (λ x p → G x (inj₁ p)) ω∈) (inlK κ)) ⟩

adequate (inr-op ⦅ M ,, Nil ⦆) {γ = γ} {d} G d∈ with inrᵉ-inv d d∈
... | inj₁ ⟨ v' , ⟨ refl , ⟨ v'∈ , v'≢ ⟩ ⟩ ⟩ with conv (adequate M (λ x p → G x (inj₁ p)) v'∈) v'≢
...   | ⟨ v , ⟨ e , r ⟩ ⟩ = inj₂ ⟨ inr v , ⟨ (λ κ → refl ∷↠ e (inrK κ) ++↠ refl ∷↠ done) , r ⟩ ⟩
adequate (inr-op ⦅ M ,, Nil ⦆) {γ = γ} {d} G d∈ | inj₂ ⟨ refl , ω∈ ⟩ =
  inj₁ ⟨ refl , (λ κ → (refl ∷↠ done) ⟫ err (adequate M (λ x p → G x (inj₁ p)) ω∈) (inrK κ)) ⟩

adequate (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) {ρ} {γ} G (inj₁ ⟨ u , ⟨ U , ⟨ allL , ⟨ w∈ , _ ⟩ ⟩ ⟩ ⟩)
    with conv (adequate L (λ x p → G x (inj₁ p)) (allL u (here refl))) (λ ())
... | ⟨ inl w , ⟨ eL , _ ⟩ ⟩
    with adequate M (𝔾-ext (u ∷ U) w (λ x p → G x (inj₂ (inj₁ p)))
           (all→𝕍s (u ∷ U) (λ d' d'∈ → collectℝ eL (adequate L (λ x p → G x (inj₁ p)) (allL d' d'∈))))) w∈
... | inj₁ ⟨ refl , eM ⟩ =
  inj₁ ⟨ refl , (λ κ → (refl ∷↠ eL (caseK M N γ κ) ++↠ refl ∷↠ done) ⟫ eM κ) ⟩
... | inj₂ ⟨ v , ⟨ eM , r ⟩ ⟩ =
  inj₂ ⟨ v , ⟨ (λ κ → refl ∷↠ eL (caseK M N γ κ) ++↠ refl ∷↠ eM κ) , r ⟩ ⟩
adequate (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) {ρ} {γ} G (inj₂ (inj₁ ⟨ u , ⟨ U , ⟨ allR , ⟨ w∈ , _ ⟩ ⟩ ⟩ ⟩))
    with conv (adequate L (λ x p → G x (inj₁ p)) (allR u (here refl))) (λ ())
... | ⟨ inr w , ⟨ eL , _ ⟩ ⟩
    with adequate N (𝔾-ext (u ∷ U) w (λ x p → G x (inj₂ (inj₂ (inj₁ p))))
           (all→𝕍s (u ∷ U) (λ d' d'∈ → collectℝ eL (adequate L (λ x p → G x (inj₁ p)) (allR d' d'∈))))) w∈
... | inj₁ ⟨ refl , eN ⟩ =
  inj₁ ⟨ refl , (λ κ → (refl ∷↠ eL (caseK M N γ κ) ++↠ refl ∷↠ done) ⟫ eN κ) ⟩
... | inj₂ ⟨ v , ⟨ eN , r ⟩ ⟩ =
  inj₂ ⟨ v , ⟨ (λ κ → refl ∷↠ eL (caseK M N γ κ) ++↠ refl ∷↠ eN κ) , r ⟩ ⟩
adequate (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) {γ = γ} G (inj₂ (inj₂ ⟨ refl , inj₁ ω∈ ⟩)) =
  inj₁ ⟨ refl , (λ κ → (refl ∷↠ done) ⟫ err (adequate L (λ x p → G x (inj₁ p)) ω∈) (caseK M N γ κ)) ⟩
adequate (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) {γ = γ} G (inj₂ (inj₂ ⟨ refl , inj₂ ⟨ e , ⟨ e∈ , ⟨ e≢ , ni ⟩ ⟩ ⟩ ⟩))
    with conv (adequate L (λ x p → G x (inj₁ p)) e∈) e≢
... | ⟨ v , ⟨ eL , r ⟩ ⟩ =
  inj₁ ⟨ refl , (λ κ → (refl ∷↠ eL (caseK M N γ κ)) ⟫ here! (notinj-stop e v r ni M N γ κ)) ⟩

adequate (prim p ⦅ L ,, M ,, Nil ⦆) {γ = γ} G (inj₁ ⟨ n , ⟨ m , ⟨ n∈ , ⟨ m∈ , refl ⟩ ⟩ ⟩ ⟩)
    with conv (adequate L (λ x q → G x (inj₁ q)) n∈) (λ ())
       | conv (adequate M (λ x q → G x (inj₂ (inj₁ q))) m∈) (λ ())
... | ⟨ _ , ⟨ eL , refl ⟩ ⟩ | ⟨ _ , ⟨ eM , refl ⟩ ⟩ =
  inj₂ ⟨ out (δ p n m)
       , ⟨ (λ κ → refl ∷↠ eL (primL p M γ κ) ++↠ refl ∷↠ eM (primR p (const Int n) κ) ++↠ refl ∷↠ done)
         , 𝕍-out (δ p n m) ⟩ ⟩
adequate (prim p ⦅ L ,, M ,, Nil ⦆) {γ = γ} G (inj₂ ⟨ refl , inj₁ (inj₁ ω∈) ⟩) =
  inj₁ ⟨ refl , (λ κ → (refl ∷↠ done) ⟫ err (adequate L (λ x q → G x (inj₁ q)) ω∈) (primL p M γ κ)) ⟩
adequate (prim p ⦅ L ,, M ,, Nil ⦆) {γ = γ} G (inj₂ ⟨ refl , inj₁ (inj₂ ⟨ ⟨ d , ⟨ d∈ , d≢ ⟩ ⟩ , inj₁ ω∈ ⟩) ⟩)
    with conv (adequate L (λ x q → G x (inj₁ q)) d∈) d≢
... | ⟨ v , ⟨ eL , _ ⟩ ⟩ =
  inj₁ ⟨ refl , (λ κ → (refl ∷↠ eL (primL p M γ κ) ++↠ refl ∷↠ done)
                        ⟫ err (adequate M (λ x q → G x (inj₂ (inj₁ q))) ω∈) (primR p v κ)) ⟩
adequate (prim p ⦅ L ,, M ,, Nil ⦆) {γ = γ} G
    (inj₂ ⟨ refl , inj₂ (inj₁ ⟨ ⟨ d , ⟨ d∈ , ⟨ d≢ , ni ⟩ ⟩ ⟩ , ⟨ e , ⟨ e∈ , e≢ ⟩ ⟩ ⟩) ⟩)
    with conv (adequate L (λ x q → G x (inj₁ q)) d∈) d≢
       | conv (adequate M (λ x q → G x (inj₂ (inj₁ q))) e∈) e≢
... | ⟨ v , ⟨ eL , r ⟩ ⟩ | ⟨ w , ⟨ eM , _ ⟩ ⟩ =
  inj₁ ⟨ refl , (λ κ → (refl ∷↠ eL (primL p M γ κ) ++↠ refl ∷↠ eM (primR p v κ))
                 ⟫ here! (cong (λ m → ret? m κ) (cong (map out) (δ?-nothing₁ p (obs v) (obs w) (notint-obs d v r ni))))) ⟩
adequate (prim p ⦅ L ,, M ,, Nil ⦆) {γ = γ} G
    (inj₂ ⟨ refl , inj₂ (inj₂ ⟨ ⟨ d , ⟨ d∈ , d≢ ⟩ ⟩ , ⟨ e , ⟨ e∈ , ⟨ e≢ , ni ⟩ ⟩ ⟩ ⟩) ⟩)
    with conv (adequate L (λ x q → G x (inj₁ q)) d∈) d≢
       | conv (adequate M (λ x q → G x (inj₂ (inj₁ q))) e∈) e≢
... | ⟨ v , ⟨ eL , _ ⟩ ⟩ | ⟨ w , ⟨ eM , r ⟩ ⟩ =
  inj₁ ⟨ refl , (λ κ → (refl ∷↠ eL (primL p M γ κ) ++↠ refl ∷↠ eM (primR p v κ))
                 ⟫ here! (cong (λ m → ret? m κ) (cong (map out) (δ?-nothing₂ p (obs v) (obs w) (notint-obs e w r ni))))) ⟩

adequate (let-op ⦅ M ,, ⟩ N ,, Nil ⦆) G (inj₁ ⟨ [] , ⟨ _ , ⟨ _ , ⟨ ne , _ ⟩ ⟩ ⟩ ⟩) = ⊥-elim (ne refl)
adequate (let-op ⦅ M ,, ⟩ N ,, Nil ⦆) {ρ} {γ} G (inj₁ ⟨ u ∷ U , ⟨ ⟨ w∈ , _ ⟩ , ⟨ V⊆ , ⟨ _ , noe ⟩ ⟩ ⟩ ⟩)
    with conv (adequate M (λ x p → G x (inj₁ p)) (V⊆ u (here refl))) (head≢ω noe)
... | ⟨ vM , ⟨ eM , _ ⟩ ⟩
    with adequate N (𝔾-ext (u ∷ U) vM (λ x p → G x (inj₂ (inj₁ p)))
           (all→𝕍s (u ∷ U) (λ d' d'∈ → collectℝ eM (adequate M (λ x p → G x (inj₁ p)) (V⊆ d' d'∈))))) w∈
... | inj₁ ⟨ refl , eN ⟩ = inj₁ ⟨ refl , (λ κ → (refl ∷↠ eM (letK N γ κ) ++↠ refl ∷↠ done) ⟫ eN κ) ⟩
... | inj₂ ⟨ v , ⟨ eN , r ⟩ ⟩ = inj₂ ⟨ v , ⟨ (λ κ → refl ∷↠ eM (letK N γ κ) ++↠ refl ∷↠ eN κ) , r ⟩ ⟩
adequate (let-op ⦅ M ,, ⟩ N ,, Nil ⦆) G (inj₂ ⟨ refl , inj₁ () ⟩)
adequate (let-op ⦅ M ,, ⟩ N ,, Nil ⦆) G (inj₂ ⟨ refl , inj₂ (inj₁ ⟨ d' , ⟨ d'∈ , ⟨ _ , nf ⟩ ⟩ ⟩) ⟩) =
  ⊥-elim (nf (Λᵉ-fun d' d'∈))
adequate (let-op ⦅ M ,, ⟩ N ,, Nil ⦆) {γ = γ} G (inj₂ ⟨ refl , inj₂ (inj₂ ⟨ _ , ω∈ ⟩) ⟩) =
  inj₁ ⟨ refl , (λ κ → (refl ∷↠ done) ⟫ err (adequate M (λ x p → G x (inj₁ p)) ω∈) (letK N γ κ)) ⟩

adequate-args {zero} Nil G vs = ⟨ [] , ⟨ [] , ⟨ refl , (λ ()) ⟩ ⟩ ⟩
adequate-args {suc n} (M ,, args) G vs
    with conv (adequate M (λ x p → G x (inj₁ p)) (proj₁ (proj₂ (vs zero)))) (proj₂ (proj₂ (vs zero)))
       | adequate-args args (λ x p → G x (inj₂ p)) (λ j → vs (suc j))
... | ⟨ v , ⟨ e , _ ⟩ ⟩ | ⟨ ws , ⟨ es , ⟨ len , rs ⟩ ⟩ ⟩ =
  ⟨ v ∷ ws , ⟨ e ∷ es , ⟨ cong suc len , R ⟩ ⟩ ⟩
  where
  R : ∀ j d → d ∈ nthD (⟦ M ,, args ⟧₊ _) j → 𝕍At j d (v ∷ ws)
  R zero d d∈ = ⟨ len , collectℝ e (adequate M (λ x p → G x (inj₁ p)) d∈) ⟩
  R (suc j) d d∈ = rs j d d∈

tuple-err {suc n} (M ,, args) {γ = γ} G (inj₁ ω∈) acc κ =
  err (adequate M (λ x p → G x (inj₁ p)) ω∈) (tupK acc (args→list args) γ κ)
tuple-err {suc n} (M ,, args) {γ = γ} G (inj₂ ⟨ ⟨ d , ⟨ d∈ , d≢ ⟩ ⟩ , e ⟩) acc κ
    with conv (adequate M (λ x p → G x (inj₁ p)) d∈) d≢
... | ⟨ v , ⟨ eM , _ ⟩ ⟩ =
  (eM (tupK acc (args→list args) γ κ) ++↠ (refl ∷↠ done))
    ⟫ tuple-err args (λ x p → G x (inj₂ p)) e (v ∷ acc) κ

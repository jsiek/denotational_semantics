{-

  Adequacy of the monadic graph model with errors for the ISWIM machine:
  every element of the denotation of a closed program is witnessed by a
  run of the machine, and ω by a run that stops with an error.

  As in proof/Adequacy/GraphErr/LogRel.agda, 𝕍 d v relates denotational
  values to machine values, and ℂ d c lifts it to computations (c, a
  state for any continuation): ω is related to a computation that stops
  with an error, any other value to one that returns a related value.

  The lifting goes through the monad once (ℂ-bind): an element of
  D ≫= F is ω because D errs, and the computation of D, in any frame,
  errs; or it is in F on the values of D, which are all related to the
  one value the computation of D returns (the machine is deterministic).
  So each operator's case in the fundamental lemma handles only its
  kernel: the check of the kind of its operand, and its success.

-}

module proof.Adequacy.GraphErrM.LogRel where

open import Framework.Primitives using (Base; base-rep; Int; Nat; 𝔹; Unit; Void; Blame)
open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.Domain
  using (Value; _↦_; ν; ω; ⦅_,_⦆; tup[_]_; left; right; ⟨⟩)
  renaming (const to dconst)
open import proof.Framework.GraphModel.OpsBase using (nthD)
open import proof.Framework.GraphModel.Ops using (𝒯; ⋆; 𝒞) renaming (proj to projD; inl to inlD; inr to inrD)
open import proof.Framework.GraphModel.DOpSig using (Results)
open import proof.Framework.GraphModel.ErrorMonad hiding (Val)
open import proof.Semantics.GraphErrM.Prim using (primD) renaming (out to dout)
open import Language.Prim using (int; bool; δ)
open import Language.ISWIM
open import proof.Framework.Syntax.Uses Op sig
open import proof.Semantics.GraphErrM.ISWIM using (⟦_⟧; ⟦_⟧₊)
open import proof.Adequacy.GraphErrM.Soundness using (vkind)
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
open import Data.List using (List; []; _∷_; length; replicate; reverse)
open import Data.List.Base using (reverseAcc)
open import Data.List.Properties using (reverse-involutive)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing; map)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; Σ-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (¬_)

VEnv : Set₁
VEnv = proof.Framework.GraphModel.Env.Env Value

{- Computations, and errors ------------------------------------------------------}

{- a computation: a state, in any continuation -}
Comp : Set
Comp = Cont → State

infix 4 _⇓_
_⇓_ : Comp → Val → Set
c ⇓ v = ∀ κ → c κ ↠ ret v κ

{- a run from s to a state that stops with an error -}
Err : State → Set
Err s = Σ[ t ∈ State ] s ↠ t × step t ≡ stop o-error

_⟫_ : ∀ {s s'} → s ↠ s' → Err s' → Err s
σ ⟫ ⟨ t , ⟨ τ , st ⟩ ⟩ = ⟨ t , ⟨ σ ++↠ τ , st ⟩ ⟩
infixr 4 _⟫_

⇓-det : ∀ {c v₁ v₂} → c ⇓ v₁ → c ⇓ v₂ → v₁ ≡ v₂
⇓-det e₁ e₂ with ↠-final-det (e₁ halt) (e₂ halt) refl refl
... | refl = refl

obs-ok : ∀ v → stop {S = State} (obs v) ≡ stop o-error → ⊥
obs-ok (clo N γ) ()
obs-ok (const B k) ()
obs-ok (tup vs) ()
obs-ok (inl v) ()
obs-ok (inr v) ()

{- a computation does not both return a value and stop with an error -}
⇓-err : ∀ {c v} → c ⇓ v → (∀ κ → Err (c κ)) → ⊥
⇓-err {v = v} e er with er halt
... | ⟨ t , ⟨ τ , st ⟩ ⟩ with ↠-final-det (e halt) τ refl st
... | refl = obs-ok v st

{- The logical relation ----------------------------------------------------------}

𝕍 : Value → Val → Set
𝕍s : List Value → Val → Set
𝕍At : ∀ {n} → Fin n → Value → List Val → Set
ℂ : Value → Comp → Set
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
ℂ d c = (d ≡ ω × (∀ κ → Err (c κ))) ⊎ (Σ[ v ∈ Val ] c ⇓ v × 𝕍 d v)

ℝ d γ M = ℂ d (eval M γ)

𝕍-ω : ∀ {v} → 𝕍 ω v → ⊥
𝕍-ω {clo N γ} ()

conv : ∀ {d c} → ℂ d c → d ≢ ω → Σ[ v ∈ Val ] c ⇓ v × 𝕍 d v
conv (inj₁ ⟨ refl , _ ⟩) d≢ = ⊥-elim (d≢ refl)
conv (inj₂ r) d≢ = r

err : ∀ {c} → ℂ ω c → ∀ κ → Err (c κ)
err (inj₁ ⟨ _ , e ⟩) = e
err (inj₂ ⟨ v , ⟨ _ , r ⟩ ⟩) = ⊥-elim (𝕍-ω {v} r)

{- the value a computation returns is related to every element -}
collect : ∀ {c v d} → c ⇓ v → ℂ d c → 𝕍 d v
collect e (inj₁ ⟨ _ , er ⟩) = ⊥-elim (⇓-err e er)
collect e (inj₂ ⟨ v' , ⟨ e' , r ⟩ ⟩) with ⇓-det e e'
... | refl = r

{- a computation that runs first to another -}
prepend : ∀ {c c' w} → (∀ κ → c κ ↠ c' κ) → ℂ w c' → ℂ w c
prepend σ (inj₁ ⟨ refl , e ⟩) = inj₁ ⟨ refl , (λ κ → σ κ ⟫ e κ) ⟩
prepend σ (inj₂ ⟨ v , ⟨ e , r ⟩ ⟩) = inj₂ ⟨ v , ⟨ (λ κ → σ κ ++↠ e κ) , r ⟩ ⟩

step₁ : ∀ {c c' w} → (∀ κ → step (c κ) ≡ next (c' κ)) → ℂ w c' → ℂ w c
step₁ st = prepend (λ κ → st κ ∷↠ done)

{- a computation that stops with an error -}
ℂ-stop : ∀ {c w} → (∀ κ → step (c κ) ≡ stop o-error) → w ≡ ω → ℂ w c
ℂ-stop st refl = inj₁ ⟨ refl , (λ κ → ⟨ _ , ⟨ done , st κ ⟩ ⟩) ⟩

{- bind, through the relation: the operand D is computed by c, and then
   the frame f runs on its value -}
ℂ-bind : ∀ {D F c w} (f : Cont → Cont) → (∀ d → d ∈ D → ℂ d c) → w ∈ (D ≫= F)
  → (∀ v → (∀ d → d ∈ ⌊ D ⌋ → 𝕍 d v) → ∀ w → w ∈ F ⌊ D ⌋ → ℂ w (λ κ → ret v (f κ)))
  → ℂ w (λ κ → c (f κ))
ℂ-bind f h (inj₁ ⟨ refl , ω∈ ⟩) k = inj₁ ⟨ refl , (λ κ → err (h ω ω∈) (f κ)) ⟩
ℂ-bind f h (inj₂ ⟨ ⟨ d , ⟨ d∈ , d≢ ⟩ ⟩ , w∈ ⟩) k with conv (h d d∈) d≢
... | ⟨ v , ⟨ e , _ ⟩ ⟩ = prepend (λ κ → e (f κ)) (k v (λ d' d'∈ → collect e (h d' (proj₁ d'∈))) _ w∈)

{- The kinds of related values ----------------------------------------------------}

𝕍At-length : ∀ {n} (i : Fin n) d vs → 𝕍At i d vs → length vs ≡ n
𝕍At-length {suc n} zero d (v ∷ vs) ⟨ len , _ ⟩ = cong suc len
𝕍At-length (suc i) d (v ∷ vs) r = cong suc (𝕍At-length i d vs r)

𝕍-kind : ∀ d v → 𝕍 d v → kind d ≡ vkind v
𝕍-kind (dconst k) (const B k) refl = refl
𝕍-kind (V ↦ w) (clo N γ) _ = refl
𝕍-kind ν (clo N γ) _ = refl
𝕍-kind ⟨⟩ (tup vs) refl = refl
𝕍-kind (tup[ i ] d) (tup vs) r = cong tup (sym (𝕍At-length i d vs r))
𝕍-kind (left d) (inl v) _ = refl
𝕍-kind (right d) (inr v) _ = refl

𝕍-left : ∀ {d} v → 𝕍 (left d) v → Σ[ v' ∈ Val ] v ≡ inl v'
𝕍-left (inl v') _ = ⟨ v' , refl ⟩

𝕍-right : ∀ {d} v → 𝕍 (right d) v → Σ[ v' ∈ Val ] v ≡ inr v'
𝕍-right (inr v') _ = ⟨ v' , refl ⟩

{- a value of another kind in an operand, all of whose values are related
   to v: v is of another kind -}
bad-kind : ∀ {k X v} → (∀ d → d ∈ X → 𝕍 d v) → Bad k X → vkind v ≢ k
bad-kind all ⟨ e , ⟨ e∈ , ek ⟩ ⟩ eq = ek (trans (𝕍-kind e _ (all e e∈)) eq)

{- a kernel that needs a value of kind k, on an operand related to a
   value of another kind, yields only ω -}
needs-ω : ∀ {k X A v w} → (∀ d → d ∈ X → 𝕍 d v) → vkind v ≢ k → Needs k X A → w ∈ A → w ≡ ω
needs-ω all nk n w∈ with n _ w∈
... | inj₁ eq = eq
... | inj₂ ⟨ u , ⟨ u∈ , uk ⟩ ⟩ = ⊥-elim (nk (trans (sym (𝕍-kind u _ (all u u∈))) uk))

{- The machine's checks fail on values of another kind -----------------------}

clo? : ∀ v → (Σ[ N ∈ AST ] Σ[ γ ∈ Env ] v ≡ clo N γ) ⊎ vkind v ≢ fun
clo? (clo N γ) = inj₁ ⟨ N , ⟨ γ , refl ⟩ ⟩
clo? (const B k) = inj₂ (λ ())
clo? (tup vs) = inj₂ (λ ())
clo? (inl v) = inj₂ (λ ())
clo? (inr v) = inj₂ (λ ())

notfun-stop : ∀ v → vkind v ≢ fun → ∀ M γ κ → step (ret v (appL M γ κ)) ≡ stop o-error
notfun-stop (clo N γ') nf M γ κ = ⊥-elim (nf refl)
notfun-stop (const B k) nf M γ κ = refl
notfun-stop (tup vs) nf M γ κ = refl
notfun-stop (inl v) nf M γ κ = refl
notfun-stop (inr v) nf M γ κ = refl

proj-just-length : ∀ {n} (i : Fin n) (vs : List Val) {v} → proj i vs ≡ just v → length vs ≡ n
proj-just-length {suc n} zero (v ∷ vs) eq with has-length n vs in h
proj-just-length {suc n} zero (v ∷ vs) refl | true = cong suc (has-length→length n vs h)
proj-just-length {suc n} zero (v ∷ vs) () | false
proj-just-length (suc i) (v ∷ vs) eq = cong suc (proj-just-length i vs eq)

nottup-stop : ∀ {n} (i : Fin n) v → vkind v ≢ tup n → ∀ κ → step (ret v (getK i κ)) ≡ stop o-error
nottup-stop i (tup vs) nt κ with proj i vs in p
... | just v = ⊥-elim (nt (cong tup (proj-just-length i vs p)))
... | nothing = refl
nottup-stop i (clo N γ) nt κ = refl
nottup-stop i (const B k) nt κ = refl
nottup-stop i (inl v) nt κ = refl
nottup-stop i (inr v) nt κ = refl

notinj-stop : ∀ v → vkind v ≢ inj → ∀ M N γ κ → step (ret v (caseK M N γ κ)) ≡ stop o-error
notinj-stop (inl v) ni M N γ κ = ⊥-elim (ni refl)
notinj-stop (inr v) ni M N γ κ = ⊥-elim (ni refl)
notinj-stop (clo N' γ') ni M N γ κ = refl
notinj-stop (const B k) ni M N γ κ = refl
notinj-stop (tup vs) ni M N γ κ = refl

{- a value of another kind than an integer is not observed as one -}
notint-obs : ∀ v → vkind v ≢ base Int → ∀ n → obs v ≢ o-const Int n
notint-obs (const .Int k) ni n refl = ni refl

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

{- Shapes and lists ---------------------------------------------------------------}

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

UsesP : AST → Var → Set
UsesP M x = Uses x M

{- The fundamental lemma ----------------------------------------------------------}

adequate : ∀ M {ρ γ d} → 𝔾 (UsesP M) ρ γ → d ∈ ⟦ M ⟧ ρ → ℝ d γ M

{- the operands of a tuple, bound left to right by the machine's tupK -}
tuple-ℂ : ∀ {m} (as : Args (replicate m ■)) {ρ γ} → 𝔾 (λ x → UsesArgs x as) ρ γ
  → ∀ {K w} acc → w ∈ binds m (⟦ as ⟧₊ ρ) K
  → (∀ vs Xs → length vs ≡ m → (∀ j d → d ∈ nthD Xs j → 𝕍At j d vs) → ∀ w → w ∈ K Xs
       → ℂ w (λ κ → ret (tup (reverse (reverseAcc acc vs))) κ))
  → ℂ w (λ κ → tuple-next acc (args→list as) γ κ)
tuple-ℂ {zero} Nil G acc w∈ k = k [] ptt refl (λ ()) _ w∈
tuple-ℂ {suc m} (M ,, as) {ρ} {γ} G {K} acc w∈ k =
  ℂ-bind {F = λ X → binds m (⟦ as ⟧₊ ρ) (λ Xs → K ⟨ X , Xs ⟩)} (λ κ → tupK acc (args→list as) γ κ) (λ d → adequate M (λ x p → G x (inj₁ p))) w∈
    λ v all w w∈′ → step₁ (λ κ → refl) (tuple-ℂ as (λ x p → G x (inj₂ p)) (v ∷ acc) w∈′
      λ vs Xs len rs w′ w∈″ → k (v ∷ vs) _ (cong suc len)
        (λ { zero d d∈ → ⟨ len , all d d∈ ⟩ ; (suc j) d d∈ → rs j d d∈ }) w′ w∈″)

adequate (` x) {γ = γ} G d∈ with G x refl _ d∈
... | ⟨ v , ⟨ look , r ⟩ ⟩ = inj₂ ⟨ v , ⟨ (λ κ → cong (λ m → ret? m κ) look ∷↠ done) , r ⟩ ⟩

adequate (lam ⦅ ⟩ N ,, Nil ⦆) {γ = γ} {d = ν} G d∈ = inj₂ ⟨ clo N γ , ⟨ (λ κ → refl ∷↠ done) , tt ⟩ ⟩
adequate (lam ⦅ ⟩ N ,, Nil ⦆) {γ = γ} {d = V ↦ w} G ⟨ ⟨ w∈ , _ ⟩ , _ ⟩ =
  inj₂ ⟨ clo N γ , ⟨ (λ κ → refl ∷↠ done)
       , (λ v Vv → adequate N (𝔾-ext V v (λ x u → G x (inj₁ u)) Vv) w∈) ⟩ ⟩

adequate (app ⦅ L ,, M ,, Nil ⦆) {ρ} {γ} G w∈ =
  step₁ (λ κ → refl) (ℂ-bind {F = λ X → checked fun X (⟦ M ⟧ ρ ≫= λ Y → ⋆ ⟨ X , ⟨ Y , ptt ⟩ ⟩)} (λ κ → appL M γ κ) (λ d → adequate L (λ x p → G x (inj₁ p))) w∈ APP)
  where
  X = ⌊ ⟦ L ⟧ ρ ⌋
  APP : ∀ v → (∀ d → d ∈ X → 𝕍 d v) → ∀ w → w ∈ checked fun X (⟦ M ⟧ ρ ≫= λ Y → ⋆ ⟨ X , ⟨ Y , ptt ⟩ ⟩)
    → ℂ w (λ κ → ret v (appL M γ κ))
  APP v all w (inj₁ ⟨ refl , bad ⟩) = ℂ-stop (notfun-stop v (bad-kind all bad) M γ) refl
  APP v all w (inj₂ w∈′) with clo? v
  ... | inj₂ nf = ℂ-stop (notfun-stop v nf M γ) (needs-ω {A = ⟦ M ⟧ ρ ≫= λ Y → ⋆ ⟨ X , ⟨ Y , ptt ⟩ ⟩} all nf (≫=-needs {D = ⟦ M ⟧ ρ} (λ {Y} → ⋆-needs {X} {Y})) w∈′)
  ... | inj₁ ⟨ N , ⟨ γ' , refl ⟩ ⟩ =
    step₁ (λ κ → refl) (ℂ-bind {F = λ Y → ⋆ ⟨ X , ⟨ Y , ptt ⟩ ⟩} (λ κ → appR (clo N γ') κ) (λ d → adequate M (λ x p → G x (inj₂ (inj₁ p)))) w∈′
      λ { u allM w ⟨ V , ⟨ f∈ , ⟨ V⊆ , _ ⟩ ⟩ ⟩ →
          step₁ (λ κ → refl) (all (V ↦ w) f∈ u (all→𝕍s V (λ d d∈ → allM d (V⊆ d d∈)))) })

adequate (lit B k ⦅ Nil ⦆) {d = dconst k'} G ⟨ refl , refl ⟩ =
  inj₂ ⟨ const B k , ⟨ (λ κ → refl ∷↠ done) , refl ⟩ ⟩

adequate (tuple n ⦅ args ⦆) {γ = γ} G w∈ =
  step₁ (λ κ → refl) (tuple-ℂ args G [] w∈ TUP)
  where
  TUP : ∀ vs Xs → length vs ≡ n → (∀ j d → d ∈ nthD Xs j → 𝕍At j d vs) → ∀ w → w ∈ 𝒯 n Xs
    → ℂ w (λ κ → ret (tup (reverse (reverseAcc [] vs))) κ)
  TUP vs Xs len rs w w∈ rewrite reverse-involutive vs = inj₂ ⟨ tup vs , ⟨ (λ κ → done) , T Xs vs len rs w w∈ ⟩ ⟩
    where
    T : ∀ {m} (Ys : Results (𝒫 Value) (replicate m ■)) vs → length vs ≡ m
      → (∀ j d → d ∈ nthD Ys j → 𝕍At j d vs) → ∀ w → w ∈ 𝒯 m Ys → 𝕍 w (tup vs)
    T {zero} Ys [] refl rs ⟨⟩ _ = refl
    T {suc m} Ys vs len rs (tup[ i ] d) ⟨ refl , ⟨ d∈ , _ ⟩ ⟩ = rs i d d∈

adequate (get {n} i ⦅ M ,, Nil ⦆) {ρ} {γ} G w∈ =
  step₁ (λ κ → refl) (ℂ-bind {F = λ X → checked (tup n) X (projD i ⟨ X , ptt ⟩)} (getK i) (λ d → adequate M (λ x p → G x (inj₁ p))) w∈ GET)
  where
  X = ⌊ ⟦ M ⟧ ρ ⌋
  GET : ∀ v → (∀ d → d ∈ X → 𝕍 d v) → ∀ w → w ∈ checked (tup n) X (projD i ⟨ X , ptt ⟩)
    → ℂ w (λ κ → ret v (getK i κ))
  GET v all w (inj₁ ⟨ refl , bad ⟩) = ℂ-stop (nottup-stop i v (bad-kind all bad)) refl
  GET v all w (inj₂ t∈) with v | all _ t∈
  ... | tup vs | r with 𝕍At-proj i _ vs r
  ...   | ⟨ u , ⟨ p , r' ⟩ ⟩ = inj₂ ⟨ u , ⟨ (λ κ → cong (λ m → ret? m κ) p ∷↠ done) , r' ⟩ ⟩

adequate (inl-op ⦅ M ,, Nil ⦆) {ρ} G w∈ =
  step₁ (λ κ → refl) (ℂ-bind {F = λ X → inlD ⟨ X , ptt ⟩} inlK (λ d → adequate M (λ x p → G x (inj₁ p))) w∈ INL)
  where
  INL : ∀ v → (∀ d → d ∈ ⌊ ⟦ M ⟧ ρ ⌋ → 𝕍 d v) → ∀ w → w ∈ inlD ⟨ ⌊ ⟦ M ⟧ ρ ⌋ , ptt ⟩ → ℂ w (λ κ → ret v (inlK κ))
  INL v all (left d) d∈ = inj₂ ⟨ inl v , ⟨ (λ κ → refl ∷↠ done) , all d d∈ ⟩ ⟩

adequate (inr-op ⦅ M ,, Nil ⦆) {ρ} G w∈ =
  step₁ (λ κ → refl) (ℂ-bind {F = λ X → inrD ⟨ X , ptt ⟩} inrK (λ d → adequate M (λ x p → G x (inj₁ p))) w∈ INR)
  where
  INR : ∀ v → (∀ d → d ∈ ⌊ ⟦ M ⟧ ρ ⌋ → 𝕍 d v) → ∀ w → w ∈ inrD ⟨ ⌊ ⟦ M ⟧ ρ ⌋ , ptt ⟩ → ℂ w (λ κ → ret v (inrK κ))
  INR v all (right d) d∈ = inj₂ ⟨ inr v , ⟨ (λ κ → refl ∷↠ done) , all d d∈ ⟩ ⟩

adequate (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) {ρ} {γ} G w∈ =
  step₁ (λ κ → refl) (ℂ-bind {F = λ X → checked inj X (𝒞 ⟨ X ⇂ ValPayload , ⟨ (λ Z → ⟦ M ⟧ (Z • ρ)) , ⟨ (λ Z → ⟦ N ⟧ (Z • ρ)) , ptt ⟩ ⟩ ⟩)} (caseK M N γ) (λ d → adequate L (λ x p → G x (inj₁ p))) w∈ CASE)
  where
  X = ⌊ ⟦ L ⟧ ρ ⌋
  CASE : ∀ v → (∀ d → d ∈ X → 𝕍 d v) → ∀ w
    → w ∈ checked inj X (𝒞 ⟨ X ⇂ ValPayload , ⟨ (λ Z → ⟦ M ⟧ (Z • ρ)) , ⟨ (λ Z → ⟦ N ⟧ (Z • ρ)) , ptt ⟩ ⟩ ⟩)
    → ℂ w (λ κ → ret v (caseK M N γ κ))
  CASE v all w (inj₁ ⟨ refl , bad ⟩) = ℂ-stop (notinj-stop v (bad-kind all bad) M N γ) refl
  CASE v all w (inj₂ (inj₁ ⟨ u , ⟨ U , ⟨ allL , ⟨ w∈′ , _ ⟩ ⟩ ⟩ ⟩)) with 𝕍-left v (all _ (proj₁ (allL u (here refl))))
  ... | ⟨ v' , refl ⟩ =
    step₁ (λ κ → refl) (adequate M (𝔾-ext (u ∷ U) v' (λ x p → G x (inj₂ (inj₁ p)))
                          (all→𝕍s (u ∷ U) (λ d d∈ → all (left d) (proj₁ (allL d d∈))))) w∈′)
  CASE v all w (inj₂ (inj₂ ⟨ u , ⟨ U , ⟨ allR , ⟨ w∈′ , _ ⟩ ⟩ ⟩ ⟩)) with 𝕍-right v (all _ (proj₁ (allR u (here refl))))
  ... | ⟨ v' , refl ⟩ =
    step₁ (λ κ → refl) (adequate N (𝔾-ext (u ∷ U) v' (λ x p → G x (inj₂ (inj₂ (inj₁ p))))
                          (all→𝕍s (u ∷ U) (λ d d∈ → all (right d) (proj₁ (allR d d∈))))) w∈′)

adequate (prim p ⦅ L ,, M ,, Nil ⦆) {ρ} {γ} G w∈ =
  step₁ (λ κ → refl) (ℂ-bind {F = λ X → ⟦ M ⟧ ρ ≫= λ Y → K X Y} (primL p M γ) (λ d → adequate L (λ x q → G x (inj₁ q))) w∈
    λ v allL w w∈′ → step₁ (λ κ → refl) (ℂ-bind {F = K X} (primR p v) (λ d → adequate M (λ x q → G x (inj₂ (inj₁ q)))) w∈′
      (PRIM v allL)))
  where
  K = λ X Y → checked (base Int) X (checked (base Int) Y (primD p ⟨ X , ⟨ Y , ptt ⟩ ⟩))
  X = ⌊ ⟦ L ⟧ ρ ⌋
  Y = ⌊ ⟦ M ⟧ ρ ⌋
  PRIM : ∀ v → (∀ d → d ∈ X → 𝕍 d v) → ∀ u → (∀ d → d ∈ Y → 𝕍 d u) → ∀ w
    → w ∈ checked (base Int) X (checked (base Int) Y (primD p ⟨ X , ⟨ Y , ptt ⟩ ⟩)) → ℂ w (λ κ → ret u (primR p v κ))
  PRIM v allL u allM w (inj₁ ⟨ refl , bad ⟩) =
    ℂ-stop (λ κ → cong (λ m → ret? m κ) (cong (map out) (δ?-nothing₁ p (obs v) (obs u) (notint-obs v (bad-kind allL bad))))) refl
  PRIM v allL u allM w (inj₂ (inj₁ ⟨ refl , bad ⟩)) =
    ℂ-stop (λ κ → cong (λ m → ret? m κ) (cong (map out) (δ?-nothing₂ p (obs v) (obs u) (notint-obs u (bad-kind allM bad))))) refl
  PRIM v allL u allM w (inj₂ (inj₂ ⟨ n , ⟨ m , ⟨ n∈ , ⟨ m∈ , refl ⟩ ⟩ ⟩ ⟩)) with allL _ n∈ | allM _ m∈
  ... | refl | refl = inj₂ ⟨ out (δ p n m) , ⟨ (λ κ → refl ∷↠ done) , 𝕍-out (δ p n m) ⟩ ⟩

adequate (let-op ⦅ M ,, ⟩ N ,, Nil ⦆) {ρ} {γ} G w∈ =
  step₁ (λ κ → refl) (ℂ-bind {F = λ X → ⋆ ⟨ Λᵐ ⟨ F , ptt ⟩ , ⟨ X , ptt ⟩ ⟩} (letK N γ) (λ d → adequate M (λ x p → G x (inj₁ p)))
    (proj₁ (letᵐ-unfold {⟦ M ⟧ ρ} {F}) _ w∈)
    λ { v all w ⟨ V , ⟨ ⟨ ⟨ w∈′ , _ ⟩ , _ ⟩ , ⟨ V⊆ , _ ⟩ ⟩ ⟩ →
        step₁ (λ κ → refl) (adequate N (𝔾-ext V v (λ x p → G x (inj₂ (inj₁ p))) (all→𝕍s V (λ d d∈ → all d (V⊆ d d∈)))) w∈′) })
  where F = λ Y → ⟦ N ⟧ (Y • ρ)

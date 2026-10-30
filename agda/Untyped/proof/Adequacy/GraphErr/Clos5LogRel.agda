{-

  Adequacy of the graph model with errors for the Clos5 machine:
  every element of the denotation of a well-formed program is witnessed
  by a run of the machine, for the table ds of its global definitions,
  and ω by a run that stops with an error.

  As for ISWIM (proof/Adequacy/GraphErr/LogRel.agda), 𝕍 d v relates
  denotational values to machine values, and ℂ d c lifts it to
  computations: ω is related to a computation that stops with an error,
  any other value to one that returns a related value. The lifting goes
  through the monad once (ℂ-bind), so each operator's case handles only
  its kernel: the check of the kind of its operand, and its success.

  As for Clos5 in the graph model (proof/Adequacy/Clos5LogRel.agda), a
  code pointer is related to the entries of code: X ↦ (Y ↦ w) is related
  to code k when the machine finds a definition at k whose body, run on
  values related to all of X and Y, is related to w. The fundamental
  lemma assumes that the table is related to the code pointers it refers
  to (𝕋), and the table of the program is (tab). A call binds its code,
  environment and argument, and only then checks the code (the late
  check). An unbound variable denotes {ω} and errs in the machine, so
  environments are related on all variables (𝔾).

-}

open import Data.List using (List; []; _∷_; length; replicate; reverse)
open import Untyped.Language.Clos5 using (AST)

module Untyped.proof.Adequacy.GraphErr.Clos5LogRel (ds : List AST) where

open import Framework.Primitives using (Int)
open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.Domain
  using (Value; _↦_; ν; ω; ⦅_,_⦆; tup[_]_; left; right; ⟨⟩)
  renaming (const to dconst)
open import proof.Framework.GraphModel.OpsBase using (nthD)
open import proof.Framework.GraphModel.Ops using (𝒯; ⋆; 𝒞) renaming (proj to projD; inl to inlD; inr to inrD; pair to pairD; car to carD; cdr to cdrD)
open import proof.Framework.GraphModel.DOpSig using (Results)
open import proof.Framework.GraphModel.ErrorMonad hiding (Val)
open import proof.Semantics.GraphErr.Prim using (primD) renaming (out to dout)
open import Language.Prim using (int; bool; δ)
open import Untyped.Language.Clos5 hiding (AST)
open import Untyped.Semantics.GraphErr.Clos5 using (Table; ⟦_⟧[_]; ⟦_⟧₊[_]; table; init)
import proof.Framework.GraphModel.Env
open import Framework.Syntax.SyntaxUtil using (_,,_; Nil; ⟩_,,_)
open import proof.Framework.ListUtil
open import Semantics.Observation
open import Untyped.Semantics.CEK.Clos5
open import proof.Semantics.CEK.Smallstep using (next; stop)
open import Untyped.proof.Compiler.HoistTable using (_⊑_; ∷-⊑; global-⊑)
open import proof.Adequacy.Common using (ShapeOf; ShapeAt; has-length→length; length→has-length)
open import proof.Adequacy.GraphErr.LogRel using (δ?-nothing₁; δ?-nothing₂)
open import Untyped.proof.Adequacy.GraphErr.Clos5Soundness using (vkind)
open import Untyped.proof.Adequacy.GraphErr.Clos5WF using (DefsWF; RB; RB-args)
open import Untyped.proof.Adequacy.GraphErr.Clos5Common ds

open import Data.Bool using (true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin; zero; suc)
open import Data.List.Base using (reverseAcc)
open import Data.List.Properties using (reverse-involutive)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing; map)
open import Data.Nat using (ℕ; zero; suc; _<_; _≟_)
open import Data.Nat.Properties using (≤-pred; m≤n⇒m<n∨m≡n)
open import Data.Product using (_×_; Σ-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (yes; no)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)

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
Err s = Σ[ t ∈ State ] s ↠ t × step ds t ≡ stop o-error

_⟫_ : ∀ {s s'} → s ↠ s' → Err s' → Err s
σ ⟫ ⟨ t , ⟨ τ , st ⟩ ⟩ = ⟨ t , ⟨ σ ++↠ τ , st ⟩ ⟩
infixr 4 _⟫_

⇓-det : ∀ {c v₁ v₂} → c ⇓ v₁ → c ⇓ v₂ → v₁ ≡ v₂
⇓-det e₁ e₂ with ↠-final-det (e₁ halt) (e₂ halt) refl refl
... | refl = refl

obs-ok : ∀ v → stop {S = State} (obs v) ≡ stop o-error → ⊥
obs-ok (code k) ()
obs-ok (pair v w) ()
obs-ok (const B k) ()
obs-ok (tup vs) ()
obs-ok (inl v) ()
obs-ok (inr v) ()

⇓-err : ∀ {c v} → c ⇓ v → (∀ κ → Err (c κ)) → ⊥
⇓-err {v = v} e er with er halt
... | ⟨ t , ⟨ τ , st ⟩ ⟩ with ↠-final-det (e halt) τ refl st
... | refl = obs-ok v st

{- The logical relation ----------------------------------------------------------}

𝕍 : Value → Val → Set
𝕍code : List Value → Value → ℕ → Set
𝕍s : List Value → Val → Set
𝕍At : ∀ {n} → Fin n → Value → List Val → Set
ℂ : Value → Comp → Set
ℝ : Value → Env → AST → Set

𝕍 (dconst {B} k) v = v ≡ const B k
𝕍 ν (code k) = ⊤
𝕍 (X ↦ w) (code k) = 𝕍code X w k
𝕍 ⦅ u₁ , u₂ ⦆ (pair v w) = 𝕍 u₁ v × 𝕍 u₂ w
𝕍 ⟨⟩ (tup vs) = vs ≡ []
𝕍 (tup[ i ] d) (tup vs) = 𝕍At i d vs
𝕍 (left d) (inl v) = 𝕍 d v
𝕍 (right d) (inr v) = 𝕍 d v
𝕍 _ _ = ⊥

{- the entries of code: the machine runs definition k -}
𝕍code X ν k = ⊤
𝕍code X (Y ↦ w) k = ∀ e → 𝕍s X e → ∀ a → 𝕍s Y a
  → Σ[ N ∈ AST ] global ds k ≡ just N × ℝ w (a ∷ e ∷ []) N
𝕍code X _ k = ⊥

𝕍s [] v = ⊤
𝕍s (d ∷ V) v = 𝕍 d v × 𝕍s V v

𝕍At {suc n} zero d (v ∷ vs) = length vs ≡ n × 𝕍 d v
𝕍At (suc i) d (v ∷ vs) = 𝕍At i d vs
𝕍At _ d [] = ⊥

ℂ d c = (d ≡ ω × (∀ κ → Err (c κ))) ⊎ (Σ[ v ∈ Val ] c ⇓ v × 𝕍 d v)

ℝ d γ M = ℂ d (eval M γ)

𝕍-ω : ∀ {v} → 𝕍 ω v → ⊥
𝕍-ω {code k} ()

conv : ∀ {d c} → ℂ d c → d ≢ ω → Σ[ v ∈ Val ] c ⇓ v × 𝕍 d v
conv (inj₁ ⟨ refl , _ ⟩) d≢ = ⊥-elim (d≢ refl)
conv (inj₂ r) d≢ = r

err : ∀ {c} → ℂ ω c → ∀ κ → Err (c κ)
err (inj₁ ⟨ _ , e ⟩) = e
err (inj₂ ⟨ v , ⟨ _ , r ⟩ ⟩) = ⊥-elim (𝕍-ω {v} r)

collect : ∀ {c v d} → c ⇓ v → ℂ d c → 𝕍 d v
collect e (inj₁ ⟨ _ , er ⟩) = ⊥-elim (⇓-err e er)
collect e (inj₂ ⟨ v' , ⟨ e' , r ⟩ ⟩) with ⇓-det e e'
... | refl = r

prepend : ∀ {c c' w} → (∀ κ → c κ ↠ c' κ) → ℂ w c' → ℂ w c
prepend σ (inj₁ ⟨ refl , e ⟩) = inj₁ ⟨ refl , (λ κ → σ κ ⟫ e κ) ⟩
prepend σ (inj₂ ⟨ v , ⟨ e , r ⟩ ⟩) = inj₂ ⟨ v , ⟨ (λ κ → σ κ ++↠ e κ) , r ⟩ ⟩

step₁ : ∀ {c c' w} → (∀ κ → step ds (c κ) ≡ next (c' κ)) → ℂ w c' → ℂ w c
step₁ st = prepend (λ κ → st κ ∷↠ done)

ℂ-stop : ∀ {c w} → (∀ κ → step ds (c κ) ≡ stop o-error) → w ≡ ω → ℂ w c
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
𝕍-kind ν (code k) _ = refl
𝕍-kind (X ↦ w) (code k) _ = refl
𝕍-kind ⦅ u₁ , u₂ ⦆ (pair v w) _ = refl
𝕍-kind ⟨⟩ (tup vs) refl = refl
𝕍-kind (tup[ i ] d) (tup vs) r = cong tup (sym (𝕍At-length i d vs r))
𝕍-kind (left d) (inl v) _ = refl
𝕍-kind (right d) (inr v) _ = refl

𝕍-left : ∀ {d} v → 𝕍 (left d) v → Σ[ v' ∈ Val ] v ≡ inl v'
𝕍-left (inl v') _ = ⟨ v' , refl ⟩

𝕍-right : ∀ {d} v → 𝕍 (right d) v → Σ[ v' ∈ Val ] v ≡ inr v'
𝕍-right (inr v') _ = ⟨ v' , refl ⟩

{- a value of another kind in an operand all of whose values are related
   to v: v is of another kind -}
bad-kind : ∀ {k X v} → (∀ d → d ∈ X → 𝕍 d v) → Bad k X → vkind v ≢ k
bad-kind all ⟨ e , ⟨ e∈ , ek ⟩ ⟩ eq = ek (trans (𝕍-kind e _ (all e e∈)) eq)

{- The machine's checks fail on values of another kind -----------------------}

notcode-stop : ∀ v → vkind v ≢ fun → ∀ a e κ → step ds (ret a (appA v e κ)) ≡ stop o-error
notcode-stop (code k) nf a e κ = ⊥-elim (nf refl)
notcode-stop (pair v w) nf a e κ = refl
notcode-stop (const B k) nf a e κ = refl
notcode-stop (tup vs) nf a e κ = refl
notcode-stop (inl v) nf a e κ = refl
notcode-stop (inr v) nf a e κ = refl

nonpair-stop : ∀ v → vkind v ≢ prod → ∀ κ
  → step ds (ret v (fstK κ)) ≡ stop o-error × step ds (ret v (sndK κ)) ≡ stop o-error
nonpair-stop (pair v w) np κ = ⊥-elim (np refl)
nonpair-stop (code k) np κ = ⟨ refl , refl ⟩
nonpair-stop (const B k) np κ = ⟨ refl , refl ⟩
nonpair-stop (tup vs) np κ = ⟨ refl , refl ⟩
nonpair-stop (inl v) np κ = ⟨ refl , refl ⟩
nonpair-stop (inr v) np κ = ⟨ refl , refl ⟩

proj-just-length : ∀ {n} (i : Fin n) (vs : List Val) {v} → proj i vs ≡ just v → length vs ≡ n
proj-just-length {suc n} zero (v ∷ vs) eq with has-length n vs in h
proj-just-length {suc n} zero (v ∷ vs) refl | true = cong suc (has-length→length n vs h)
proj-just-length {suc n} zero (v ∷ vs) () | false
proj-just-length (suc i) (v ∷ vs) eq = cong suc (proj-just-length i vs eq)

nottup-stop : ∀ {n} (i : Fin n) v → vkind v ≢ tup n → ∀ κ → step ds (ret v (getK i κ)) ≡ stop o-error
nottup-stop i (tup vs) nt κ with proj i vs in p
... | just v = ⊥-elim (nt (cong tup (proj-just-length i vs p)))
... | nothing = refl
nottup-stop i (code k) nt κ = refl
nottup-stop i (pair v w) nt κ = refl
nottup-stop i (const B k) nt κ = refl
nottup-stop i (inl v) nt κ = refl
nottup-stop i (inr v) nt κ = refl

notinj-stop : ∀ v → vkind v ≢ inj → ∀ M N γ κ → step ds (ret v (caseK M N γ κ)) ≡ stop o-error
notinj-stop (inl v) ni M N γ κ = ⊥-elim (ni refl)
notinj-stop (inr v) ni M N γ κ = ⊥-elim (ni refl)
notinj-stop (code k) ni M N γ κ = refl
notinj-stop (pair v w) ni M N γ κ = refl
notinj-stop (const B k) ni M N γ κ = refl
notinj-stop (tup vs) ni M N γ κ = refl

notint-obs : ∀ v → vkind v ≢ base Int → ∀ n → obs v ≢ o-const Int n
notint-obs (const .Int k) ni n refl = ni refl

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

length-obs-list : ∀ vs → length (obs-list vs) ≡ length vs
length-obs-list [] = refl
length-obs-list (v ∷ vs) = cong suc (length-obs-list vs)

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

{- Related environments and tables ------------------------------------------------}

{- every variable: unbound (and then {ω}), or bound to a related value -}
𝔾 : VEnv → Env → Set
𝔾 ρ γ = ∀ x d → d ∈ ρ x → (d ≡ ω × γ ‼ x ≡ nothing) ⊎ (Σ[ v ∈ Val ] γ ‼ x ≡ just v × 𝕍 d v)

𝔾-ext : ∀ {ρ γ} V v → 𝔾 ρ γ → 𝕍s V v → 𝔾 (mem V • ρ) (v ∷ γ)
𝔾-ext V v G Vv zero d d∈ = inj₂ ⟨ v , ⟨ refl , 𝕍s-∈ V Vv d∈ ⟩ ⟩
𝔾-ext V v G Vv (suc x) d d∈ = G x d d∈

{- the entries of the table for the first n references are related to the
   code pointers -}
𝕋 : ℕ → Table → Set
𝕋 n T = ∀ k → k < n → ∀ d → d ∈ T k → 𝕍 d (code k)

{- The fundamental lemma ----------------------------------------------------------}

adequate : ∀ M {T n ρ γ d} → 𝕋 n T → RB n M → 𝔾 ρ γ → d ∈ ⟦ M ⟧[ T ] ρ → ℝ d γ M

{- the operands of a tuple, bound left to right by the machine's tupK -}
tuple-ℂ : ∀ {m} (as : Args (replicate m ■)) {T n ρ γ} → 𝕋 n T → RB-args n as → 𝔾 ρ γ
  → ∀ {K w} acc → w ∈ binds m (⟦ as ⟧₊[ T ] ρ) K
  → (∀ vs Xs → length vs ≡ m → (∀ j d → d ∈ nthD Xs j → 𝕍At j d vs) → ∀ w → w ∈ K Xs
       → ℂ w (λ κ → ret (tup (reverse (reverseAcc acc vs))) κ))
  → ℂ w (λ κ → tuple-next acc (args→list as) γ κ)
tuple-ℂ {zero} Nil 𝕋T rb G acc w∈ k = k [] ptt refl (λ ()) _ w∈
tuple-ℂ {suc m} (M ,, as) {T} {n} {ρ} {γ} 𝕋T ⟨ rM , rs ⟩ G {K} acc w∈ k =
  ℂ-bind {F = λ X → binds m (⟦ as ⟧₊[ T ] ρ) (λ Xs → K ⟨ X , Xs ⟩)} (tupK acc (args→list as) γ) (λ d → adequate M 𝕋T rM G) w∈
    λ v all w w∈′ → step₁ (λ κ → refl) (tuple-ℂ as 𝕋T rs G (v ∷ acc) w∈′
      λ vs Xs len rels w′ w∈″ → k (v ∷ vs) _ (cong suc len)
        (λ { zero d d∈ → ⟨ len , all d d∈ ⟩ ; (suc j) d d∈ → rels j d d∈ }) w′ w∈″)

adequate (` x) {γ = γ} 𝕋T rb G d∈ with G x _ d∈
... | inj₁ ⟨ refl , look ⟩ = ℂ-stop (λ κ → cong (λ m → ret? m κ) look) refl
... | inj₂ ⟨ v , ⟨ look , r ⟩ ⟩ = inj₂ ⟨ v , ⟨ (λ κ → cong (λ m → ret? m κ) look ∷↠ done) , r ⟩ ⟩

adequate (fun-ref k ⦅ Nil ⦆) {d = d} 𝕋T k< G d∈ =
  inj₂ ⟨ code k , ⟨ (λ κ → refl ∷↠ done) , 𝕋T k k< d d∈ ⟩ ⟩

adequate (app ⦅ L ,, M ,, N ,, Nil ⦆) {T} {n} {ρ} {γ} 𝕋T ⟨ rL , ⟨ rM , ⟨ rN , _ ⟩ ⟩ ⟩ G w∈ =
  step₁ (λ κ → refl) (ℂ-bind {F = λ F → Mᵀ ≫= λ E → Nᵀ ≫= λ X → K F E X} (appF M N γ) (λ d → adequate L 𝕋T rL G) w∈
    λ f allF w w∈₁ → step₁ (λ κ → refl) (ℂ-bind {F = λ E → Nᵀ ≫= λ X → K Lᵛ E X} (appE f N γ) (λ d → adequate M 𝕋T rM G) w∈₁
    λ e allE w w∈₂ → step₁ (λ κ → refl) (ℂ-bind {F = K Lᵛ Mᵛ} (appA f e) (λ d → adequate N 𝕋T rN G) w∈₂
    (CALL f allF e allE))))
  where
  Mᵀ = ⟦ M ⟧[ T ] ρ
  Nᵀ = ⟦ N ⟧[ T ] ρ
  Lᵛ = ⌊ ⟦ L ⟧[ T ] ρ ⌋
  Mᵛ = ⌊ Mᵀ ⌋
  K = λ F E X → checked fun F (⋆ ⟨ ⋆ ⟨ F , ⟨ E , ptt ⟩ ⟩ , ⟨ X , ptt ⟩ ⟩)
  CALL : ∀ f → (∀ d → d ∈ Lᵛ → 𝕍 d f) → ∀ e → (∀ d → d ∈ Mᵛ → 𝕍 d e) → ∀ a → (∀ d → d ∈ ⌊ Nᵀ ⌋ → 𝕍 d a)
    → ∀ w → w ∈ K Lᵛ Mᵛ ⌊ Nᵀ ⌋ → ℂ w (λ κ → ret a (appA f e κ))
  CALL f allF e allE a allN w (inj₁ ⟨ refl , bad ⟩) = ℂ-stop (notcode-stop f (bad-kind allF bad) a e) refl
  CALL f allF e allE a allN w (inj₂ ⟨ U , ⟨ ⟨ V , ⟨ f∈ , ⟨ V⊆ , _ ⟩ ⟩ ⟩ , ⟨ U⊆ , _ ⟩ ⟩ ⟩) with f | allF _ f∈
  ... | code j | r with r e (all→𝕍s V (λ d d∈ → allE d (V⊆ d d∈))) a (all→𝕍s U (λ d d∈ → allN d (U⊆ d d∈)))
  ...   | ⟨ B , ⟨ g , rB ⟩ ⟩ = prepend (λ κ → cong (λ m → call m a e κ) g ∷↠ done) rB

adequate (lit B k ⦅ Nil ⦆) {d = dconst k'} 𝕋T rb G ⟨ refl , refl ⟩ =
  inj₂ ⟨ const B k , ⟨ (λ κ → refl ∷↠ done) , refl ⟩ ⟩

adequate (pair-op ⦅ L ,, M ,, Nil ⦆) {T} {n} {ρ} {γ} 𝕋T ⟨ rL , ⟨ rM , _ ⟩ ⟩ G w∈ =
  step₁ (λ κ → refl) (ℂ-bind {F = λ X → ⟦ M ⟧[ T ] ρ ≫= λ Y → pairD ⟨ X , ⟨ Y , ptt ⟩ ⟩} (pairL M γ) (λ d → adequate L 𝕋T rL G) w∈
    λ v₁ all₁ w w∈₁ → step₁ (λ κ → refl) (ℂ-bind {F = λ Y → pairD ⟨ ⌊ ⟦ L ⟧[ T ] ρ ⌋ , ⟨ Y , ptt ⟩ ⟩} (pairR v₁) (λ d → adequate M 𝕋T rM G) w∈₁
    λ { v₂ all₂ ⦅ u₁ , u₂ ⦆ ⟨ u₁∈ , u₂∈ ⟩ → inj₂ ⟨ pair v₁ v₂ , ⟨ (λ κ → refl ∷↠ done) , ⟨ all₁ u₁ u₁∈ , all₂ u₂ u₂∈ ⟩ ⟩ ⟩ }))

adequate (fst-op ⦅ M ,, Nil ⦆) {T} {n} {ρ} {γ} 𝕋T ⟨ rM , _ ⟩ G w∈ =
  step₁ (λ κ → refl) (ℂ-bind {F = λ X → checked prod X (carD ⟨ X , ptt ⟩)} fstK (λ d → adequate M 𝕋T rM G) w∈ FST)
  where
  FST : ∀ v → (∀ d → d ∈ ⌊ ⟦ M ⟧[ T ] ρ ⌋ → 𝕍 d v) → ∀ w → w ∈ checked prod ⌊ ⟦ M ⟧[ T ] ρ ⌋ (carD ⟨ ⌊ ⟦ M ⟧[ T ] ρ ⌋ , ptt ⟩)
    → ℂ w (λ κ → ret v (fstK κ))
  FST v all w (inj₁ ⟨ refl , bad ⟩) = ℂ-stop (λ κ → proj₁ (nonpair-stop v (bad-kind all bad) κ)) refl
  FST v all w (inj₂ ⟨ b , p∈ ⟩) with v | all _ p∈
  ... | pair v₁ v₂ | ⟨ r , _ ⟩ = inj₂ ⟨ v₁ , ⟨ (λ κ → refl ∷↠ done) , r ⟩ ⟩

adequate (snd-op ⦅ M ,, Nil ⦆) {T} {n} {ρ} {γ} 𝕋T ⟨ rM , _ ⟩ G w∈ =
  step₁ (λ κ → refl) (ℂ-bind {F = λ X → checked prod X (cdrD ⟨ X , ptt ⟩)} sndK (λ d → adequate M 𝕋T rM G) w∈ SND)
  where
  SND : ∀ v → (∀ d → d ∈ ⌊ ⟦ M ⟧[ T ] ρ ⌋ → 𝕍 d v) → ∀ w → w ∈ checked prod ⌊ ⟦ M ⟧[ T ] ρ ⌋ (cdrD ⟨ ⌊ ⟦ M ⟧[ T ] ρ ⌋ , ptt ⟩)
    → ℂ w (λ κ → ret v (sndK κ))
  SND v all w (inj₁ ⟨ refl , bad ⟩) = ℂ-stop (λ κ → proj₂ (nonpair-stop v (bad-kind all bad) κ)) refl
  SND v all w (inj₂ ⟨ a , p∈ ⟩) with v | all _ p∈
  ... | pair v₁ v₂ | ⟨ _ , r ⟩ = inj₂ ⟨ v₂ , ⟨ (λ κ → refl ∷↠ done) , r ⟩ ⟩

adequate (tuple m ⦅ args ⦆) {γ = γ} 𝕋T rb G w∈ =
  step₁ (λ κ → refl) (tuple-ℂ args 𝕋T rb G [] w∈ TUP)
  where
  TUP : ∀ vs Xs → length vs ≡ m → (∀ j d → d ∈ nthD Xs j → 𝕍At j d vs) → ∀ w → w ∈ 𝒯 m Xs
    → ℂ w (λ κ → ret (tup (reverse (reverseAcc [] vs))) κ)
  TUP vs Xs len rs w w∈ rewrite reverse-involutive vs = inj₂ ⟨ tup vs , ⟨ (λ κ → done) , T' Xs vs len rs w w∈ ⟩ ⟩
    where
    T' : ∀ {m} (Ys : Results (𝒫 Value) (replicate m ■)) vs → length vs ≡ m
      → (∀ j d → d ∈ nthD Ys j → 𝕍At j d vs) → ∀ w → w ∈ 𝒯 m Ys → 𝕍 w (tup vs)
    T' {zero} Ys [] refl rs ⟨⟩ _ = refl
    T' {suc m} Ys vs len rs (tup[ i ] d) ⟨ refl , ⟨ d∈ , _ ⟩ ⟩ = rs i d d∈

adequate (get {m} i ⦅ M ,, Nil ⦆) {T} {n} {ρ} {γ} 𝕋T ⟨ rM , _ ⟩ G w∈ =
  step₁ (λ κ → refl) (ℂ-bind {F = λ X → checked (tup m) X (projD i ⟨ X , ptt ⟩)} (getK i) (λ d → adequate M 𝕋T rM G) w∈ GET)
  where
  X = ⌊ ⟦ M ⟧[ T ] ρ ⌋
  GET : ∀ v → (∀ d → d ∈ X → 𝕍 d v) → ∀ w → w ∈ checked (tup m) X (projD i ⟨ X , ptt ⟩)
    → ℂ w (λ κ → ret v (getK i κ))
  GET v all w (inj₁ ⟨ refl , bad ⟩) = ℂ-stop (nottup-stop i v (bad-kind all bad)) refl
  GET v all w (inj₂ t∈) with v | all _ t∈
  ... | tup vs | r with 𝕍At-proj i _ vs r
  ...   | ⟨ u , ⟨ p , r' ⟩ ⟩ = inj₂ ⟨ u , ⟨ (λ κ → cong (λ m → ret? m κ) p ∷↠ done) , r' ⟩ ⟩

adequate (inl-op ⦅ M ,, Nil ⦆) {T} {n} {ρ} 𝕋T ⟨ rM , _ ⟩ G w∈ =
  step₁ (λ κ → refl) (ℂ-bind {F = λ X → inlD ⟨ X , ptt ⟩} inlK (λ d → adequate M 𝕋T rM G) w∈
    λ { v all (left d) d∈ → inj₂ ⟨ inl v , ⟨ (λ κ → refl ∷↠ done) , all d d∈ ⟩ ⟩ })

adequate (inr-op ⦅ M ,, Nil ⦆) {T} {n} {ρ} 𝕋T ⟨ rM , _ ⟩ G w∈ =
  step₁ (λ κ → refl) (ℂ-bind {F = λ X → inrD ⟨ X , ptt ⟩} inrK (λ d → adequate M 𝕋T rM G) w∈
    λ { v all (right d) d∈ → inj₂ ⟨ inr v , ⟨ (λ κ → refl ∷↠ done) , all d d∈ ⟩ ⟩ })

adequate (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) {T} {n} {ρ} {γ} 𝕋T ⟨ rL , ⟨ rM , ⟨ rN , _ ⟩ ⟩ ⟩ G w∈ =
  step₁ (λ κ → refl) (ℂ-bind {F = λ X → checked inj X (𝒞 ⟨ X ⇂ ValPayload , ⟨ F₁ , ⟨ F₂ , ptt ⟩ ⟩ ⟩)} (caseK M N γ) (λ d → adequate L 𝕋T rL G) w∈ CASE)
  where
  X = ⌊ ⟦ L ⟧[ T ] ρ ⌋
  F₁ = λ Z → ⟦ M ⟧[ T ] (Z • ρ)
  F₂ = λ Z → ⟦ N ⟧[ T ] (Z • ρ)
  CASE : ∀ v → (∀ d → d ∈ X → 𝕍 d v) → ∀ w → w ∈ checked inj X (𝒞 ⟨ X ⇂ ValPayload , ⟨ F₁ , ⟨ F₂ , ptt ⟩ ⟩ ⟩)
    → ℂ w (λ κ → ret v (caseK M N γ κ))
  CASE v all w (inj₁ ⟨ refl , bad ⟩) = ℂ-stop (notinj-stop v (bad-kind all bad) M N γ) refl
  CASE v all w (inj₂ (inj₁ ⟨ u , ⟨ U , ⟨ allL , ⟨ w∈′ , _ ⟩ ⟩ ⟩ ⟩)) with 𝕍-left v (all _ (proj₁ (allL u (here refl))))
  ... | ⟨ v' , refl ⟩ = step₁ (λ κ → refl) (adequate M 𝕋T rM (𝔾-ext (u ∷ U) v' G
                          (all→𝕍s (u ∷ U) (λ d d∈ → all (left d) (proj₁ (allL d d∈))))) w∈′)
  CASE v all w (inj₂ (inj₂ ⟨ u , ⟨ U , ⟨ allR , ⟨ w∈′ , _ ⟩ ⟩ ⟩ ⟩)) with 𝕍-right v (all _ (proj₁ (allR u (here refl))))
  ... | ⟨ v' , refl ⟩ = step₁ (λ κ → refl) (adequate N 𝕋T rN (𝔾-ext (u ∷ U) v' G
                          (all→𝕍s (u ∷ U) (λ d d∈ → all (right d) (proj₁ (allR d d∈))))) w∈′)

adequate (prim p ⦅ L ,, M ,, Nil ⦆) {T} {n} {ρ} {γ} 𝕋T ⟨ rL , ⟨ rM , _ ⟩ ⟩ G w∈ =
  step₁ (λ κ → refl) (ℂ-bind {F = λ X → ⟦ M ⟧[ T ] ρ ≫= λ Y → K X Y} (primL p M γ) (λ d → adequate L 𝕋T rL G) w∈
    λ v allL w w∈′ → step₁ (λ κ → refl) (ℂ-bind {F = K X} (primR p v) (λ d → adequate M 𝕋T rM G) w∈′
      (PRIM v allL)))
  where
  K = λ X Y → checked (base Int) X (checked (base Int) Y (primD p ⟨ X , ⟨ Y , ptt ⟩ ⟩))
  X = ⌊ ⟦ L ⟧[ T ] ρ ⌋
  Y = ⌊ ⟦ M ⟧[ T ] ρ ⌋
  PRIM : ∀ v → (∀ d → d ∈ X → 𝕍 d v) → ∀ u → (∀ d → d ∈ Y → 𝕍 d u) → ∀ w
    → w ∈ K X Y → ℂ w (λ κ → ret u (primR p v κ))
  PRIM v allL u allM w (inj₁ ⟨ refl , bad ⟩) =
    ℂ-stop (λ κ → cong (λ m → ret? m κ) (cong (map out) (δ?-nothing₁ p (obs v) (obs u) (notint-obs v (bad-kind allL bad))))) refl
  PRIM v allL u allM w (inj₂ (inj₁ ⟨ refl , bad ⟩)) =
    ℂ-stop (λ κ → cong (λ m → ret? m κ) (cong (map out) (δ?-nothing₂ p (obs v) (obs u) (notint-obs u (bad-kind allM bad))))) refl
  PRIM v allL u allM w (inj₂ (inj₂ ⟨ n , ⟨ m , ⟨ n∈ , ⟨ m∈ , refl ⟩ ⟩ ⟩ ⟩)) with allL _ n∈ | allM _ m∈
  ... | refl | refl = inj₂ ⟨ out (δ p n m) , ⟨ (λ κ → refl ∷↠ done) , 𝕍-out (δ p n m) ⟩ ⟩

adequate (let-op ⦅ M ,, ⟩ N ,, Nil ⦆) {T} {n} {ρ} {γ} 𝕋T ⟨ rM , ⟨ rN , _ ⟩ ⟩ G w∈ =
  step₁ (λ κ → refl) (ℂ-bind {F = λ X → ⋆ ⟨ Λᵐ ⟨ F , ptt ⟩ , ⟨ X , ptt ⟩ ⟩} (letK N γ) (λ d → adequate M 𝕋T rM G)
    (proj₁ (letᵐ-unfold {⟦ M ⟧[ T ] ρ} {F}) _ w∈)
    λ { v all w ⟨ V , ⟨ ⟨ ⟨ w∈′ , _ ⟩ , _ ⟩ , ⟨ V⊆ , _ ⟩ ⟩ ⟩ →
        step₁ (λ κ → refl) (adequate N 𝕋T rN (𝔾-ext V v G (all→𝕍s V (λ d d∈ → all d (V⊆ d d∈)))) w∈′) })
  where F = λ Y → ⟦ N ⟧[ T ] (Y • ρ)

{- The table of the program --------------------------------------------------------}

tab : ∀ Ns → Ns ⊑ ds → DefsWF Ns → 𝕋 (length Ns) (table Ns)
tab (N ∷ Ns) p wf k k< d d∈ with k ≟ length Ns
tab (N ∷ Ns) p wf k k< d d∈ | no k≢ with m≤n⇒m<n∨m≡n (≤-pred k<)
... | inj₁ lt = tab Ns (∷-⊑ p) (proj₂ wf) k lt d d∈
... | inj₂ eq = ⊥-elim (k≢ eq)
tab (N ∷ Ns) p wf .(length Ns) k< ν d∈ | yes refl = tt
tab (N ∷ Ns) p wf .(length Ns) k< (X ↦ ν) d∈ | yes refl = tt
tab (N ∷ Ns) p wf .(length Ns) k< (X ↦ (Y ↦ w)) ⟨ ⟨ ⟨ w∈ , _ ⟩ , _ ⟩ , _ ⟩ | yes refl =
  λ e Xe a Ya → ⟨ N , ⟨ global-⊑ p , adequate N (tab Ns (∷-⊑ p) (proj₂ wf)) (proj₁ wf) (G e Xe a Ya) w∈ ⟩ ⟩
  where
  G : ∀ e → 𝕍s X e → ∀ a → 𝕍s Y a → 𝔾 (mem Y • mem X • (λ _ → init)) (a ∷ e ∷ [])
  G e Xe a Ya zero d d∈ = inj₂ ⟨ a , ⟨ refl , 𝕍s-∈ Y Ya d∈ ⟩ ⟩
  G e Xe a Ya (suc zero) d d∈ = inj₂ ⟨ e , ⟨ refl , 𝕍s-∈ X Xe d∈ ⟩ ⟩
  G e Xe a Ya (suc (suc x)) d refl = inj₁ ⟨ refl , refl ⟩

{- the empty environment: every variable is unbound -}
𝔾-[] : 𝔾 (λ _ → init) []
𝔾-[] x d refl = inj₁ ⟨ refl , refl ⟩

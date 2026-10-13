{-

  Adequacy of the graph model with errors for the Clos5 machine: every
  element of the denotation of a well-formed program is witnessed by a
  run of the machine, for the table ds of its global definitions, and ω
  by a run that stops with an error.

  As for ISWIM (Adequacy/GraphErr/LogRel.agda), a logical relation 𝕍 d v
  relates denotational values to machine values, by recursion on d, and
  ℝ d γ M relates ω to a term that stops with an error and any other
  value to a term that evaluates to a related value. As for Clos5 in the
  graph model (Adequacy/Clos5LogRel.agda), a code pointer is related to
  the entries Λ X. Λ Y. … of code: X ↦ (Y ↦ w) is related to code k when
  the machine finds a definition at k whose body, run on values related
  to all of X and Y, is related to w by ℝ, so it may stop with an error.
  The fundamental lemma (adequate) assumes that the table is related to
  the code pointers it refers to (𝕋), and the table of the program is
  (tab), by induction on the definitions.

  The fundamental lemma has a case for each error of each operator, in
  the machine's evaluation order: a call evaluates its code, environment
  and argument and only then checks that the code is a code pointer (the
  late check, callᵉ); fst and snd fail on a non-pair. An unbound variable
  denotes {ω} and errs in the machine, so environments are related on
  all variables (𝔾), and no scoping condition is needed.

-}

open import Data.List using (List; []; _∷_; length; replicate; reverse)
open import Language.Clos5 using (AST)

module proof.Adequacy.GraphErr.Clos5LogRel (ds : List AST) where

open import Framework.Primitives using (Int)
open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.Domain
  using (Value; _↦_; ν; ω; ⦅_,_⦆; tup[_]_; left; right; ⟨⟩)
  renaming (const to dconst)
open import proof.Framework.GraphModel.OpsBase using (nthD)
open import proof.Framework.GraphModel.ErrorOps
  using (val∈; wrong; errs; vals; IsFun; IsInj; IsTup; IsPair; NoErr; inlᵉ-inv; inrᵉ-inv; Λᵉ-fun)
open import proof.Semantics.GraphErr.Prim using (IsInt) renaming (out to dout)
open import Language.Prim using (int; bool; δ)
open import Language.Clos5 hiding (AST)
open import Semantics.GraphErr.Clos5 using (Table; ⟦_⟧[_]; ⟦_⟧₊[_]; table; init)
import proof.Framework.GraphModel.Env
open import Framework.Syntax.SyntaxUtil using (_,,_; Nil; ⟩_,,_)
open import proof.Framework.ListUtil
open import Semantics.Observation
open import Semantics.CEK.Clos5
open import proof.Semantics.CEK.Smallstep using (next; stop)
open import proof.Compiler.GlobalizeTable using (_⊑_; ∷-⊑; global-⊑)
open import proof.Adequacy.Common using (ShapeOf; ShapeAt; has-length→length; length→has-length)
open import proof.Adequacy.GraphErr.LogRel using (head≢ω; δ?-nothing₁; δ?-nothing₂)
open import proof.Adequacy.GraphErr.Clos5WF using (DefsWF; RB; RB-args)
open import proof.Adequacy.GraphErr.Clos5Common ds

open import Data.Bool using (true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin; zero; suc)
open import Data.List.Base using (reverseAcc)
open import Data.List.Properties using (reverse-involutive)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing; map)
open import Data.Nat using (ℕ; zero; suc; _<_; _≟_; s≤s)
open import Data.Nat.Properties using (≤-pred; m≤n⇒m<n∨m≡n)
open import Data.Product using (_×_; Σ-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (yes; no; ¬_)

VEnv : Set₁
VEnv = proof.Framework.GraphModel.Env.Env Value

{- Evaluation, and errors ---------------------------------------------------------}

infix 4 _⊢_⇓_
_⊢_⇓_ : Env → AST → Val → Set
γ ⊢ M ⇓ v = ∀ κ → eval M γ κ ↠ ret v κ

{- a run from s to a state that stops with an error -}
Err : State → Set
Err s = Σ[ t ∈ State ] s ↠ t × step ds t ≡ stop o-error

infix 4 _⊢_⇓err
_⊢_⇓err : Env → AST → Set
γ ⊢ M ⇓err = ∀ κ → Err (eval M γ κ)

{- an error after a run -}
_⟫_ : ∀ {s s'} → s ↠ s' → Err s' → Err s
σ ⟫ ⟨ t , ⟨ τ , st ⟩ ⟩ = ⟨ t , ⟨ σ ++↠ τ , st ⟩ ⟩
infixr 4 _⟫_

{- a state that stops with an error right away -}
here! : ∀ {s} → step ds s ≡ stop o-error → Err s
here! {s} st = ⟨ s , ⟨ done , st ⟩ ⟩

⇓-det : ∀ {γ M v₁ v₂} → γ ⊢ M ⇓ v₁ → γ ⊢ M ⇓ v₂ → v₁ ≡ v₂
⇓-det {v₁ = v₁} {v₂} e₁ e₂ with ↠-final-det (e₁ halt) (e₂ halt) refl refl
... | refl = refl

obs-ok : ∀ v → stop {S = State} (obs v) ≡ stop o-error → ⊥
obs-ok (code k) ()
obs-ok (pair v w) ()
obs-ok (const B k) ()
obs-ok (tup vs) ()
obs-ok (inl v) ()
obs-ok (inr v) ()

{- a term does not both evaluate to a value and stop with an error -}
⇓-⇓err : ∀ {γ M v} → γ ⊢ M ⇓ v → γ ⊢ M ⇓err → ⊥
⇓-⇓err {v = v} e er with er halt
... | ⟨ t , ⟨ τ , st ⟩ ⟩ with ↠-final-det (e halt) τ refl st
... | refl = obs-ok v st

{- The logical relation ----------------------------------------------------------}

𝕍 : Value → Val → Set
𝕍code : List Value → Value → ℕ → Set
𝕍s : List Value → Val → Set
𝕍At : ∀ {n} → Fin n → Value → List Val → Set
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

{- the entries of code, Λ X. Λ Y. N: the machine runs definition k -}
𝕍code X ν k = ⊤
𝕍code X (Y ↦ w) k = ∀ e → 𝕍s X e → ∀ a → 𝕍s Y a
  → Σ[ N ∈ AST ] global ds k ≡ just N × ℝ w (a ∷ e ∷ []) N
𝕍code X _ k = ⊥

𝕍s [] v = ⊤
𝕍s (d ∷ V) v = 𝕍 d v × 𝕍s V v

𝕍At {suc n} zero d (v ∷ vs) = length vs ≡ n × 𝕍 d v
𝕍At (suc i) d (v ∷ vs) = 𝕍At i d vs
𝕍At _ d [] = ⊥

{- ω means an error, any other value a related value -}
ℝ d γ M = (d ≡ ω × γ ⊢ M ⇓err) ⊎ (Σ[ v ∈ Val ] γ ⊢ M ⇓ v × 𝕍 d v)

𝕍-ω : ∀ {v} → 𝕍 ω v → ⊥
𝕍-ω {code k} ()
𝕍-ω {pair v w} ()
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

length-obs-list : ∀ vs → length (obs-list vs) ≡ length vs
length-obs-list [] = refl
length-obs-list (v ∷ vs) = cong suc (length-obs-list vs)

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

{- The machine's checks fail on related values of the wrong kind ----------------}

{- calling a value related to a non-function is an error -}
notcode-stop : ∀ d v → 𝕍 d v → ¬ IsFun d → ∀ a e κ → step ds (ret a (appA v e κ)) ≡ stop o-error
notcode-stop ν (code k) r nf a e κ = ⊥-elim (nf tt)
notcode-stop (X ↦ w) (code k) r nf a e κ = ⊥-elim (nf tt)
notcode-stop (dconst k') (code k) () nf a e κ
notcode-stop d (pair v w) r nf a e κ = refl
notcode-stop d (const B k) r nf a e κ = refl
notcode-stop d (tup vs) r nf a e κ = refl
notcode-stop d (inl v) r nf a e κ = refl
notcode-stop d (inr v) r nf a e κ = refl

{- fst and snd of a value related to a non-pair are errors -}
nonpair-stop : ∀ d v → 𝕍 d v → ¬ IsPair d → ∀ κ
  → step ds (ret v (fstK κ)) ≡ stop o-error × step ds (ret v (sndK κ)) ≡ stop o-error
nonpair-stop ⦅ u₁ , u₂ ⦆ (pair v w) r np κ = ⊥-elim (np tt)
nonpair-stop (dconst k') (pair v w) () np κ
nonpair-stop d (code k) r np κ = ⟨ refl , refl ⟩
nonpair-stop d (const B k) r np κ = ⟨ refl , refl ⟩
nonpair-stop d (tup vs) r np κ = ⟨ refl , refl ⟩
nonpair-stop d (inl v) r np κ = ⟨ refl , refl ⟩
nonpair-stop d (inr v) r np κ = ⟨ refl , refl ⟩

{- a projection from a value related to a non-tuple of n components is an
   error -}
proj-nothing-[] : ∀ {n} (i : Fin n) → proj {A = Val} i [] ≡ nothing
proj-nothing-[] zero = refl
proj-nothing-[] (suc i) = refl

nottup-stop : ∀ {n} (i : Fin n) d v → 𝕍 d v → ¬ IsTup n d → ∀ κ → step ds (ret v (getK i κ)) ≡ stop o-error
nottup-stop i ⟨⟩ (tup []) refl nt κ = cong (λ m → ret? m κ) (proj-nothing-[] i)
nottup-stop {n} i (tup[_]_ {m} j d) (tup vs) r nt κ with proj i vs in p
... | just v = ⊥-elim (nt (trans (sym (𝕍At-length j d vs r)) (proj-just-length i vs p)))
... | nothing = refl
nottup-stop i (dconst k') (tup vs) () nt κ
nottup-stop i d (code k) r nt κ = refl
nottup-stop i d (pair v w) r nt κ = refl
nottup-stop i d (const B k) r nt κ = refl
nottup-stop i d (inl v) r nt κ = refl
nottup-stop i d (inr v) r nt κ = refl

{- a case on a value related to a non-injection is an error -}
notinj-stop : ∀ d v → 𝕍 d v → ¬ IsInj d → ∀ M N γ κ → step ds (ret v (caseK M N γ κ)) ≡ stop o-error
notinj-stop (left d) (inl v) r ni M N γ κ = ⊥-elim (ni tt)
notinj-stop (right d) (inr v) r ni M N γ κ = ⊥-elim (ni tt)
notinj-stop (dconst k') (inl v) () ni M N γ κ
notinj-stop (dconst k') (inr v) () ni M N γ κ
notinj-stop d (code k) r ni M N γ κ = refl
notinj-stop d (pair v w) r ni M N γ κ = refl
notinj-stop d (const B k) r ni M N γ κ = refl
notinj-stop d (tup vs) r ni M N γ κ = refl

{- a value related to a non-integer is not observed as an integer -}
notint-obs : ∀ d v → 𝕍 d v → ¬ IsInt d → ∀ n → obs v ≢ o-const Int n
notint-obs (dconst k) (const B k) refl ni n refl = ni tt
notint-obs d (code k) r ni n ()
notint-obs d (pair v w) r ni n ()
notint-obs d (tup vs) r ni n ()
notint-obs d (inl v) r ni n ()
notint-obs d (inr v) r ni n ()

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

Evals : Env → List AST → List Val → Set
Evals γ = Pointwise (λ M v → γ ⊢ M ⇓ v)

tuple-run : ∀ {γ κ} acc Ms vs → Evals γ Ms vs
  → tuple-next acc Ms γ κ ↠ ret (tup (reverse (reverseAcc acc vs))) κ
tuple-run acc [] [] [] = done
tuple-run {γ} {κ} acc (M ∷ Ms) (v ∷ vs) (e ∷ es) =
  e (tupK acc Ms γ κ) ++↠ (refl ∷↠ tuple-run (v ∷ acc) Ms vs es)

{- The fundamental lemma ----------------------------------------------------------}

adequate : ∀ M {T n ρ γ d} → 𝕋 n T → RB n M → 𝔾 ρ γ → d ∈ ⟦ M ⟧[ T ] ρ → ℝ d γ M
adequate-args : ∀ {k} (args : Args (replicate k ■)) {T n ρ γ} → 𝕋 n T → RB-args n args
  → 𝔾 ρ γ → vals k (⟦ args ⟧₊[ T ] ρ)
  → Σ[ vs ∈ List Val ] Evals γ (args→list args) vs × length vs ≡ k
      × (∀ j d → d ∈ nthD (⟦ args ⟧₊[ T ] ρ) j → 𝕍At j d vs)
tuple-err : ∀ {k} (args : Args (replicate k ■)) {T n ρ γ} → 𝕋 n T → RB-args n args
  → 𝔾 ρ γ → errs k (⟦ args ⟧₊[ T ] ρ)
  → ∀ acc κ → Err (tuple-next acc (args→list args) γ κ)

adequate (` x) {γ = γ} 𝕋T rb G d∈ with G x _ d∈
... | inj₁ ⟨ refl , look ⟩ = inj₁ ⟨ refl , (λ κ → here! (cong (λ m → ret? m κ) look)) ⟩
... | inj₂ ⟨ v , ⟨ look , r ⟩ ⟩ = inj₂ ⟨ v , ⟨ (λ κ → cong (λ m → ret? m κ) look ∷↠ done) , r ⟩ ⟩

adequate (fun-ref k ⦅ Nil ⦆) {d = d} 𝕋T k< G d∈ =
  inj₂ ⟨ code k , ⟨ (λ κ → refl ∷↠ done) , 𝕋T k k< d d∈ ⟩ ⟩

adequate (app ⦅ L ,, M ,, N ,, Nil ⦆) 𝕋T rb G (inj₁ ⟨ [] , ⟨ _ , ⟨ _ , ⟨ _ , ⟨ _ , ⟨ ne , _ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩) =
  ⊥-elim (ne refl)
adequate (app ⦅ L ,, M ,, N ,, Nil ⦆) 𝕋T rb G (inj₁ ⟨ _ ∷ _ , ⟨ [] , ⟨ _ , ⟨ _ , ⟨ _ , ⟨ _ , ⟨ ne , _ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩) =
  ⊥-elim (ne refl)
adequate (app ⦅ L ,, M ,, N ,, Nil ⦆) {γ = γ} {d} 𝕋T ⟨ rL , ⟨ rM , ⟨ rN , _ ⟩ ⟩ ⟩ G
    (inj₁ ⟨ v₀ ∷ V , ⟨ u₀ ∷ U , ⟨ f∈ , ⟨ V⊆ , ⟨ U⊆ , ⟨ _ , ⟨ _ , ⟨ nV , nU ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩)
    with conv (adequate L 𝕋T rL G f∈) (λ ())
       | conv (adequate M 𝕋T rM G (V⊆ v₀ (here refl))) (head≢ω nV)
       | conv (adequate N 𝕋T rN G (U⊆ u₀ (here refl))) (head≢ω nU)
... | ⟨ code j , ⟨ eL , relL ⟩ ⟩ | ⟨ e , ⟨ eM , _ ⟩ ⟩ | ⟨ a , ⟨ eN , _ ⟩ ⟩
    with relL e (all→𝕍s (v₀ ∷ V) (λ d' d'∈ → collectℝ eM (adequate M 𝕋T rM G (V⊆ d' d'∈))))
              a (all→𝕍s (u₀ ∷ U) (λ d' d'∈ → collectℝ eN (adequate N 𝕋T rN G (U⊆ d' d'∈))))
... | ⟨ B , ⟨ g , inj₁ ⟨ refl , eB ⟩ ⟩ ⟩ =
  inj₁ ⟨ refl , (λ κ → (refl ∷↠ eL (appF M N γ κ) ++↠ refl ∷↠ eM (appE (code j) N γ κ)
                         ++↠ refl ∷↠ eN (appA (code j) e κ) ++↠ cong (λ m → call m a e κ) g ∷↠ done)
                        ⟫ eB κ) ⟩
... | ⟨ B , ⟨ g , inj₂ ⟨ v , ⟨ eB , r ⟩ ⟩ ⟩ ⟩ =
  inj₂ ⟨ v , ⟨ (λ κ → refl ∷↠ eL (appF M N γ κ) ++↠ refl ∷↠ eM (appE (code j) N γ κ)
                  ++↠ refl ∷↠ eN (appA (code j) e κ) ++↠ cong (λ m → call m a e κ) g ∷↠ eB κ)
        , r ⟩ ⟩
adequate (app ⦅ L ,, M ,, N ,, Nil ⦆) {γ = γ} 𝕋T ⟨ rL , ⟨ rM , ⟨ rN , _ ⟩ ⟩ ⟩ G
    (inj₂ ⟨ refl , inj₁ (inj₁ ω∈) ⟩) =
  inj₁ ⟨ refl , (λ κ → (refl ∷↠ done) ⟫ err (adequate L 𝕋T rL G ω∈) (appF M N γ κ)) ⟩
adequate (app ⦅ L ,, M ,, N ,, Nil ⦆) {γ = γ} 𝕋T ⟨ rL , ⟨ rM , ⟨ rN , _ ⟩ ⟩ ⟩ G
    (inj₂ ⟨ refl , inj₁ (inj₂ ⟨ ⟨ f , ⟨ f∈ , f≢ ⟩ ⟩ , inj₁ ω∈ ⟩) ⟩)
    with conv (adequate L 𝕋T rL G f∈) f≢
... | ⟨ fv , ⟨ eL , _ ⟩ ⟩ =
  inj₁ ⟨ refl , (λ κ → (refl ∷↠ eL (appF M N γ κ) ++↠ refl ∷↠ done)
                        ⟫ err (adequate M 𝕋T rM G ω∈) (appE fv N γ κ)) ⟩
adequate (app ⦅ L ,, M ,, N ,, Nil ⦆) {γ = γ} 𝕋T ⟨ rL , ⟨ rM , ⟨ rN , _ ⟩ ⟩ ⟩ G
    (inj₂ ⟨ refl , inj₁ (inj₂ ⟨ ⟨ f , ⟨ f∈ , f≢ ⟩ ⟩ , inj₂ ⟨ ⟨ m , ⟨ m∈ , m≢ ⟩ ⟩ , inj₁ ω∈ ⟩ ⟩) ⟩)
    with conv (adequate L 𝕋T rL G f∈) f≢ | conv (adequate M 𝕋T rM G m∈) m≢
... | ⟨ fv , ⟨ eL , _ ⟩ ⟩ | ⟨ e , ⟨ eM , _ ⟩ ⟩ =
  inj₁ ⟨ refl , (λ κ → (refl ∷↠ eL (appF M N γ κ) ++↠ refl ∷↠ eM (appE fv N γ κ) ++↠ refl ∷↠ done)
                        ⟫ err (adequate N 𝕋T rN G ω∈) (appA fv e κ)) ⟩
adequate (app ⦅ L ,, M ,, N ,, Nil ⦆) 𝕋T rb G (inj₂ ⟨ refl , inj₁ (inj₂ ⟨ _ , inj₂ ⟨ _ , inj₂ ⟨ _ , () ⟩ ⟩ ⟩) ⟩)
adequate (app ⦅ L ,, M ,, N ,, Nil ⦆) {γ = γ} 𝕋T ⟨ rL , ⟨ rM , ⟨ rN , _ ⟩ ⟩ ⟩ G
    (inj₂ ⟨ refl , inj₂ ⟨ ⟨ f , ⟨ f∈ , ⟨ f≢ , nf ⟩ ⟩ ⟩ , ⟨ ⟨ m , ⟨ m∈ , m≢ ⟩ ⟩ , ⟨ n , ⟨ n∈ , n≢ ⟩ ⟩ ⟩ ⟩ ⟩)
    with conv (adequate L 𝕋T rL G f∈) f≢ | conv (adequate M 𝕋T rM G m∈) m≢
       | conv (adequate N 𝕋T rN G n∈) n≢
... | ⟨ fv , ⟨ eL , r ⟩ ⟩ | ⟨ e , ⟨ eM , _ ⟩ ⟩ | ⟨ a , ⟨ eN , _ ⟩ ⟩ =
  inj₁ ⟨ refl , (λ κ → (refl ∷↠ eL (appF M N γ κ) ++↠ refl ∷↠ eM (appE fv N γ κ)
                         ++↠ refl ∷↠ eN (appA fv e κ))
                        ⟫ here! (notcode-stop f fv r nf a e κ)) ⟩

adequate (lit B k ⦅ Nil ⦆) {d = dconst k'} 𝕋T rb G ⟨ refl , refl ⟩ =
  inj₂ ⟨ const B k , ⟨ (λ κ → refl ∷↠ done) , refl ⟩ ⟩

adequate (pair-op ⦅ L ,, M ,, Nil ⦆) {γ = γ} {d = ⦅ u₁ , u₂ ⦆} 𝕋T ⟨ rL , ⟨ rM , _ ⟩ ⟩ G
    ⟨ u₁∈ , ⟨ u₂∈ , ⟨ u₁≢ , u₂≢ ⟩ ⟩ ⟩
    with conv (adequate L 𝕋T rL G u₁∈) u₁≢ | conv (adequate M 𝕋T rM G u₂∈) u₂≢
... | ⟨ v₁ , ⟨ e₁ , r₁ ⟩ ⟩ | ⟨ v₂ , ⟨ e₂ , r₂ ⟩ ⟩ =
  inj₂ ⟨ pair v₁ v₂ , ⟨ (λ κ → refl ∷↠ e₁ (pairL M γ κ) ++↠ refl ∷↠ e₂ (pairR v₁ κ) ++↠ refl ∷↠ done)
                    , ⟨ r₁ , r₂ ⟩ ⟩ ⟩
adequate (pair-op ⦅ L ,, M ,, Nil ⦆) {γ = γ} {d = ω} 𝕋T ⟨ rL , ⟨ rM , _ ⟩ ⟩ G (inj₁ ω∈) =
  inj₁ ⟨ refl , (λ κ → (refl ∷↠ done) ⟫ err (adequate L 𝕋T rL G ω∈) (pairL M γ κ)) ⟩
adequate (pair-op ⦅ L ,, M ,, Nil ⦆) {γ = γ} {d = ω} 𝕋T ⟨ rL , ⟨ rM , _ ⟩ ⟩ G
    (inj₂ ⟨ ⟨ u , ⟨ u∈ , u≢ ⟩ ⟩ , inj₁ ω∈ ⟩)
    with conv (adequate L 𝕋T rL G u∈) u≢
... | ⟨ v₁ , ⟨ e₁ , _ ⟩ ⟩ =
  inj₁ ⟨ refl , (λ κ → (refl ∷↠ e₁ (pairL M γ κ) ++↠ refl ∷↠ done)
                        ⟫ err (adequate M 𝕋T rM G ω∈) (pairR v₁ κ)) ⟩
adequate (pair-op ⦅ L ,, M ,, Nil ⦆) {d = ω} 𝕋T rb G (inj₂ ⟨ _ , inj₂ ⟨ _ , () ⟩ ⟩)

adequate (fst-op ⦅ M ,, Nil ⦆) {γ = γ} 𝕋T ⟨ rM , _ ⟩ G (inj₁ ⟨ u₂ , d∈ ⟩)
    with conv (adequate M 𝕋T rM G d∈) (λ ())
... | ⟨ pair v₁ v₂ , ⟨ e , ⟨ r , _ ⟩ ⟩ ⟩ =
  inj₂ ⟨ v₁ , ⟨ (λ κ → refl ∷↠ e (fstK κ) ++↠ refl ∷↠ done) , r ⟩ ⟩
adequate (fst-op ⦅ M ,, Nil ⦆) {γ = γ} 𝕋T ⟨ rM , _ ⟩ G (inj₂ ⟨ refl , inj₁ ω∈ ⟩) =
  inj₁ ⟨ refl , (λ κ → (refl ∷↠ done) ⟫ err (adequate M 𝕋T rM G ω∈) (fstK κ)) ⟩
adequate (fst-op ⦅ M ,, Nil ⦆) {γ = γ} 𝕋T ⟨ rM , _ ⟩ G (inj₂ ⟨ refl , inj₂ ⟨ u , ⟨ u∈ , ⟨ u≢ , np ⟩ ⟩ ⟩ ⟩)
    with conv (adequate M 𝕋T rM G u∈) u≢
... | ⟨ v , ⟨ e , r ⟩ ⟩ =
  inj₁ ⟨ refl , (λ κ → (refl ∷↠ e (fstK κ)) ⟫ here! (proj₁ (nonpair-stop u v r np κ))) ⟩

adequate (snd-op ⦅ M ,, Nil ⦆) {γ = γ} 𝕋T ⟨ rM , _ ⟩ G (inj₁ ⟨ u₁ , d∈ ⟩)
    with conv (adequate M 𝕋T rM G d∈) (λ ())
... | ⟨ pair v₁ v₂ , ⟨ e , ⟨ _ , r ⟩ ⟩ ⟩ =
  inj₂ ⟨ v₂ , ⟨ (λ κ → refl ∷↠ e (sndK κ) ++↠ refl ∷↠ done) , r ⟩ ⟩
adequate (snd-op ⦅ M ,, Nil ⦆) {γ = γ} 𝕋T ⟨ rM , _ ⟩ G (inj₂ ⟨ refl , inj₁ ω∈ ⟩) =
  inj₁ ⟨ refl , (λ κ → (refl ∷↠ done) ⟫ err (adequate M 𝕋T rM G ω∈) (sndK κ)) ⟩
adequate (snd-op ⦅ M ,, Nil ⦆) {γ = γ} 𝕋T ⟨ rM , _ ⟩ G (inj₂ ⟨ refl , inj₂ ⟨ u , ⟨ u∈ , ⟨ u≢ , np ⟩ ⟩ ⟩ ⟩)
    with conv (adequate M 𝕋T rM G u∈) u≢
... | ⟨ v , ⟨ e , r ⟩ ⟩ =
  inj₁ ⟨ refl , (λ κ → (refl ∷↠ e (sndK κ)) ⟫ here! (proj₂ (nonpair-stop u v r np κ))) ⟩

adequate (tuple n ⦅ args ⦆) {d = ω} 𝕋T rb G e =
  inj₁ ⟨ refl , (λ κ → (refl ∷↠ done) ⟫ tuple-err args 𝕋T rb G e [] κ) ⟩
adequate (tuple zero ⦅ Nil ⦆) {d = ⟨⟩} 𝕋T rb G tt = inj₂ ⟨ tup [] , ⟨ (λ κ → refl ∷↠ done) , refl ⟩ ⟩
adequate (tuple (suc n) ⦅ args ⦆) {γ = γ} {d = tup[ i ] d} 𝕋T rb G ⟨ refl , ⟨ d∈ , vs ⟩ ⟩
    with adequate-args args 𝕋T rb G vs
... | ⟨ ws , ⟨ es , ⟨ len , rs ⟩ ⟩ ⟩ =
  inj₂ ⟨ tup ws
       , ⟨ (λ κ → refl ∷↠ subst (λ us → tuple-next [] (args→list args) γ κ ↠ ret (tup us) κ)
                                 (reverse-involutive ws) (tuple-run [] (args→list args) ws es))
         , rs i d d∈ ⟩ ⟩

adequate (get i ⦅ M ,, Nil ⦆) {γ = γ} 𝕋T ⟨ rM , _ ⟩ G (inj₁ t∈) with conv (adequate M 𝕋T rM G t∈) (λ ())
... | ⟨ tup vs , ⟨ e , r ⟩ ⟩ with 𝕍At-proj i _ vs r
... | ⟨ v , ⟨ p , r' ⟩ ⟩ =
  inj₂ ⟨ v , ⟨ (λ κ → refl ∷↠ e (getK i κ) ++↠ cong (λ m → ret? m κ) p ∷↠ done) , r' ⟩ ⟩
adequate (get i ⦅ M ,, Nil ⦆) {γ = γ} 𝕋T ⟨ rM , _ ⟩ G (inj₂ ⟨ refl , inj₁ ω∈ ⟩) =
  inj₁ ⟨ refl , (λ κ → (refl ∷↠ done) ⟫ err (adequate M 𝕋T rM G ω∈) (getK i κ)) ⟩
adequate (get i ⦅ M ,, Nil ⦆) {γ = γ} 𝕋T ⟨ rM , _ ⟩ G (inj₂ ⟨ refl , inj₂ ⟨ e , ⟨ e∈ , ⟨ e≢ , nt ⟩ ⟩ ⟩ ⟩)
    with conv (adequate M 𝕋T rM G e∈) e≢
... | ⟨ v , ⟨ eM , r ⟩ ⟩ =
  inj₁ ⟨ refl , (λ κ → (refl ∷↠ eM (getK i κ)) ⟫ here! (nottup-stop i e v r nt κ)) ⟩

adequate (inl-op ⦅ M ,, Nil ⦆) {γ = γ} {d} 𝕋T ⟨ rM , _ ⟩ G d∈ with inlᵉ-inv d d∈
... | inj₁ ⟨ v' , ⟨ refl , ⟨ v'∈ , v'≢ ⟩ ⟩ ⟩ with conv (adequate M 𝕋T rM G v'∈) v'≢
...   | ⟨ v , ⟨ e , r ⟩ ⟩ = inj₂ ⟨ inl v , ⟨ (λ κ → refl ∷↠ e (inlK κ) ++↠ refl ∷↠ done) , r ⟩ ⟩
adequate (inl-op ⦅ M ,, Nil ⦆) {γ = γ} {d} 𝕋T ⟨ rM , _ ⟩ G d∈ | inj₂ ⟨ refl , ω∈ ⟩ =
  inj₁ ⟨ refl , (λ κ → (refl ∷↠ done) ⟫ err (adequate M 𝕋T rM G ω∈) (inlK κ)) ⟩

adequate (inr-op ⦅ M ,, Nil ⦆) {γ = γ} {d} 𝕋T ⟨ rM , _ ⟩ G d∈ with inrᵉ-inv d d∈
... | inj₁ ⟨ v' , ⟨ refl , ⟨ v'∈ , v'≢ ⟩ ⟩ ⟩ with conv (adequate M 𝕋T rM G v'∈) v'≢
...   | ⟨ v , ⟨ e , r ⟩ ⟩ = inj₂ ⟨ inr v , ⟨ (λ κ → refl ∷↠ e (inrK κ) ++↠ refl ∷↠ done) , r ⟩ ⟩
adequate (inr-op ⦅ M ,, Nil ⦆) {γ = γ} {d} 𝕋T ⟨ rM , _ ⟩ G d∈ | inj₂ ⟨ refl , ω∈ ⟩ =
  inj₁ ⟨ refl , (λ κ → (refl ∷↠ done) ⟫ err (adequate M 𝕋T rM G ω∈) (inrK κ)) ⟩

adequate (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) {γ = γ} 𝕋T ⟨ rL , ⟨ rM , ⟨ rN , _ ⟩ ⟩ ⟩ G
    (inj₁ ⟨ u , ⟨ U , ⟨ allL , ⟨ w∈ , _ ⟩ ⟩ ⟩ ⟩)
    with conv (adequate L 𝕋T rL G (allL u (here refl))) (λ ())
... | ⟨ inl w , ⟨ eL , _ ⟩ ⟩
    with adequate M 𝕋T rM (𝔾-ext (u ∷ U) w G
           (all→𝕍s (u ∷ U) (λ d' d'∈ → collectℝ eL (adequate L 𝕋T rL G (allL d' d'∈))))) w∈
... | inj₁ ⟨ refl , eM ⟩ =
  inj₁ ⟨ refl , (λ κ → (refl ∷↠ eL (caseK M N γ κ) ++↠ refl ∷↠ done) ⟫ eM κ) ⟩
... | inj₂ ⟨ v , ⟨ eM , r ⟩ ⟩ =
  inj₂ ⟨ v , ⟨ (λ κ → refl ∷↠ eL (caseK M N γ κ) ++↠ refl ∷↠ eM κ) , r ⟩ ⟩
adequate (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) {γ = γ} 𝕋T ⟨ rL , ⟨ rM , ⟨ rN , _ ⟩ ⟩ ⟩ G
    (inj₂ (inj₁ ⟨ u , ⟨ U , ⟨ allR , ⟨ w∈ , _ ⟩ ⟩ ⟩ ⟩))
    with conv (adequate L 𝕋T rL G (allR u (here refl))) (λ ())
... | ⟨ inr w , ⟨ eL , _ ⟩ ⟩
    with adequate N 𝕋T rN (𝔾-ext (u ∷ U) w G
           (all→𝕍s (u ∷ U) (λ d' d'∈ → collectℝ eL (adequate L 𝕋T rL G (allR d' d'∈))))) w∈
... | inj₁ ⟨ refl , eN ⟩ =
  inj₁ ⟨ refl , (λ κ → (refl ∷↠ eL (caseK M N γ κ) ++↠ refl ∷↠ done) ⟫ eN κ) ⟩
... | inj₂ ⟨ v , ⟨ eN , r ⟩ ⟩ =
  inj₂ ⟨ v , ⟨ (λ κ → refl ∷↠ eL (caseK M N γ κ) ++↠ refl ∷↠ eN κ) , r ⟩ ⟩
adequate (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) {γ = γ} 𝕋T ⟨ rL , _ ⟩ G (inj₂ (inj₂ ⟨ refl , inj₁ ω∈ ⟩)) =
  inj₁ ⟨ refl , (λ κ → (refl ∷↠ done) ⟫ err (adequate L 𝕋T rL G ω∈) (caseK M N γ κ)) ⟩
adequate (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) {γ = γ} 𝕋T ⟨ rL , _ ⟩ G
    (inj₂ (inj₂ ⟨ refl , inj₂ ⟨ e , ⟨ e∈ , ⟨ e≢ , ni ⟩ ⟩ ⟩ ⟩))
    with conv (adequate L 𝕋T rL G e∈) e≢
... | ⟨ v , ⟨ eL , r ⟩ ⟩ =
  inj₁ ⟨ refl , (λ κ → (refl ∷↠ eL (caseK M N γ κ)) ⟫ here! (notinj-stop e v r ni M N γ κ)) ⟩

adequate (prim p ⦅ L ,, M ,, Nil ⦆) {γ = γ} 𝕋T ⟨ rL , ⟨ rM , _ ⟩ ⟩ G
    (inj₁ ⟨ n , ⟨ m , ⟨ n∈ , ⟨ m∈ , refl ⟩ ⟩ ⟩ ⟩)
    with conv (adequate L 𝕋T rL G n∈) (λ ()) | conv (adequate M 𝕋T rM G m∈) (λ ())
... | ⟨ _ , ⟨ eL , refl ⟩ ⟩ | ⟨ _ , ⟨ eM , refl ⟩ ⟩ =
  inj₂ ⟨ out (δ p n m)
       , ⟨ (λ κ → refl ∷↠ eL (primL p M γ κ) ++↠ refl ∷↠ eM (primR p (const Int n) κ) ++↠ refl ∷↠ done)
         , 𝕍-out (δ p n m) ⟩ ⟩
adequate (prim p ⦅ L ,, M ,, Nil ⦆) {γ = γ} 𝕋T ⟨ rL , ⟨ rM , _ ⟩ ⟩ G (inj₂ ⟨ refl , inj₁ (inj₁ ω∈) ⟩) =
  inj₁ ⟨ refl , (λ κ → (refl ∷↠ done) ⟫ err (adequate L 𝕋T rL G ω∈) (primL p M γ κ)) ⟩
adequate (prim p ⦅ L ,, M ,, Nil ⦆) {γ = γ} 𝕋T ⟨ rL , ⟨ rM , _ ⟩ ⟩ G
    (inj₂ ⟨ refl , inj₁ (inj₂ ⟨ ⟨ d , ⟨ d∈ , d≢ ⟩ ⟩ , inj₁ ω∈ ⟩) ⟩)
    with conv (adequate L 𝕋T rL G d∈) d≢
... | ⟨ v , ⟨ eL , _ ⟩ ⟩ =
  inj₁ ⟨ refl , (λ κ → (refl ∷↠ eL (primL p M γ κ) ++↠ refl ∷↠ done)
                        ⟫ err (adequate M 𝕋T rM G ω∈) (primR p v κ)) ⟩
adequate (prim p ⦅ L ,, M ,, Nil ⦆) 𝕋T rb G (inj₂ ⟨ refl , inj₁ (inj₂ ⟨ _ , inj₂ ⟨ _ , () ⟩ ⟩) ⟩)
adequate (prim p ⦅ L ,, M ,, Nil ⦆) {γ = γ} 𝕋T ⟨ rL , ⟨ rM , _ ⟩ ⟩ G
    (inj₂ ⟨ refl , inj₂ (inj₁ ⟨ ⟨ d , ⟨ d∈ , ⟨ d≢ , ni ⟩ ⟩ ⟩ , ⟨ e , ⟨ e∈ , e≢ ⟩ ⟩ ⟩) ⟩)
    with conv (adequate L 𝕋T rL G d∈) d≢ | conv (adequate M 𝕋T rM G e∈) e≢
... | ⟨ v , ⟨ eL , r ⟩ ⟩ | ⟨ w , ⟨ eM , _ ⟩ ⟩ =
  inj₁ ⟨ refl , (λ κ → (refl ∷↠ eL (primL p M γ κ) ++↠ refl ∷↠ eM (primR p v κ))
                 ⟫ here! (cong (λ m → ret? m κ) (cong (map out) (δ?-nothing₁ p (obs v) (obs w) (notint-obs d v r ni))))) ⟩
adequate (prim p ⦅ L ,, M ,, Nil ⦆) {γ = γ} 𝕋T ⟨ rL , ⟨ rM , _ ⟩ ⟩ G
    (inj₂ ⟨ refl , inj₂ (inj₂ ⟨ ⟨ d , ⟨ d∈ , d≢ ⟩ ⟩ , ⟨ e , ⟨ e∈ , ⟨ e≢ , ni ⟩ ⟩ ⟩ ⟩) ⟩)
    with conv (adequate L 𝕋T rL G d∈) d≢ | conv (adequate M 𝕋T rM G e∈) e≢
... | ⟨ v , ⟨ eL , _ ⟩ ⟩ | ⟨ w , ⟨ eM , r ⟩ ⟩ =
  inj₁ ⟨ refl , (λ κ → (refl ∷↠ eL (primL p M γ κ) ++↠ refl ∷↠ eM (primR p v κ))
                 ⟫ here! (cong (λ m → ret? m κ) (cong (map out) (δ?-nothing₂ p (obs v) (obs w) (notint-obs e w r ni))))) ⟩

adequate (let-op ⦅ M ,, ⟩ N ,, Nil ⦆) 𝕋T rb G (inj₁ ⟨ [] , ⟨ _ , ⟨ _ , ⟨ ne , _ ⟩ ⟩ ⟩ ⟩) = ⊥-elim (ne refl)
adequate (let-op ⦅ M ,, ⟩ N ,, Nil ⦆) {γ = γ} 𝕋T ⟨ rM , ⟨ rN , _ ⟩ ⟩ G
    (inj₁ ⟨ u ∷ U , ⟨ ⟨ w∈ , _ ⟩ , ⟨ V⊆ , ⟨ _ , noe ⟩ ⟩ ⟩ ⟩)
    with conv (adequate M 𝕋T rM G (V⊆ u (here refl))) (head≢ω noe)
... | ⟨ vM , ⟨ eM , _ ⟩ ⟩
    with adequate N 𝕋T rN (𝔾-ext (u ∷ U) vM G
           (all→𝕍s (u ∷ U) (λ d' d'∈ → collectℝ eM (adequate M 𝕋T rM G (V⊆ d' d'∈))))) w∈
... | inj₁ ⟨ refl , eN ⟩ = inj₁ ⟨ refl , (λ κ → (refl ∷↠ eM (letK N γ κ) ++↠ refl ∷↠ done) ⟫ eN κ) ⟩
... | inj₂ ⟨ v , ⟨ eN , r ⟩ ⟩ = inj₂ ⟨ v , ⟨ (λ κ → refl ∷↠ eM (letK N γ κ) ++↠ refl ∷↠ eN κ) , r ⟩ ⟩
adequate (let-op ⦅ M ,, ⟩ N ,, Nil ⦆) 𝕋T rb G (inj₂ ⟨ refl , inj₁ () ⟩)
adequate (let-op ⦅ M ,, ⟩ N ,, Nil ⦆) 𝕋T rb G (inj₂ ⟨ refl , inj₂ (inj₁ ⟨ d' , ⟨ d'∈ , ⟨ _ , nf ⟩ ⟩ ⟩) ⟩) =
  ⊥-elim (nf (Λᵉ-fun d' d'∈))
adequate (let-op ⦅ M ,, ⟩ N ,, Nil ⦆) {γ = γ} 𝕋T ⟨ rM , _ ⟩ G (inj₂ ⟨ refl , inj₂ (inj₂ ⟨ _ , ω∈ ⟩) ⟩) =
  inj₁ ⟨ refl , (λ κ → (refl ∷↠ done) ⟫ err (adequate M 𝕋T rM G ω∈) (letK N γ κ)) ⟩

adequate-args {zero} Nil 𝕋T rb G vs = ⟨ [] , ⟨ [] , ⟨ refl , (λ ()) ⟩ ⟩ ⟩
adequate-args {suc k} (M ,, args) 𝕋T ⟨ rM , rs ⟩ G vs
    with conv (adequate M 𝕋T rM G (proj₁ (proj₂ (vs zero)))) (proj₂ (proj₂ (vs zero)))
       | adequate-args args 𝕋T rs G (λ j → vs (suc j))
... | ⟨ v , ⟨ e , _ ⟩ ⟩ | ⟨ ws , ⟨ es , ⟨ len , rels ⟩ ⟩ ⟩ =
  ⟨ v ∷ ws , ⟨ e ∷ es , ⟨ cong suc len , R ⟩ ⟩ ⟩
  where
  R : ∀ j d → d ∈ nthD (⟦ M ,, args ⟧₊[ _ ] _) j → 𝕍At j d (v ∷ ws)
  R zero d d∈ = ⟨ len , collectℝ e (adequate M 𝕋T rM G d∈) ⟩
  R (suc j) d d∈ = rels j d d∈

tuple-err {suc k} (M ,, args) {γ = γ} 𝕋T ⟨ rM , rs ⟩ G (inj₁ ω∈) acc κ =
  err (adequate M 𝕋T rM G ω∈) (tupK acc (args→list args) γ κ)
tuple-err {suc k} (M ,, args) {γ = γ} 𝕋T ⟨ rM , rs ⟩ G (inj₂ ⟨ ⟨ d , ⟨ d∈ , d≢ ⟩ ⟩ , e ⟩) acc κ
    with conv (adequate M 𝕋T rM G d∈) d≢
... | ⟨ v , ⟨ eM , _ ⟩ ⟩ =
  (eM (tupK acc (args→list args) γ κ) ++↠ (refl ∷↠ done))
    ⟫ tuple-err args 𝕋T rs G e (v ∷ acc) κ

{- The table of the program --------------------------------------------------------}

tab : ∀ Ns → Ns ⊑ ds → DefsWF Ns → 𝕋 (length Ns) (table Ns)
tab (N ∷ Ns) p wf k k< d d∈ with k ≟ length Ns
tab (N ∷ Ns) p wf k k< d d∈ | no k≢ with m≤n⇒m<n∨m≡n (≤-pred k<)
... | inj₁ lt = tab Ns (∷-⊑ p) (proj₂ wf) k lt d d∈
... | inj₂ eq = ⊥-elim (k≢ eq)
tab (N ∷ Ns) p wf .(length Ns) k< ν d∈ | yes refl = tt
tab (N ∷ Ns) p wf .(length Ns) k< (X ↦ ν) d∈ | yes refl = tt
tab (N ∷ Ns) p wf .(length Ns) k< (X ↦ (Y ↦ w)) ⟨ ⟨ w∈ , _ ⟩ , _ ⟩ | yes refl = rel
  where
  rel : 𝕍 (X ↦ (Y ↦ w)) (code (length Ns))
  rel e Xe a Ya =
    ⟨ N , ⟨ global-⊑ p , adequate N (tab Ns (∷-⊑ p) (proj₂ wf)) (proj₁ wf) G w∈ ⟩ ⟩
    where
    G : 𝔾 (mem Y • mem X • (λ _ → init)) (a ∷ e ∷ [])
    G zero d d∈ = inj₂ ⟨ a , ⟨ refl , 𝕍s-∈ Y Ya d∈ ⟩ ⟩
    G (suc zero) d d∈ = inj₂ ⟨ e , ⟨ refl , 𝕍s-∈ X Xe d∈ ⟩ ⟩
    G (suc (suc x)) d refl = inj₁ ⟨ refl , refl ⟩

{- the empty environment: every variable is unbound -}
𝔾-[] : 𝔾 (λ _ → init) []
𝔾-[] x d refl = inj₁ ⟨ refl , refl ⟩

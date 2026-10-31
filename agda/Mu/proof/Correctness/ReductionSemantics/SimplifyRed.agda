{-

  Correctness of the simplify pass (FPC → FPC) by a simulation of
  the target by the source, between their reduction semantics, as for
  the untyped simplify (proof/Correctness/Reduction/SimplifyRed.agda; see
  the design note in Semantics/Reduction/Smallstep.agda).

  The target takes fewer steps than the source: simplify did some of the
  source's reductions ahead of time, under binders. So each target step
  is answered by one or more source steps (the source catches up with
  the reductions simplify did, then takes the same step), and the
  forward simulation goes from the target to the source; Equivalent is
  symmetric.

  The relation (_≽_, the source on the left) is a congruence, closed
  under substitution, with more rules. step: the source may take a
  reduction step first. letλ: a β redex is related to a target let.
  letλv, letv: a β redex or a let is related to a let of a value that
  simplify kept, whose body it simplified knowing the value, through
  the bodies after β. Since simplify reduces under binders, the source's
  steps are steps on open terms, where a variable stands for a value
  (_⟶_, on the values SV); in a closed term they are steps of the
  reduction semantics (closed-red). Typed terms are closed by
  construction, so the source needs no scope invariant.

  The main lemma (simp-ok): if what simp knows of each variable x is
  true of τ x (the source's substitution) after υ (the target's), then
  what simp E M says of M is true of sub τ M (Desc): sub τ M is related
  to its term after υ, and to its known value. A known value of a
  term, a value K with sub τ M ≽ sub υ K, is reached by the source:
  sub τ M steps to a value related to sub υ K (eval-sv). A known function
  λ N is reached by the source too, as λ N closed by a substitution of
  whose variables N's Facts are true (KDesc), so a call that simplify
  inlined is the source reaching the function, then β. A value bound by
  copy propagation keeps what is known of it: by determinism (det), the
  source reaches the same value either way (desc-to).

-}

module Mu.proof.Correctness.ReductionSemantics.SimplifyRed where

open import Framework.Primitives using (Int)
import Language.Prim as Pr
open import Mu.Language.Type hiding (_[_])
open import Mu.Language.FPC
open import Mu.Framework.AllUtil using (All; []; _∷_; lookup; All₂; lookup₂)
open import Mu.proof.Compiler.SimplifyFacts as P
  using (Info; _∣_; term; known; Known; Facts; self; info; under; known-as; shift-info; shift-known;
         simp; simps; simp-app; lam?; is-lam; other; simp-call; simp-let; size; inline-size; inline-fuel;
         simp-get; simp-case; simp-prim; simp-unfold; simplify; small; value; component; branch; unfolded; int-of;
         prim-term; SV; SVs; value-sv; small-sv; sv-trav; svs-trav; sv-ren; prim-term-sv; svs-lookup;
         int-inv; comp-inv; branch-inl; branch-inr; unfold-inv)
open import Semantics.Observation
open import proof.Framework.Reduction Obs o-error hiding (Each; []; _∷_)
open import Mu.proof.Framework.ReductionAll Obs o-error using (ans-∷; Each; []; _∷_)
open import Semantics.Reduction.Smallstep using (Equivalent)
open import proof.Framework.Simulation Obs using (equiv-sym)
import Mu.proof.Semantics.ReductionSemantics.FPC as S
open S using (sub; ren; tmK; tmL)
import Relation.Binary.Construct.Closure.ReflexiveTransitive as RT
open RT using (Star; gmap)

open import Data.Bool using (true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Integer using (_≟_)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; zero; suc; _≤ᵇ_)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂)
open import Relation.Nullary using (does)

{- Substitution ----------------------------------------------------------------}

Sb : Ctx → Ctx → Set
Sb Γ Δ = ∀ {B} → Γ ∋ B → Tm Δ B

{- substituting V for variable 0 of an open term -}
_[_]ₒ : ∀ {Γ A B} → Tm (A ∷ Γ) B → Tm Γ A → Tm Γ B
N [ V ]ₒ = sub (V S.• `_) N

{- a term, weakened and then substituted -}
wk-[]ₒ : ∀ {Γ A C} (V : Tm Γ A) (W : Tm Γ C) → ren S V [ W ]ₒ ≡ V
wk-[]ₒ V W = trans (S.ren-trav tmK {τ = `_} (λ _ → refl) V) (S.sub-id (λ _ → refl) V)

{- under a binder, then for the bound variable -}
exts-[]ₒ : ∀ {Γ Δ A C} (σ : Sb Γ Δ) (W : Tm Δ C) (N : Tm (C ∷ Γ) A) → sub (S.exts tmK σ) N [ W ]ₒ ≡ sub (W S.• σ) N
exts-[]ₒ σ W = S.trav-sub tmL λ { Z → refl ; (S x) → wk-[]ₒ (σ x) W }

sub-[] : ∀ {Γ Δ A B} (τ : Sb Γ Δ) (N : Tm (A ∷ Γ) B) V → sub τ (N [ V ]ₒ) ≡ sub (S.exts tmK τ) N [ sub τ V ]ₒ
sub-[] τ N V = trans (S.trav-sub tmL (λ { Z → refl ; (S x) → refl }) N) (sym (exts-[]ₒ τ (sub τ V) N))

{- in a closed term, the semantics' substitution -}
closed-[] : ∀ {A B} (N : Tm (A ∷ []) B) V → N S.[ V ] ≡ N [ V ]ₒ
closed-[] N V = trans (cong (S._[ V ]) (sym (S.sub-id (S.sub-id-exts (λ _ → refl)) N))) (S.exts-[] `_ V N)

rename-sub : ∀ {Γ Δ A} (r : ∀ {B} → Γ ∋ B → Δ ∋ B) (M : Tm Γ A) → ren r M ≡ sub (λ x → ` r x) M
rename-sub r M = trans (sym (S.sub-id (λ _ → refl) (ren r M))) (S.ren-trav tmK (λ _ → refl) M)

sub-lookup : ∀ {Γ Δ Δ' A} (τ : Sb Γ Δ) (Ks : All (Tm Γ) Δ') (i : Δ' ∋ A) → sub τ (lookup Ks i) ≡ lookup (S.travs tmK τ Ks) i
sub-lookup τ (K ∷ Ks) Z = refl
sub-lookup τ (K ∷ Ks) (S i) = sub-lookup τ Ks i

sub-prim-term : ∀ {Γ Δ} (τ : Sb Γ Δ) p n m → sub τ (prim-term p n m) ≡ prim-term p n m
sub-prim-term τ Pr.sub n m = refl
sub-prim-term τ Pr.eq n m with does (n ≟ m)
... | true = refl
... | false = refl

prim-term-out : ∀ p n m → S.out {[]} p n m ≡ prim-term p n m
prim-term-out Pr.sub n m = refl
prim-term-out Pr.eq n m = refl

{- Reduction of open terms, where a variable stands for a value ---------------}

infix 4 _⟶_ _⟶s_ _⟶*_
data _⟶_ {Γ} : ∀ {A} → Tm Γ A → Tm Γ A → Set
data _⟶s_ {Γ} : ∀ {Δ} → All (Tm Γ) Δ → All (Tm Γ) Δ → Set

data _⟶_ {Γ} where
  β : ∀ {A B} {N : Tm (A ∷ Γ) B} {V} → SV V → app (lam N) V ⟶ N [ V ]ₒ
  app₁ : ∀ {A B} {L L' : Tm Γ (A ⇒ B)} {M} → L ⟶ L' → app L M ⟶ app L' M
  app₂ : ∀ {A B} {N : Tm (A ∷ Γ) B} {M M'} → M ⟶ M' → app (lam N) M ⟶ app (lam N) M'
  tuple : ∀ {Δ} {Ms Ms' : All (Tm Γ) Δ} → Ms ⟶s Ms' → tuple Ms ⟶ tuple Ms'
  get : ∀ {Δ A} {i : Δ ∋ A} {Ks} → SVs Ks → get i (tuple Ks) ⟶ lookup Ks i
  get₁ : ∀ {Δ A} {i : Δ ∋ A} {M M'} → M ⟶ M' → get i M ⟶ get i M'
  inl₁ : ∀ {A B} {M M' : Tm Γ A} → M ⟶ M' → inl {B = B} M ⟶ inl M'
  inr₁ : ∀ {A B} {M M' : Tm Γ B} → M ⟶ M' → inr {A = A} M ⟶ inr M'
  case-l : ∀ {A B C} {V : Tm Γ A} {M : Tm (A ∷ Γ) C} {N : Tm (B ∷ Γ) C} → SV V → case (inl V) M N ⟶ M [ V ]ₒ
  case-r : ∀ {A B C} {V : Tm Γ B} {M : Tm (A ∷ Γ) C} {N : Tm (B ∷ Γ) C} → SV V → case (inr V) M N ⟶ N [ V ]ₒ
  case₁ : ∀ {A B C} {L L' : Tm Γ (A ⊹ B)} {M : Tm (A ∷ Γ) C} {N} → L ⟶ L' → case L M N ⟶ case L' M N
  prim : ∀ {p n m} → prim p (lit Int n) (lit Int m) ⟶ prim-term p n m
  prim₁ : ∀ {p L L' M} → L ⟶ L' → prim p L M ⟶ prim p L' M
  prim₂ : ∀ {p V M M'} → SV V → M ⟶ M' → prim p V M ⟶ prim p V M'
  letβ : ∀ {A B} {V : Tm Γ A} {N : Tm (A ∷ Γ) B} → SV V → let′ V N ⟶ N [ V ]ₒ
  let₁ : ∀ {A B} {M M' : Tm Γ A} {N : Tm (A ∷ Γ) B} → M ⟶ M' → let′ M N ⟶ let′ M' N
  fold₁ : ∀ {A} {M M' : Tm Γ (unroll A)} → M ⟶ M' → fold {A = A} M ⟶ fold M'
  unfoldβ : ∀ {A} {V : Tm Γ (unroll A)} → SV V → unfold (fold {A = A} V) ⟶ V
  unfold₁ : ∀ {A} {M M' : Tm Γ (μ A)} → M ⟶ M' → unfold M ⟶ unfold M'

data _⟶s_ {Γ} where
  here : ∀ {A Δ} {M M' : Tm Γ A} {Ms : All (Tm Γ) Δ} → M ⟶ M' → (M ∷ Ms) ⟶s (M' ∷ Ms)
  there : ∀ {A Δ} {V : Tm Γ A} {Ms Ms' : All (Tm Γ) Δ} → SV V → Ms ⟶s Ms' → (V ∷ Ms) ⟶s (V ∷ Ms')

_⟶*_ : ∀ {Γ A} → Tm Γ A → Tm Γ A → Set
_⟶*_ = Star _⟶_

{- a value does not step -}
sv-nostep : ∀ {Γ A} {V M : Tm Γ A} → SV V → V ⟶ M → ⊥
svs-nostep : ∀ {Γ Δ} {Ms Ms' : All (Tm Γ) Δ} → SVs Ms → Ms ⟶s Ms' → ⊥
sv-nostep (P.tuple vs) (tuple s) = svs-nostep vs s
sv-nostep (P.inl v) (inl₁ s) = sv-nostep v s
sv-nostep (P.inr v) (inr₁ s) = sv-nostep v s
sv-nostep (P.fold v) (fold₁ s) = sv-nostep v s
svs-nostep (v P.∷ vs) (here s) = sv-nostep v s
svs-nostep (v P.∷ vs) (there _ s) = svs-nostep vs s

{- reduction is deterministic -}
det : ∀ {Γ A} {M M₁ M₂ : Tm Γ A} → M ⟶ M₁ → M ⟶ M₂ → M₁ ≡ M₂
dets : ∀ {Γ Δ} {Ms Ms₁ Ms₂ : All (Tm Γ) Δ} → Ms ⟶s Ms₁ → Ms ⟶s Ms₂ → Ms₁ ≡ Ms₂
det (β v) (β _) = refl
det (β v) (app₂ s) = ⊥-elim (sv-nostep v s)
det (app₂ s) (β v) = ⊥-elim (sv-nostep v s)
det (app₂ s) (app₂ s') = cong (app _) (det s s')
det (app₁ s) (app₁ s') = cong (λ X → app X _) (det s s')
det (app₁ s) (β _) = ⊥-elim (sv-nostep P.lam s)
det (app₁ s) (app₂ _) = ⊥-elim (sv-nostep P.lam s)
det (β _) (app₁ s) = ⊥-elim (sv-nostep P.lam s)
det (app₂ _) (app₁ s) = ⊥-elim (sv-nostep P.lam s)
det (tuple s) (tuple s') = cong tuple (dets s s')
det (get vs) (get _) = refl
det (get vs) (get₁ s) = ⊥-elim (sv-nostep (P.tuple vs) s)
det (get₁ s) (get vs) = ⊥-elim (sv-nostep (P.tuple vs) s)
det (get₁ s) (get₁ s') = cong (get _) (det s s')
det (inl₁ s) (inl₁ s') = cong inl (det s s')
det (inr₁ s) (inr₁ s') = cong inr (det s s')
det (case-l v) (case-l _) = refl
det (case-l v) (case₁ s) = ⊥-elim (sv-nostep (P.inl v) s)
det (case-r v) (case-r _) = refl
det (case-r v) (case₁ s) = ⊥-elim (sv-nostep (P.inr v) s)
det (case₁ s) (case-l v) = ⊥-elim (sv-nostep (P.inl v) s)
det (case₁ s) (case-r v) = ⊥-elim (sv-nostep (P.inr v) s)
det (case₁ s) (case₁ s') = cong (λ X → case X _ _) (det s s')
det prim prim = refl
det prim (prim₁ s) = ⊥-elim (sv-nostep P.lit s)
det prim (prim₂ _ s) = ⊥-elim (sv-nostep P.lit s)
det (prim₁ s) prim = ⊥-elim (sv-nostep P.lit s)
det (prim₁ s) (prim₁ s') = cong (λ X → prim _ X _) (det s s')
det (prim₁ s) (prim₂ v _) = ⊥-elim (sv-nostep v s)
det (prim₂ _ s) prim = ⊥-elim (sv-nostep P.lit s)
det (prim₂ v _) (prim₁ s) = ⊥-elim (sv-nostep v s)
det (prim₂ _ s) (prim₂ _ s') = cong (prim _ _) (det s s')
det (letβ _) (letβ _) = refl
det (letβ v) (let₁ s) = ⊥-elim (sv-nostep v s)
det (let₁ s) (letβ v) = ⊥-elim (sv-nostep v s)
det (let₁ s) (let₁ s') = cong (λ X → let′ X _) (det s s')
det (fold₁ s) (fold₁ s') = cong fold (det s s')
det (unfoldβ _) (unfoldβ _) = refl
det (unfoldβ v) (unfold₁ s) = ⊥-elim (sv-nostep (P.fold v) s)
det (unfold₁ s) (unfoldβ v) = ⊥-elim (sv-nostep (P.fold v) s)
det (unfold₁ s) (unfold₁ s') = cong unfold (det s s')
dets (here s) (here s') = cong (_∷ _) (det s s')
dets (here s) (there v _) = ⊥-elim (sv-nostep v s)
dets (there v _) (here s) = ⊥-elim (sv-nostep v s)
dets (there _ s) (there _ s') = cong (_ ∷_) (dets s s')

star-det : ∀ {Γ A} {X W W' : Tm Γ A} → X ⟶* W → X ⟶* W' → SV W → SV W' → W ≡ W'
star-det RT.ε RT.ε _ _ = refl
star-det RT.ε (s RT.◅ _) w _ = ⊥-elim (sv-nostep w s)
star-det (s RT.◅ _) RT.ε _ w = ⊥-elim (sv-nostep w s)
star-det (s RT.◅ σ) (s' RT.◅ σ') w w' with det s s'
... | refl = star-det σ σ' w w'

{- closed values reduce to val -}
sv-red : ∀ {A} {V : Tm [] A} → SV V → S.red V ≡ val
svs-red : ∀ {Δ} {Vs : All (Tm []) Δ} → SVs Vs → S.reds Vs ≡ val
sv-red P.lam = refl
sv-red P.lit = refl
sv-red (P.tuple vs) rewrite svs-red vs = refl
sv-red (P.inl v) rewrite sv-red v = refl
sv-red (P.inr v) rewrite sv-red v = refl
sv-red (P.fold v) rewrite sv-red v = refl
svs-red P.[] = refl
svs-red (v P.∷ vs) rewrite sv-red v | svs-red vs = refl

each-svs : ∀ {Δ} {Vs : All (Tm []) Δ} → Each SV Vs → SVs Vs
each-svs [] = P.[]
each-svs (v ∷ vs) = v P.∷ each-svs vs

{- substitution by values commutes with steps -}
sub-⟶ : ∀ {Γ Δ A} {τ : Sb Γ Δ} {M M' : Tm Γ A} → (∀ {B} (x : Γ ∋ B) → SV (τ x)) → M ⟶ M' → sub τ M ⟶ sub τ M'
sub-⟶s : ∀ {Γ Δ Δ'} {τ : Sb Γ Δ} {Ms Ms' : All (Tm Γ) Δ'} → (∀ {B} (x : Γ ∋ B) → SV (τ x)) → Ms ⟶s Ms'
  → S.travs tmK τ Ms ⟶s S.travs tmK τ Ms'
sub-⟶ {τ = τ} h (β {N = N} {V} v) rewrite sub-[] τ N V = β (sv-trav h v)
sub-⟶ h (app₁ s) = app₁ (sub-⟶ h s)
sub-⟶ h (app₂ s) = app₂ (sub-⟶ h s)
sub-⟶ h (tuple s) = tuple (sub-⟶s h s)
sub-⟶ {τ = τ} h (get {i = i} {Ks} vs) rewrite sub-lookup τ Ks i = get (svs-trav h vs)
sub-⟶ h (get₁ s) = get₁ (sub-⟶ h s)
sub-⟶ h (inl₁ s) = inl₁ (sub-⟶ h s)
sub-⟶ h (inr₁ s) = inr₁ (sub-⟶ h s)
sub-⟶ {τ = τ} h (case-l {V = V} {M} v) rewrite sub-[] τ M V = case-l (sv-trav h v)
sub-⟶ {τ = τ} h (case-r {V = V} {N = N} v) rewrite sub-[] τ N V = case-r (sv-trav h v)
sub-⟶ h (case₁ s) = case₁ (sub-⟶ h s)
sub-⟶ {τ = τ} h (prim {p} {n} {m}) rewrite sub-prim-term τ p n m = prim
sub-⟶ h (prim₁ s) = prim₁ (sub-⟶ h s)
sub-⟶ h (prim₂ v s) = prim₂ (sv-trav h v) (sub-⟶ h s)
sub-⟶ {τ = τ} h (letβ {V = V} {N} v) rewrite sub-[] τ N V = letβ (sv-trav h v)
sub-⟶ h (let₁ s) = let₁ (sub-⟶ h s)
sub-⟶ h (fold₁ s) = fold₁ (sub-⟶ h s)
sub-⟶ h (unfoldβ v) = unfoldβ (sv-trav h v)
sub-⟶ h (unfold₁ s) = unfold₁ (sub-⟶ h s)
sub-⟶s h (here s) = here (sub-⟶ h s)
sub-⟶s h (there v s) = there (sv-trav h v) (sub-⟶s h s)

{- in a closed term, a step of the reduction semantics -}
closed-red : ∀ {A} {M M' : Tm [] A} → M ⟶ M' → S.red M ≡ to M'
closed-reds : ∀ {Δ} {Ms Ms' : All (Tm []) Δ} → Ms ⟶s Ms' → S.reds Ms ≡ to Ms'
closed-red (β {N = N} {V} v) rewrite sv-red v = cong to (closed-[] N V)
closed-red (app₁ s) rewrite closed-red s = refl
closed-red (app₂ s) rewrite closed-red s = refl
closed-red (tuple s) rewrite closed-reds s = refl
closed-red (get vs) rewrite svs-red vs = refl
closed-red (get₁ s) rewrite closed-red s = refl
closed-red (inl₁ s) rewrite closed-red s = refl
closed-red (inr₁ s) rewrite closed-red s = refl
closed-red (case-l {V = V} {M} v) rewrite sv-red v = cong to (closed-[] M V)
closed-red (case-r {V = V} {N = N} v) rewrite sv-red v = cong to (closed-[] N V)
closed-red (case₁ s) rewrite closed-red s = refl
closed-red (prim {p} {n} {m}) = cong to (prim-term-out p n m)
closed-red (prim₁ s) rewrite closed-red s = refl
closed-red (prim₂ v s) rewrite sv-red v | closed-red s = refl
closed-red (letβ {V = V} {N} v) rewrite sv-red v = cong to (closed-[] N V)
closed-red (let₁ s) rewrite closed-red s = refl
closed-red (fold₁ s) rewrite closed-red s = refl
closed-red (unfoldβ v) rewrite sv-red v = refl
closed-red (unfold₁ s) rewrite closed-red s = refl
closed-reds (here s) rewrite closed-red s = refl
closed-reds (there v s) rewrite sv-red v | closed-reds s = refl

{- The relation on terms: the source on the left -------------------------------}

infix 4 _≽_
data _≽_ {Γ} : ∀ {A} → Tm Γ A → Tm Γ A → Set where
  var≽ : ∀ {A} {x : Γ ∋ A} → ` x ≽ ` x
  lam≽ : ∀ {A B} {N N' : Tm (A ∷ Γ) B} → N ≽ N' → lam N ≽ lam N'
  app≽ : ∀ {A B} {L L' : Tm Γ (A ⇒ B)} {M M'} → L ≽ L' → M ≽ M' → app L M ≽ app L' M'
  lit≽ : ∀ {B c} → lit B c ≽ lit B c
  tuple≽ : ∀ {Δ} {Ms Ms' : All (Tm Γ) Δ} → All₂ (λ M' M → M ≽ M') Ms' Ms → tuple Ms ≽ tuple Ms'
  get≽ : ∀ {Δ A} {i : Δ ∋ A} {M M'} → M ≽ M' → get i M ≽ get i M'
  inl≽ : ∀ {A B} {M M' : Tm Γ A} → M ≽ M' → inl {B = B} M ≽ inl M'
  inr≽ : ∀ {A B} {M M' : Tm Γ B} → M ≽ M' → inr {A = A} M ≽ inr M'
  case≽ : ∀ {A B C} {L L' : Tm Γ (A ⊹ B)} {M M' : Tm (A ∷ Γ) C} {N N'} → L ≽ L' → M ≽ M' → N ≽ N'
    → case L M N ≽ case L' M' N'
  prim≽ : ∀ {p L L' M M'} → L ≽ L' → M ≽ M' → prim p L M ≽ prim p L' M'
  {- the source steps first -}
  step : ∀ {A} {M M₁ M' : Tm Γ A} → M ⟶ M₁ → M₁ ≽ M' → M ≽ M'
  let≽ : ∀ {A B} {M M' : Tm Γ A} {N N' : Tm (A ∷ Γ) B} → M ≽ M' → N ≽ N' → let′ M N ≽ let′ M' N'
  {- a β redex for a let -}
  letλ≽ : ∀ {A B} {M M' : Tm Γ A} {N N' : Tm (A ∷ Γ) B} → M ≽ M' → N ≽ N' → app (lam N) M ≽ let′ M' N'
  {- a β redex or a let, for a let of a value that simplify kept: the
     bodies after β -}
  letλv≽ : ∀ {A B} {W V' : Tm Γ A} {N N' : Tm (A ∷ Γ) B} → SV W → W ≽ V' → N [ W ]ₒ ≽ N' [ V' ]ₒ
    → app (lam N) W ≽ let′ V' N'
  letv≽ : ∀ {A B} {W V' : Tm Γ A} {N N' : Tm (A ∷ Γ) B} → SV W → W ≽ V' → N [ W ]ₒ ≽ N' [ V' ]ₒ
    → let′ W N ≽ let′ V' N'
  fold≽ : ∀ {A} {M M' : Tm Γ (unroll A)} → M ≽ M' → fold {A = A} M ≽ fold M'
  unfold≽ : ∀ {A} {M M' : Tm Γ (μ A)} → M ≽ M' → unfold M ≽ unfold M'

{- the converse, for a simulation, which takes the simulated machine
   (here the target) first -}
R˘ : ∀ {Γ A} → Tm Γ A → Tm Γ A → Set
R˘ M' M = M ≽ M'

steps : ∀ {Γ A} {M M₁ M' : Tm Γ A} → M ⟶* M₁ → M₁ ≽ M' → M ≽ M'
steps RT.ε r = r
steps (s RT.◅ σ) r = step s (steps σ r)

{- Closure under substitution -------------------------------------------------}

module Kit (Pr : ∀ {Γ Δ} → Sb Γ Δ → Sb Γ Δ → Set) (p≽ : ∀ {Γ Δ} {τ υ : Sb Γ Δ} → Pr τ υ → ∀ {B} (x : Γ ∋ B) → τ x ≽ υ x)
  (pok : ∀ {Γ Δ} {τ υ : Sb Γ Δ} → Pr τ υ → ∀ {B} (x : Γ ∋ B) → SV (τ x))
  (pexts : ∀ {Γ Δ C} {τ υ : Sb Γ Δ} → Pr τ υ → Pr (S.exts tmK {B = C} τ) (S.exts tmK υ)) where

  ≽-sub : ∀ {Γ Δ A} {τ υ : Sb Γ Δ} {M M' : Tm Γ A} → Pr τ υ → M ≽ M' → sub τ M ≽ sub υ M'
  ≽-subs : ∀ {Γ Δ Δ'} {τ υ : Sb Γ Δ} {Ms Ms' : All (Tm Γ) Δ'} → Pr τ υ → All₂ R˘ Ms' Ms
    → All₂ R˘ (S.travs tmK υ Ms') (S.travs tmK τ Ms)
  ≽-sub p (var≽ {x = x}) = p≽ p x
  ≽-sub p (lam≽ r) = lam≽ (≽-sub (pexts p) r)
  ≽-sub p (app≽ r s) = app≽ (≽-sub p r) (≽-sub p s)
  ≽-sub p lit≽ = lit≽
  ≽-sub p (tuple≽ rs) = tuple≽ (≽-subs p rs)
  ≽-sub p (get≽ r) = get≽ (≽-sub p r)
  ≽-sub p (inl≽ r) = inl≽ (≽-sub p r)
  ≽-sub p (inr≽ r) = inr≽ (≽-sub p r)
  ≽-sub p (case≽ r s t) = case≽ (≽-sub p r) (≽-sub (pexts p) s) (≽-sub (pexts p) t)
  ≽-sub p (prim≽ r s) = prim≽ (≽-sub p r) (≽-sub p s)
  ≽-sub p (step s r) = step (sub-⟶ (pok p) s) (≽-sub p r)
  ≽-sub p (let≽ r s) = let≽ (≽-sub p r) (≽-sub (pexts p) s)
  ≽-sub p (letλ≽ r s) = letλ≽ (≽-sub p r) (≽-sub (pexts p) s)
  ≽-sub {τ = τ} {υ} p (letλv≽ {W = W} {V'} {N} {N'} w r s) =
    letλv≽ (sv-trav (pok p) w) (≽-sub p r) (subst₂ _≽_ (sub-[] τ N W) (sub-[] υ N' V') (≽-sub p s))
  ≽-sub {τ = τ} {υ} p (letv≽ {W = W} {V'} {N} {N'} w r s) =
    letv≽ (sv-trav (pok p) w) (≽-sub p r) (subst₂ _≽_ (sub-[] τ N W) (sub-[] υ N' V') (≽-sub p s))
  ≽-sub p (fold≽ r) = fold≽ (≽-sub p r)
  ≽-sub p (unfold≽ r) = unfold≽ (≽-sub p r)
  ≽-subs p [] = []
  ≽-subs p (r ∷ rs) = ≽-sub p r ∷ ≽-subs p rs

{- substitutions by the same variables -}
Vars : ∀ {Γ Δ} → Sb Γ Δ → Sb Γ Δ → Set
Vars {Γ} {Δ} τ υ = ∀ {B} (x : Γ ∋ B) → Σ[ y ∈ Δ ∋ B ] τ x ≡ ` y × υ x ≡ ` y

var-ext : ∀ {Δ B C} {a b : Tm Δ B} → Σ[ y ∈ Δ ∋ B ] a ≡ ` y × b ≡ ` y → Σ[ y ∈ (C ∷ Δ) ∋ B ] ren S a ≡ ` y × ren S b ≡ ` y
var-ext (y , refl , refl) = S y , refl , refl

module KV = Kit Vars (λ h x → subst₂ _≽_ (sym (proj₁ (proj₂ (h x)))) (sym (proj₂ (proj₂ (h x)))) var≽)
  (λ h x → subst SV (sym (proj₁ (proj₂ (h x)))) (P.var (proj₁ (h x))))
  (λ h → λ { Z → Z , refl , refl ; (S x) → var-ext (h x) })

≽-ren : ∀ {Γ Δ A} (r : ∀ {B} → Γ ∋ B → Δ ∋ B) {M M' : Tm Γ A} → M ≽ M' → ren r M ≽ ren r M'
≽-ren r {M} {M'} m = subst₂ _≽_ (sym (rename-sub r M)) (sym (rename-sub r M')) (KV.≽-sub (λ x → r x , refl , refl) m)

sv-exts : ∀ {Γ Δ C} {τ : Sb Γ Δ} → (∀ {B} (x : Γ ∋ B) → SV (τ x)) → ∀ {B} (x : (C ∷ Γ) ∋ B) → SV (S.exts tmK τ x)
sv-exts h Z = P.var Z
sv-exts h (S x) = sv-ren S (h x)

{- the source's substitution substitutes values -}
Rel : ∀ {Γ Δ} → Sb Γ Δ → Sb Γ Δ → Set
Rel {Γ} τ υ = (∀ {B} (x : Γ ∋ B) → τ x ≽ υ x) × (∀ {B} (x : Γ ∋ B) → SV (τ x))

module KS = Kit Rel (λ p → proj₁ p) (λ p → proj₂ p)
  (λ p → (λ { Z → var≽ ; (S x) → ≽-ren S (proj₁ p x) }) , sv-exts (proj₂ p))

≽-[] : ∀ {Γ A B} {N N' : Tm (A ∷ Γ) B} {V V'} → SV V → V ≽ V' → N ≽ N' → N [ V ]ₒ ≽ N' [ V' ]ₒ
≽-[] v r n = KS.≽-sub ((λ { Z → r ; (S x) → var≽ }) , (λ { Z → v ; (S x) → P.var x })) n

{- Values: the source reaches the values that the target has -------------------}

eval-sv : ∀ {Γ A} {M V' : Tm Γ A} → SV V' → M ≽ V' → Σ[ W ∈ Tm Γ A ] M ⟶* W × SV W × W ≽ V'
eval-svs : ∀ {Γ Δ} {Ms Ms' : All (Tm Γ) Δ} → SVs Ms' → All₂ R˘ Ms' Ms
  → Σ[ Ws ∈ All (Tm Γ) Δ ] Star _⟶s_ Ms Ws × SVs Ws × All₂ R˘ Ms' Ws
eval-sv (P.var x) var≽ = ` x , RT.ε , P.var x , var≽
eval-sv P.lam (lam≽ r) = _ , RT.ε , P.lam , lam≽ r
eval-sv P.lit lit≽ = _ , RT.ε , P.lit , lit≽
eval-sv (P.tuple vs) (tuple≽ rs) with eval-svs vs rs
... | Ws , σ , ws , rs' = tuple Ws , gmap tuple tuple σ , P.tuple ws , tuple≽ rs'
eval-sv (P.inl v) (inl≽ r) with eval-sv v r
... | W , σ , w , r' = _ , gmap inl inl₁ σ , P.inl w , inl≽ r'
eval-sv (P.inr v) (inr≽ r) with eval-sv v r
... | W , σ , w , r' = _ , gmap inr inr₁ σ , P.inr w , inr≽ r'
eval-sv (P.fold v) (fold≽ r) with eval-sv v r
... | W , σ , w , r' = _ , gmap fold fold₁ σ , P.fold w , fold≽ r'
eval-sv v (step s r) with eval-sv v r
... | W , σ , w , r' = W , s RT.◅ σ , w , r'
eval-svs P.[] [] = [] , RT.ε , P.[] , []
eval-svs (v P.∷ vs) (r ∷ rs) with eval-sv v r | eval-svs vs rs
... | W , σ , w , r' | Ws , σs , ws , rs' =
  W ∷ Ws , (gmap (_∷ _) here σ RT.◅◅ gmap (W ∷_) (there w) σs) , w P.∷ ws , r' ∷ rs'

{- the shapes of related values -}
inl-inv : ∀ {Γ A B} {W : Tm Γ (A ⊹ B)} {V'} → SV W → W ≽ inl V' → Σ[ W₀ ∈ Tm Γ A ] W ≡ inl W₀ × SV W₀ × W₀ ≽ V'
inl-inv (P.inl w) (inl≽ r) = _ , refl , w , r
inl-inv w (step s _) = ⊥-elim (sv-nostep w s)

inr-inv : ∀ {Γ A B} {W : Tm Γ (A ⊹ B)} {V'} → SV W → W ≽ inr V' → Σ[ W₀ ∈ Tm Γ B ] W ≡ inr W₀ × SV W₀ × W₀ ≽ V'
inr-inv (P.inr w) (inr≽ r) = _ , refl , w , r
inr-inv w (step s _) = ⊥-elim (sv-nostep w s)

tuple-inv : ∀ {Γ Δ} {W : Tm Γ (tup Δ)} {Ms'} → SV W → W ≽ tuple Ms'
  → Σ[ Ws ∈ All (Tm Γ) Δ ] W ≡ tuple Ws × SVs Ws × All₂ R˘ Ms' Ws
tuple-inv (P.tuple ws) (tuple≽ rs) = _ , refl , ws , rs
tuple-inv w (step s _) = ⊥-elim (sv-nostep w s)

fold-inv : ∀ {Γ A} {W : Tm Γ (μ A)} {V'} → SV W → W ≽ fold V'
  → Σ[ W₀ ∈ Tm Γ (unroll A) ] W ≡ fold W₀ × SV W₀ × W₀ ≽ V'
fold-inv (P.fold w) (fold≽ r) = _ , refl , w , r
fold-inv w (step s _) = ⊥-elim (sv-nostep w s)

lit-inv : ∀ {Γ B c} {W : Tm Γ (base B)} → SV W → W ≽ lit B c → W ≡ lit B c
lit-inv P.lit lit≽ = refl
lit-inv w (step s _) = ⊥-elim (sv-nostep w s)

≽-prim-term : ∀ {Γ} p n m → prim-term {Γ} p n m ≽ prim-term p n m
≽-prim-term Pr.sub n m = lit≽
≽-prim-term Pr.eq n m with does (n ≟ m)
... | true = inl≽ (tuple≽ [])
... | false = inr≽ (tuple≽ [])

{- What simp knows, and what it means -------------------------------------------}

{- I is true of the source term X after υ: X is related to its term, and
   to what it is known to be: a value, or a function λ N closed by a source
   substitution τ of whose variables its Facts are true, which X reaches -}
record Desc {Γ Θ A} (X : Tm Θ A) (I : Info Γ A) (υ : Sb Γ Θ) : Set
record Inv {Δ Γ Θ} (E : Facts Δ Γ) (τ : Sb Δ Θ) (υ : Sb Γ Θ) : Set
KDesc : ∀ {Γ Θ A} → Tm Θ A → Known Γ A → Sb Γ Θ → Set

record Desc X I υ where
  inductive
  constructor desc
  field
    tm : X ≽ sub υ (term I)
    kn : ∀ {K} → known I ≡ just K → KDesc X K υ
open Desc

record Inv {Δ} E τ υ where
  inductive
  field
    at : ∀ {B} (x : Δ ∋ B) → Desc (τ x) (E x) υ
    svτ : ∀ {B} (x : Δ ∋ B) → SV (τ x)
    svυ : ∀ {B} x → SV {A = B} (υ x)
open Inv

KDesc X (P.val K) υ = SV K × X ≽ sub υ K
KDesc {Θ = Θ} X (P.fun {Δ} N E) υ = Σ[ τ ∈ Sb Δ Θ ] Inv E τ υ × X ⟶* sub τ (lam N)

desc-steps : ∀ {Γ Θ A} {X X₁ : Tm Θ A} {I : Info Γ A} {υ : Sb Γ Θ} → X ⟶* X₁ → Desc X₁ I υ → Desc X I υ
desc-steps {X = X} {X₁} {υ = υ} σ d = desc (steps σ (tm d)) (λ e → G _ (kn d e))
  where
  G : ∀ K → KDesc X₁ K υ → KDesc X K υ
  G (P.val K) (v , r) = v , steps σ r
  G (P.fun N E) (τ , ok , σ') = τ , ok , σ RT.◅◅ σ'

desc-self : ∀ {Γ Θ A} {X : Tm Θ A} {V : Tm Γ A} {υ : Sb Γ Θ} → SV V → X ≽ sub υ V → Desc X (self V) υ
desc-self v r = desc r (λ { refl → v , r })

desc-info : ∀ {Γ Θ A} {X : Tm Θ A} {M : Tm Γ A} {υ : Sb Γ Θ} → X ≽ sub υ M → Desc X (info M) υ
desc-info {M = M} r with value M in e
... | true = desc r (λ { refl → value-sv M e , r })
... | false = desc r (λ ())

{- what I says of X it says of the value W that X reaches -}
desc-to : ∀ {Γ Θ A} {X W : Tm Θ A} {I : Info Γ A} {υ : Sb Γ Θ} → (∀ {B} (x : Γ ∋ B) → SV (υ x)) → Desc X I υ → X ⟶* W → SV W
  → W ≽ sub υ (term I) → Desc W I υ
desc-to {X = X} {W} {I} {υ} h d σ w r = desc r (λ e → G _ (kn d e))
  where
  G : ∀ K → KDesc X K υ → KDesc W K υ
  G (P.val K) (k , r') with eval-sv (sv-trav h k) r'
  ... | W' , σ' , w' , r'' = k , subst (_≽ sub υ K) (sym (star-det σ σ' w w')) r''
  G (P.fun N E) (τ , ok , σ') = τ , ok , subst (_⟶* _) (sym (star-det σ σ' w P.lam)) RT.ε

{- under one more binder, in the source and the target -}
ren-⟶* : ∀ {Γ A C} {X Y : Tm Γ A} → X ⟶* Y → ren (S {b = C}) X ⟶* ren S Y
ren-⟶* = gmap (ren S) (λ {X} {Y} s → subst₂ _⟶_ (sym (rename-sub S X)) (sym (rename-sub S Y)) (sub-⟶ (λ x → P.var (S x)) s))

tm-ext : ∀ {Γ Θ A C} (T : Tm Γ A) (υ : Sb Γ Θ) {X} → X ≽ sub υ T → ren (S {b = C}) X ≽ sub (S.exts tmK υ) (ren S T)
tm-ext T υ r = subst (_ ≽_) (sym (S.Laws.exts-ren tmL υ T)) (≽-ren S r)

desc-ext : ∀ {Γ Θ A C} (I : Info Γ A) {X : Tm Θ A} {υ : Sb Γ Θ} → Desc X I υ → Desc (ren (S {b = C}) X) (shift-info I) (S.exts tmK υ)
kdesc-ext : ∀ {Γ Θ A C} (K : Known Γ A) {X : Tm Θ A} {υ : Sb Γ Θ} → KDesc X K υ → KDesc (ren (S {b = C}) X) (shift-known K) (S.exts tmK υ)
desc-ext (T ∣ nothing) {υ = υ} d = desc (tm-ext T υ (tm d)) (λ ())
desc-ext (T ∣ just K) {υ = υ} d = desc (tm-ext T υ (tm d)) (λ { refl → kdesc-ext K (kn d refl) })
kdesc-ext (P.val K) {υ = υ} (v , r) = sv-ren S v , tm-ext K υ r
kdesc-ext (P.fun N E) {X = X} (τ , ok , σ) =
  (λ x → ren S (τ x))
  , record { at = λ x → desc-ext (E x) (at ok x) ; svτ = λ x → sv-ren S (svτ ok x) ; svυ = sv-exts (svυ ok) }
  , subst (ren S X ⟶*_) (S.sub-ren (λ _ → refl) (lam N)) (ren-⟶* σ)

{- under one more binder, in the target only, bound to V -}
tm-cons : ∀ {Γ Θ A C} (T : Tm Γ A) (υ : Sb Γ Θ) {X} (V : Tm Θ C) → X ≽ sub υ T → X ≽ sub (V S.• υ) (ren S T)
tm-cons T υ V r = subst (_ ≽_) (sym (S.ren-trav tmK (λ _ → refl) T)) r

desc-cons : ∀ {Γ Θ A C} (I : Info Γ A) {X : Tm Θ A} {υ : Sb Γ Θ} (V : Tm Θ C) → SV V → Desc X I υ → Desc X (shift-info I) (V S.• υ)
kdesc-cons : ∀ {Γ Θ A C} (K : Known Γ A) {X : Tm Θ A} {υ : Sb Γ Θ} (V : Tm Θ C) → SV V → KDesc X K υ → KDesc X (shift-known K) (V S.• υ)
desc-cons (T ∣ nothing) {υ = υ} V v d = desc (tm-cons T υ V (tm d)) (λ ())
desc-cons (T ∣ just K) {υ = υ} V v d = desc (tm-cons T υ V (tm d)) (λ { refl → kdesc-cons K V v (kn d refl) })
kdesc-cons (P.val K) {υ = υ} V v (k , r) = sv-ren S k , tm-cons K υ V r
kdesc-cons (P.fun N E) V v (τ , ok , σ) =
  τ , record { at = λ x → desc-cons (E x) V v (at ok x) ; svτ = svτ ok ; svυ = λ { Z → v ; (S x) → svυ ok x } } , σ

inv-under : ∀ {Δ Γ Θ C} {E : Facts Δ Γ} {τ : Sb Δ Θ} {υ : Sb Γ Θ} → Inv E τ υ → Inv (under {B = C} E) (S.exts tmK τ) (S.exts tmK υ)
inv-under {E = E} ok = record
  { at = λ { Z → desc-self (P.var Z) var≽ ; (S x) → desc-ext (E x) (at ok x) }
  ; svτ = sv-exts (svτ ok) ; svυ = sv-exts (svυ ok) }

{- the source binds X in N: a β redex, or a let -}
data Form : Set where
  appF letF : Form

bnd : ∀ {Θ A B} → Form → Tm (A ∷ Θ) B → Tm Θ A → Tm Θ B
bnd appF N X = app (lam N) X
bnd letF N X = let′ X N

bnd-cong : ∀ {Θ A B} f {N : Tm (A ∷ Θ) B} {X X'} → X ⟶ X' → bnd f N X ⟶ bnd f N X'
bnd-cong appF = app₂
bnd-cong letF = let₁

bnd-β : ∀ {Θ A B} f {N : Tm (A ∷ Θ) B} {W} → SV W → bnd f N W ⟶ N [ W ]ₒ
bnd-β appF = β
bnd-β letF = letβ

bnd-let : ∀ {Θ A B} f {X M' : Tm Θ A} {N N' : Tm (A ∷ Θ) B} → X ≽ M' → N ≽ N' → bnd f N X ≽ let′ M' N'
bnd-let appF = letλ≽
bnd-let letF = let≽

bnd-letv : ∀ {Θ A B} f {W V' : Tm Θ A} {N N' : Tm (A ∷ Θ) B} → SV W → W ≽ V' → N [ W ]ₒ ≽ N' [ V' ]ₒ
  → bnd f N W ≽ let′ V' N'
bnd-letv appF = letλv≽
bnd-letv letF = letv≽

{- The main lemma -------------------------------------------------------------------}

simp-ok : ∀ {Δ Γ Θ A} fl (M : Tm Δ A) {E : Facts Δ Γ} {τ : Sb Δ Θ} {υ : Sb Γ Θ} → Inv E τ υ → Desc (sub τ M) (simp fl E M) υ
simps-ok : ∀ {Δ Γ Θ Δ'} fl (Ms : All (Tm Δ) Δ') {E : Facts Δ Γ} {τ : Sb Δ Θ} {υ : Sb Γ Θ} → Inv E τ υ
  → All₂ R˘ (S.travs tmK υ (simps fl E Ms)) (S.travs tmK τ Ms)
app-ok : ∀ {Δ Γ Θ A B} fl (L : Tm Δ (A ⇒ B)) M {E : Facts Δ Γ} {τ : Sb Δ Θ} {υ : Sb Γ Θ} {I} → Inv E τ υ → Desc (sub τ M) I υ
  → Desc (sub τ (app L M)) (simp-app fl E L I) υ
let-ok : ∀ {Δ Γ Θ A B} fl f (N : Tm (A ∷ Δ) B) {E : Facts Δ Γ} {τ : Sb Δ Θ} {υ : Sb Γ Θ} {I X} → Inv E τ υ → Desc X I υ
  → Desc (bnd f (sub (S.exts tmK τ) N) X) (simp-let fl E N I) υ
call-ok : ∀ {Γ Θ A B} fl (J : Info Γ (A ⇒ B)) I {υ : Sb Γ Θ} {L M} → Desc L J υ → Desc M I υ → Desc (app L M) (simp-call fl J I) υ
case-ok : ∀ {Δ Γ Θ A B C} fl (L : Tm Δ (A ⊹ B)) (M : Tm (A ∷ Δ) C) N {E : Facts Δ Γ} {τ : Sb Δ Θ} {υ : Sb Γ Θ} {I} → Inv E τ υ
  → Desc (sub τ L) I υ → Desc (sub τ (case L M N)) (simp-case fl E I M N) υ

simp-ok fl (` x) ok = at ok x
simp-ok fl (lam N) {τ = τ} ok = desc (lam≽ (tm (simp-ok fl N (inv-under ok)))) (λ { refl → τ , ok , RT.ε })
simp-ok fl (app L M) ok = app-ok fl L M ok (simp-ok fl M ok)
simp-ok fl (lit B c) ok = desc-self P.lit lit≽
simp-ok fl (tuple Ms) ok = desc-info (tuple≽ (simps-ok fl Ms ok))
simp-ok fl (get i L) {E} {τ} {υ} ok = get-ok (simp fl E L) (simp-ok fl L ok)
  where
  {- the component of a known tuple, which the source reaches -}
  get-ok : ∀ I → Desc (sub τ L) I υ → Desc (sub τ (get i L)) (simp-get i I) υ
  get-ok I d with component i (known I) refl in e
  ... | nothing = desc (get≽ (tm d)) (λ ())
  ... | just K with comp-inv i (known I) refl e
  ...   | Ks , k , refl with kn d k
  ...     | P.tuple vs , r with eval-sv (sv-trav (svυ ok) (P.tuple vs)) r
  ...       | W , σ , w , r' with tuple-inv w r'
  ...         | Ws , refl , ws , rs with steps (gmap (get i) get₁ σ RT.◅◅ (get ws RT.◅ RT.ε))
                                             (subst (_ ≽_) (sym (sub-lookup υ Ks i)) (lookup₂ rs i)) | small (lookup Ks i)
  ...           | r'' | true = desc-self (svs-lookup vs i) r''
  ...           | r'' | false = desc (get≽ (tm d)) (λ { refl → svs-lookup vs i , r'' })
simp-ok fl (inl M) ok = desc-info (inl≽ (tm (simp-ok fl M ok)))
simp-ok fl (inr M) ok = desc-info (inr≽ (tm (simp-ok fl M ok)))
simp-ok fl (case L M N) ok = case-ok fl L M N ok (simp-ok fl L ok)
simp-ok fl (prim p L M) {E} {τ} {υ} ok = prim-ok (simp fl E L) (simp fl E M) (simp-ok fl L ok) (simp-ok fl M ok)
  where
  {- a known integer, which the source reaches -}
  int-eval : ∀ {Y : Tm _ (base Int)} k {n} → int-of k ≡ just n → (∀ {K} → k ≡ just K → KDesc Y K υ) → Y ⟶* lit Int n
  int-eval k e h with int-inv k e
  ... | refl , k' with h k'
  ...   | v , r with eval-sv P.lit r
  ...     | W , σ , w , r' with lit-inv w r'
  ...       | refl = σ
  prim-ok : ∀ I J → Desc (sub τ L) I υ → Desc (sub τ M) J υ → Desc (sub τ (prim p L M)) (simp-prim p I J) υ
  prim-ok I J dI dJ with int-of (known I) in e₁
  ... | nothing = desc (prim≽ (tm dI) (tm dJ)) (λ ())
  ... | just n with int-of (known J) in e₂
  ...   | nothing = desc (prim≽ (tm dI) (tm dJ)) (λ ())
  ...   | just m =
    desc-steps (gmap (λ X → prim p X (sub τ M)) prim₁ (int-eval (known I) e₁ (kn dI))
                RT.◅◅ gmap (prim p (lit Int n)) (prim₂ P.lit) (int-eval (known J) e₂ (kn dJ))
                RT.◅◅ (prim RT.◅ RT.ε))
      (desc-self (prim-term-sv p n m) (subst (_ ≽_) (sym (sub-prim-term υ p n m)) (≽-prim-term p n m)))
simp-ok fl (let′ M N) ok = let-ok fl letF N ok (simp-ok fl M ok)
simp-ok fl (fold M) ok = desc-info (fold≽ (tm (simp-ok fl M ok)))
simp-ok fl (unfold L) {E} {τ} {υ} ok = unfold-ok (simp fl E L) (simp-ok fl L ok)
  where
  {- the value under a known fold, which the source reaches -}
  unfold-ok : ∀ I → Desc (sub τ L) I υ → Desc (sub τ (unfold L)) (simp-unfold I) υ
  unfold-ok I d with unfolded (known I) refl in e
  ... | nothing = desc (unfold≽ (tm d)) (λ ())
  ... | just K with kn d (unfold-inv (known I) refl e)
  ...   | P.fold v , r with eval-sv (sv-trav (svυ ok) (P.fold v)) r
  ...     | W , σ , w , r' with fold-inv w r'
  ...       | W₀ , refl , w₀ , r₀ with steps (gmap unfold unfold₁ σ RT.◅◅ (unfoldβ w₀ RT.◅ RT.ε)) r₀ | small K
  ...         | r'' | true = desc-self v r''
  ...         | r'' | false = desc (unfold≽ (tm d)) (λ { refl → v , r'' })

simps-ok fl [] ok = []
simps-ok fl (M ∷ Ms) ok = tm (simp-ok fl M ok) ∷ simps-ok fl Ms ok

{- an application: β if the operator is a function, and otherwise a call -}
app-ok fl L M ok d with lam? L
... | is-lam N = let-ok fl appF N ok d
... | other = call-ok fl _ _ (simp-ok fl L ok) d

{- a call of a known function: the source reaches the function, then β -}
call-ok (suc fl) (T ∣ just (P.fun N E)) I {M = M} dJ dI with size (term (simp-let fl E N I)) ≤ᵇ inline-size | kn dJ refl
... | true | τ , ok , σ = desc-steps (gmap (λ X → app X M) app₁ σ) (let-ok fl appF N ok dI)
... | false | _ = desc (app≽ (tm dJ) (tm dI)) (λ ())
call-ok zero J I dJ dI = desc (app≽ (tm dJ) (tm dI)) (λ ())
call-ok (suc fl) (T ∣ nothing) I dJ dI = desc (app≽ (tm dJ) (tm dI)) (λ ())
call-ok (suc fl) (T ∣ just (P.val K)) I dJ dI = desc (app≽ (tm dJ) (tm dI)) (λ ())

{- β: the source evaluates the operand to a value W -}
let-ok fl f N {E} {τ} {υ} {I} ok d with small (term I) in s | value (term I) in v
... | true | _ with eval-sv (sv-trav (svυ ok) (small-sv (term I) s)) (tm d)
...   | W , σ , w , r =
  desc-steps (gmap (bnd f (sub (S.exts tmK τ) N)) (bnd-cong f) σ RT.◅◅ (bnd-β f w RT.◅ RT.ε))
    (subst (λ X → Desc X _ υ) (sym (exts-[]ₒ τ W N)) (simp-ok fl N ok'))
  where
  ok' : Inv (I P.• E) (W S.• τ) υ
  ok' = record { at = λ { Z → desc-to (svυ ok) d σ w r ; (S x) → at ok x }
               ; svτ = λ { Z → w ; (S x) → svτ ok x } ; svυ = svυ ok }
let-ok fl f N {E} {τ} {υ} {I} ok d | false | true with eval-sv (sv-trav (svυ ok) (value-sv (term I) v)) (tm d)
...   | W , σ , w , r =
  desc (steps (gmap (bnd f (sub (S.exts tmK τ) N)) (bnd-cong f) σ)
          (bnd-letv f w r (subst₂ _≽_ (sym (exts-[]ₒ τ W N)) (sym (exts-[]ₒ υ V N')) (tm (simp-ok fl N ok')))))
       (λ ())
  where
  V = sub υ (term I)
  N' = term (simp fl (known-as I E) N)
  vV = sv-trav (svυ ok) (value-sv (term I) v)
  ok' : Inv (known-as I E) (W S.• τ) (V S.• υ)
  ok' = record
    { at = λ { Z → desc r (kn (desc-cons I V vV (desc-to (svυ ok) d σ w r)))
             ; (S x) → desc-cons (E x) V vV (at ok x) }
    ; svτ = λ { Z → w ; (S x) → svτ ok x }
    ; svυ = λ { Z → vV ; (S x) → svυ ok x } }
let-ok fl f N ok d | false | false = desc (bnd-let f (tm d) (tm (simp-ok fl N (inv-under ok)))) (λ ())

{- a case on a known injection: the source evaluates the scrutinee to it -}
case-ok fl L M N {E} {τ} {υ} {I} ok d with branch (known I) refl in e
... | nothing = desc (case≽ (tm d) (tm (simp-ok fl M (inv-under ok))) (tm (simp-ok fl N (inv-under ok)))) (λ ())
... | just (inj₁ K) with branch-inl (known I) refl e
...   | k , _ with kn d k
...     | P.inl v , r with eval-sv (sv-trav (svυ ok) (P.inl v)) r
...       | W , σ , w , r' with inl-inv w r'
...         | W₀ , refl , w₀ , r₀ =
  desc-steps (gmap (λ X → case X (sub (S.exts tmK τ) M) (sub (S.exts tmK τ) N)) case₁ σ RT.◅◅ (case-l w₀ RT.◅ RT.ε))
    (subst (λ X → Desc X _ υ) (sym (exts-[]ₒ τ W₀ M)) (simp-ok fl M ok'))
  where
  ok' : Inv (self K P.• E) (W₀ S.• τ) υ
  ok' = record { at = λ { Z → desc-self v r₀ ; (S x) → at ok x }
               ; svτ = λ { Z → w₀ ; (S x) → svτ ok x } ; svυ = svυ ok }
case-ok fl L M N {E} {τ} {υ} {I} ok d | just (inj₂ K) with branch-inr (known I) refl e
...   | k , _ with kn d k
...     | P.inr v , r with eval-sv (sv-trav (svυ ok) (P.inr v)) r
...       | W , σ , w , r' with inr-inv w r'
...         | W₀ , refl , w₀ , r₀ =
  desc-steps (gmap (λ X → case X (sub (S.exts tmK τ) M) (sub (S.exts tmK τ) N)) case₁ σ RT.◅◅ (case-r w₀ RT.◅ RT.ε))
    (subst (λ X → Desc X _ υ) (sym (exts-[]ₒ τ W₀ N)) (simp-ok fl N ok'))
  where
  ok' : Inv (self K P.• E) (W₀ S.• τ) υ
  ok' = record { at = λ { Z → desc-self v r₀ ; (S x) → at ok x }
               ; svτ = λ { Z → w₀ ; (S x) → svτ ok x } ; svυ = svυ ok }

{- the program is related to itself, simplified -}
simplify-≽ : ∀ {A} (M : Tm [] A) → M ≽ simplify M
simplify-≽ M = subst₂ _≽_ (S.sub-id (λ _ → refl) M) (S.sub-id (λ _ → refl) _) (tm (simp-ok inline-fuel M ok₀))
  where ok₀ : Inv (λ x → self (` x)) `_ `_
        ok₀ = record { at = λ x → desc-self (P.var x) var≽ ; svτ = P.var ; svυ = P.var }

{- The simulation of the target by the source -----------------------------------}

Ans′ : ∀ {A} → Tm [] A → Red (Tm [] A) → Tm [] A → Set
Ans′ = Ans S.red SV R˘

{- a target term related to a source value is a value, observed alike -}
≽-value : ∀ {A} {W V' : Tm [] A} → SV W → W ≽ V' → SV V'
≽-values : ∀ {Δ} {Ws Vs' : All (Tm []) Δ} → SVs Ws → All₂ R˘ Vs' Ws → SVs Vs'
≽-value P.lam (lam≽ _) = P.lam
≽-value P.lit lit≽ = P.lit
≽-value (P.tuple vs) (tuple≽ rs) = P.tuple (≽-values vs rs)
≽-value (P.inl v) (inl≽ r) = P.inl (≽-value v r)
≽-value (P.inr v) (inr≽ r) = P.inr (≽-value v r)
≽-value (P.fold v) (fold≽ r) = P.fold (≽-value v r)
≽-value v (step s _) = ⊥-elim (sv-nostep v s)
≽-values P.[] [] = P.[]
≽-values (v P.∷ vs) (r ∷ rs) = ≽-value v r P.∷ ≽-values vs rs

obs≽ : ∀ {A} {W V' : Tm [] A} → SV W → W ≽ V' → S.obs W ≡ S.obs V'
obs≽s : ∀ {Δ} {Ws Vs' : All (Tm []) Δ} → SVs Ws → All₂ R˘ Vs' Ws → S.obss Ws ≡ S.obss Vs'
obs≽ P.lam (lam≽ _) = refl
obs≽ P.lit lit≽ = refl
obs≽ (P.tuple vs) (tuple≽ rs) = cong o-tuple (obs≽s vs rs)
obs≽ (P.inl v) (inl≽ r) = cong o-inl (obs≽ v r)
obs≽ (P.inr v) (inr≽ r) = cong o-inr (obs≽ v r)
obs≽ (P.fold v) (fold≽ r) = obs≽ v r
obs≽ v (step s _) = ⊥-elim (sv-nostep v s)
obs≽s P.[] [] = refl
obs≽s (v P.∷ vs) (r ∷ rs) = cong₂ _∷_ (obs≽ v r) (obs≽s vs rs)

{- the body of a function, after β, is related to the target's -}
β≽ : ∀ {A B} {N N' : Tm (A ∷ []) B} {W V'} → N ≽ N' → W ≽ V' → SV W → R˘ (N' S.[ V' ]) (N S.[ W ])
β≽ {N = N} {N'} {W} {V'} r s v = subst₂ _≽_ (sym (closed-[] N W)) (sym (closed-[] N' V')) (≽-[] v s r)

≽-out : ∀ p n m → S.out {[]} p n m ≽ S.out p n m
≽-out p n m rewrite prim-term-out p n m = ≽-prim-term p n m

{- a target let of a value takes its step -}
let-val : ∀ {A B} {N' : Tm (A ∷ []) B} {V' W M} → SV W → W ≽ V' → Ans′ (let′ V' N') (to (N' S.[ V' ])) M
  → Ans′ (let′ V' N') (S.red (let′ V' N')) M
let-val {N' = N'} {V'} {M = M} v r a = subst (λ x → Ans′ (let′ V' N') x M) (sym (val-in (sv-red (≽-value v r)))) a

sim : ∀ {A} {M M' : Tm [] A} → M ≽ M' → Ans′ M' (S.red M') M
sims : ∀ {Δ} {Ms Ms' : All (Tm []) Δ} → All₂ R˘ Ms' Ms → Ans S.reds (Each SV) (All₂ R˘) Ms' (S.reds Ms') Ms
sim (lam≽ r) = val ε P.lam (lam≽ r)
sim (app≽ {M = M} {M'} r s) = ans-in (frame _ (λ _ → refl)) (λ r' → app≽ r' s) (sim r) app-sim
  where
  app-sim : ∀ {W} → SV W → R˘ _ W → Ans′ (app _ M') _ (app W M)
  app-sim {W = W} P.lam (lam≽ r₁) =
    ans-in (frame {g = app W} _ (λ X → refl)) (λ s' → app≽ (lam≽ r₁) s') (sim s)
           λ v' s' → to (one (val-in (sv-red v'))) (β≽ r₁ s' v')
  app-sim v (step st _) = ⊥-elim (sv-nostep v st)
sim lit≽ = val ε P.lit lit≽
sim (tuple≽ rs) = ans-in (frame _ (λ _ → refl)) tuple≽ (sims rs)
  (λ vs ms → val ε (P.tuple (each-svs vs)) (tuple≽ ms))
sim (get≽ {i = i} r) = ans-in (frame _ (λ _ → refl)) get≽ (sim r) get-sim
  where
  get-sim : ∀ {W} → SV W → R˘ _ W → Ans′ (get i _) _ (get i W)
  get-sim v@(P.tuple _) (tuple≽ rs) = to (one (val-in (sv-red v))) (lookup₂ rs i)
  get-sim v (step st _) = ⊥-elim (sv-nostep v st)
sim (inl≽ r) = ans-in (frame _ (λ _ → refl)) inl≽ (sim r) (λ v r' → val ε (P.inl v) (inl≽ r'))
sim (inr≽ r) = ans-in (frame _ (λ _ → refl)) inr≽ (sim r) (λ v r' → val ε (P.inr v) (inr≽ r'))
sim (case≽ {M = M} {M'} {N} {N'} r s t) = ans-in (frame _ (λ _ → refl)) (λ r' → case≽ r' s t) (sim r) case-sim
  where
  case-sim : ∀ {W} → SV W → R˘ _ W → Ans′ (case _ M' N') _ (case W M N)
  case-sim v@(P.inl v₁) (inl≽ r') = to (one (val-in (sv-red v))) (β≽ s r' v₁)
  case-sim v@(P.inr v₁) (inr≽ r') = to (one (val-in (sv-red v))) (β≽ t r' v₁)
  case-sim v (step st _) = ⊥-elim (sv-nostep v st)
sim (prim≽ {p = p} {M = M} {M'} r s) = ans-in (frame _ (λ _ → refl)) (λ r' → prim≽ r' s) (sim r) prim-sim
  where
  prim-sim₂ : ∀ {n W V'} → SV W → R˘ V' W → Ans′ (prim p (lit Int n) V') (S.prim? p (lit Int n) V') (prim p (lit Int n) W)
  prim-sim₂ P.lit lit≽ = to (one refl) (≽-out p _ _)
  prim-sim₂ v (step st _) = ⊥-elim (sv-nostep v st)
  prim-sim : ∀ {W V'} → SV W → R˘ V' W
    → Ans′ (prim p V' M') (step-in (prim p V') (S.red M') (S.prim? p V' M')) (prim p W M)
  prim-sim P.lit lit≽ = ans-in (frame {g = prim p _} _ (λ _ → refl)) (prim≽ lit≽) (sim s) prim-sim₂
  prim-sim v (step st _) = ⊥-elim (sv-nostep v st)
sim (step st r) = ans-step (closed-red st) (sim r)
sim (let≽ r s) = ans-in (frame _ (λ _ → refl)) (λ r' → let≽ r' s) (sim r) λ v r' → to (one (val-in (sv-red v))) (β≽ s r' v)
sim (letλ≽ {N = N} r s) = ans-in (frame {g = app (lam N)} _ (λ _ → refl)) (λ r' → letλ≽ r' s) (sim r)
  λ v r' → to (one (val-in (sv-red v))) (β≽ s r' v)
sim (letλv≽ {W = W} {V'} {N} {N'} wv r₁ r₂) = let-val wv r₁
  (to (one (val-in (sv-red wv))) (subst₂ _≽_ (sym (closed-[] N W)) (sym (closed-[] N' V')) r₂))
sim (letv≽ {W = W} {V'} {N} {N'} wv r₁ r₂) = let-val wv r₁
  (to (one (val-in (sv-red wv))) (subst₂ _≽_ (sym (closed-[] N W)) (sym (closed-[] N' V')) r₂))
sim (fold≽ r) = ans-in (frame _ (λ _ → refl)) fold≽ (sim r) (λ v r' → val ε (P.fold v) (fold≽ r'))
sim (unfold≽ r) = ans-in (frame _ (λ _ → refl)) unfold≽ (sim r) unfold-sim
  where
  unfold-sim : ∀ {W} → SV W → R˘ _ W → Ans′ (unfold _) _ (unfold W)
  unfold-sim v@(P.fold _) (fold≽ r') = to (one (val-in (sv-red v))) r'
  unfold-sim v (step st _) = ⊥-elim (sv-nostep v st)
sims [] = val ε [] []
sims (r ∷ rs) = ans-∷ S.reds (λ _ _ → refl) sv-red rs (sim r) (sims rs)

{- The end theorem: for every closed program ----------------------------------------}

simplify-correct : ∀ {A} (M : Tm [] A) → Equivalent (S.sem M) (S.sem (simplify M))
simplify-correct M = equiv-sym (red-equivalent sv-red R˘ sim (λ m _ v → sym (obs≽ v m)) (simplify-≽ M))

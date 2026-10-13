{-

  Correctness of the simplify pass (ISWIM → ISWIM) by a simulation of the
  target by the source, between their reduction semantics (see the
  design note in Semantics/Reduction/Smallstep.agda).

  The target takes fewer steps than the source: simplify did some of the
  source's reductions ahead of time, under binders. So each target step
  is answered by one or more source steps (the source catches up with
  the reductions simplify did, then takes the same step), and the
  forward simulation goes from the target to the source; Equivalent is
  symmetric.

  The relation (_≼_, the target on the left) is a congruence, closed
  under substitution, with two more rules. step: the source may take a
  reduction step first. let: a let of a value that simplify kept, whose
  body it simplified knowing the value, is related through the bodies
  after β. Since simplify reduces under binders, the source's steps are
  steps on open terms, where a variable stands for a value (_⟶_, on the
  values SV); in a closed term they are steps of the reduction semantics
  (closed-red), so the source is kept closed (R).

  The main lemma (simp-ok): if what simp knows of each variable x is
  true of τ x (the source's substitution) after υ (the target's), then
  what simp E M says of M is true of sub τ M (Desc): its term, after υ,
  is related to sub τ M, and so is its known value. A known value of a
  term, a value K with sub υ K ≼ sub τ M, is reached by the source:
  sub τ M steps to a value related to sub υ K (eval-sv).

-}

module proof.Correctness.Reduction.SimplifyRed where

open import Framework.Primitives using (Int)
open import Framework.Syntax.SyntaxUtil using (_,,_; Nil; ⟩_,,_)
open import Language.ISWIM
open import Language.Prim using (Out; int; bool; δ)
open import proof.Compiler.SimplifyFacts as P
  using (Info; _∣_; term; known; Facts; self; info; under; shift-info; simp; simp-args; simp-app; simp-let;
         simp-get; simp-case; simp-prim; simplify; small; value; component; branch; int-of; prim-term;
         SV; SVs; value-sv; small-sv; sv-sub; svs-sub; sv-rename; prim-term-sv; int-of-just; component-just)
open import Compiler.EncloseScope using (Closed)
open import proof.Compiler.SimplifyScope using (closed-ws; ws-proj; ws-prim-term)
open import Semantics.Observation
open import proof.Framework.Reduction Obs o-wrong
open import Semantics.Reduction.Smallstep using (Equivalent)
open import proof.Framework.Simulation Obs using (equiv-sym)
import Semantics.Reduction.ISWIM as S
open import Framework.Syntax.Uses Op sig using (bound; bound-args)
import proof.Framework.Syntax.Subst Op sig as SS
open SS using (Subst; sub; sub-args; exts; ids; _[_])
import proof.Framework.Syntax.SubstRel Op sig Op sig as SubstRel
open import Framework.Syntax.Rename Op sig using (rename; shift)
open import Framework.Syntax.Scope Op sig using (WS; WS-arg; WS-args)
open import proof.Framework.Syntax.ScopeSubst Op sig using (ws-sub)
open import proof.Framework.ListUtil using (proj; args→list; has-length; proj-pw; proj-map)
import Relation.Binary.Construct.Closure.ReflexiveTransitive as RT
open RT using (Star; gmap)

open import Data.Bool using (true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.List using (replicate; _∷_)
import Data.Maybe
import Data.Maybe.Relation.Binary.Pointwise as M
open import Data.Maybe using (just; nothing; map)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; _⊔_; _∸_; s≤s; z≤n)
open import Data.Nat.Properties using (m⊔n≤o⇒m≤o; m⊔n≤o⇒n≤o; ≤-trans; m≤n+m∸n)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂)

{- The values of the ISWIM reduction semantics; closed programs ----------------}

module V where
  data Value : AST → Set
  infixr 5 _∷_
  data Values : ∀ {n} → Args (replicate n ■) → Set

  data Value where
    lam : ∀ {N} → Value (lam ⦅ ⟩ N ,, Nil ⦆)
    lit : ∀ {B k} → Value (lit B k ⦅ Nil ⦆)
    tuple : ∀ {n as} → Values as → Value (tuple n ⦅ as ⦆)
    inl : ∀ {V} → Value V → Value (inl-op ⦅ V ,, Nil ⦆)
    inr : ∀ {V} → Value V → Value (inr-op ⦅ V ,, Nil ⦆)

  data Values where
    [] : Values Nil
    _∷_ : ∀ {n V} {as : Args (replicate n ■)} → Value V → Values as → Values (V ,, as)

  value-red : ∀ {V} → Value V → S.red V ≡ val
  values-red : ∀ {n} {as : Args (replicate n ■)} → Values as → S.red-args as ≡ val
  value-red lam = refl
  value-red lit = refl
  value-red (tuple vs) rewrite values-red vs = refl
  value-red (inl v) rewrite value-red v = refl
  value-red (inr v) rewrite value-red v = refl
  values-red [] = refl
  values-red (v ∷ vs) rewrite value-red v | values-red vs = refl


open V using (Value; Values; value-red; values-red)

{- Reduction of open terms, where a variable stands for a value ---------------}

infix 4 _⟶_ _⟶s_ _⟶*_
data _⟶_ : AST → AST → Set
data _⟶s_ : ∀ {n} → Args (replicate n ■) → Args (replicate n ■) → Set

data _⟶_ where
  β : ∀ {N V} → SV V → app ⦅ lam ⦅ ⟩ N ,, Nil ⦆ ,, V ,, Nil ⦆ ⟶ N [ V ]
  app₂ : ∀ {N M M'} → M ⟶ M' → app ⦅ lam ⦅ ⟩ N ,, Nil ⦆ ,, M ,, Nil ⦆ ⟶ app ⦅ lam ⦅ ⟩ N ,, Nil ⦆ ,, M' ,, Nil ⦆
  tuple : ∀ {n as as'} → as ⟶s as' → tuple n ⦅ as ⦆ ⟶ tuple n ⦅ as' ⦆
  get : ∀ {n m} {i : Fin n} {as : Args (replicate m ■)} {V}
    → SVs as → proj i (args→list as) ≡ just V → get i ⦅ tuple m ⦅ as ⦆ ,, Nil ⦆ ⟶ V
  get₁ : ∀ {n} {i : Fin n} {M M'} → M ⟶ M' → get i ⦅ M ,, Nil ⦆ ⟶ get i ⦅ M' ,, Nil ⦆
  inl₁ : ∀ {M M'} → M ⟶ M' → inl-op ⦅ M ,, Nil ⦆ ⟶ inl-op ⦅ M' ,, Nil ⦆
  inr₁ : ∀ {M M'} → M ⟶ M' → inr-op ⦅ M ,, Nil ⦆ ⟶ inr-op ⦅ M' ,, Nil ⦆
  case-l : ∀ {V M N} → SV V → case-op ⦅ inl-op ⦅ V ,, Nil ⦆ ,, ⟩ M ,, ⟩ N ,, Nil ⦆ ⟶ M [ V ]
  case-r : ∀ {V M N} → SV V → case-op ⦅ inr-op ⦅ V ,, Nil ⦆ ,, ⟩ M ,, ⟩ N ,, Nil ⦆ ⟶ N [ V ]
  case₁ : ∀ {L L' M N} → L ⟶ L' → case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆ ⟶ case-op ⦅ L' ,, ⟩ M ,, ⟩ N ,, Nil ⦆
  prim : ∀ {p n m} → prim p ⦅ lit Int n ⦅ Nil ⦆ ,, lit Int m ⦅ Nil ⦆ ,, Nil ⦆ ⟶ prim-term (δ p n m)
  prim₁ : ∀ {p L L' M} → L ⟶ L' → prim p ⦅ L ,, M ,, Nil ⦆ ⟶ prim p ⦅ L' ,, M ,, Nil ⦆
  prim₂ : ∀ {p V M M'} → SV V → M ⟶ M' → prim p ⦅ V ,, M ,, Nil ⦆ ⟶ prim p ⦅ V ,, M' ,, Nil ⦆

data _⟶s_ where
  here : ∀ {n M M'} {as : Args (replicate n ■)} → M ⟶ M' → (M ,, as) ⟶s (M' ,, as)
  there : ∀ {n V} {as as' : Args (replicate n ■)} → SV V → as ⟶s as' → (V ,, as) ⟶s (V ,, as')

_⟶*_ : AST → AST → Set
_⟶*_ = Star _⟶_

{- a value does not step -}
sv-nostep : ∀ {V M} → SV V → V ⟶ M → ⊥
svs-nostep : ∀ {n} {as as' : Args (replicate n ■)} → SVs as → as ⟶s as' → ⊥
sv-nostep (P.tuple vs) (tuple s) = svs-nostep vs s
sv-nostep (P.inl v) (inl₁ s) = sv-nostep v s
sv-nostep (P.inr v) (inr₁ s) = sv-nostep v s
svs-nostep (v P.∷ vs) (here s) = sv-nostep v s
svs-nostep (v P.∷ vs) (there _ s) = svs-nostep vs s

val-sv : ∀ {V} → Value V → SV V
vals-sv : ∀ {n} {as : Args (replicate n ■)} → Values as → SVs as
val-sv V.lam = P.lam
val-sv V.lit = P.lit
val-sv (V.tuple vs) = P.tuple (vals-sv vs)
val-sv (V.inl v) = P.inl (val-sv v)
val-sv (V.inr v) = P.inr (val-sv v)
vals-sv V.[] = P.[]
vals-sv (v V.∷ vs) = val-sv v P.∷ vals-sv vs

{- a closed value is a value of the reduction semantics -}
sv-value : ∀ {V} → SV V → WS 0 V → Value V
svs-value : ∀ {n} {as : Args (replicate n ■)} → SVs as → WS-args 0 as → Values as
sv-value P.lam _ = V.lam
sv-value P.lit _ = V.lit
sv-value (P.tuple vs) w = V.tuple (svs-value vs w)
sv-value (P.inl v) (w , _) = V.inl (sv-value v w)
sv-value (P.inr v) (w , _) = V.inr (sv-value v w)
svs-value P.[] _ = V.[]
svs-value (v P.∷ vs) (w , ws) = sv-value v w V.∷ svs-value vs ws

prim-term-out : ∀ o → S.out o ≡ prim-term o
prim-term-out (int n) = refl
prim-term-out (bool true) = refl
prim-term-out (bool false) = refl

{- substitution -}
sub-[] : ∀ τ N V → sub τ (N [ V ]) ≡ sub (exts τ) N [ sub τ V ]
sub-[] τ N V =
  trans (SS.sub-sub τ (V SS.• ids) N)
    (trans (SS.sub-cong (λ { zero → refl ; (suc x) → refl }) N) (sym (SS.exts-[] (sub τ V) τ N)))

sub-prim-term : ∀ τ o → sub τ (prim-term o) ≡ prim-term o
sub-prim-term τ (int n) = refl
sub-prim-term τ (bool true) = refl
sub-prim-term τ (bool false) = refl

sub-proj : ∀ τ {n m} (i : Fin n) (as : Args (replicate m ■)) {V} → proj i (args→list as) ≡ just V
  → proj i (args→list (sub-args τ as)) ≡ just (sub τ V)
sub-proj τ i as e rewrite SS.sub-args-list τ as | proj-map (sub τ) i (args→list as) | e = refl

sub-⟶ : ∀ {τ M M'} → (∀ x → SV (τ x)) → M ⟶ M' → sub τ M ⟶ sub τ M'
sub-⟶s : ∀ {τ n} {as as' : Args (replicate n ■)} → (∀ x → SV (τ x)) → as ⟶s as' → sub-args τ as ⟶s sub-args τ as'
sub-⟶ {τ} h (β {N} {V} v) rewrite sub-[] τ N V = β (sv-sub h v)
sub-⟶ h (app₂ s) = app₂ (sub-⟶ h s)
sub-⟶ h (tuple s) = tuple (sub-⟶s h s)
sub-⟶ {τ} h (get {i = i} {as} vs e) = get (svs-sub h vs) (sub-proj τ i as e)
sub-⟶ h (get₁ s) = get₁ (sub-⟶ h s)
sub-⟶ h (inl₁ s) = inl₁ (sub-⟶ h s)
sub-⟶ h (inr₁ s) = inr₁ (sub-⟶ h s)
sub-⟶ {τ} h (case-l {V} {M} v) rewrite sub-[] τ M V = case-l (sv-sub h v)
sub-⟶ {τ} h (case-r {V} {N = N} v) rewrite sub-[] τ N V = case-r (sv-sub h v)
sub-⟶ {τ} h (prim {p} {n} {m}) rewrite sub-prim-term τ (δ p n m) = prim
sub-⟶ h (case₁ s) = case₁ (sub-⟶ h s)
sub-⟶ h (prim₁ s) = prim₁ (sub-⟶ h s)
sub-⟶ h (prim₂ v s) = prim₂ (sv-sub h v) (sub-⟶ h s)
sub-⟶s h (here s) = here (sub-⟶ h s)
sub-⟶s h (there v s) = there (sv-sub h v) (sub-⟶s h s)

{- in a closed term, a step of the reduction semantics -}
closed-red : ∀ {M M'} → WS 0 M → M ⟶ M' → S.red M ≡ to M'
closed-reds : ∀ {n} {as as' : Args (replicate n ■)} → WS-args 0 as → as ⟶s as' → S.red-args as ≡ to as'
closed-red (_ , wV , _) (β v) rewrite value-red (sv-value v wV) = refl
closed-red (_ , wM , _) (app₂ s) rewrite closed-red wM s = refl
closed-red w (tuple s) rewrite closed-reds w s = refl
closed-red (w , _) (get vs e) rewrite values-red (svs-value vs w) | e = refl
closed-red (w , _) (get₁ s) rewrite closed-red w s = refl
closed-red (w , _) (inl₁ s) rewrite closed-red w s = refl
closed-red (w , _) (inr₁ s) rewrite closed-red w s = refl
closed-red ((w , _) , _) (case-l v) rewrite value-red (sv-value v w) = refl
closed-red ((w , _) , _) (case-r v) rewrite value-red (sv-value v w) = refl
closed-red (w , _) (case₁ s) rewrite closed-red w s = refl
closed-red _ (prim {p} {n} {m}) = cong to (prim-term-out (δ p n m))
closed-red (w , _) (prim₁ s) rewrite closed-red w s = refl
closed-red (wV , wM , _) (prim₂ v s) rewrite value-red (sv-value v wV) | closed-red wM s = refl
closed-reds (w , _) (here s) rewrite closed-red w s = refl
closed-reds (wV , ws) (there v s) rewrite value-red (sv-value v wV) | closed-reds ws s = refl

{- and the term stays closed -}
ws-one : ∀ {V} → WS 0 V → ∀ x → x < 1 → WS 0 ((V SS.• ids) x)
ws-one w zero _ = w
ws-one w (suc x) (s≤s ())

ws-⟶ : ∀ {M M'} → WS 0 M → M ⟶ M' → WS 0 M'
ws-⟶s : ∀ {n} {as as' : Args (replicate n ■)} → WS-args 0 as → as ⟶s as' → WS-args 0 as'
ws-⟶ {app ⦅ lam ⦅ ⟩ N ,, Nil ⦆ ,, V ,, Nil ⦆} ((wN , _) , wV , _) (β v) = ws-sub _ N (ws-one wV) wN
ws-⟶ (wL , wM , _) (app₂ s) = wL , ws-⟶ wM s , tt
ws-⟶ w (tuple s) = ws-⟶s w s
ws-⟶ {get i ⦅ tuple m ⦅ as ⦆ ,, Nil ⦆} (w , _) (get vs e) = ws-proj i as w e
ws-⟶ (w , _) (get₁ s) = ws-⟶ w s , tt
ws-⟶ (w , _) (inl₁ s) = ws-⟶ w s , tt
ws-⟶ (w , _) (inr₁ s) = ws-⟶ w s , tt
ws-⟶ {case-op ⦅ _ ,, ⟩ M ,, ⟩ N ,, Nil ⦆} ((w , _) , wM , _) (case-l v) = ws-sub _ M (ws-one w) wM
ws-⟶ {case-op ⦅ _ ,, ⟩ M ,, ⟩ N ,, Nil ⦆} ((w , _) , _ , wN , _) (case-r v) = ws-sub _ N (ws-one w) wN
ws-⟶ (wL , wM , wN , _) (case₁ s) = ws-⟶ wL s , wM , wN , tt
ws-⟶ _ (prim {p} {n} {m}) = ws-prim-term (δ p n m)
ws-⟶ (wL , wM , _) (prim₁ s) = ws-⟶ wL s , wM , tt
ws-⟶ (wL , wM , _) (prim₂ v s) = wL , ws-⟶ wM s , tt
ws-⟶s (w , ws) (here s) = ws-⟶ w s , ws
ws-⟶s (w , ws) (there v s) = w , ws-⟶s ws s

{- The relation on terms: the target on the left -------------------------------}

infix 4 _≼_
data _≼_ : AST → AST → Set where
  var≼ : ∀ {x} → ` x ≼ ` x
  lam≼ : ∀ {N' N} → N' ≼ N → lam ⦅ ⟩ N' ,, Nil ⦆ ≼ lam ⦅ ⟩ N ,, Nil ⦆
  app≼ : ∀ {L' L M' M} → L' ≼ L → M' ≼ M → app ⦅ L' ,, M' ,, Nil ⦆ ≼ app ⦅ L ,, M ,, Nil ⦆
  lit≼ : ∀ {B k} → lit B k ⦅ Nil ⦆ ≼ lit B k ⦅ Nil ⦆
  tuple≼ : ∀ {n as' as} → Pw _≼_ {n} as' as → tuple n ⦅ as' ⦆ ≼ tuple n ⦅ as ⦆
  get≼ : ∀ {n} {i : Fin n} {M' M} → M' ≼ M → get i ⦅ M' ,, Nil ⦆ ≼ get i ⦅ M ,, Nil ⦆
  inl≼ : ∀ {M' M} → M' ≼ M → inl-op ⦅ M' ,, Nil ⦆ ≼ inl-op ⦅ M ,, Nil ⦆
  inr≼ : ∀ {M' M} → M' ≼ M → inr-op ⦅ M' ,, Nil ⦆ ≼ inr-op ⦅ M ,, Nil ⦆
  case≼ : ∀ {L' L M' M N' N} → L' ≼ L → M' ≼ M → N' ≼ N
    → case-op ⦅ L' ,, ⟩ M' ,, ⟩ N' ,, Nil ⦆ ≼ case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆
  prim≼ : ∀ {p L' L M' M} → L' ≼ L → M' ≼ M → prim p ⦅ L' ,, M' ,, Nil ⦆ ≼ prim p ⦅ L ,, M ,, Nil ⦆
  {- the source steps first -}
  step : ∀ {M' M M₁} → M ⟶ M₁ → M' ≼ M₁ → M' ≼ M
  {- a let of a value that simplify kept: the bodies after β -}
  let≼ : ∀ {N' V' N W} → SV W → V' ≼ W → N' [ V' ] ≼ N [ W ]
    → app ⦅ lam ⦅ ⟩ N' ,, Nil ⦆ ,, V' ,, Nil ⦆ ≼ app ⦅ lam ⦅ ⟩ N ,, Nil ⦆ ,, W ,, Nil ⦆

steps : ∀ {M' M M₁} → M ⟶* M₁ → M' ≼ M₁ → M' ≼ M
steps RT.ε r = r
steps (s RT.◅ σ) r = step s (steps σ r)

{- Closure under substitution -------------------------------------------------}

{- the source's substitution substitutes values -}
Ok : Subst → Subst → Set
Ok υ τ = ∀ x → SV (τ x)

module Kit (Pr : Subst → Subst → Set) (p≼ : ∀ {υ τ} → Pr υ τ → ∀ x → υ x ≼ τ x)
  (pok : ∀ {υ τ} → Pr υ τ → Ok υ τ) (pexts : ∀ {υ τ} → Pr υ τ → Pr (exts υ) (exts τ)) where

  ≼-sub : ∀ {υ τ M' M} → Pr υ τ → M' ≼ M → sub υ M' ≼ sub τ M
  ≼-subs : ∀ {υ τ n as' as} → Pr υ τ → Pw _≼_ {n} as' as → Pw _≼_ (sub-args υ as') (sub-args τ as)
  ≼-sub p var≼ = p≼ p _
  ≼-sub p (lam≼ r) = lam≼ (≼-sub (pexts p) r)
  ≼-sub p (app≼ r s) = app≼ (≼-sub p r) (≼-sub p s)
  ≼-sub p lit≼ = lit≼
  ≼-sub p (tuple≼ rs) = tuple≼ (≼-subs p rs)
  ≼-sub p (get≼ r) = get≼ (≼-sub p r)
  ≼-sub p (inl≼ r) = inl≼ (≼-sub p r)
  ≼-sub p (inr≼ r) = inr≼ (≼-sub p r)
  ≼-sub p (case≼ r s t) = case≼ (≼-sub p r) (≼-sub (pexts p) s) (≼-sub (pexts p) t)
  ≼-sub p (prim≼ r s) = prim≼ (≼-sub p r) (≼-sub p s)
  ≼-sub p (step s r) = step (sub-⟶ (pok p) s) (≼-sub p r)
  ≼-sub {υ} {τ} p (let≼ {N'} {V'} {N} {W} w r s) =
    let≼ (sv-sub (pok p) w) (≼-sub p r) (subst₂ _≼_ (sub-[] υ N' V') (sub-[] τ N W) (≼-sub p s))
  ≼-subs p [] = []
  ≼-subs p (r ∷ rs) = ≼-sub p r ∷ ≼-subs p rs

sv-exts : ∀ {τ} → (∀ x → SV (τ x)) → ∀ x → SV (exts τ x)
sv-exts h zero = P.var 0
sv-exts h (suc x) = sv-rename suc (h x)

open SubstRel.Closure _≼_ var≼ Ok (λ h x → subst SV (sym (proj₂ (proj₂ (h x)))) (P.var (proj₁ (h x))))
  (λ {υ} {τ} → sv-exts {τ}) Kit.≼-sub
  using () renaming (≈-rename to ≼-rename; ≈-subst to ≼-subst)

{- substituting one value -}
one-sub : ∀ {V' W} → V' ≼ W → SV W → (∀ x → (V' SS.• ids) x ≼ (W SS.• ids) x) × Ok (V' SS.• ids) (W SS.• ids)
one-sub r w = (λ { zero → r ; (suc x) → var≼ }) , (λ { zero → w ; (suc x) → P.var x })

{- Values: the source reaches the values that the target has -------------------}

eval-sv : ∀ {V' M} → SV V' → V' ≼ M → Σ[ W ∈ AST ] M ⟶* W × SV W × V' ≼ W
eval-svs : ∀ {n} {as' as : Args (replicate n ■)} → SVs as' → Pw _≼_ as' as
  → Σ[ Ws ∈ Args (replicate n ■) ] Star _⟶s_ as Ws × SVs Ws × Pw _≼_ as' Ws
eval-sv (P.var x) var≼ = ` x , RT.ε , P.var x , var≼
eval-sv P.lam (lam≼ r) = _ , RT.ε , P.lam , lam≼ r
eval-sv P.lit lit≼ = _ , RT.ε , P.lit , lit≼
eval-sv (P.tuple {n} vs) (tuple≼ rs) with eval-svs vs rs
... | Ws , σ , ws , rs' = tuple n ⦅ Ws ⦆ , gmap (λ X → tuple n ⦅ X ⦆) tuple σ , P.tuple ws , tuple≼ rs'
eval-sv (P.inl v) (inl≼ r) with eval-sv v r
... | W , σ , w , r' = _ , gmap (λ X → inl-op ⦅ X ,, Nil ⦆) inl₁ σ , P.inl w , inl≼ r'
eval-sv (P.inr v) (inr≼ r) with eval-sv v r
... | W , σ , w , r' = _ , gmap (λ X → inr-op ⦅ X ,, Nil ⦆) inr₁ σ , P.inr w , inr≼ r'
eval-sv v (step s r) with eval-sv v r
... | W , σ , w , r' = W , s RT.◅ σ , w , r'
eval-svs P.[] [] = Nil , RT.ε , P.[] , []
eval-svs (v P.∷ vs) (r ∷ rs) with eval-sv v r | eval-svs vs rs
... | W , σ , w , r' | Ws , σs , ws , rs' =
  (W ,, Ws) , (gmap (λ X → X ,, _) here σ RT.◅◅ gmap (λ Xs → W ,, Xs) (there w) σs) , w P.∷ ws , r' ∷ rs'

{- the shapes of related values -}
inl-inv : ∀ {V' W} → SV W → inl-op ⦅ V' ,, Nil ⦆ ≼ W → Σ[ W₀ ∈ AST ] W ≡ inl-op ⦅ W₀ ,, Nil ⦆ × SV W₀ × V' ≼ W₀
inl-inv (P.inl w) (inl≼ r) = _ , refl , w , r
inl-inv w (step s _) = ⊥-elim (sv-nostep w s)

inr-inv : ∀ {V' W} → SV W → inr-op ⦅ V' ,, Nil ⦆ ≼ W → Σ[ W₀ ∈ AST ] W ≡ inr-op ⦅ W₀ ,, Nil ⦆ × SV W₀ × V' ≼ W₀
inr-inv (P.inr w) (inr≼ r) = _ , refl , w , r
inr-inv w (step s _) = ⊥-elim (sv-nostep w s)

tuple-inv : ∀ {n} {as' : Args (replicate n ■)} {W} → SV W → tuple n ⦅ as' ⦆ ≼ W
  → Σ[ Ws ∈ Args (replicate n ■) ] W ≡ tuple n ⦅ Ws ⦆ × SVs Ws × Pw _≼_ as' Ws
tuple-inv (P.tuple ws) (tuple≼ rs) = _ , refl , ws , rs
tuple-inv w (step s _) = ⊥-elim (sv-nostep w s)

lit-inv : ∀ {B k W} → SV W → lit B k ⦅ Nil ⦆ ≼ W → W ≡ lit B k ⦅ Nil ⦆
lit-inv P.lit lit≼ = refl
lit-inv w (step s _) = ⊥-elim (sv-nostep w s)

pw-just : ∀ {a mb} → M.Pointwise _≼_ (just a) mb → Σ[ b ∈ AST ] mb ≡ just b × a ≼ b
pw-just (M.just r) = _ , refl , r

≼-prim-term : ∀ o → prim-term o ≼ prim-term o
≼-prim-term (int n) = lit≼
≼-prim-term (bool true) = inl≼ (tuple≼ [])
≼-prim-term (bool false) = inr≼ (tuple≼ [])

{- What simp knows, and what it means -------------------------------------------}

{- I is true of the source term X after υ: its term, and its known value,
   are related to X -}
record Desc (I : Info) (υ : Subst) (X : AST) : Set where
  constructor desc
  field
    tm : sub υ (term I) ≼ X
    kn : ∀ {K} → known I ≡ just K → SV K × sub υ K ≼ X
open Desc

record Inv (E : Facts) (τ υ : Subst) : Set where
  field
    at : ∀ x → Desc (E x) υ (τ x)
    svτ : ∀ x → SV (τ x)
    svυ : ∀ x → SV (υ x)
open Inv

desc-steps : ∀ {I υ X X₁} → X ⟶* X₁ → Desc I υ X₁ → Desc I υ X
desc-steps σ (desc t k) = desc (steps σ t) (λ e → proj₁ (k e) , steps σ (proj₂ (k e)))

desc-self : ∀ {V υ X} → SV V → sub υ V ≼ X → Desc (self V) υ X
desc-self v r = desc r (λ { refl → v , r })

desc-info : ∀ {M υ X} → sub υ M ≼ X → Desc (info M) υ X
desc-info {M} r with value M in e
... | true = desc r (λ { refl → value-sv M e , r })
... | false = desc r (λ ())

{- under one more binder, in the source and the target -}
desc-ext : ∀ {I υ X} → Desc I υ X → Desc (shift-info I) (exts υ) (shift X)
desc-ext {T ∣ k} {υ} (desc t kn) = desc (subst (_≼ _) (sym (SS.exts-shift υ T)) (≼-rename suc t)) (G k kn)
  where
  G : ∀ k → (∀ {K} → k ≡ just K → SV K × sub υ K ≼ _)
    → ∀ {K} → map shift k ≡ just K → SV K × sub (exts υ) K ≼ _
  G (just K) h refl = sv-rename suc (proj₁ (h refl)) , subst (_≼ _) (sym (SS.exts-shift υ K)) (≼-rename suc (proj₂ (h refl)))

{- under one more binder, in the target only, bound to V -}
desc-cons : ∀ {I υ X} V → Desc I υ X → Desc (shift-info I) (V SS.• υ) X
desc-cons {T ∣ k} {υ} V (desc t kn) = desc (subst (_≼ _) (sym (SS.sub-shift V υ T)) t) (G k kn)
  where
  G : ∀ k → (∀ {K} → k ≡ just K → SV K × sub υ K ≼ _)
    → ∀ {K} → map shift k ≡ just K → SV K × sub (V SS.• υ) K ≼ _
  G (just K) h refl = sv-rename suc (proj₁ (h refl)) , subst (_≼ _) (sym (SS.sub-shift V υ K)) (proj₂ (h refl))

inv-under : ∀ {E τ υ} → Inv E τ υ → Inv (under E) (exts τ) (exts υ)
inv-under ok = record
  { at = λ { zero → desc-self (P.var 0) var≼ ; (suc x) → desc-ext (at ok x) }
  ; svτ = sv-exts (svτ ok) ; svυ = sv-exts (svυ ok) }

{- The main lemma -------------------------------------------------------------------}

simp-ok : ∀ M {E τ υ} → Inv E τ υ → Desc (simp E M) υ (sub τ M)
simp-args-ok : ∀ {n} (as : Args (replicate n ■)) {E τ υ} → Inv E τ υ
  → Pw _≼_ (sub-args υ (simp-args E as)) (sub-args τ as)
app-ok : ∀ L M {E τ υ I} → Inv E τ υ → Desc I υ (sub τ M)
  → Desc (simp-app E L I) υ (sub τ (app ⦅ L ,, M ,, Nil ⦆))
let-ok : ∀ N M {E τ υ I} → Inv E τ υ → Desc I υ (sub τ M)
  → Desc (simp-let E N I) υ (sub τ (app ⦅ lam ⦅ ⟩ N ,, Nil ⦆ ,, M ,, Nil ⦆))
case-ok : ∀ L M N {E τ υ I} → Inv E τ υ → Desc I υ (sub τ L)
  → Desc (simp-case E I M N) υ (sub τ (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆))

simp-ok (` x) ok = at ok x
simp-ok (lam ⦅ ⟩ N ,, Nil ⦆) ok = desc-self P.lam (lam≼ (tm (simp-ok N (inv-under ok))))
simp-ok (app ⦅ L ,, M ,, Nil ⦆) ok = app-ok L M ok (simp-ok M ok)
simp-ok (lit B k ⦅ Nil ⦆) ok = desc-self P.lit lit≼
simp-ok (tuple n ⦅ as ⦆) ok = desc-info (tuple≼ (simp-args-ok as ok))
simp-ok (get i ⦅ L ,, Nil ⦆) {E} {τ} {υ} ok = get-ok (simp E L) (simp-ok L ok)
  where
  {- the component of a known tuple, which the source reaches -}
  comp : ∀ k {K} → component i k ≡ just K → (∀ {Kt} → k ≡ just Kt → SV Kt × sub υ Kt ≼ sub τ L)
    → SV K × sub υ K ≼ sub τ (get i ⦅ L ,, Nil ⦆)
  comp (just Kt) e h with h refl
  ... | P.tuple {m} {Ks} vs , r with eval-sv (sv-sub (svυ ok) (P.tuple vs)) r
  ...   | W , σ , w , r' with tuple-inv w r'
  ...     | Ws , refl , ws , rs
            with pw-just (subst (λ m → M.Pointwise _≼_ m (proj i (args→list Ws)))
                                (sub-proj υ i Ks e) (proj-pw i (pw-list rs)))
  ...       | Wi , e' , r'' =
    component-just i vs e , steps (gmap (λ X → get i ⦅ X ,, Nil ⦆) get₁ σ RT.◅◅ (get ws e' RT.◅ RT.ε)) r''
  get-ok : ∀ I → Desc I υ (sub τ L) → Desc (simp-get i I) υ (sub τ (get i ⦅ L ,, Nil ⦆))
  get-ok I d with component i (known I) in e
  ... | nothing = desc (get≼ (tm d)) (λ ())
  ... | just K with comp (known I) e (kn d) | small K
  ...   | v , r | true = desc-self v r
  ...   | v , r | false = desc (get≼ (tm d)) (λ { refl → v , r })
simp-ok (inl-op ⦅ M ,, Nil ⦆) ok = desc-info (inl≼ (tm (simp-ok M ok)))
simp-ok (inr-op ⦅ M ,, Nil ⦆) ok = desc-info (inr≼ (tm (simp-ok M ok)))
simp-ok (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) ok = case-ok L M N ok (simp-ok L ok)
simp-ok (prim p ⦅ L ,, M ,, Nil ⦆) {E} {τ} {υ} ok = prim-ok (simp E L) (simp E M) (simp-ok L ok) (simp-ok M ok)
  where
  {- a known integer, which the source reaches -}
  int-eval : ∀ k {n X} → int-of k ≡ just n → (∀ {K} → k ≡ just K → SV K × sub υ K ≼ X) → X ⟶* lit Int n ⦅ Nil ⦆
  int-eval (just K) e h with h refl
  ... | v , r with int-of-just v e
  ...   | refl with eval-sv P.lit r
  ...     | W , σ , w , r' with lit-inv w r'
  ...       | refl = σ
  prim-ok : ∀ I J → Desc I υ (sub τ L) → Desc J υ (sub τ M) → Desc (simp-prim p I J) υ (sub τ (prim p ⦅ L ,, M ,, Nil ⦆))
  prim-ok I J dI dJ with int-of (known I) in e₁
  ... | nothing = desc (prim≼ (tm dI) (tm dJ)) (λ ())
  ... | just n with int-of (known J) in e₂
  ...   | nothing = desc (prim≼ (tm dI) (tm dJ)) (λ ())
  ...   | just m =
    desc-steps (gmap (λ X → prim p ⦅ X ,, sub τ M ,, Nil ⦆) prim₁ (int-eval (known I) e₁ (kn dI))
                RT.◅◅ gmap (λ X → prim p ⦅ lit Int n ⦅ Nil ⦆ ,, X ,, Nil ⦆) (prim₂ P.lit) (int-eval (known J) e₂ (kn dJ))
                RT.◅◅ (prim RT.◅ RT.ε))
      (desc-self (prim-term-sv (δ p n m)) (subst (_≼ _) (sym (sub-prim-term υ (δ p n m))) (≼-prim-term (δ p n m))))

simp-args-ok {zero} Nil ok = []
simp-args-ok {suc n} (M ,, as) ok = tm (simp-ok M ok) ∷ simp-args-ok as ok

{- an application whose operator is not a function stays -}
app-ok (lam ⦅ ⟩ N ,, Nil ⦆) M ok d = let-ok N M ok d
app-ok L@(` x) M ok d = desc (app≼ (tm (simp-ok L ok)) (tm d)) (λ ())
app-ok L@(app ⦅ _ ⦆) M ok d = desc (app≼ (tm (simp-ok L ok)) (tm d)) (λ ())
app-ok L@(lit B k ⦅ _ ⦆) M ok d = desc (app≼ (tm (simp-ok L ok)) (tm d)) (λ ())
app-ok L@(tuple n ⦅ _ ⦆) M ok d = desc (app≼ (tm (simp-ok L ok)) (tm d)) (λ ())
app-ok L@(get i ⦅ _ ⦆) M ok d = desc (app≼ (tm (simp-ok L ok)) (tm d)) (λ ())
app-ok L@(inl-op ⦅ _ ⦆) M ok d = desc (app≼ (tm (simp-ok L ok)) (tm d)) (λ ())
app-ok L@(inr-op ⦅ _ ⦆) M ok d = desc (app≼ (tm (simp-ok L ok)) (tm d)) (λ ())
app-ok L@(case-op ⦅ _ ⦆) M ok d = desc (app≼ (tm (simp-ok L ok)) (tm d)) (λ ())
app-ok L@(prim p ⦅ _ ⦆) M ok d = desc (app≼ (tm (simp-ok L ok)) (tm d)) (λ ())

{- β: the source evaluates the operand to a value W -}
let-ok N M {E} {τ} {υ} {I} ok d with small (term I) in s | value (term I) in v
... | true | _ with eval-sv (sv-sub (svυ ok) (small-sv (term I) s)) (tm d)
...   | W , σ , w , r =
  desc-steps (gmap (λ X → app ⦅ lam ⦅ ⟩ sub (exts τ) N ,, Nil ⦆ ,, X ,, Nil ⦆) app₂ σ RT.◅◅ (β w RT.◅ RT.ε))
    (subst (Desc _ υ) (sym (SS.exts-[] W τ N)) (simp-ok N ok'))
  where
  ok' : Inv (self (term I) • E) (W SS.• τ) υ
  ok' = record { at = λ { zero → desc-self (small-sv (term I) s) r ; (suc x) → at ok x }
               ; svτ = λ { zero → w ; (suc x) → svτ ok x } ; svυ = svυ ok }
let-ok N M {E} {τ} {υ} {I} ok d | false | true with eval-sv (sv-sub (svυ ok) (value-sv (term I) v)) (tm d)
...   | W , σ , w , r =
  desc (steps (gmap (λ X → app ⦅ lam ⦅ ⟩ sub (exts τ) N ,, Nil ⦆ ,, X ,, Nil ⦆) app₂ σ)
          (let≼ w r (subst₂ _≼_ (sym (SS.exts-[] (sub υ (term I)) υ N')) (sym (SS.exts-[] W τ N)) (tm (simp-ok N ok')))))
       (λ ())
  where
  E' = ((` 0) ∣ just (shift (term I))) • (λ x → shift-info (E x))
  N' = term (simp E' N)
  ok' : Inv E' (W SS.• τ) (sub υ (term I) SS.• υ)
  ok' = record
    { at = λ { zero → desc r (λ { refl → sv-rename suc (value-sv (term I) v)
                                        , subst (_≼ _) (sym (SS.sub-shift (sub υ (term I)) υ (term I))) r })
             ; (suc x) → desc-cons (sub υ (term I)) (at ok x) }
    ; svτ = λ { zero → w ; (suc x) → svτ ok x }
    ; svυ = λ { zero → sv-sub (svυ ok) (value-sv (term I) v) ; (suc x) → svυ ok x } }
let-ok N M ok d | false | false = desc (app≼ (lam≼ (tm (simp-ok N (inv-under ok)))) (tm d)) (λ ())

{- a case on a known injection: the source evaluates the scrutinee to it -}
case-ok L M N {E} {τ} {υ} {I} ok d with branch (known I) in e
... | nothing = desc (case≼ (tm d) (tm (simp-ok M (inv-under ok))) (tm (simp-ok N (inv-under ok)))) (λ ())
... | just (true , K) = taken (known I) e (kn d)
  where
  taken : ∀ k → branch k ≡ just (true , K) → (∀ {Kt} → k ≡ just Kt → SV Kt × sub υ Kt ≼ sub τ L)
    → Desc (simp (self K • E) M) υ (sub τ (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆))
  taken (just Kt) e h with h refl
  taken (just Kt) e h | P.inl {K₀} v , r with small K₀ | e
  taken (just Kt) e h | P.inl {K₀} v , r | true | refl with eval-sv (sv-sub (svυ ok) (P.inl v)) r
  ... | W , σ , w , r' with inl-inv w r'
  ...   | W₀ , refl , w₀ , r₀ =
    desc-steps (gmap (λ X → case-op ⦅ X ,, ⟩ sub (exts τ) M ,, ⟩ sub (exts τ) N ,, Nil ⦆) case₁ σ RT.◅◅ (case-l w₀ RT.◅ RT.ε))
      (subst (Desc _ υ) (sym (SS.exts-[] W₀ τ M)) (simp-ok M ok'))
    where
    ok' : Inv (self K • E) (W₀ SS.• τ) υ
    ok' = record { at = λ { zero → desc-self v r₀ ; (suc x) → at ok x }
                 ; svτ = λ { zero → w₀ ; (suc x) → svτ ok x } ; svυ = svυ ok }
  taken (just Kt) e h | P.inl {K₀} v , r | false | ()
  taken (just Kt) e h | P.inr {K₀} v , r with small K₀ | e
  taken (just Kt) e h | P.inr {K₀} v , r | true | ()
  taken (just Kt) e h | P.inr {K₀} v , r | false | ()
... | just (false , K) = taken (known I) e (kn d)
  where
  taken : ∀ k → branch k ≡ just (false , K) → (∀ {Kt} → k ≡ just Kt → SV Kt × sub υ Kt ≼ sub τ L)
    → Desc (simp (self K • E) N) υ (sub τ (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆))
  taken (just Kt) e h with h refl
  taken (just Kt) e h | P.inr {K₀} v , r with small K₀ | e
  taken (just Kt) e h | P.inr {K₀} v , r | true | refl with eval-sv (sv-sub (svυ ok) (P.inr v)) r
  ... | W , σ , w , r' with inr-inv w r'
  ...   | W₀ , refl , w₀ , r₀ =
    desc-steps (gmap (λ X → case-op ⦅ X ,, ⟩ sub (exts τ) M ,, ⟩ sub (exts τ) N ,, Nil ⦆) case₁ σ RT.◅◅ (case-r w₀ RT.◅ RT.ε))
      (subst (Desc _ υ) (sym (SS.exts-[] W₀ τ N)) (simp-ok N ok'))
    where
    ok' : Inv (self K • E) (W₀ SS.• τ) υ
    ok' = record { at = λ { zero → desc-self v r₀ ; (suc x) → at ok x }
                 ; svτ = λ { zero → w₀ ; (suc x) → svτ ok x } ; svυ = svυ ok }
  taken (just Kt) e h | P.inr {K₀} v , r | false | ()
  taken (just Kt) e h | P.inl {K₀} v , r with small K₀ | e
  taken (just Kt) e h | P.inl {K₀} v , r | true | ()
  taken (just Kt) e h | P.inl {K₀} v , r | false | ()

{- the program, simplified, is related to itself -}
simplify-≼ : ∀ M → simplify M ≼ M
simplify-≼ M = subst₂ _≼_ (SS.sub-id _) (SS.sub-id M) (tm (simp-ok M ok₀))
  where ok₀ : Inv (λ x → self (` x)) ids ids
        ok₀ = record { at = λ x → desc-self (P.var x) var≼ ; svτ = P.var ; svυ = P.var }

{- The simulation of the target by the source -----------------------------------}

{- related terms, the source closed -}
R : AST → AST → Set
R M' M = M' ≼ M × WS 0 M

Ans′ = Ans S.red Value R

{- a target term related to a source value is a value, observed alike -}
≼-value : ∀ {V' W} → Value W → V' ≼ W → Value V'
≼-values : ∀ {n} {as' as : Args (replicate n ■)} → Values as → Pw _≼_ as' as → Values as'
≼-value V.lam (lam≼ _) = V.lam
≼-value V.lit lit≼ = V.lit
≼-value (V.tuple vs) (tuple≼ rs) = V.tuple (≼-values vs rs)
≼-value (V.inl v) (inl≼ r) = V.inl (≼-value v r)
≼-value (V.inr v) (inr≼ r) = V.inr (≼-value v r)
≼-value v (step s _) = ⊥-elim (sv-nostep (val-sv v) s)
≼-values V.[] [] = V.[]
≼-values (v V.∷ vs) (r ∷ rs) = ≼-value v r V.∷ ≼-values vs rs

obs≼ : ∀ {V' W} → Value W → V' ≼ W → S.obs V' ≡ S.obs W
obs≼s : ∀ {n} {as' as : Args (replicate n ■)} → Values as → Pw _≼_ as' as → S.obs-args as' ≡ S.obs-args as
obs≼ V.lam (lam≼ _) = refl
obs≼ V.lit lit≼ = refl
obs≼ (V.tuple vs) (tuple≼ rs) = cong o-tuple (obs≼s vs rs)
obs≼ (V.inl v) (inl≼ r) = cong o-inl (obs≼ v r)
obs≼ (V.inr v) (inr≼ r) = cong o-inr (obs≼ v r)
obs≼ v (step s _) = ⊥-elim (sv-nostep (val-sv v) s)
obs≼s V.[] [] = refl
obs≼s (v V.∷ vs) (r ∷ rs) = cong₂ _∷_ (obs≼ v r) (obs≼s vs rs)

zipR : ∀ {n as' as} → Pw _≼_ {n} as' as → WS-args 0 as → Pw R as' as
zipR [] _ = []
zipR (r ∷ rs) (w , ws) = (r , w) ∷ zipR rs ws

unzipR : ∀ {n as' as} → Pw R {n} as' as → Pw _≼_ as' as × WS-args 0 as
unzipR [] = [] , tt
unzipR ((r , w) ∷ rs) = (r ∷ proj₁ (unzipR rs)) , w , proj₂ (unzipR rs)

ret?-ans : ∀ {M mv mw X} → M.Pointwise R mv mw → S.red X ≡ S.ret? mw → Ans′ M (S.ret? mv) X
ret?-ans (M.just r) e = to (one e) r
ret?-ans M.nothing e = wrong ε e

{- the body N' of a function, after β, is related to the source's -}
β≼ : ∀ {N' N V' W} → N' ≼ N → V' ≼ W → Value W → WS 1 N → WS 0 W → R (N' [ V' ]) (N [ W ])
β≼ {N = N} r s v wN wW = ≼-subst (one-sub s (val-sv v)) r , ws-sub _ N (ws-one wW) wN

sim : ∀ {M' M} → M' ≼ M → WS 0 M → Ans′ M' (S.red M') M
sims : ∀ {n as' as} → Pw _≼_ {n} as' as → WS-args 0 as → Ans S.red-args Values (Pw R) as' (S.red-args as') as
sim var≼ w = wrong ε refl
sim (lam≼ r) w = val ε V.lam (lam≼ r , w)
sim (app≼ r s) (wL , wM , _) =
  ans-in (frame _ (λ _ → refl)) (λ (r' , w') → app≼ r' s , w' , wM , tt) (sim r wL) (λ v m → app-sim v m s wM)
  where
  app-sim : ∀ {L' W M' M} → Value W → R L' W → M' ≼ M → WS 0 M
    → Ans′ (app ⦅ L' ,, M' ,, Nil ⦆) (S.app? L' (S.red M') M') (app ⦅ W ,, M ,, Nil ⦆)
  app-sim {W = W} V.lam (lam≼ r₁ , wW) s wM =
    ans-in (frame {g = λ X → app ⦅ W ,, X ,, Nil ⦆} _ (λ X → refl))
           (λ (s' , w') → app≼ (lam≼ r₁) s' , wW , w' , tt) (sim s wM)
           λ v' (s' , w') → to (one (val-in (value-red v'))) (β≼ r₁ s' v' (proj₁ wW) w')
  app-sim V.lit (lit≼ , _) s wM = wrong ε refl
  app-sim v@(V.tuple _) (tuple≼ _ , _) s wM = wrong ε (val-in (value-red v))
  app-sim v@(V.inl _) (inl≼ _ , _) s wM = wrong ε (val-in (value-red v))
  app-sim v@(V.inr _) (inr≼ _ , _) s wM = wrong ε (val-in (value-red v))
  app-sim v (step st _ , _) s wM = ⊥-elim (sv-nostep (val-sv v) st)
sim lit≼ w = val ε V.lit (lit≼ , w)
sim (tuple≼ rs) ws =
  ans-in (frame _ (λ _ → refl)) (λ ms → tuple≼ (proj₁ (unzipR ms)) , proj₂ (unzipR ms)) (sims rs ws)
         (λ vs ms → val ε (V.tuple vs) (tuple≼ (proj₁ (unzipR ms)) , proj₂ (unzipR ms)))
sim (get≼ {i = i} r) (w , _) = ans-in (frame _ (λ _ → refl)) (λ (r' , w') → get≼ r' , w' , tt) (sim r w) get-sim
  where
  get-sim : ∀ {M' W} → Value W → R M' W → Ans′ (get i ⦅ M' ,, Nil ⦆) (S.get? i M') (get i ⦅ W ,, Nil ⦆)
  get-sim v@(V.tuple _) (tuple≼ rs , ws) = ret?-ans (proj-pw {R = R} i (pw-list (zipR rs ws))) (val-in (value-red v))
  get-sim V.lam (lam≼ _ , _) = wrong ε refl
  get-sim V.lit (lit≼ , _) = wrong ε refl
  get-sim v@(V.inl _) (inl≼ _ , _) = wrong ε (val-in (value-red v))
  get-sim v@(V.inr _) (inr≼ _ , _) = wrong ε (val-in (value-red v))
  get-sim v (step st _ , _) = ⊥-elim (sv-nostep (val-sv v) st)
sim (inl≼ r) (w , _) =
  ans-in (frame _ (λ _ → refl)) (λ (r' , w') → inl≼ r' , w' , tt) (sim r w) (λ v (r' , w') → val ε (V.inl v) (inl≼ r' , w' , tt))
sim (inr≼ r) (w , _) =
  ans-in (frame _ (λ _ → refl)) (λ (r' , w') → inr≼ r' , w' , tt) (sim r w) (λ v (r' , w') → val ε (V.inr v) (inr≼ r' , w' , tt))
sim (case≼ {M' = M'} {M} {N'} {N} r s t) (wL , wM , wN , _) =
  ans-in (frame _ (λ _ → refl)) (λ (r' , w') → case≼ r' s t , w' , wM , wN , tt) (sim r wL) case-sim
  where
  case-sim : ∀ {L' W} → Value W → R L' W
    → Ans′ (case-op ⦅ L' ,, ⟩ M' ,, ⟩ N' ,, Nil ⦆) (S.case? L' M' N') (case-op ⦅ W ,, ⟩ M ,, ⟩ N ,, Nil ⦆)
  case-sim v@(V.inl v₁) (inl≼ r' , w' , _) = to (one (val-in (value-red v))) (β≼ s r' v₁ wM w')
  case-sim v@(V.inr v₁) (inr≼ r' , w' , _) = to (one (val-in (value-red v))) (β≼ t r' v₁ wN w')
  case-sim V.lam (lam≼ _ , _) = wrong ε refl
  case-sim V.lit (lit≼ , _) = wrong ε refl
  case-sim v@(V.tuple _) (tuple≼ _ , _) = wrong ε (val-in (value-red v))
  case-sim v (step st _ , _) = ⊥-elim (sv-nostep (val-sv v) st)
sim (prim≼ {p} r s) (wL , wM , _) =
  ans-in (frame _ (λ _ → refl)) (λ (r' , w') → prim≼ r' s , w' , wM , tt) (sim r wL)
    λ v (r' , w') → ans-in (frame {g = λ X → prim p ⦅ _ ,, X ,, Nil ⦆} _ (λ X → val-in (value-red v)))
                           (λ (s' , w'') → prim≼ r' s' , w' , w'' , tt) (sim s wM)
      λ v' (s' , w'') → ret?-ans (out≼ (obs≼ v r') (obs≼ v' s')) (trans (val-in (value-red v)) (val-in (value-red v')))
  where
  out≼ : ∀ {o₁ o₁' o₂ o₂'} → o₁ ≡ o₁' → o₂ ≡ o₂'
    → M.Pointwise R (map S.out (δ? p o₁ o₂)) (map S.out (δ? p o₁' o₂'))
  out≼ {o₁} {_} {o₂} refl refl with δ? p o₁ o₂
  ... | nothing = M.nothing
  ... | just (int n) = M.just (lit≼ , tt)
  ... | just (bool true) = M.just (inl≼ (tuple≼ []) , tt , tt)
  ... | just (bool false) = M.just (inr≼ (tuple≼ []) , tt , tt)
sim (step st r) w = ans-step (closed-red w st) (sim r (ws-⟶ w st))
sim (let≼ {N'} {V'} {N} {W} wv r₁ r₂) ((wN , _) , wW , _) =
  subst (λ x → Ans′ (app ⦅ lam ⦅ ⟩ N' ,, Nil ⦆ ,, V' ,, Nil ⦆) x (app ⦅ lam ⦅ ⟩ N ,, Nil ⦆ ,, W ,, Nil ⦆))
        (sym (val-in (value-red (≼-value v r₁))))
        (to (one (val-in (value-red v))) (r₂ , ws-sub _ N (ws-one wW) wN))
  where v = sv-value wv wW
sims [] _ = val ε V.[] []
sims (r ∷ rs) (w , ws) =
  ans-in (frame _ (λ _ → refl)) (λ m → m ∷ zipR rs ws) (sim r w)
    λ v m → ans-in (frame {g = λ Xs → _ ,, Xs} _ (λ X → val-in (value-red v))) (m ∷_) (sims rs ws)
      λ vs ms → val ε (v V.∷ vs) (m ∷ ms)

{- The end theorem: for closed programs ------------------------------------------}

simplify-correct : ∀ M → Closed M → Equivalent (S.sem M) (S.sem (simplify M))
simplify-correct M c =
  equiv-sym (red-equivalent value-red R (λ (m , w) → sim m w) (λ (m , _) _ v → obs≼ v m) (simplify-≼ M , closed-ws {M} c))

{-

  Correctness of the enclose pass (ISWIM → Clos2) by a forward simulation
  between their reduction semantics (see the design note in
  Semantics/Reduction/Smallstep.agda).

  The two reductions run in lock step: an ISWIM function and the Clos2
  closure of a closed program are both values, since the free variables
  that the closure captures have been replaced by values.

  The relation on terms (_≈_) is a congruence, closed under substitution
  (≈-subst), except for functions. Substitution goes into an ISWIM
  function, but not into the code of a Clos2 closure, only into the
  terms it captures. So an ISWIM function lam (sub (exts σ) N), the
  function N of the program after the substitution σ, is related to the
  closure of enclose N that captures terms related to σ (on the variables
  N uses). Applying them substitutes related values in N and enclose N,
  which gives related terms (enc, the fundamental lemma: sub τ M is
  related to sub τ' (enclose M) for related τ and τ').

  A closure captures variables or values (VV). The target program is
  closed, and stays closed (R), so a closure that is reduced captures
  values only, and is a value.

-}

module proof.Correctness.Reduction.EncloseRed where

open import Framework.Syntax.SyntaxUtil using (_,,_; Nil; ⟩_,,_)
open import Language.ISWIM
import Language.Clos2 as C
open import Compiler.Optimize using (bind-n-ast)
open import Language.Clos2 using (unbind-n)
open import Compiler.Enclose using (enclose; enc-args; fv-vars)
open import proof.Compiler.EncloseScope using (Closed; enclose-closed; module Enclosed)
open import Semantics.Observation
open import proof.Framework.Reduction Obs o-wrong
open import Semantics.Reduction.Smallstep using (Equivalent)
import Semantics.Reduction.ISWIM as S
import proof.Semantics.Reduction.Clos2 as T
open T using (Value; Values; value-red; values-red; value-sub)
open import proof.Framework.Syntax.Uses Op sig using (Uses; UsesArg; UsesArgs; bound; uses-bound; <-∸1)
import proof.Framework.Syntax.Subst Op sig as IS
import Framework.Syntax.Rename Op sig as IR
import Framework.Syntax.Rename C.Op C.sig as CR
import proof.Framework.Syntax.SubstRel Op sig C.Op C.sig as SubstRel
import proof.Framework.Syntax.Subst C.Op C.sig as CS
open IS using (exts; sub; sub-args; ids; _[_])
open import proof.Framework.Syntax.ScopeSubst C.Op C.sig using (ws-sub; SFits; sfits-extend)
open import Framework.Syntax.Scope C.Op C.sig using (WS; WS-args)
open import proof.Framework.ListUtil using (proj-pw)

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin)
open import Data.List using (replicate; _∷_)
import Data.Maybe.Relation.Binary.Pointwise as M
open import Data.Maybe using (just; nothing; map)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≤_; _<_; z≤n; s≤s)
open import Data.Nat.Properties using (m≤n+m∸n; ≤-pred; m≤n⇒m<n∨m≡n; +-identityʳ; ≤-trans)
open import Data.Product using (_×_; Σ-syntax; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Language.Prim using (int; bool)
open import Data.Bool using (true; false)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂)

{- The relation on terms -------------------------------------------------------}

{- what a closure captures: a variable or a value -}
data VV : C.AST → Set where
  vv-val : ∀ {V} → Value V → VV V
  vv-var : ∀ x → VV (C.` x)

data VVs : ∀ {n} → C.Args (replicate n ■) → Set where
  [] : VVs C.nil
  _∷_ : ∀ {n F} {Fs : C.Args (replicate n ■)} → VV F → VVs Fs → VVs (F ,, Fs)

infix 4 _≈_
data _≈_ : AST → C.AST → Set where
  var≈ : ∀ {x} → ` x ≈ C.` x
  lam≈ : ∀ {m N σ Fs} → bound N ≤ suc m
    → (∀ k → Uses (suc k) N → σ k ≈ CS.extend Fs CS.ids k) → VVs Fs
    → lam ⦅ ⟩ sub (exts σ) N ,, Nil ⦆ ≈ C.clos-op m C.⦅ C.cons (C.clear (bind-n-ast m (enclose N))) Fs ⦆
  app≈ : ∀ {L L' M M'} → L ≈ L' → M ≈ M' → app ⦅ L ,, M ,, Nil ⦆ ≈ C.app C.⦅ L' ,, M' ,, Nil ⦆
  lit≈ : ∀ {B k} → lit B k ⦅ Nil ⦆ ≈ C.lit B k C.⦅ Nil ⦆
  tuple≈ : ∀ {n as as'} → Pw _≈_ {n} as as' → tuple n ⦅ as ⦆ ≈ C.tuple n C.⦅ as' ⦆
  get≈ : ∀ {n} {i : Fin n} {M M'} → M ≈ M' → get i ⦅ M ,, Nil ⦆ ≈ C.get i C.⦅ M' ,, Nil ⦆
  inl≈ : ∀ {M M'} → M ≈ M' → inl-op ⦅ M ,, Nil ⦆ ≈ C.inl-op C.⦅ M' ,, Nil ⦆
  inr≈ : ∀ {M M'} → M ≈ M' → inr-op ⦅ M ,, Nil ⦆ ≈ C.inr-op C.⦅ M' ,, Nil ⦆
  case≈ : ∀ {L L' M M' N N'} → L ≈ L' → M ≈ M' → N ≈ N'
    → case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆ ≈ C.case-op C.⦅ L' ,, ⟩ M' ,, ⟩ N' ,, Nil ⦆
  prim≈ : ∀ {p L L' M M'} → L ≈ L' → M ≈ M' → prim p ⦅ L ,, M ,, Nil ⦆ ≈ C.prim p C.⦅ L' ,, M' ,, Nil ⦆

{- Closure under substitution -------------------------------------------------}

vv-sub : ∀ {σ' F} → (∀ x → VV (σ' x)) → VV F → VV (CS.sub σ' F)
vv-sub h (vv-val v) = vv-val (value-sub _ v)
vv-sub h (vv-var x) = h x

vvs-sub : ∀ {σ' n} {Fs : C.Args (replicate n ■)} → (∀ x → VV (σ' x)) → VVs Fs → VVs (CS.sub-args σ' Fs)
vvs-sub h [] = []
vvs-sub h (v ∷ vs) = vv-sub h v ∷ vvs-sub h vs

{- substituting by any P-related substitutions, where P is preserved under
   binders: first for renamings, then for all substitutions -}
module Kit (P : IS.Subst → CS.Subst → Set)
  (p≈ : ∀ {σ σ'} → P σ σ' → ∀ x → σ x ≈ σ' x) (pvv : ∀ {σ σ'} → P σ σ' → ∀ x → VV (σ' x))
  (pexts : ∀ {σ σ'} → P σ σ' → P (exts σ) (CS.exts σ')) where

  ≈-sub : ∀ {σ σ' M M'} → P σ σ' → M ≈ M' → sub σ M ≈ CS.sub σ' M'
  ≈-subs : ∀ {σ σ' n as as'} → P σ σ' → Pw _≈_ {n} as as' → Pw _≈_ (sub-args σ as) (CS.sub-args σ' as')
  ≈-sub p var≈ = p≈ p _
  ≈-sub {σ} {σ'} p (lam≈ {m} {N} {σ₀} {Fs} b c vs) =
    subst (λ X → lam ⦅ ⟩ X ,, Nil ⦆ ≈ _) (sym fuse) (lam≈ b c' (vvs-sub (pvv p) vs))
    where
    fuse : sub (exts σ) (sub (exts σ₀) N) ≡ sub (exts (λ x → sub σ (σ₀ x))) N
    fuse = trans (IS.sub-sub _ _ N) (IS.sub-cong (IS.exts-sub-comm σ σ₀) N)
    c' : ∀ k → Uses (suc k) N → sub σ (σ₀ k) ≈ CS.extend (CS.sub-args σ' Fs) CS.ids k
    c' k u = subst (_ ≈_) (sym (CS.extend-sub σ' Fs CS.ids CS.ids k
                                  (≤-trans (<-∸1 (uses-bound (suc k) N u)) (sub≤ b))))
                   (≈-sub p (c k u))
      where sub≤ : ∀ {b m} → b ≤ suc m → b ∸ 1 ≤ m
            sub≤ {zero} _ = z≤n
            sub≤ {suc b} (s≤s le) = le
  ≈-sub p (app≈ r s) = app≈ (≈-sub p r) (≈-sub p s)
  ≈-sub p lit≈ = lit≈
  ≈-sub p (tuple≈ rs) = tuple≈ (≈-subs p rs)
  ≈-sub p (get≈ r) = get≈ (≈-sub p r)
  ≈-sub p (inl≈ r) = inl≈ (≈-sub p r)
  ≈-sub p (inr≈ r) = inr≈ (≈-sub p r)
  ≈-sub p (case≈ r s t) = case≈ (≈-sub p r) (≈-sub (pexts p) s) (≈-sub (pexts p) t)
  ≈-sub p (prim≈ r s) = prim≈ (≈-sub p r) (≈-sub p s)
  ≈-subs p [] = []
  ≈-subs p (r ∷ rs) = ≈-sub p r ∷ ≈-subs p rs

vv-exts : ∀ {σ'} → (∀ x → VV (σ' x)) → ∀ x → VV (CS.exts σ' x)
vv-exts h zero = vv-var 0
vv-exts {σ'} h (suc x) = subst VV (sym (CS.rename-sub suc (σ' x))) (vv-sub (λ y → vv-var (suc y)) (h x))

{- related substitutions: related terms, and the target's are variables or values -}
open SubstRel.Closure _≈_ var≈ (λ _ σ' → ∀ x → VV (σ' x))
  (λ h x → subst VV (sym (proj₂ (proj₂ (h x)))) (vv-var _)) vv-exts Kit.≈-sub
  using (≈-rename; ≈-subst; SubP)

{- one related value for the bound variable -}
sub-one : ∀ {V V'} → V ≈ V' → Value V' → SubP (V • ids) (V' • CS.ids)
sub-one r v = (λ { zero → r ; (suc x) → var≈ }) , (λ { zero → vv-val v ; (suc x) → vv-var x })

{- The fundamental lemma --------------------------------------------------------}

unbind-bind : ∀ m N → unbind-n m (bind-n-ast m N) ≡ N
unbind-bind zero N = refl
unbind-bind (suc m) N = unbind-bind m N

{- the closure of enclose captures the variables below m -}
fv-extend : ∀ τ' m ρ k → k < m → CS.extend (CS.sub-args τ' (fv-vars m)) ρ k ≡ τ' k
fv-extend τ' (suc m) ρ k k< with m≤n⇒m<n∨m≡n (≤-pred k<)
... | inj₁ k<m = fv-extend τ' m (τ' m • ρ) k k<m
... | inj₂ refl = subst (λ y → CS.extend (CS.sub-args τ' (fv-vars k)) (τ' k • ρ) y ≡ τ' k) (+-identityʳ k)
                        (CS.extend-skip (CS.sub-args τ' (fv-vars k)) (τ' k • ρ) 0)

fv-vvs : ∀ {τ'} m → (∀ x → VV (τ' x)) → VVs (CS.sub-args τ' (fv-vars m))
fv-vvs zero vv = []
fv-vvs (suc m) vv = vv m ∷ fv-vvs m vv

enc : ∀ {τ τ'} M → (∀ x → Uses x M → τ x ≈ τ' x) → (∀ x → VV (τ' x))
  → sub τ M ≈ CS.sub τ' (enclose M)
encs : ∀ {τ τ' n} (as : Args (replicate n ■)) → (∀ x → UsesArgs x as → τ x ≈ τ' x)
  → (∀ x → VV (τ' x)) → Pw _≈_ (sub-args τ as) (CS.sub-args τ' (enc-args as))
enc (` x) h vv = h x refl
enc {τ' = τ'} (lam ⦅ ⟩ N ,, Nil ⦆) h vv =
  lam≈ (m≤n+m∸n (bound N) 1)
       (λ k u → subst (_ ≈_) (sym (fv-extend τ' _ CS.ids k (<-∸1 (uses-bound (suc k) N u)))) (h k (inj₁ u)))
       (fv-vvs _ vv)
enc (app ⦅ L ,, M ,, Nil ⦆) h vv = app≈ (enc L (λ x u → h x (inj₁ u)) vv) (enc M (λ x u → h x (inj₂ (inj₁ u))) vv)
enc (lit B k ⦅ Nil ⦆) h vv = lit≈
enc (tuple n ⦅ as ⦆) h vv = tuple≈ (encs as h vv)
enc (get i ⦅ M ,, Nil ⦆) h vv = get≈ (enc M (λ x u → h x (inj₁ u)) vv)
enc (inl-op ⦅ M ,, Nil ⦆) h vv = inl≈ (enc M (λ x u → h x (inj₁ u)) vv)
enc (inr-op ⦅ M ,, Nil ⦆) h vv = inr≈ (enc M (λ x u → h x (inj₁ u)) vv)
enc (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) h vv =
  case≈ (enc L (λ x u → h x (inj₁ u)) vv)
        (enc M (under {M = M} (λ x u → h x (inj₂ (inj₁ u)))) (vv-exts vv))
        (enc N (under {M = N} (λ x u → h x (inj₂ (inj₂ (inj₁ u))))) (vv-exts vv))
  where
  under : ∀ {τ τ' M} → (∀ x → Uses (suc x) M → τ x ≈ τ' x) → ∀ x → Uses x M → exts τ x ≈ CS.exts τ' x
  under h zero u = var≈
  under h (suc x) u = ≈-rename suc (h x u)
enc (prim p ⦅ L ,, M ,, Nil ⦆) h vv = prim≈ (enc L (λ x u → h x (inj₁ u)) vv) (enc M (λ x u → h x (inj₂ (inj₁ u))) vv)
encs {n = zero} Nil h vv = []
encs {n = suc n} (M ,, as) h vv = enc M (λ x u → h x (inj₁ u)) vv ∷ encs as (λ x u → h x (inj₂ u)) vv

{- The simulation -----------------------------------------------------------------}

{- related terms, the target closed -}
R : AST → C.AST → Set
R M M' = M ≈ M' × WS 0 M'

Ans′ = Ans T.red Value R

pw-R : ∀ {n as as'} → Pw R {n} as as' → Pw _≈_ as as' × WS-args 0 as'
pw-R [] = [] , tt
pw-R ((r , w) ∷ rs) = (r ∷ proj₁ (pw-R rs)) , w , proj₂ (pw-R rs)

zipR : ∀ {n as as'} → Pw _≈_ {n} as as' → WS-args 0 as' → Pw R as as'
zipR [] _ = []
zipR (r ∷ rs) (w , ws) = (r , w) ∷ zipR rs ws

{- the substitution of a closure's body: values, or variables -}
vv-extend : ∀ {n} {Fs : C.Args (replicate n ■)} {ρ} → Values Fs → (∀ x → VV (ρ x)) → ∀ x → VV (CS.extend Fs ρ x)
vv-extend T.[] h = h
vv-extend (v T.∷ vs) h = vv-extend vs λ { zero → vv-val v ; (suc x) → h x }

values : ∀ {n} {Fs : C.Args (replicate n ■)} → VVs Fs → WS-args 0 Fs → Values Fs
values [] _ = T.[]
values (vv-val v ∷ vs) (_ , ws) = v T.∷ values vs ws
values (vv-var x ∷ vs) (() , _)

obs≈ : ∀ {M M'} → M ≈ M' → S.obs M ≡ T.obs M'
obs≈s : ∀ {n as as'} → Pw _≈_ {n} as as' → S.obs-args as ≡ T.obs-args as'
obs≈ var≈ = refl
obs≈ (lam≈ _ _ _) = refl
obs≈ (app≈ _ _) = refl
obs≈ lit≈ = refl
obs≈ (tuple≈ rs) = cong o-tuple (obs≈s rs)
obs≈ (get≈ _) = refl
obs≈ (inl≈ r) = cong o-inl (obs≈ r)
obs≈ (inr≈ r) = cong o-inr (obs≈ r)
obs≈ (case≈ _ _ _) = refl
obs≈ (prim≈ _ _) = refl
obs≈s [] = refl
obs≈s (r ∷ rs) = cong₂ _∷_ (obs≈ r) (obs≈s rs)

{- a lookup or a projection, related pointwise -}
ret?-ans : ∀ {M mv mw X} → M.Pointwise R mv mw → T.red X ≡ T.ret? mw → Ans′ M (S.ret? mv) X
ret?-ans (M.just r) e = to (one e) r
ret?-ans M.nothing e = wrong ε e

sim : ∀ {M M'} → M ≈ M' → WS 0 M' → Ans′ M (S.red M) M'
sims : ∀ {n as as'} → Pw _≈_ {n} as as' → WS-args 0 as' → Ans T.red-args Values (Pw R) as (S.red-args as) as'
sim var≈ w = wrong ε refl
sim (lam≈ b c vs) w = val ε (T.clos (values vs (proj₂ w))) (lam≈ b c vs , w)
sim (app≈ r s) (wL , wM , _) =
  ans-in (frame _ (λ _ → refl)) (λ (r' , w') → app≈ r' s , w' , wM , tt) (sim r wL) (λ v m → app-sim v m s wM)
  where
  app-sim : ∀ {L V' M M'} → Value V' → R L V' → M ≈ M' → WS 0 M'
    → Ans′ (app ⦅ L ,, M ,, Nil ⦆) (S.app? L (S.red M) M) (C.app C.⦅ V' ,, M' ,, Nil ⦆)
  app-sim (T.clos vs) (lam≈ {m} {N} {σ} {Fs} b c vv , w) s wM =
    ans-in (frame {g = λ X → C.app C.⦅ _ ,, X ,, Nil ⦆} _ (λ X → val-in (value-red (T.clos vs))))
           (λ (s' , w') → app≈ (lam≈ b c vv) s' , w , w' , tt) (sim s wM)
           λ v (s' , w') → to (one (trans (val-in (value-red (T.clos vs))) (val-in (value-red v))))
             (subst (R _) (cong (CS.sub _) (sym (unbind-bind m (enclose N)))) (β v s' w'))
    where
    β : ∀ {M W'} → Value W' → M ≈ W' → WS 0 W'
      → R (sub (exts σ) N [ M ]) (CS.sub (W' CS.• CS.extend Fs CS.ids) (enclose N))
    β v s' w' =
      subst (_≈ _) (sym (IS.exts-[] _ σ N))
            (enc N (λ { zero u → s' ; (suc k) u → c k u }) (λ { zero → vv-val v ; (suc k) → vv-extend vs vv-var k }))
      , ws-sub _ (enclose N)
          (λ { zero _ → w' ; (suc x) (s≤s x<) → sfits-extend Fs (proj₂ w) (λ _ ()) x (subst (x <_) (sym (+-identityʳ m)) x<) })
          (Enclosed.enclose-ws N b)
  app-sim T.lit (lit≈ , _) s wM = wrong ε refl
  app-sim v@(T.tuple _) (tuple≈ _ , _) s wM = wrong ε (val-in (value-red v))
  app-sim v@(T.inl _) (inl≈ _ , _) s wM = wrong ε (val-in (value-red v))
  app-sim v@(T.inr _) (inr≈ _ , _) s wM = wrong ε (val-in (value-red v))
sim lit≈ w = val ε T.lit (lit≈ , w)
sim (tuple≈ rs) w =
  ans-in (frame _ (λ _ → refl)) (λ ms → tuple≈ (proj₁ (pw-R ms)) , proj₂ (pw-R ms)) (sims rs w)
         (λ vs ms → val ε (T.tuple vs) (tuple≈ (proj₁ (pw-R ms)) , proj₂ (pw-R ms)))
sim (get≈ {i = i} r) (w , _) =
  ans-in (frame _ (λ _ → refl)) (λ (r' , w') → get≈ r' , w' , tt) (sim r w) get-sim
  where
  get-sim : ∀ {M V'} → Value V' → R M V' → Ans′ (get i ⦅ M ,, Nil ⦆) (S.get? i M) (C.get i C.⦅ V' ,, Nil ⦆)
  get-sim (T.tuple vs) (tuple≈ rs , w) =
    ret?-ans (proj-pw {R = R} i (pw-list (zipR rs w))) (val-in (value-red (T.tuple vs)))
  get-sim v@(T.clos _) (lam≈ _ _ _ , _) = wrong ε (val-in (value-red v))
  get-sim T.lit (lit≈ , _) = wrong ε refl
  get-sim v@(T.inl _) (inl≈ _ , _) = wrong ε (val-in (value-red v))
  get-sim v@(T.inr _) (inr≈ _ , _) = wrong ε (val-in (value-red v))
sim (inl≈ r) (w , _) =
  ans-in (frame _ (λ _ → refl)) (λ (r' , w') → inl≈ r' , w' , tt) (sim r w) (λ v (r' , w') → val ε (T.inl v) (inl≈ r' , w' , tt))
sim (inr≈ r) (w , _) =
  ans-in (frame _ (λ _ → refl)) (λ (r' , w') → inr≈ r' , w' , tt) (sim r w) (λ v (r' , w') → val ε (T.inr v) (inr≈ r' , w' , tt))
sim (case≈ {M = M} {M'} {N} {N'} r s t) (wL , wM , wN , _) =
  ans-in (frame _ (λ _ → refl)) (λ (r' , w') → case≈ r' s t , w' , wM , wN , tt) (sim r wL) case-sim
  where
  case-sim : ∀ {L V'} → Value V' → R L V'
    → Ans′ (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) (S.case? L M N) (C.case-op C.⦅ V' ,, ⟩ M' ,, ⟩ N' ,, Nil ⦆)
  case-sim (T.inl v) (inl≈ r' , w') =
    to (one (val-in (value-red (T.inl v))))
       (≈-subst (sub-one r' v) s , ws-sub _ M' (λ { zero _ → proj₁ w' ; (suc x) (s≤s ()) }) wM)
  case-sim (T.inr v) (inr≈ r' , w') =
    to (one (val-in (value-red (T.inr v))))
       (≈-subst (sub-one r' v) t , ws-sub _ N' (λ { zero _ → proj₁ w' ; (suc x) (s≤s ()) }) wN)
  case-sim v@(T.clos _) (lam≈ _ _ _ , _) = wrong ε (val-in (value-red v))
  case-sim T.lit (lit≈ , _) = wrong ε refl
  case-sim v@(T.tuple _) (tuple≈ _ , _) = wrong ε (val-in (value-red v))
sim (prim≈ {p} r s) (wL , wM , _) =
  ans-in (frame _ (λ _ → refl)) (λ (r' , w') → prim≈ r' s , w' , wM , tt) (sim r wL)
    λ v (r' , w') →
      ans-in (frame {g = λ X → C.prim p C.⦅ _ ,, X ,, Nil ⦆} _ (λ X → val-in (value-red v))) (λ (s' , w'') → prim≈ r' s' , w' , w'' , tt) (sim s wM)
        λ v' (s' , w'') → ret?-ans (out≈ (obs≈ r') (obs≈ s')) (trans (val-in (value-red v)) (val-in (value-red v')))
  where
  out≈ : ∀ {o₁ o₁' o₂ o₂'} → o₁ ≡ o₁' → o₂ ≡ o₂'
    → M.Pointwise R (map S.out (δ? p o₁ o₂)) (map T.out (δ? p o₁' o₂'))
  out≈ {o₁} {_} {o₂} refl refl with δ? p o₁ o₂
  ... | nothing = M.nothing
  ... | just (int n) = M.just (lit≈ , tt)
  ... | just (bool true) = M.just (inl≈ (tuple≈ []) , (tt , tt))
  ... | just (bool false) = M.just (inr≈ (tuple≈ []) , (tt , tt))
sims [] _ = val ε T.[] []
sims (r ∷ rs) (w , ws) =
  ans-in (frame _ (λ _ → refl)) (λ m → m ∷ zipR rs ws) (sim r w)
    λ v m → ans-in (frame {g = λ Xs → _ ,, Xs} _ (λ X → val-in (value-red v))) (λ ms → m ∷ ms) (sims rs ws)
      λ vs ms → val ε (v T.∷ vs) (m ∷ ms)

{- The end theorem: for closed programs -------------------------------------------}

enclose-correct : ∀ M → Closed M → Equivalent (S.sem M) (T.sem (enclose M))
enclose-correct M c =
  red-equivalent value-red R (λ (m , w) → sim m w) (λ (m , _) _ _ → obs≈ m)
    (subst₂ _≈_ (IS.sub-id M) (CS.sub-id (enclose M))
            (enc M (λ x u → ⊥-elim (x<0 (subst (x <_) c (uses-bound x M u)))) (λ x → vv-var x))
    , enclose-closed M c)
  where x<0 : ∀ {x} → x < 0 → ⊥
        x<0 ()

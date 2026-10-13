{-

  Correctness of the optimize pass (Clos2 → Clos2) by a forward
  simulation of the Clos2 reduction semantics by itself (see the design
  note in Semantics/Reduction/Smallstep.agda).

  optimize drops the free variables of a closure that its code does not
  use, if they are variables. In a closed program, the reduct of such a
  variable is a value, so a closure is a value in the source exactly
  when it is one in the target, and the two run in lock step: the
  dropped free variables take no steps (unlike in the machines, which
  look them up).

  The relation on terms (_≈_) is a congruence, closed under substitution
  (≈-subst), except for closures. Their code, which no substitution
  enters, is related by the compilation function: the target's is the
  source's optimized with the renaming index that prune computes. Their
  free variables are related by Pr, which follows prune: a free
  variable the code uses is kept, and related; one that it does not use
  may be dropped if it is a variable or a value (VV). Applying related
  closures substitutes related values in their code (pr-lookup), which
  gives related terms by the fundamental lemma (opt): sub τ M is related
  to sub τ' (optimize r M) when τ x is related to τ' (r x).

  The precondition: the program is closed (WS 0), which enclose
  produces. A dropped free variable that the source reduces must be a
  value, not a variable: the source is closed, and stays closed (R).

-}

module proof.Correctness.Reduction.OptimizeRed where

open import Framework.Syntax.SigUtil using (ν-n)
open import Framework.Syntax.SyntaxUtil using (_,,_; Nil; ⟩_,,_)
open import Language.Clos2
open import Compiler.Optimize hiding (bound; bound-arg; bound-args)
open import Semantics.Observation
open import proof.Framework.Reduction Obs o-wrong
open import Semantics.Reduction.Smallstep using (Equivalent)
import proof.Semantics.Reduction.Clos2 as T
open T using (Value; Values; value-red; value-sub)
import proof.Framework.Syntax.Subst Op sig as SS
import Framework.Syntax.Rename Op sig as R
import proof.Framework.Syntax.SubstRel Op sig Op sig as SubstRel
open SS using (sub; sub-args; exts; ids; extend)
open import Framework.Syntax.Scope Op sig using (WS; WS-arg; WS-args)
open import proof.Framework.Syntax.ScopeSubst Op sig using (ws-sub; sfits-•; sfits-extend₀; module Unbind)
open import proof.Framework.ListUtil using (proj-pw)

open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin)
open import Data.List using (replicate; _∷_)
import Data.Maybe.Relation.Binary.Pointwise as M
open import Data.Maybe using (just; nothing; map)
open import Data.Nat using (ℕ; zero; suc; _+_; _<_; s≤s; z≤n)
open import Data.Nat.Properties using (+-identityʳ; +-suc)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Language.Prim using (int; bool)
open import Data.Bool using (true; false)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂)
open import Relation.Nullary using (¬_; Dec; yes; no)

{- The relation on terms -------------------------------------------------------}

{- what a closure may drop: a variable or a value -}
open VarOrValue Value value-sub

infix 4 _≈_
data _≈_ : AST → AST → Set

{- Pr U b Fs Gs idx: the free variables Fs of a closure whose code uses
   the positions U, and the ones Gs that its optimized closure keeps, as
   prune makes them with the renumbering b of the positions past Fs;
   idx is the renumbering of all positions that results -}
data Pr (U : ℕ → Set) : ∀ {n m} → (ℕ → ℕ) → Args (replicate n ■) → Args (replicate m ■) → (ℕ → ℕ) → Set where
  nil : ∀ {b} → Pr U b Nil Nil b
  keep≈ : ∀ {n m b idx F G} {Fs : Args (replicate n ■)} {Gs : Args (replicate m ■)}
    → F ≈ G → Pr U (keep-base b) Fs Gs idx → Pr U b (F ,, Fs) (G ,, Gs) idx
  drop≈ : ∀ {n m b idx F} {Fs : Args (replicate n ■)} {Gs : Args (replicate m ■)}
    → ¬ U n → VV F → Pr U (drop-base b) Fs Gs idx → Pr U b (F ,, Fs) Gs idx

data _≈_ where
  var≈ : ∀ {x} → ` x ≈ ` x
  clos≈ : ∀ {n m a Fs Gs idx} → Pr (λ j → Uses (suc j) (unbind-n n a)) (λ k → k) Fs Gs idx
    → clos-op n ⦅ cons (clear a) Fs ⦆ ≈ clos-op m ⦅ cons (clear (bind-n-ast m (opt-body (ext-var idx) n a))) Gs ⦆
  app≈ : ∀ {L L' M M'} → L ≈ L' → M ≈ M' → app ⦅ L ,, M ,, Nil ⦆ ≈ app ⦅ L' ,, M' ,, Nil ⦆
  lit≈ : ∀ {B k} → lit B k ⦅ Nil ⦆ ≈ lit B k ⦅ Nil ⦆
  tuple≈ : ∀ {n as as'} → Pw _≈_ {n} as as' → tuple n ⦅ as ⦆ ≈ tuple n ⦅ as' ⦆
  get≈ : ∀ {n} {i : Fin n} {M M'} → M ≈ M' → get i ⦅ M ,, Nil ⦆ ≈ get i ⦅ M' ,, Nil ⦆
  inl≈ : ∀ {M M'} → M ≈ M' → inl-op ⦅ M ,, Nil ⦆ ≈ inl-op ⦅ M' ,, Nil ⦆
  inr≈ : ∀ {M M'} → M ≈ M' → inr-op ⦅ M ,, Nil ⦆ ≈ inr-op ⦅ M' ,, Nil ⦆
  case≈ : ∀ {L L' M M' N N'} → L ≈ L' → M ≈ M' → N ≈ N'
    → case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆ ≈ case-op ⦅ L' ,, ⟩ M' ,, ⟩ N' ,, Nil ⦆
  prim≈ : ∀ {p L L' M M'} → L ≈ L' → M ≈ M' → prim p ⦅ L ,, M ,, Nil ⦆ ≈ prim p ⦅ L' ,, M' ,, Nil ⦆
  let≈ : ∀ {M M' N N'} → M ≈ M' → N ≈ N' → let-op ⦅ M ,, ⟩ N ,, Nil ⦆ ≈ let-op ⦅ M' ,, ⟩ N' ,, Nil ⦆

{- a used free variable is related to the kept one that idx renumbers it to -}
pr-lookup : ∀ {U n m b Fs Gs idx ρ ρ'} → Pr U {n} {m} b Fs Gs idx
  → (∀ k → U (n + k) → ρ k ≈ ρ' (b k)) → ∀ j → U j → extend Fs ρ j ≈ extend Gs ρ' (idx j)
pr-lookup nil h j u = h j u
pr-lookup {U} {suc n} {b = b} {F ,, Fs} {G ,, Gs} {ρ = ρ} {ρ'} (keep≈ r pr) h = pr-lookup pr h'
  where h' : ∀ k → U (n + k) → (F • ρ) k ≈ (G • ρ') (keep-base b k)
        h' zero _ = r
        h' (suc k) u = h k (subst U (+-suc n k) u)
pr-lookup {U} {suc n} {b = b} {F ,, Fs} {ρ = ρ} {ρ'} (drop≈ nu _ pr) h = pr-lookup pr h'
  where h' : ∀ k → U (n + k) → (F • ρ) k ≈ ρ' (drop-base b k)
        h' zero u = ⊥-elim (nu (subst U (+-identityʳ n) u))
        h' (suc k) u = h k (subst U (+-suc n k) u)

{- Closure under substitution -------------------------------------------------}

Ok : SS.Subst → SS.Subst → Set
Ok σ σ' = ∀ x → VV (σ x)

module Kit (P : SS.Subst → SS.Subst → Set) (p≈ : ∀ {σ σ'} → P σ σ' → ∀ x → σ x ≈ σ' x)
  (pok : ∀ {σ σ'} → P σ σ' → Ok σ σ') (pexts : ∀ {σ σ'} → P σ σ' → P (exts σ) (exts σ')) where

  ≈-sub : ∀ {σ σ' M M'} → P σ σ' → M ≈ M' → sub σ M ≈ sub σ' M'
  ≈-subs : ∀ {σ σ' n as as'} → P σ σ' → Pw _≈_ {n} as as' → Pw _≈_ (sub-args σ as) (sub-args σ' as')
  pr-sub : ∀ {σ σ' U n m b Fs Gs idx} → P σ σ' → Pr U {n} {m} b Fs Gs idx
    → Pr U b (sub-args σ Fs) (sub-args σ' Gs) idx
  ≈-sub p var≈ = p≈ p _
  ≈-sub p (clos≈ pr) = clos≈ (pr-sub p pr)
  ≈-sub p (app≈ r s) = app≈ (≈-sub p r) (≈-sub p s)
  ≈-sub p lit≈ = lit≈
  ≈-sub p (tuple≈ rs) = tuple≈ (≈-subs p rs)
  ≈-sub p (get≈ r) = get≈ (≈-sub p r)
  ≈-sub p (inl≈ r) = inl≈ (≈-sub p r)
  ≈-sub p (inr≈ r) = inr≈ (≈-sub p r)
  ≈-sub p (case≈ r s t) = case≈ (≈-sub p r) (≈-sub (pexts p) s) (≈-sub (pexts p) t)
  ≈-sub p (prim≈ r s) = prim≈ (≈-sub p r) (≈-sub p s)
  ≈-sub p (let≈ r s) = let≈ (≈-sub p r) (≈-sub (pexts p) s)
  ≈-subs p [] = []
  ≈-subs p (r ∷ rs) = ≈-sub p r ∷ ≈-subs p rs
  pr-sub p nil = nil
  pr-sub p (keep≈ r pr) = keep≈ (≈-sub p r) (pr-sub p pr)
  pr-sub p (drop≈ nu vv pr) = drop≈ nu (vv-sub (pok p) vv) (pr-sub p pr)

open SubstRel.Closure _≈_ var≈ Ok (λ h x → subst VV (sym (proj₁ (proj₂ (h x)))) (vv-var _)) vv-exts Kit.≈-sub
  using (≈-rename; ≈-subst; ≈-[])

{- The fundamental lemma --------------------------------------------------------}

{- under a binder -}
under : ∀ {τ τ' r M} → (∀ x → Uses (suc x) M → τ x ≈ τ' (r x)) → ∀ x → Uses x M → exts τ x ≈ exts τ' (ext-var r x)
under h zero u = var≈
under h (suc x) u = ≈-rename suc (h x u)

opt : ∀ {τ τ'} r M → (∀ x → Uses x M → τ x ≈ τ' (r x)) → (∀ x → VV (τ x))
  → sub τ M ≈ sub τ' (optimize r M)
opts : ∀ {τ τ' n} r (as : Args (replicate n ■)) → (∀ x → UsesArgs x as → τ x ≈ τ' (r x))
  → (∀ x → VV (τ x)) → Pw _≈_ (sub-args τ as) (sub-args τ' (opt-args r as))
pr-opt : ∀ {τ τ'} r {U} (dec : ∀ j → Dec (U j)) n (Fs : Args (replicate n ■)) b
  → (∀ x → UsesArgs x Fs → τ x ≈ τ' (r x)) → (∀ x → VV (τ x))
  → Pr U b (sub-args τ Fs) (sub-args τ' (kept (prune n r dec Fs b))) (index (prune n r dec Fs b))
opt r (` x) h vv = h x refl
opt r (clos-op n ⦅ cons (clear a) Fs ⦆) h vv =
  clos≈ (pr-opt r (λ j → uses? (suc j) (unbind-n n a)) n Fs (λ k → k) (λ x u → h x (inj₂ u)) vv)
opt r (app ⦅ L ,, M ,, Nil ⦆) h vv = app≈ (opt r L (λ x u → h x (inj₁ u)) vv) (opt r M (λ x u → h x (inj₂ (inj₁ u))) vv)
opt r (lit B k ⦅ Nil ⦆) h vv = lit≈
opt r (tuple n ⦅ as ⦆) h vv = tuple≈ (opts r as h vv)
opt r (get i ⦅ M ,, Nil ⦆) h vv = get≈ (opt r M (λ x u → h x (inj₁ u)) vv)
opt r (inl-op ⦅ M ,, Nil ⦆) h vv = inl≈ (opt r M (λ x u → h x (inj₁ u)) vv)
opt r (inr-op ⦅ M ,, Nil ⦆) h vv = inr≈ (opt r M (λ x u → h x (inj₁ u)) vv)
opt r (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) h vv =
  case≈ (opt r L (λ x u → h x (inj₁ u)) vv)
        (opt (ext-var r) M (under {M = M} (λ x u → h x (inj₂ (inj₁ u)))) (vv-exts vv))
        (opt (ext-var r) N (under {M = N} (λ x u → h x (inj₂ (inj₂ (inj₁ u))))) (vv-exts vv))
opt r (prim p ⦅ L ,, M ,, Nil ⦆) h vv = prim≈ (opt r L (λ x u → h x (inj₁ u)) vv) (opt r M (λ x u → h x (inj₂ (inj₁ u))) vv)
opt r (let-op ⦅ M ,, ⟩ N ,, Nil ⦆) h vv =
  let≈ (opt r M (λ x u → h x (inj₁ u)) vv) (opt (ext-var r) N (under {M = N} (λ x u → h x (inj₂ (inj₁ u)))) (vv-exts vv))
opts {n = zero} r Nil h vv = []
opts {n = suc n} r (M ,, as) h vv = opt r M (λ x u → h x (inj₁ u)) vv ∷ opts r as (λ x u → h x (inj₂ u)) vv
pr-opt r dec zero Nil b h vv = nil
pr-opt r dec (suc n) ((` y) ,, Fs) b h vv with dec n
... | yes _ = keep≈ (h y (inj₁ refl)) (pr-opt r dec n Fs (keep-base b) (λ x u → h x (inj₂ u)) vv)
... | no nu = drop≈ nu (vv y) (pr-opt r dec n Fs (drop-base b) (λ x u → h x (inj₂ u)) vv)
pr-opt r dec (suc n) ((op ⦅ as ⦆) ,, Fs) b h vv =
  keep≈ (opt r (op ⦅ as ⦆) (λ x u → h x (inj₁ u)) vv) (pr-opt r dec n Fs (keep-base b) (λ x u → h x (inj₂ u)) vv)

opt-body-eq : ∀ r k (a : Arg (ν-n k (ν ■))) → opt-body r k a ≡ optimize r (unbind-n k a)
opt-body-eq r zero (bind (ast N)) = refl
opt-body-eq r (suc k) (bind a) = opt-body-eq r k a

open Unbind unbind-n (λ _ → refl) (λ _ _ → refl)

{- The simulation -----------------------------------------------------------------}

{- related terms, the source closed -}
Rel : AST → AST → Set
Rel M M' = M ≈ M' × WS 0 M

Ans′ = Ans T.red Value Rel

{- a closed source term related to a target value is a value -}
≈-value : ∀ {V V'} → Value V' → V ≈ V' → WS 0 V → Value V
≈-values : ∀ {n as as'} → Values as' → Pw _≈_ {n} as as' → WS-args 0 as → Values as
pr-values : ∀ {U n m b Fs Gs idx} → Values Gs → Pr U {n} {m} b Fs Gs idx → WS-args 0 Fs → Values Fs
≈-value (T.clos vs) (clos≈ pr) (_ , ws) = T.clos (pr-values vs pr ws)
≈-value T.lit lit≈ _ = T.lit
≈-value (T.tuple vs) (tuple≈ rs) ws = T.tuple (≈-values vs rs ws)
≈-value (T.inl v) (inl≈ r) (w , _) = T.inl (≈-value v r w)
≈-value (T.inr v) (inr≈ r) (w , _) = T.inr (≈-value v r w)
≈-values T.[] [] _ = T.[]
≈-values (v T.∷ vs) (r ∷ rs) (w , ws) = ≈-value v r w T.∷ ≈-values vs rs ws
pr-values T.[] nil _ = T.[]
pr-values (v T.∷ vs) (keep≈ r pr) (w , ws) = ≈-value v r w T.∷ pr-values vs pr ws
pr-values vs (drop≈ _ vv pr) (w , ws) = vv-value vv w T.∷ pr-values vs pr ws

obs≈ : ∀ {M M'} → Value M' → M ≈ M' → T.obs M ≡ T.obs M'
obs≈s : ∀ {n as as'} → Values as' → Pw _≈_ {n} as as' → T.obs-args as ≡ T.obs-args as'
obs≈ (T.clos _) (clos≈ _) = refl
obs≈ T.lit lit≈ = refl
obs≈ (T.tuple vs) (tuple≈ rs) = cong o-tuple (obs≈s vs rs)
obs≈ (T.inl v) (inl≈ r) = cong o-inl (obs≈ v r)
obs≈ (T.inr v) (inr≈ r) = cong o-inr (obs≈ v r)
obs≈s T.[] [] = refl
obs≈s (v T.∷ vs) (r ∷ rs) = cong₂ _∷_ (obs≈ v r) (obs≈s vs rs)

sim : ∀ {M M'} → M ≈ M' → WS 0 M → Ans′ M (T.red M) M'
sims : ∀ {n as as'} → Pw _≈_ {n} as as' → WS-args 0 as → Ans T.red-args Values (Pw Rel) as (T.red-args as) as'
prs : ∀ {U n m b Fs Gs idx} → Pr U {n} {m} b Fs Gs idx → WS-args 0 Fs
  → Ans T.red-args Values (λ Fs' Gs' → Pr U b Fs' Gs' idx × WS-args 0 Fs') Fs (T.red-args Fs) Gs
sim var≈ w = wrong ε refl
sim (clos≈ pr) (wa , ws) =
  ans-in (frame _ (λ _ → refl)) (λ (pr' , ws') → clos≈ pr' , wa , ws') (prs pr ws)
         (λ vs (pr' , ws') → val ε (T.clos vs) (clos≈ pr' , wa , ws'))
sim (app≈ r s) (wL , wM , _) =
  ans-in (frame _ (λ _ → refl)) (λ (r' , w') → app≈ r' s , w' , wM , tt) (sim r wL) (λ v m → app-sim v m s wM)
  where
  app-sim : ∀ {L V' M M'} → Value V' → Rel L V' → M ≈ M' → WS 0 M
    → Ans′ (app ⦅ L ,, M ,, Nil ⦆) (T.app? L (T.red M) M) (app ⦅ V' ,, M' ,, Nil ⦆)
  app-sim v@(T.clos vs) (clos≈ {n} {m} {a} {Fs} {Gs} {idx} pr , wa , wFs) s wM =
    ans-in (frame {g = λ X → app ⦅ _ ,, X ,, Nil ⦆} _ (λ X → val-in (value-red v)))
           (λ (s' , w') → app≈ (clos≈ pr) s' , (wa , wFs) , w' , tt) (sim s wM)
      λ v' (s' , w') → to (one (trans (val-in (value-red v)) (val-in (value-red v')))) (β v' s' w')
    where
    β : ∀ {M W'} → Value W' → M ≈ W' → WS 0 M
      → Rel (sub (M • extend Fs ids) (unbind-n n a)) (sub (W' • extend Gs ids) (unbind-n m (bind-n-ast m (opt-body (ext-var idx) n a))))
    β {M} {W'} v' s' w' =
      subst (λ B → sub (M • extend Fs ids) (unbind-n n a) ≈ sub (W' • extend Gs ids) B)
            (sym (trans (unbind-bind bind-n-ast (λ _ → refl) (λ _ _ → refl) m _) (opt-body-eq (ext-var idx) n a)))
            (opt (ext-var idx) (unbind-n n a)
                 (λ { zero u → s' ; (suc j) u → pr-lookup pr (λ k _ → var≈) j u })
                 (λ { zero → vv-val (≈-value v' s' w') ; (suc x) → vv-extend (pr-values vs pr wFs) vv-var x }))
      , ws-sub _ (unbind-n n a)
          (sfits-• w' (sfits-extend₀ Fs wFs))
          (ws-unbind₀ n a wa)
  app-sim T.lit (lit≈ , _) s wM = wrong ε refl
  app-sim v@(T.tuple _) (tuple≈ _ , _) s wM = wrong ε (val-in (value-red v))
  app-sim v@(T.inl _) (inl≈ _ , _) s wM = wrong ε (val-in (value-red v))
  app-sim v@(T.inr _) (inr≈ _ , _) s wM = wrong ε (val-in (value-red v))
sim lit≈ w = val ε T.lit (lit≈ , w)
sim (tuple≈ rs) ws =
  ans-in (frame _ (λ _ → refl)) (λ ms → tuple≈ (proj₁ (unzipˡ ms)) , proj₂ (unzipˡ ms)) (sims rs ws)
         (λ vs ms → val ε (T.tuple vs) (tuple≈ (proj₁ (unzipˡ ms)) , proj₂ (unzipˡ ms)))
sim (get≈ {i = i} r) (w , _) = ans-in (frame _ (λ _ → refl)) (λ (r' , w') → get≈ r' , w' , tt) (sim r w) get-sim
  where
  get-sim : ∀ {M V'} → Value V' → Rel M V' → Ans′ (get i ⦅ M ,, Nil ⦆) (T.get? i M) (get i ⦅ V' ,, Nil ⦆)
  get-sim v@(T.tuple _) (tuple≈ rs , ws) = ret?-ans (proj-pw {R = Rel} i (pw-list (zipˡ rs ws))) (val-in (value-red v))
  get-sim v@(T.clos _) (clos≈ _ , _) = wrong ε (val-in (value-red v))
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
  case-sim : ∀ {L V'} → Value V' → Rel L V'
    → Ans′ (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) (T.case? L M N) (case-op ⦅ V' ,, ⟩ M' ,, ⟩ N' ,, Nil ⦆)
  case-sim v@(T.inl v₁) (inl≈ r' , w' , _) =
    to (one (val-in (value-red v)))
       (≈-[] (vv-one (≈-value v₁ r' w')) r' s , ws-sub _ M (sfits-• w' (λ _ ())) wM)
  case-sim v@(T.inr v₁) (inr≈ r' , w' , _) =
    to (one (val-in (value-red v)))
       (≈-[] (vv-one (≈-value v₁ r' w')) r' t , ws-sub _ N (sfits-• w' (λ _ ())) wN)
  case-sim v@(T.clos _) (clos≈ _ , _) = wrong ε (val-in (value-red v))
  case-sim T.lit (lit≈ , _) = wrong ε refl
  case-sim v@(T.tuple _) (tuple≈ _ , _) = wrong ε (val-in (value-red v))
sim (prim≈ {p} r s) (wL , wM , _) =
  ans-in (frame _ (λ _ → refl)) (λ (r' , w') → prim≈ r' s , w' , wM , tt) (sim r wL)
    λ v (r' , w') → ans-in (frame {g = λ X → prim p ⦅ _ ,, X ,, Nil ⦆} _ (λ X → val-in (value-red v)))
                           (λ (s' , w'') → prim≈ r' s' , w' , w'' , tt) (sim s wM)
      λ v' (s' , w'') → ret?-ans (out≈ (obs≈ v r') (obs≈ v' s')) (trans (val-in (value-red v)) (val-in (value-red v')))
  where
  out≈ : ∀ {o₁ o₁' o₂ o₂'} → o₁ ≡ o₁' → o₂ ≡ o₂'
    → M.Pointwise Rel (map T.out (δ? p o₁ o₂)) (map T.out (δ? p o₁' o₂'))
  out≈ {o₁} {_} {o₂} refl refl with δ? p o₁ o₂
  ... | nothing = M.nothing
  ... | just (int n) = M.just (lit≈ , tt)
  ... | just (bool true) = M.just (inl≈ (tuple≈ []) , tt , tt)
  ... | just (bool false) = M.just (inr≈ (tuple≈ []) , tt , tt)
sim (let≈ {N = N} r s) (wM , wN , _) =
  ans-in (frame _ (λ _ → refl)) (λ (r' , w') → let≈ r' s , w' , wN , tt) (sim r wM)
    λ v (r' , w') → to (one (val-in (value-red v)))
       (≈-[] (vv-one (≈-value v r' w')) r' s , ws-sub _ N (sfits-• w' (λ _ ())) wN)
sims [] _ = val ε T.[] []
sims (r ∷ rs) (w , ws) = ans-cons T.red-args (λ _ _ → refl) value-red (zipˡ rs ws) (sim r w) (sims rs ws)
prs nil _ = val ε T.[] (nil , tt)
prs (keep≈ r pr) (w , ws) =
  ans-in (frame _ (λ _ → refl)) (λ (r' , w') → keep≈ r' pr , w' , ws) (sim r w)
    λ v (r' , w') → ans-in (frame {g = λ Xs → _ ,, Xs} _ (λ X → val-in (value-red v)))
                           (λ (pr' , ws') → keep≈ r' pr' , w' , ws') (prs pr ws)
      λ vs (pr' , ws') → val ε (v T.∷ vs) (keep≈ r' pr' , w' , ws')
prs (drop≈ nu vv pr) (w , ws) =
  ans-skip (value-red (vv-value vv w))
    (ans-in frame-id (λ (pr' , ws') → drop≈ nu vv pr' , w , ws') (prs pr ws)
            (λ vs (pr' , ws') → val ε vs (drop≈ nu vv pr' , w , ws')))

{- The end theorem: for closed programs ------------------------------------------}

optimize-correct : ∀ M → WS 0 M → Equivalent (T.sem M) (T.sem (optimize-program M))
optimize-correct M w =
  red-equivalent value-red Rel (λ (m , w) → sim m w) (λ (m , _) _ v → obs≈ v m)
    (subst₂ _≈_ (SS.sub-id M) (SS.sub-id (optimize-program M)) (opt (λ x → x) M (λ x u → var≈) vv-var) , w)

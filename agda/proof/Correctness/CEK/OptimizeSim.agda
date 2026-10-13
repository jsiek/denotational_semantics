{-

  Correctness of the optimize pass (Clos2 → Clos2) by a forward simulation
  of the Clos2 machine by itself (see the design note in Semantics/CEK/Smallstep.agda).

  The machines run in lock step, except while building a closure: the
  source also evaluates the free variables that the optimized closure
  drops (two source steps each, eval and ret, and no target step). These
  stuttering steps are matched by zero target steps, with a decreasing
  index (measure-simulation): the index of a match is 0, except in the
  middle of dropping a free variable, where it bounds the number of
  source steps left until the next free variable that the target keeps.

  Optimize renames variables, so environments agree through a renaming r:
  Agree M k r ρ₁ ρ₂ says that M, under k binders, finds related values
  at x in ρ₁ and at r x in ρ₂ for every variable x it uses. Values are
  related (_≈_) when they agree, except that a closure of N and vs is
  related to a closure of optimize (ext-var r) N and ws when vs and ws
  agree through r on the variables N uses.

  While a closure is being built (Building), the values collected so far
  agree through the renumbering b of positions that prune computes from
  the free variables already seen. A dropped free variable is a variable;
  it is defined in the source environment because the closure uses it.

  The program must be well scoped (WS 0 M): every variable is bound, so
  in particular a closure's code uses only its parameter and free
  variables. enclose produces such programs from closed ISWIM programs
  (enclose-closed, in Compiler.EncloseScope).

-}

module proof.Correctness.CEK.OptimizeSim where

open import Framework.Syntax.SigUtil using (ν-n)
open import Framework.Syntax.SyntaxUtil using (_,,_; Nil; ⟩_,,_; !_,,_)
open import Language.Clos2
open import Compiler.Optimize hiding (bound; bound-arg; bound-args)
open import proof.Framework.Syntax.Scope Op sig using (WS; WS-arg; WS-args; ws-uses)
import proof.Correctness.CEK.EncloseSim as E
open import Semantics.Observation
open import proof.Semantics.CEK.Smallstep
open import proof.Semantics.CEK.Simulation
open import proof.Framework.ListUtil
import Semantics.CEK.Clos2 as T

open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin)
open import Data.List using ([]; _∷_; map; replicate)
open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_; reverse⁺)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Language.Prim using (int; bool)
open import Data.Bool using (true; false)
open import Data.Maybe using (just; nothing)
import Data.Maybe.Relation.Binary.Pointwise as M
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties
  using (≤-refl; ≤-pred; <-≤-trans; <-irrefl; n<1+n; n≮0; +-suc; +-identityʳ; +-monoʳ-≤)
open import Data.Product using (_×_; Σ-syntax; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst; cong₂)
open import Relation.Nullary using (¬_; Dec; yes; no)

{- Well-scoped terms (Framework.Syntax.Scope) ------------------------------------}

{- the code of a closure with n free variables -}
ws-body : ∀ n k (a : Arg (ν-n n (ν ■))) → WS-arg k a → WS (suc (n + k)) (T.body n a)
ws-body zero k (bind (ast N)) w = w
ws-body (suc n) k (bind a) w =
  subst (λ x → WS (suc x) (T.body n a)) (+-suc n k) (ws-body n (suc k) a w)

{- The simulation relation -----------------------------------------------------}

infix 4 _≈_ _≈k_

data _≈_ : T.Val → T.Val → Set
Lookup : T.Env → ℕ → T.Env → ℕ → Set
data Agree (M : AST) (k : ℕ) (r : Var → Var) (ρ₁ ρ₂ : T.Env) : Set

data _≈_ where
  clo≈ : ∀ {N vs ws r} → Agree N 1 r vs ws → T.clos N vs ≈ T.clos (optimize (ext-var r) N) ws
  const≈ : ∀ {B k} → T.const B k ≈ T.const B k
  tup≈ : ∀ {vs ws} → Pointwise _≈_ vs ws → T.tup vs ≈ T.tup ws
  inl≈ : ∀ {v w} → v ≈ w → T.inl v ≈ T.inl w
  inr≈ : ∀ {v w} → v ≈ w → T.inr v ≈ T.inr w

{- the source value at x and the target value at y are defined and related -}
Lookup ρ₁ x ρ₂ y =
  Σ[ v ∈ T.Val ] Σ[ w ∈ T.Val ] (ρ₁ ‼ x ≡ just v) × (ρ₂ ‼ y ≡ just w) × v ≈ w

{- the scope is only needed for the code of closures inside M -}
data Agree M k r ρ₁ ρ₂ where
  agree : ∀ {j} → WS j M → (∀ x → Uses (k + x) M → Lookup ρ₁ x ρ₂ (r x)) → Agree M k r ρ₁ ρ₂

{- the free variables of a closure, still to be evaluated -}
data AgreeArgs {n} (fvs : Args (replicate n ■)) (r : Var → Var) (ρ₁ ρ₂ : T.Env) : Set where
  agree-args : ∀ {j} → WS-args j fvs → (∀ x → UsesArgs x fvs → Lookup ρ₁ x ρ₂ (r x))
    → AgreeArgs fvs r ρ₁ ρ₂

{- building a closure of code N, with m free variables left: U k says that
   N uses position k (its variable suc k), and the positions k past the m
   left are renumbered b k in the values ws that the target collected -}
record Building (N : AST) (U : ℕ → Set) (m : ℕ) (b : ℕ → ℕ) (vs ws : T.Env) : Set where
  constructor building
  field
    scope : Σ[ j ∈ ℕ ] WS j N
    used : ∀ k → Uses (suc k) N → U k
    collected : ∀ k → U (m + k) → Lookup vs k ws (b k)

{- whether the code N₀ of a closure uses position j (its variable suc j),
   as optimize decides it (N₀ is unbind-n n a, equal to the body) -}
Used : AST → ℕ → Set
Used N₀ j = Uses (suc j) N₀

used? : ∀ N₀ j → Dec (Used N₀ j)
used? N₀ j = uses? (suc j) N₀

{- the frame of a closure (closK) is for a free variable that is kept -}
data _≈k_ : T.Cont → T.Cont → Set where
  halt : T.halt ≈k T.halt
  appL : ∀ {M r ρ₁ ρ₂ κ₁ κ₂} → Agree M 0 r ρ₁ ρ₂ → κ₁ ≈k κ₂
    → T.appL M ρ₁ κ₁ ≈k T.appL (optimize r M) ρ₂ κ₂
  appR : ∀ {v w κ₁ κ₂} → v ≈ w → κ₁ ≈k κ₂ → T.appR v κ₁ ≈k T.appR w κ₂
  tupK : ∀ {vs ws Ms r ρ₁ ρ₂ κ₁ κ₂} → Pointwise _≈_ vs ws
    → All (λ M → Agree M 0 r ρ₁ ρ₂) Ms → κ₁ ≈k κ₂
    → T.tupK vs Ms ρ₁ κ₁ ≈k T.tupK ws (map (optimize r) Ms) ρ₂ κ₂
  closK : ∀ {N m b vs ws r ρ₁ ρ₂ κ₁ κ₂} {fvs : Args (replicate m ■)} (N₀ : AST)
    → Building N (Used N₀) (suc m) b vs ws → AgreeArgs fvs r ρ₁ ρ₂ → κ₁ ≈k κ₂
    → T.closK N vs (args→list fvs) ρ₁ κ₁
      ≈k T.closK (optimize (ext-var (index (prune m r (used? N₀) fvs (keep-base b)))) N) ws
                 (args→list (kept (prune m r (used? N₀) fvs (keep-base b)))) ρ₂ κ₂
  getK : ∀ {n} {i : Fin n} {κ₁ κ₂} → κ₁ ≈k κ₂ → T.getK i κ₁ ≈k T.getK i κ₂
  inlK : ∀ {κ₁ κ₂} → κ₁ ≈k κ₂ → T.inlK κ₁ ≈k T.inlK κ₂
  inrK : ∀ {κ₁ κ₂} → κ₁ ≈k κ₂ → T.inrK κ₁ ≈k T.inrK κ₂
  caseK : ∀ {M N r ρ₁ ρ₂ κ₁ κ₂} → Agree M 1 r ρ₁ ρ₂ → Agree N 1 r ρ₁ ρ₂ → κ₁ ≈k κ₂
    → T.caseK M N ρ₁ κ₁ ≈k T.caseK (optimize (ext-var r) M) (optimize (ext-var r) N) ρ₂ κ₂
  primL : ∀ {p M r ρ₁ ρ₂ κ₁ κ₂} → Agree M 0 r ρ₁ ρ₂ → κ₁ ≈k κ₂
    → T.primL p M ρ₁ κ₁ ≈k T.primL p (optimize r M) ρ₂ κ₂
  primR : ∀ {p v w κ₁ κ₂} → v ≈ w → κ₁ ≈k κ₂ → T.primR p v κ₁ ≈k T.primR p w κ₂

{- Match i s₁ s₂, with index i. While the source evaluates a dropped free
   variable (drop-eval~, drop-ret~), the target waits at the state that
   continues the closure with the free variables left. -}
data Match : ℕ → T.State → T.State → Set where
  eval~ : ∀ {M r ρ₁ ρ₂ κ₁ κ₂} → Agree M 0 r ρ₁ ρ₂ → κ₁ ≈k κ₂
    → Match 0 (T.eval M ρ₁ κ₁) (T.eval (optimize r M) ρ₂ κ₂)
  ret~ : ∀ {v w κ₁ κ₂} → v ≈ w → κ₁ ≈k κ₂ → Match 0 (T.ret v κ₁) (T.ret w κ₂)
  drop-eval~ : ∀ {N m b vs ws y v r ρ₁ ρ₂ κ₁ κ₂} {fvs : Args (replicate m ■)} (N₀ : AST)
    → Building N (Used N₀) (suc m) b vs ws → ¬ Used N₀ m → ρ₁ ‼ y ≡ just v
    → AgreeArgs fvs r ρ₁ ρ₂ → κ₁ ≈k κ₂
    → Match (suc (suc (m * 2))) (T.eval (` y) ρ₁ (T.closK N vs (args→list fvs) ρ₁ κ₁))
        (T.clos-next (optimize (ext-var (index (prune m r (used? N₀) fvs (drop-base b)))) N) ws
                     (args→list (kept (prune m r (used? N₀) fvs (drop-base b)))) ρ₂ κ₂)
  drop-ret~ : ∀ {N m b vs ws v r ρ₁ ρ₂ κ₁ κ₂} {fvs : Args (replicate m ■)} (N₀ : AST)
    → Building N (Used N₀) (suc m) b vs ws → ¬ Used N₀ m → AgreeArgs fvs r ρ₁ ρ₂ → κ₁ ≈k κ₂
    → Match (suc (m * 2)) (T.ret v (T.closK N vs (args→list fvs) ρ₁ κ₁))
        (T.clos-next (optimize (ext-var (index (prune m r (used? N₀) fvs (drop-base b)))) N) ws
                     (args→list (kept (prune m r (used? N₀) fvs (drop-base b)))) ρ₂ κ₂)

{- Related values are observed alike -}
obs≈ : ∀ {v w} → v ≈ w → T.obs v ≡ T.obs w
obs≈-list : ∀ {vs ws} → Pointwise _≈_ vs ws → T.obs-list vs ≡ T.obs-list ws
obs≈ (clo≈ _) = refl
obs≈ const≈ = refl
obs≈ (tup≈ rs) = cong o-tuple (obs≈-list rs)
obs≈ (inl≈ r) = cong o-inl (obs≈ r)
obs≈ (inr≈ r) = cong o-inr (obs≈ r)
obs≈-list [] = refl
obs≈-list (r ∷ rs) = cong₂ _∷_ (obs≈ r) (obs≈-list rs)

{- related operands give related results of a primitive -}
prim≈ : ∀ p {v₁ v₂ w₁ w₂} → v₁ ≈ w₁ → v₂ ≈ w₂ → M.Pointwise _≈_ (T.prim? p v₁ v₂) (T.prim? p w₁ w₂)
prim≈ p {w₁ = w₁} {w₂ = w₂} r s rewrite obs≈ r | obs≈ s with δ? p (T.obs w₁) (T.obs w₂)
... | nothing = M.nothing
... | just (int n) = M.just const≈
... | just (bool true) = M.just (inl≈ (tup≈ []))
... | just (bool false) = M.just (inr≈ (tup≈ []))

{- Agreement of environments ---------------------------------------------------}

agree-ext : ∀ {M r ρ₁ ρ₂ v w} → v ≈ w → Agree M 1 r ρ₁ ρ₂
  → Agree M 0 (ext-var r) (v ∷ ρ₁) (w ∷ ρ₂)
agree-ext {M} {r} {ρ₁} {ρ₂} {v} {w} vw (agree sc look) = agree sc look'
  where
  look' : ∀ x → Uses x M → Lookup (v ∷ ρ₁) x (w ∷ ρ₂) (ext-var r x)
  look' zero _ = v , w , refl , refl , vw
  look' (suc x) u = look x u

{- a subterm M' of M, under k binders -}
agree-sub : ∀ {k M M' r ρ₁ ρ₂} → (∀ {j} → WS j M → WS (k + j) M')
  → (∀ x → Uses (k + x) M' → Uses x M) → Agree M 0 r ρ₁ ρ₂ → Agree M' k r ρ₁ ρ₂
agree-sub sc sub (agree w look) = agree (sc w) (λ x u → look x (sub x u))

agree-all : ∀ {n j r ρ₁ ρ₂} (args : Args (replicate n ■)) → WS-args j args
  → (∀ x → UsesArgs x args → Lookup ρ₁ x ρ₂ (r x))
  → All (λ M → Agree M 0 r ρ₁ ρ₂) (args→list args)
agree-all {zero} Nil _ look = []
agree-all {suc n} (M ,, args) (w , ws) look =
  agree w (λ x u → look x (inj₁ u)) ∷ agree-all args ws (λ x u → look x (inj₂ u))

lookup-pw : ∀ ρ₁ x ρ₂ y → Lookup ρ₁ x ρ₂ y → M.Pointwise _≈_ (ρ₁ ‼ x) (ρ₂ ‼ y)
lookup-pw ρ₁ x ρ₂ y (v , w , e₁ , e₂ , vw) rewrite e₁ | e₂ = M.just vw

{- after a kept or a dropped free variable -}
keep-building : ∀ {N U m b vs ws v w} → v ≈ w → Building N U (suc m) b vs ws
  → Building N U m (keep-base b) (v ∷ vs) (w ∷ ws)
keep-building {N} {U} {m} {b} {vs} {ws} {v} {w} vw (building sc us col) = building sc us col'
  where
  col' : ∀ k → U (m + k) → Lookup (v ∷ vs) k (w ∷ ws) (keep-base b k)
  col' zero _ = v , w , refl , refl , vw
  col' (suc k) u = col k (subst U (+-suc m k) u)

drop-building : ∀ {N U m b vs ws v} → ¬ U m → Building N U (suc m) b vs ws
  → Building N U m (drop-base b) (v ∷ vs) ws
drop-building {N} {U} {m} {b} {vs} {ws} {v} nu (building sc us col) = building sc us col'
  where
  col' : ∀ k → U (m + k) → Lookup (v ∷ vs) k ws (drop-base b k)
  col' zero u = ⊥-elim (nu (subst U (+-identityʳ m) u))
  col' (suc k) u = col k (subst U (+-suc m k) u)

{- the source and target code of a closure -}
opt-body-body : ∀ r k (a : Arg (ν-n k (ν ■))) → opt-body r k a ≡ optimize r (T.body k a)
opt-body-body r zero (bind (ast N)) = refl
opt-body-body r (suc k) (bind a) = opt-body-body r k a

unbind-body : ∀ k (a : Arg (ν-n k (ν ■))) → unbind-n k a ≡ T.body k a
unbind-body zero (bind (ast N)) = refl
unbind-body (suc k) (bind a) = unbind-body k a

{- The simulation, for any Clos2 program P -------------------------------------}

module _ (P : AST) where

  L₂ = T.sem P

  one : ∀ {s s'} → T.step s ≡ next s' → Plus L₂ s s'
  one eq = plus eq ε

  {- answering a lookup or a projection -}
  ret?-answers : ∀ {mv mw κ₁ κ₂ s₂} → M.Pointwise _≈_ mv mw → κ₁ ≈k κ₂
    → T.step s₂ ≡ T.ret? mw κ₂ → Answers≺ L₂ Match 0 (T.ret? mv κ₁) s₂
  ret?-answers (M.just r) κ eq = steps (one eq) (ret~ r κ)
  ret?-answers M.nothing κ eq = stops eq

  tuple-next~ : ∀ {vs ws Ms r ρ₁ ρ₂ κ₁ κ₂} → Pointwise _≈_ vs ws
    → All (λ M → Agree M 0 r ρ₁ ρ₂) Ms → κ₁ ≈k κ₂
    → Match 0 (T.tuple-next vs Ms ρ₁ κ₁) (T.tuple-next ws (map (optimize r) Ms) ρ₂ κ₂)
  tuple-next~ rs [] κ = ret~ (tup≈ (reverse⁺ rs)) κ
  tuple-next~ rs (ag ∷ ags) κ = eval~ ag (tupK rs ags κ)

  {- the next free variable of a closure: kept (eval~), dropped
     (drop-eval~), or none left (ret~ of the closure) -}
  clos-next~ : ∀ {N m b vs ws r ρ₁ ρ₂ κ₁ κ₂} (N₀ : AST) (fvs : Args (replicate m ■))
    → Building N (Used N₀) m b vs ws → AgreeArgs fvs r ρ₁ ρ₂ → κ₁ ≈k κ₂
    → Σ[ i ∈ ℕ ] i ≤ m * 2 × Match i (T.clos-next N vs (args→list fvs) ρ₁ κ₁)
        (T.clos-next (optimize (ext-var (index (prune m r (used? N₀) fvs b))) N) ws
                     (args→list (kept (prune m r (used? N₀) fvs b))) ρ₂ κ₂)
  clos-next~ {m = zero} N₀ Nil (building (_ , sc) us col) _ κ =
    0 , z≤n , ret~ (clo≈ (agree sc (λ x u → col x (us x u)))) κ
  clos-next~ {m = suc m} N₀ ((` y) ,, fvs) bld (agree-args (w , ws) look) κ
    with uses? (suc m) N₀
  ... | yes _ =
    0 , z≤n , eval~ (agree w (λ x u → look x (inj₁ u)))
                    (closK N₀ bld (agree-args ws (λ x u → look x (inj₂ u))) κ)
  ... | no nu with look y (inj₁ refl)
  ...   | _ , _ , e , _ =
    suc (suc (m * 2)) , ≤-refl ,
    drop-eval~ N₀ bld nu e (agree-args ws (λ x u → look x (inj₂ u))) κ
  clos-next~ {m = suc m} N₀ ((op ⦅ args ⦆) ,, fvs) bld (agree-args (w , ws) look) κ =
    0 , z≤n , eval~ (agree w (λ x u → look x (inj₁ u)))
                    (closK N₀ bld (agree-args ws (λ x u → look x (inj₂ u))) κ)

  {- evaluating a closure: start building it -}
  closure~ : ∀ {n r ρ₁ ρ₂ κ₁ κ₂} (a : Arg (ν-n n (ν ■))) (fvs : Args (replicate n ■))
    → Agree (clos-op n ⦅ ! clear a ,, fvs ⦆) 0 r ρ₁ ρ₂ → κ₁ ≈k κ₂
    → Answers≺ L₂ Match 0 (T.step (T.eval (clos-op n ⦅ ! clear a ,, fvs ⦆) ρ₁ κ₁))
        (T.eval (optimize r (clos-op n ⦅ ! clear a ,, fvs ⦆)) ρ₂ κ₂)
  closure~ {n} {r} {ρ₁} {ρ₂} {κ₁} {κ₂} a fvs (agree (wa , wfvs) look) κ
    with clos-next~ (unbind-n n a) fvs bld (agree-args wfvs (λ x u → look x (inj₂ u))) κ
    where
    sc = ws-body n 0 a wa
    {- nothing collected yet: the code uses no position past its n free
       variables, since it is well scoped -}
    bld : Building (T.body n a) (Used (unbind-n n a)) n (λ k → k) [] []
    bld = building (_ , sc) (λ k u → subst (Uses (suc k)) (sym (unbind-body n a)) u)
      (λ k u → ⊥-elim (<-irrefl refl (<-≤-trans
         (≤-pred (ws-uses (T.body n a) sc (subst (Uses (suc (n + k))) (unbind-body n a) u)))
         (+-monoʳ-≤ n z≤n))))
  ... | i , _ , m =
    steps (one refl) (subst (λ B → Match i _ (T.clos-next B [] (args→list (kept Q)) ρ₂ κ₂))
                            (sym eq) m)
    where
    Q = prune n r (λ j → uses? (suc j) (unbind-n n a)) fvs (λ k → k)
    N' = opt-body (ext-var (index Q)) n a
    eq : T.body (count Q) (bind-n-ast (count Q) N') ≡ optimize (ext-var (index Q)) (T.body n a)
    eq = trans (E.body-bind (count Q) N') (opt-body-body (ext-var (index Q)) n a)

  sim : ∀ {i s₁ s₂} → Match i s₁ s₂ → Answers≺ L₂ Match i (T.step s₁) s₂
  sim (eval~ {M = ` x} {r} {ρ₁} {ρ₂} (agree _ look) κ) =
    ret?-answers (lookup-pw ρ₁ x ρ₂ (r x) (look x refl)) κ refl
  sim (eval~ {M = clos-op n ⦅ cons (clear a) fvs ⦆} ag κ) = closure~ a fvs ag κ
  sim (eval~ {M = app ⦅ L ,, M ,, Nil ⦆} ag κ) =
    steps (one refl) (eval~ (agree-sub proj₁ (λ x → inj₁) ag)
                            (appL (agree-sub (λ w → proj₁ (proj₂ w)) (λ x u → inj₂ (inj₁ u)) ag) κ))
  sim (eval~ {M = lit B k ⦅ Nil ⦆} ag κ) = steps (one refl) (ret~ const≈ κ)
  sim (eval~ {M = tuple n ⦅ args ⦆} {r} {ρ₁} {ρ₂} {κ₁} {κ₂} (agree w look) κ) =
    steps (one refl)
          (subst (λ Ns → Match 0 (T.tuple-next [] (args→list args) ρ₁ κ₁) (T.tuple-next [] Ns ρ₂ κ₂))
                 (sym (args→list-hom (optimize r) (opt-args r) (λ _ _ → refl) args))
                 (tuple-next~ [] (agree-all args w look) κ))
  sim (eval~ {M = get i ⦅ M ,, Nil ⦆} ag κ) =
    steps (one refl) (eval~ (agree-sub proj₁ (λ x → inj₁) ag) (getK κ))
  sim (eval~ {M = inl-op ⦅ M ,, Nil ⦆} ag κ) =
    steps (one refl) (eval~ (agree-sub proj₁ (λ x → inj₁) ag) (inlK κ))
  sim (eval~ {M = inr-op ⦅ M ,, Nil ⦆} ag κ) =
    steps (one refl) (eval~ (agree-sub proj₁ (λ x → inj₁) ag) (inrK κ))
  sim (eval~ {M = case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆} ag κ) =
    steps (one refl)
      (eval~ (agree-sub proj₁ (λ x → inj₁) ag)
        (caseK (agree-sub (λ w → proj₁ (proj₂ w)) (λ x u → inj₂ (inj₁ u)) ag)
               (agree-sub (λ w → proj₁ (proj₂ (proj₂ w))) (λ x u → inj₂ (inj₂ (inj₁ u))) ag)
               κ))
  sim (eval~ {M = prim p ⦅ L ,, M ,, Nil ⦆} ag κ) =
    steps (one refl) (eval~ (agree-sub proj₁ (λ x → inj₁) ag)
                            (primL (agree-sub (λ w → proj₁ (proj₂ w)) (λ x u → inj₂ (inj₁ u)) ag) κ))
  sim (ret~ r halt) = stops (cong stop (sym (obs≈ r)))
  sim (ret~ r@(clo≈ _) (appL ag κ)) = steps (one refl) (eval~ ag (appR r κ))
  sim (ret~ const≈ (appL ag κ)) = stops refl
  sim (ret~ (tup≈ _) (appL ag κ)) = stops refl
  sim (ret~ (inl≈ _) (appL ag κ)) = stops refl
  sim (ret~ (inr≈ _) (appL ag κ)) = stops refl
  sim (ret~ r (appR (clo≈ ag) κ)) = steps (one refl) (eval~ (agree-ext r ag) κ)
  sim (ret~ r (appR const≈ κ)) = stops refl
  sim (ret~ r (appR (tup≈ _) κ)) = stops refl
  sim (ret~ r (appR (inl≈ _) κ)) = stops refl
  sim (ret~ r (appR (inr≈ _) κ)) = stops refl
  sim (ret~ r (tupK rs ags κ)) = steps (one refl) (tuple-next~ (r ∷ rs) ags κ)
  sim (ret~ r (closK {fvs = fvs} N₀ bld ag κ)) with clos-next~ N₀ fvs (keep-building r bld) ag κ
  ... | _ , _ , m = steps (one refl) m
  sim (ret~ (tup≈ rs) (getK {i = i} κ)) = ret?-answers (proj-pw i rs) κ refl
  sim (ret~ (clo≈ _) (getK κ)) = stops refl
  sim (ret~ const≈ (getK κ)) = stops refl
  sim (ret~ (inl≈ _) (getK κ)) = stops refl
  sim (ret~ (inr≈ _) (getK κ)) = stops refl
  sim (ret~ r (inlK κ)) = steps (one refl) (ret~ (inl≈ r) κ)
  sim (ret~ r (inrK κ)) = steps (one refl) (ret~ (inr≈ r) κ)
  sim (ret~ (inl≈ r) (caseK agM agN κ)) = steps (one refl) (eval~ (agree-ext r agM) κ)
  sim (ret~ (inr≈ r) (caseK agM agN κ)) = steps (one refl) (eval~ (agree-ext r agN) κ)
  sim (ret~ (clo≈ _) (caseK _ _ κ)) = stops refl
  sim (ret~ const≈ (caseK _ _ κ)) = stops refl
  sim (ret~ (tup≈ _) (caseK _ _ κ)) = stops refl
  sim (ret~ r (primL ag κ)) = steps (one refl) (eval~ ag (primR r κ))
  sim (ret~ s (primR {p} r κ)) = ret?-answers (prim≈ p r s) κ refl
  {- the stuttering steps: the target does not move -}
  sim (drop-eval~ N₀ bld nu e ag κ) rewrite e = stutters (n<1+n _) (drop-ret~ N₀ bld nu ag κ)
  sim (drop-ret~ {v = v} {fvs = fvs} N₀ bld nu ag κ)
    with clos-next~ N₀ fvs (drop-building {v = v} nu bld) ag κ
  ... | _ , i≤ , m = stutters (s≤s i≤) m

{- The end theorem -------------------------------------------------------------}

optimize-fsim : ∀ M → WS 0 M → FSim (T.sem M) (T.sem (optimize-program M))
optimize-fsim M c =
  record { match = Match
         ; init = 0 , eval~ {r = λ x → x} (agree c (λ x u → ⊥-elim (n≮0 (ws-uses M c u)))) halt
         ; sim = sim (optimize-program M) }

optimize-correct : ∀ M → WS 0 M → Equivalent (T.sem M) (T.sem (optimize-program M))
optimize-correct M c = equivalent (optimize-fsim M c)

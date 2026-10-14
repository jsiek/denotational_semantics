{-

  Correctness of typed optimize (Clos2ᵀ → Clos2ᵀ) by a forward
  simulation of the Clos2ᵀ machine by itself (see the design note in
  Semantics/CEK/Smallstep.agda).

  The machines run in lock step, except while building a closure: the
  source also evaluates the free variables that the target dropped (two
  steps each, eval and ret, matched by no target step). A match is a
  synchronisation point (_~_) that the source reaches after i steps
  (Lag), where i is 0 except while dropping free variables.

  The pass renames variables, so environments agree through the
  renaming r on the variables that a term uses (Agree). Values are
  related (_≈_) when they agree, except that a closure of N and V is
  related to one of opt (squeeze fl) N and W when W are the values of V
  that fl keeps, related (Thin), and N uses only kept ones. While a
  closure is built, its frame says what the values still to come give
  (Done): related closures, when they are related as fl selects them.
  The only error, a failed project, happens in both machines at once.

-}

module proof.Correctness.CEK.OptimizeSim where

open import Language.Typed.Type renaming (_≟_ to _≟F_)
open import Language.Typed.Clos2
open import Compiler.Optimize
open import Framework.VecSelect
open import proof.Framework.VecSelect
open import Framework.VecUtil using (more; collected)
open import Semantics.Observation using (o-tuple; o-inl; o-inr)
open import proof.Semantics.CEK.Smallstep
open import proof.Semantics.CEK.Simulation
open import proof.Correctness.CEK.Common
  using (collected≈; toList-collected; fromList-pw; Lock; same-stop; same-next; lock)
import Semantics.CEK.Typed.Clos2 as C

open import Data.Bool using (Bool; true; false; T)
open import Data.Fin using (Fin; zero; suc)
open import Data.Integer using (_≟_)
open import Data.List using (List; []; _∷_; length; _ʳ++_)
open import Data.List.Properties using (reverse-involutive)
import Data.List.Relation.Binary.Pointwise as L
open import Data.Nat using (ℕ; suc; _+_)
open import Data.Product using (Σ-syntax; _,_; proj₂)
open import Data.Vec using (Vec; []; _∷_; lookup; toList)
open import Data.Vec.Relation.Binary.Pointwise.Inductive as V using ([]; _∷_; Pointwise-≡⇒≡)
open import Language.Prim using (sub; eq)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst₂)
open import Relation.Nullary using (yes; no; does)
open import Relation.Nullary.Decidable using (fromWitness)

{- The simulation relation -----------------------------------------------------}

infix 4 _≈_ _≈k_ _~_

data _≈_ : ∀ {A} → C.Val A → C.Val A → Set where
  clo≈ : ∀ {n N} {fl : Vec Bool n} {V W} → Thin _≈_ fl V W → (∀ x → T (uses N x) → Kept fl x)
    → C.clos N V ≈ C.clos (opt (squeeze fl) N) W
  const≈ : ∀ {B c} → C.const {B} c ≈ C.const c
  tup≈ : ∀ {n} {vs ws : Vec _ n} → V.Pointwise _≈_ vs ws → C.tup vs ≈ C.tup ws
  inl≈ : ∀ {v w} → v ≈ w → C.inl v ≈ C.inl w
  inr≈ : ∀ {v w} → v ≈ w → C.inr v ≈ C.inr w
  dyn≈ : ∀ {G v w} → v ≈ w → C.dyn G v ≈ C.dyn G w

Agree : ∀ {k k'} → (Fin k → Bool) → (Fin k → Fin k') → C.Env k → C.Env k' → Set
Agree u r ρ₁ ρ₂ = ∀ x → T (u x) → lookup ρ₁ x ≈ lookup ρ₂ (r x)

ext-agree : ∀ {k k' u r ρ₁ ρ₂ v w} → v ≈ w → Agree {k} {k'} (λ x → u (suc x)) r ρ₁ ρ₂ → Agree u (ext r) (v ∷ ρ₁) (w ∷ ρ₂)
ext-agree vw ag zero _ = vw
ext-agree vw ag (suc x) t = ag x t

{- the rest us, us' of the free variables give related closures -}
Done : ∀ {n m j} → Tm (suc n) Any → Tm (suc m) Any → Vec Bool j → List (C.Val Any) → List (C.Val Any) → Set
Done {n} {m} N N' fl vs ws = ∀ {us us'} → Thin _≈_ fl us us'
  → (e : length (toList us ʳ++ vs) + 0 ≡ n) (e' : length (toList us' ʳ++ ws) + 0 ≡ m)
  → C.clos N (collected (toList us ʳ++ vs) e) ≈ C.clos N' (collected (toList us' ʳ++ ws) e')

data _≈k_ : ∀ {A} → C.Cont A → C.Cont A → Set where
  halt : C.halt ≈k C.halt
  appL : ∀ {k k' M r} {ρ₁ : C.Env k} {ρ₂ : C.Env k'} {κ₁ κ₂} → Agree (uses M) r ρ₁ ρ₂ → κ₁ ≈k κ₂
    → C.appL M ρ₁ κ₁ ≈k C.appL (opt r M) ρ₂ κ₂
  appR : ∀ {f g κ₁ κ₂} → f ≈ g → κ₁ ≈k κ₂ → C.appR f κ₁ ≈k C.appR g κ₂
  tupK : ∀ {k k' n j vs ws r} {Ms : Vec _ j} {ρ₁ : C.Env k} {ρ₂ : C.Env k'} {e : _ ≡ n} {e' κ₁ κ₂}
    → L.Pointwise _≈_ vs ws → Agree (usesV Ms) r ρ₁ ρ₂ → κ₁ ≈k κ₂
    → C.tupK vs Ms ρ₁ e κ₁ ≈k C.tupK ws (opts r Ms) ρ₂ e' κ₂
  {- building a closure: the free variable at hand is kept -}
  closK : ∀ {k k' n m j vs ws r N N'} {u : Fin j → Bool} {fl : Vec Bool j} {Ms : Vec _ j} {ρ₁ : C.Env k} {ρ₂ : C.Env k'}
      {e : _ ≡ n} {e' : _ ≡ m} {κ₁ κ₂}
    → (∀ i → Fl (u i) (lookup fl i) (lookup Ms i)) → Agree (usesV Ms) r ρ₁ ρ₂ → Done N N' (true ∷ fl) vs ws → κ₁ ≈k κ₂
    → C.tupK vs Ms ρ₁ e (C.closK N κ₁) ≈k C.tupK ws (select fl (opts r Ms)) ρ₂ e' (C.closK N' κ₂)
  getK : ∀ {n i κ₁ κ₂} → κ₁ ≈k κ₂ → C.getK {n} i κ₁ ≈k C.getK i κ₂
  inlK : ∀ {κ₁ κ₂} → κ₁ ≈k κ₂ → C.inlK κ₁ ≈k C.inlK κ₂
  inrK : ∀ {κ₁ κ₂} → κ₁ ≈k κ₂ → C.inrK κ₁ ≈k C.inrK κ₂
  caseK : ∀ {k k' M N r} {ρ₁ : C.Env k} {ρ₂ : C.Env k'} {κ₁ κ₂}
    → Agree (λ x → uses M (suc x)) r ρ₁ ρ₂ → Agree (λ x → uses N (suc x)) r ρ₁ ρ₂ → κ₁ ≈k κ₂
    → C.caseK M N ρ₁ κ₁ ≈k C.caseK (opt (ext r) M) (opt (ext r) N) ρ₂ κ₂
  primL : ∀ {k k' p M r} {ρ₁ : C.Env k} {ρ₂ : C.Env k'} {κ₁ κ₂} → Agree (uses M) r ρ₁ ρ₂ → κ₁ ≈k κ₂
    → C.primL p M ρ₁ κ₁ ≈k C.primL p (opt r M) ρ₂ κ₂
  primR : ∀ {p n κ₁ κ₂} → κ₁ ≈k κ₂ → C.primR p n κ₁ ≈k C.primR p n κ₂
  letK : ∀ {k k' N r} {ρ₁ : C.Env k} {ρ₂ : C.Env k'} {κ₁ κ₂} → Agree (λ x → uses N (suc x)) r ρ₁ ρ₂ → κ₁ ≈k κ₂
    → C.letK N ρ₁ κ₁ ≈k C.letK (opt (ext r) N) ρ₂ κ₂
  injK : ∀ {G κ₁ κ₂} → κ₁ ≈k κ₂ → C.injK G κ₁ ≈k C.injK G κ₂
  projK : ∀ {G κ₁ κ₂} → κ₁ ≈k κ₂ → C.projK G κ₁ ≈k C.projK G κ₂

data _~_ : C.State → C.State → Set where
  eval~ : ∀ {k k' A} {M : Tm k A} {r : Fin k → Fin k'} {ρ₁ ρ₂ κ₁ κ₂} → Agree (uses M) r ρ₁ ρ₂ → κ₁ ≈k κ₂
    → C.eval M ρ₁ κ₁ ~ C.eval (opt r M) ρ₂ κ₂
  ret~ : ∀ {A} {v w : C.Val A} {κ₁ κ₂} → v ≈ w → κ₁ ≈k κ₂ → C.ret v κ₁ ~ C.ret w κ₂
  {- a closure's free variables are collected -}
  close~ : ∀ {n m N N'} {V : Vec _ n} {W : Vec _ m} {κ₁ κ₂} → C.clos N V ≈ C.clos N' W → κ₁ ≈k κ₂
    → C.ret (C.tup V) (C.closK N κ₁) ~ C.ret (C.tup W) (C.closK N' κ₂)

{- Related values are observed alike, and primitives give related values -}
obs≈ : ∀ {A} {v w : C.Val A} → v ≈ w → C.obs v ≡ C.obs w
obs≈* : ∀ {n} {vs ws : Vec _ n} → V.Pointwise _≈_ vs ws → C.obs-vec vs ≡ C.obs-vec ws
obs≈ (clo≈ _ _) = refl
obs≈ const≈ = refl
obs≈ (tup≈ rs) = cong o-tuple (obs≈* rs)
obs≈ (inl≈ r) = cong o-inl (obs≈ r)
obs≈ (inr≈ r) = cong o-inr (obs≈ r)
obs≈ (dyn≈ r) = obs≈ r
obs≈* [] = refl
obs≈* (r ∷ rs) = cong₂ _∷_ (obs≈ r) (obs≈* rs)

δ≈ : ∀ p n m → C.δᵀ p n m ≈ C.δᵀ p n m
δ≈ sub n m = const≈
δ≈ eq n m with does (n ≟ m)
... | true = inl≈ (dyn≈ (tup≈ []))
... | false = inr≈ (dyn≈ (tup≈ []))

{- all the free variables, collected -}
collected-id : ∀ {n} (us : Vec (C.Val Any) n) (e : length (toList us ʳ++ []) + 0 ≡ n) → collected (toList us ʳ++ []) e ≡ us
collected-id us e =
  Pointwise-≡⇒≡ (fromList-pw _ us (L.≡⇒Pointwise-≡ (trans (toList-collected (toList us ʳ++ []) e) (reverse-involutive (toList us)))))

{- The simulation, for any Clos2ᵀ program P ------------------------------------}

module _ (P : Tm 0 Any) where

  L₁ = C.sem P
  L₂ = C.sem (optimize-program P)
  Match = Lag L₁ _~_

  go : ∀ {i s₁ s₂ s₂'} → C.step s₂ ≡ next s₂' → s₁ ~ s₂' → Answers≺ L₂ Match i (next s₁) s₂
  go e m = steps₁≺ e (lag₀ m)

  proj~ : ∀ {H G v w κ₁ κ₂} → v ≈ w → κ₁ ≈k κ₂ → Lock (Match 0)
    (C.step (C.ret (C.dyn H v) (C.projK G κ₁))) (C.step (C.ret (C.dyn H w) (C.projK G κ₂)))
  proj~ {H} {G} r k with H ≟F flat G
  ... | yes refl = same-next (lag₀ (ret~ r k))
  ... | no _ = same-stop

  tuple-next~ : ∀ {k k' n j vs ws r} {Ms : Vec _ j} {ρ₁ : C.Env k} {ρ₂ : C.Env k'} {e : _ ≡ n} {e' κ₁ κ₂}
    → L.Pointwise _≈_ vs ws → Agree (usesV Ms) r ρ₁ ρ₂ → κ₁ ≈k κ₂
    → C.tuple-next vs Ms ρ₁ e κ₁ ~ C.tuple-next ws (opts r Ms) ρ₂ e' κ₂
  tuple-next~ {Ms = []} {e = e} {e'} rs ag k = ret~ (tup≈ (collected≈ rs e e')) k
  tuple-next~ {Ms = M ∷ Ms} rs ag k = eval~ (subL ag) (tupK rs (subR ag) k)

  {- the next free variable of a closure: kept (eval~), dropped (the
     source evaluates it, and lags), or none left (close~) -}
  clos-next~ : ∀ {k k' n m j vs ws r N N'} {u : Fin j → Bool} (fl : Vec Bool j) (Ms : Vec (Tm k Any) j)
      {ρ₁ : C.Env k} {ρ₂ : C.Env k'} {κ₁ κ₂}
    → (∀ i → Fl (u i) (lookup fl i) (lookup Ms i)) → Agree (usesV Ms) r ρ₁ ρ₂ → Done N N' fl vs ws → κ₁ ≈k κ₂
    → (e : length vs + j ≡ n) (e' : length ws + count fl ≡ m)
    → Σ[ i ∈ ℕ ] Match i (C.tuple-next vs Ms ρ₁ e (C.closK N κ₁)) (C.tuple-next ws (select fl (opts r Ms)) ρ₂ e' (C.closK N' κ₂))
  clos-next~ [] [] s ag H k e e' = lag-now (close~ (H [] e e') k)
  clos-next~ {vs = vs} (b ∷ fl) (M ∷ Ms) {ρ₁} s ag H k e e' with s zero
  ... | kept = lag-now (eval~ (subL ag) (closK (λ i → s (suc i)) (subR ag) H k))
  ... | var {x = x} _ = lag-step refl (lag-step refl
    (clos-next~ fl Ms (λ i → s (suc i)) (subR ag) (λ th → H (drop th)) k (more {v = lookup ρ₁ x} vs e) e'))

  sim : ∀ {i s₁ s₂} → s₁ ~ s₂ → Answers≺ L₂ Match i (C.step s₁) s₂
  sim (eval~ {M = ` x} ag k) = go refl (ret~ (ag x (fromWitness refl)) k)
  sim (eval~ {M = clos N Ms} ag k) = steps₁≺ refl (proj₂ (clos-next~ (keeps N Ms) Ms s ag H k refl refl))
    where
    s = flags-ok (λ i → uses N (suc i)) Ms
    H : Done N (opt (squeeze (keeps N Ms)) N) (keeps N Ms) [] []
    H {us} {us'} th e e' = subst₂ (λ V W → C.clos N V ≈ C.clos _ W) (sym (collected-id us e)) (sym (collected-id us' e'))
      (clo≈ th (covers {N = N} {Ms} s))
  sim (eval~ {M = app L M} ag k) = go refl (eval~ (subL ag) (appL (subR ag) k))
  sim (eval~ {M = lit B c} ag k) = go refl (ret~ const≈ k)
  sim (eval~ {M = tuple Ms} ag k) = go refl (tuple-next~ L.[] ag k)
  sim (eval~ {M = get i M} ag k) = go refl (eval~ ag (getK k))
  sim (eval~ {M = inl M} ag k) = go refl (eval~ ag (inlK k))
  sim (eval~ {M = inr M} ag k) = go refl (eval~ ag (inrK k))
  sim (eval~ {M = case L M N} ag k) =
    go refl (eval~ (subL ag) (caseK (subL (subR {u = uses L} ag)) (subR (subR {u = uses L} ag)) k))
  sim (eval~ {M = prim p L M} ag k) = go refl (eval~ (subL ag) (primL (subR ag) k))
  sim (eval~ {M = let′ M N} ag k) = go refl (eval~ (subL ag) (letK (subR ag) k))
  sim (eval~ {M = inject G M} ag k) = go refl (eval~ ag (injK k))
  sim (eval~ {M = project G M} ag k) = go refl (eval~ ag (projK k))
  sim (ret~ r halt) = stops (cong stop (sym (obs≈ r)))
  sim (ret~ r (appL ag k)) = go refl (eval~ ag (appR r k))
  sim (ret~ r (appR (clo≈ th cov) k)) = go refl (eval~ (λ x u → thin-lookup r th x (cov x u)) k)
  sim (ret~ r (tupK rs ag k)) = go refl (tuple-next~ (r L.∷ rs) ag k)
  sim (ret~ {v = v} {w} r (closK {vs = vs} {ws} {e = e} {e'} s ag H k)) =
    steps₁≺ refl (proj₂ (clos-next~ _ _ s ag (λ th → H (keep r th)) k (more {v = v} vs e) (more {v = w} ws e')))
  sim (ret~ (tup≈ rs) (getK {i = i} k)) = go refl (ret~ (V.lookup rs i) k)
  sim (ret~ r (inlK k)) = go refl (ret~ (inl≈ r) k)
  sim (ret~ r (inrK k)) = go refl (ret~ (inr≈ r) k)
  sim (ret~ (inl≈ r) (caseK agM agN k)) = go refl (eval~ (ext-agree r agM) k)
  sim (ret~ (inr≈ r) (caseK agM agN k)) = go refl (eval~ (ext-agree r agN) k)
  sim (ret~ const≈ (primL ag k)) = go refl (eval~ ag (primR k))
  sim (ret~ (const≈ {c = m}) (primR {p} {n} k)) = go refl (ret~ (δ≈ p n m) k)
  sim (ret~ r (letK ag k)) = go refl (eval~ (ext-agree r ag) k)
  sim (ret~ r (injK k)) = go refl (ret~ (dyn≈ r) k)
  sim (ret~ (dyn≈ r) (projK k)) = answers≺ (lock (proj~ r k))
  sim (close~ r k) = go refl (ret~ r k)

{- The end theorem: for every closed Clos2ᵀ program ----------------------------}

optimize-correct : ∀ (M : Tm 0 Any) → Equivalent (C.sem M) (C.sem (optimize-program M))
optimize-correct M = equivalent (lag-fsim (lag-now (eval~ (λ ()) halt)) (sim M))

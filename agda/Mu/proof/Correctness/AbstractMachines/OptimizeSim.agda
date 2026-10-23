{-

  Correctness of optimize (Closμ → Closμ) by a forward simulation of
  the Closμ machine by itself, as for typed optimize
  (proof/Correctness/CEK/OptimizeSim.agda).

  The machines run in lock step, except while building a closure: the
  source also evaluates the free variables that the target dropped (two
  steps each, eval and ret, matched by no target step). A match is a
  synchronisation point (_~_) that the source reaches after i steps
  (Lag), where i is 0 except while dropping free variables.

  The pass renames the variables a term uses, so environments agree
  through the renaming r on them (Agree). Values are related (_≈_) when
  they agree, except that a closure of N and V is related to one of N,
  renamed by squeeze, and W when W are the values of V that fl keeps,
  related (Thin), and N uses only kept ones (cov). While a closure is
  built, its frame says what the values still to come give (Done):
  related closures, when they are related as the flags select them.
  The values collected so far are newest first, so the closure's
  environment is vs <><ᵃ us for the values us still to come.

-}

module Mu.proof.Correctness.AbstractMachines.OptimizeSim where

open import Mu.Language.Type
open import Mu.Language.Clos
open import Mu.Compiler.Optimize
open import Mu.Framework.AllUtil
  using (All; []; _∷_; lookup; _<><_; _<><ᵃ_; Flags; kept; select; Kept; squeeze; ∨-l; ∨-r;
         All₂; lookup₂; _<><₂_; Thin; keep; drop; thin-lookup)
open import Semantics.Observation using (o-tuple; o-inl; o-inr)
open import proof.Semantics.CEK.Smallstep
open import proof.Semantics.CEK.Simulation
import Mu.Semantics.AbstractMachines.Clos as C

open import Data.Bool using (Bool; true; false; T)
open import Data.Integer using (_≟_)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ-syntax; _,_; proj₂)
open import Language.Prim using (sub; eq)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂)
open import Relation.Nullary using (does)
open import Relation.Nullary.Decidable using (fromWitness)

{- The simulation relation -----------------------------------------------------}

infix 4 _≈_ _≈k_ _~_

data _≈_ : ∀ {A} → C.Val A → C.Val A → Set where
  clo≈ : ∀ {Δ A B} {N : Tm (A ∷ Δ) B} {fl : Flags Δ} {V W} → Thin _≈_ fl V W
    → (cov : ∀ {C} (x : (A ∷ Δ) ∋ C) → T (uses N x) → Kept fl x)
    → C.pack (C.code N) (C.tup V) ≈ C.pack (C.code (opt N λ x t → squeeze fl x (cov x t))) (C.tup W)
  const≈ : ∀ {B c} → C.const {B} c ≈ C.const c
  tup≈ : ∀ {Δ} {vs ws : All _ Δ} → All₂ _≈_ vs ws → C.tup vs ≈ C.tup ws
  inl≈ : ∀ {A B v w} → v ≈ w → C.inl {A} {B} v ≈ C.inl w
  inr≈ : ∀ {A B v w} → v ≈ w → C.inr {A} {B} v ≈ C.inr w
  fold≈ : ∀ {A v w} → v ≈ w → C.fold {A} v ≈ C.fold w

Agree : ∀ {Γ Γ'} (u : ∀ {C} → Γ ∋ C → Bool) → Ren u Γ' → C.Env Γ → C.Env Γ' → Set
Agree u r ρ₁ ρ₂ = ∀ {C} x (t : T (u {C} x)) → lookup ρ₁ x ≈ lookup ρ₂ (r x t)

ext-agree : ∀ {Γ Γ' A} {u : ∀ {C} → (A ∷ Γ) ∋ C → Bool} {r : Ren (λ x → u (S x)) Γ'} {ρ₁ ρ₂ v w}
  → v ≈ w → Agree (λ x → u (S x)) r ρ₁ ρ₂ → Agree u (ext {u = u} r) (v ∷ ρ₁) (w ∷ ρ₂)
ext-agree vw ag Z _ = vw
ext-agree vw ag (S x) t = ag x t

{- the rest us, us' of the free variables give related closures -}
Done : ∀ {Δv Δw Δ A B} {fl : Flags Δ} → Tm (A ∷ (Δv <>< Δ)) B → Tm (A ∷ (Δw <>< kept fl)) B
  → All C.Val Δv → All C.Val Δw → Set
Done {fl = fl} N N' vs ws = ∀ {us us'} → Thin _≈_ fl us us'
  → C.pack (C.code N) (C.tup (vs <><ᵃ us)) ≈ C.pack (C.code N') (C.tup (ws <><ᵃ us'))

data _≈k_ : ∀ {A} → C.Cont A → C.Cont A → Set where
  halt : ∀ {A} → C.halt {A} ≈k C.halt
  appL : ∀ {Γ Γ' A B} {M : Tm Γ A} {r : Ren (uses M) Γ'} {ρ₁ ρ₂} {κ₁ κ₂ : C.Cont B} → Agree (uses M) r ρ₁ ρ₂ → κ₁ ≈k κ₂
    → C.appL M ρ₁ κ₁ ≈k C.appL (opt M r) ρ₂ κ₂
  appR : ∀ {A B f g κ₁ κ₂} → f ≈ g → κ₁ ≈k κ₂ → C.appR {A} {B} f κ₁ ≈k C.appR g κ₂
  tupK : ∀ {Γ Γ' Δ' A Δ} {vs ws : All C.Val Δ'} {Ms : All (Tm Γ) Δ} {r : Ren (usesA Ms) Γ'} {ρ₁ ρ₂ κ₁ κ₂}
    → All₂ _≈_ vs ws → Agree (usesA Ms) r ρ₁ ρ₂ → κ₁ ≈k κ₂
    → C.tupK {A = A} vs Ms ρ₁ κ₁ ≈k C.tupK ws (opts Ms r) ρ₂ κ₂
  {- building a closure: the free variable at hand is kept -}
  closK : ∀ {Γ Γ' Δv Δw C Δ A B} {vs : All C.Val Δv} {ws : All C.Val Δw} (u : ∀ {D} → Δ ∋ D → Bool)
      {Ms : All (Tm Γ) Δ} {r : Ren (usesA Ms) Γ'} {N : Tm (A ∷ (Δv <>< (C ∷ Δ))) B}
      {N' : Tm (A ∷ (Δw <>< (C ∷ kept (flags u Ms)))) B} {ρ₁ ρ₂ κ₁ κ₂}
    → Agree (usesA Ms) r ρ₁ ρ₂ → Done {fl = true ∷ flags u Ms} N N' vs ws → κ₁ ≈k κ₂
    → C.tupK vs Ms ρ₁ (C.closK N κ₁) ≈k C.tupK ws (select (flags u Ms) (opts Ms r)) ρ₂ (C.closK N' κ₂)
  getK : ∀ {Δ A i κ₁ κ₂} → κ₁ ≈k κ₂ → C.getK {Δ} {A} i κ₁ ≈k C.getK i κ₂
  inlK : ∀ {A B κ₁ κ₂} → κ₁ ≈k κ₂ → C.inlK {A} {B} κ₁ ≈k C.inlK κ₂
  inrK : ∀ {A B κ₁ κ₂} → κ₁ ≈k κ₂ → C.inrK {A} {B} κ₁ ≈k C.inrK κ₂
  caseK : ∀ {Γ Γ' A B C} {M : Tm (A ∷ Γ) C} {N : Tm (B ∷ Γ) C} {rM : Ren (λ x → uses M (S x)) Γ'}
      {rN : Ren (λ x → uses N (S x)) Γ'} {ρ₁ ρ₂ κ₁ κ₂}
    → Agree (λ x → uses M (S x)) rM ρ₁ ρ₂ → Agree (λ x → uses N (S x)) rN ρ₁ ρ₂ → κ₁ ≈k κ₂
    → C.caseK M N ρ₁ κ₁ ≈k C.caseK (opt M (ext {u = uses M} rM)) (opt N (ext {u = uses N} rN)) ρ₂ κ₂
  primL : ∀ {Γ Γ' p M} {r : Ren (uses M) Γ'} {ρ₁ : C.Env Γ} {ρ₂ κ₁ κ₂} → Agree (uses M) r ρ₁ ρ₂ → κ₁ ≈k κ₂
    → C.primL p M ρ₁ κ₁ ≈k C.primL p (opt M r) ρ₂ κ₂
  primR : ∀ {p n κ₁ κ₂} → κ₁ ≈k κ₂ → C.primR p n κ₁ ≈k C.primR p n κ₂
  letK : ∀ {Γ Γ' A B} {N : Tm (A ∷ Γ) B} {r : Ren (λ x → uses N (S x)) Γ'} {ρ₁ ρ₂ κ₁ κ₂}
    → Agree (λ x → uses N (S x)) r ρ₁ ρ₂ → κ₁ ≈k κ₂
    → C.letK N ρ₁ κ₁ ≈k C.letK (opt N (ext {u = uses N} r)) ρ₂ κ₂
  foldK : ∀ {A κ₁ κ₂} → κ₁ ≈k κ₂ → C.foldK {A} κ₁ ≈k C.foldK κ₂
  unfoldK : ∀ {A κ₁ κ₂} → κ₁ ≈k κ₂ → C.unfoldK {A} κ₁ ≈k C.unfoldK κ₂

data _~_ : C.State → C.State → Set where
  eval~ : ∀ {Γ Γ' A} {M : Tm Γ A} {r : Ren (uses M) Γ'} {ρ₁ ρ₂ κ₁ κ₂} → Agree (uses M) r ρ₁ ρ₂ → κ₁ ≈k κ₂
    → C.eval M ρ₁ κ₁ ~ C.eval (opt M r) ρ₂ κ₂
  ret~ : ∀ {A} {v w : C.Val A} {κ₁ κ₂} → v ≈ w → κ₁ ≈k κ₂ → C.ret v κ₁ ~ C.ret w κ₂
  {- a closure's free variables are collected -}
  close~ : ∀ {Δ Δ' A B N N'} {V : All _ Δ} {W : All _ Δ'} {κ₁ κ₂} → C.pack (C.code {A = A} {B} N) (C.tup V) ≈ C.pack (C.code N') (C.tup W) → κ₁ ≈k κ₂
    → C.ret (C.tup V) (C.closK N κ₁) ~ C.ret (C.tup W) (C.closK N' κ₂)

{- Related values are observed alike, and primitives give related values -}
obs≈ : ∀ {A} {v w : C.Val A} → v ≈ w → C.obs v ≡ C.obs w
obs≈* : ∀ {Δ} {vs ws : All _ Δ} → All₂ _≈_ vs ws → C.obs-all vs ≡ C.obs-all ws
obs≈ (clo≈ _ _) = refl
obs≈ const≈ = refl
obs≈ (tup≈ rs) = cong o-tuple (obs≈* rs)
obs≈ (inl≈ r) = cong o-inl (obs≈ r)
obs≈ (inr≈ r) = cong o-inr (obs≈ r)
obs≈ (fold≈ r) = obs≈ r
obs≈* [] = refl
obs≈* (r ∷ rs) = cong₂ _∷_ (obs≈ r) (obs≈* rs)

δ≈ : ∀ p n m → C.δᵀ p n m ≈ C.δᵀ p n m
δ≈ sub n m = const≈
δ≈ eq n m with does (n ≟ m)
... | true = inl≈ (tup≈ [])
... | false = inr≈ (tup≈ [])

{- The simulation, for any Closμ program P ------------------------------------}

module _ {T : Type} (P : Tm [] T) where

  L₁ = C.sem P
  L₂ = C.sem (optimize-program P)
  Match = Lag L₁ _~_

  go : ∀ {i s₁ s₂ s₂'} → C.step s₂ ≡ next s₂' → s₁ ~ s₂' → Answers≺ L₂ Match i (next s₁) s₂
  go e m = steps₁≺ e (lag₀ m)

  tuple-next~ : ∀ {Γ Γ' Δ' Δ} {vs ws : All C.Val Δ'} {Ms : All (Tm Γ) Δ} {r : Ren (usesA Ms) Γ'} {ρ₁ ρ₂}
      {κ₁ κ₂ : C.Cont (tup (Δ' <>< Δ))}
    → All₂ _≈_ vs ws → Agree (usesA Ms) r ρ₁ ρ₂ → κ₁ ≈k κ₂
    → C.tuple-next vs Ms ρ₁ κ₁ ~ C.tuple-next ws (opts Ms r) ρ₂ κ₂
  tuple-next~ {Ms = []} rs ag k = ret~ (tup≈ (rs <><₂ [])) k
  tuple-next~ {Ms = M ∷ Ms} rs ag k = eval~ (λ x t → ag x (∨-l _ t)) (tupK rs (λ x t → ag x (∨-r (uses M x) t)) k)

  {- the next free variable of a closure: kept (eval~), dropped (the
     source evaluates it, and lags), or none left (close~) -}
  clos-next~ : ∀ {Γ Γ' Δv Δw Δ A B} {vs : All C.Val Δv} {ws : All C.Val Δw} (u : ∀ {D} → Δ ∋ D → Bool)
      (Ms : All (Tm Γ) Δ) {r : Ren (usesA Ms) Γ'} {N : Tm (A ∷ (Δv <>< Δ)) B} {N' : Tm (A ∷ (Δw <>< kept (flags u Ms))) B}
      {ρ₁ ρ₂ κ₁ κ₂}
    → Agree (usesA Ms) r ρ₁ ρ₂ → Done {fl = flags u Ms} N N' vs ws → κ₁ ≈k κ₂
    → Σ[ i ∈ ℕ ] Match i (C.tuple-next vs Ms ρ₁ (C.closK N κ₁)) (C.tuple-next ws (select (flags u Ms) (opts Ms r)) ρ₂ (C.closK N' κ₂))
  clos-next~ u [] ag H k = lag-now (close~ (H []) k)
  clos-next~ u (M ∷ Ms) ag H k with keep? M (u Z) | fl-ok M (u Z)
  ... | true | _ =
    lag-now (eval~ (λ x t → ag x (∨-l _ t)) (closK (λ x → u (S x)) (λ x t → ag x (∨-r (uses M x) t)) H k))
  ... | false | var-fv = lag-step refl (lag-step refl
    (clos-next~ (λ x → u (S x)) Ms (λ x t → ag x (∨-r (uses M x) t)) (λ th → H (drop th)) k))

  sim : ∀ {i s₁ s₂} → s₁ ~ s₂ → Answers≺ L₂ Match i (C.step s₁) s₂
  sim (eval~ {M = ` x} ag k) = go refl (ret~ (ag x (fromWitness refl)) k)
  sim (eval~ {M = clos N Ms} ag k) =
    steps₁≺ refl (proj₂ (clos-next~ (λ x → uses N (S x)) Ms ag (λ th → clo≈ th (covers N Ms)) k))
  sim (eval~ {M = app L M} ag k) = go refl (eval~ (λ x t → ag x (∨-l _ t)) (appL (λ x t → ag x (∨-r (uses L x) t)) k))
  sim (eval~ {M = lit B c} ag k) = go refl (ret~ const≈ k)
  sim (eval~ {M = tuple Ms} ag k) = go refl (tuple-next~ [] ag k)
  sim (eval~ {M = get i M} ag k) = go refl (eval~ ag (getK k))
  sim (eval~ {M = inl M} ag k) = go refl (eval~ ag (inlK k))
  sim (eval~ {M = inr M} ag k) = go refl (eval~ ag (inrK k))
  sim (eval~ {M = case L M N} ag k) =
    go refl (eval~ (λ x t → ag x (∨-l _ t))
      (caseK (λ x t → ag x (∨-r (uses L x) (∨-l (uses N (S x)) t))) (λ x t → ag x (∨-r (uses L x) (∨-r (uses M (S x)) t))) k))
  sim (eval~ {M = prim p L M} ag k) = go refl (eval~ (λ x t → ag x (∨-l _ t)) (primL (λ x t → ag x (∨-r (uses L x) t)) k))
  sim (eval~ {M = let′ M N} ag k) = go refl (eval~ (λ x t → ag x (∨-l _ t)) (letK (λ x t → ag x (∨-r (uses M x) t)) k))
  sim (eval~ {M = fold M} ag k) = go refl (eval~ ag (foldK k))
  sim (eval~ {M = unfold M} ag k) = go refl (eval~ ag (unfoldK k))
  sim (ret~ r halt) = stops (cong stop (sym (obs≈ r)))
  sim (ret~ r (appL ag k)) = go refl (eval~ ag (appR r k))
  sim (ret~ r (appR (clo≈ th cov) k)) = go refl (eval~ (λ x t → thin-lookup r th x (cov x t)) k)
  sim (ret~ r (tupK rs ag k)) = go refl (tuple-next~ (r ∷ rs) ag k)
  sim (ret~ r (closK u ag H k)) = steps₁≺ refl (proj₂ (clos-next~ u _ ag (λ th → H (keep r th)) k))
  sim (ret~ (tup≈ rs) (getK {i = i} k)) = go refl (ret~ (lookup₂ rs i) k)
  sim (ret~ r (inlK k)) = go refl (ret~ (inl≈ r) k)
  sim (ret~ r (inrK k)) = go refl (ret~ (inr≈ r) k)
  sim (ret~ (inl≈ r) (caseK agM agN k)) = go refl (eval~ (ext-agree r agM) k)
  sim (ret~ (inr≈ r) (caseK agM agN k)) = go refl (eval~ (ext-agree r agN) k)
  sim (ret~ const≈ (primL ag k)) = go refl (eval~ ag (primR k))
  sim (ret~ (const≈ {c = m}) (primR {p} {n} k)) = go refl (ret~ (δ≈ p n m) k)
  sim (ret~ r (letK ag k)) = go refl (eval~ (ext-agree r ag) k)
  sim (ret~ r (foldK k)) = go refl (ret~ (fold≈ r) k)
  sim (ret~ (fold≈ r) (unfoldK k)) = go refl (ret~ r k)
  sim (close~ r k) = go refl (ret~ r k)

{- The end theorem: for every closed Closμ program ----------------------------}

optimize-correct : ∀ {A} (M : Tm [] A) → Equivalent (C.sem M) (C.sem (optimize-program M))
optimize-correct M = equivalent (lag-fsim (lag-now (eval~ (λ ()) halt)) (sim M))

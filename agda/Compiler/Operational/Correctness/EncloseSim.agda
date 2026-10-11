{-

  Correctness of the enclose pass (ISWIM → Clos2) by a forward simulation
  between their machines (see the design note in Smallstep.agda).

  The machines run in lock step, except that evaluating a function
  (one ISWIM step, building a closure of the whole environment) takes
  several Clos2 steps: evaluating the variables ` (m - 1) , ... , ` 0 that
  the closure captures, one at a time.

  Values are related (_≈_) when they agree, except that an ISWIM closure
  of N and environment ρ is related to a Clos2 closure of enclose N whose
  captured values agree with ρ on every variable N uses (Agree). States
  and continuations are related frame by frame, with the subterms related
  by enclose and their environments by Agree.

  Agree M k ρ₁ ρ₂ says that M, under k binders, finds related values in
  ρ₁ and ρ₂ for the variables it uses, and that the Clos2 environment ρ₂
  covers the bound of M, so that every variable a closure captures is
  defined. The end theorem is for closed programs.

-}

module Compiler.Operational.Correctness.EncloseSim where

open import NewSyntaxUtil using (_,,_; Nil; ⟩_,,_)
open import Compiler.Lang.ISWIM
import Compiler.Lang.Clos2 as C
open import Compiler.Lang.Uses Op sig
open import Compiler.Compile.Optimize using (bind-n-ast)
open import Compiler.Compile.Enclose
open import Compiler.Operational.Observation
open import Compiler.Operational.Smallstep
open import Compiler.Operational.Simulation
open import Compiler.Operational.Machine.Common
import Compiler.Operational.Machine.ISWIM as S
import Compiler.Operational.Machine.Clos2 as T

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; length; map; replicate)
open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_; reverse⁺)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe.Relation.Binary.Pointwise as M
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _⊔_; _≤_; _<_; z≤n; s≤s)
open import Data.Nat.Properties
  using (≤-trans; ≤-pred; <-≤-trans; n<1+n; m≤m⊔n; m≤n⊔m; +-monoʳ-≤; m≤n+m∸n;
         +-identityʳ; +-suc; n≤1+n; m≤n⇒m<n∨m≡n)
open import Data.Product using (_×_; Σ; Σ-syntax; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

{- Every variable a term uses is below its bound -------------------------------}

<-∸1 : ∀ {x b} → suc x < b → x < b ∸ 1
<-∸1 {x} {suc b} sx<sb = ≤-pred sx<sb

uses-bound : ∀ x (M : AST) → Uses x M → x < bound M
uses-bound-arg : ∀ {b} x (a : Arg b) → UsesArg x a → x < bound-arg a
uses-bound-args : ∀ {bs} x (args : Args bs) → UsesArgs x args → x < bound-args args

uses-bound x (` .x) refl = n<1+n x
uses-bound x (op ⦅ args ⦆) u = uses-bound-args x args u

uses-bound-arg x (ast M) u = uses-bound x M u
uses-bound-arg x (bind a) u = <-∸1 (uses-bound-arg (suc x) a u)

uses-bound-args x (cons a args) (inj₁ u) = <-≤-trans (uses-bound-arg x a u) (m≤m⊔n _ _)
uses-bound-args x (cons a args) (inj₂ u) =
  <-≤-trans (uses-bound-args x args u) (m≤n⊔m (bound-arg a) _)

{- The simulation relation -----------------------------------------------------}

infix 4 _≈_ _≈k_ _~_

data _≈_ : S.Val → T.Val → Set
Lookup : ℕ → S.Env → T.Env → Set
data Agree (M : AST) (k : ℕ) (ρ₁ : S.Env) (ρ₂ : T.Env) : Set

data _≈_ where
  clo≈ : ∀ {N ρ vs} → Agree N 1 ρ vs → S.clo N ρ ≈ T.clos (enclose N) vs
  const≈ : ∀ {B k} → S.const B k ≈ T.const B k
  tup≈ : ∀ {vs ws} → Pointwise _≈_ vs ws → S.tup vs ≈ T.tup ws
  inl≈ : ∀ {v w} → v ≈ w → S.inl v ≈ T.inl w
  inr≈ : ∀ {v w} → v ≈ w → S.inr v ≈ T.inr w

Lookup x ρ₁ ρ₂ =
  Σ[ v ∈ S.Val ] Σ[ w ∈ T.Val ] (ρ₁ ‼ x ≡ just v) × (ρ₂ ‼ x ≡ just w) × v ≈ w

data Agree M k ρ₁ ρ₂ where
  agree : (∀ x → Uses (k + x) M → Lookup x ρ₁ ρ₂) → bound M ≤ k + length ρ₂ → Agree M k ρ₁ ρ₂

data _≈k_ : S.Cont → T.Cont → Set where
  halt : S.halt ≈k T.halt
  appL : ∀ {M ρ₁ ρ₂ κ₁ κ₂} → Agree M 0 ρ₁ ρ₂ → κ₁ ≈k κ₂
    → S.appL M ρ₁ κ₁ ≈k T.appL (enclose M) ρ₂ κ₂
  appR : ∀ {v w κ₁ κ₂} → v ≈ w → κ₁ ≈k κ₂ → S.appR v κ₁ ≈k T.appR w κ₂
  tupK : ∀ {vs ws Ms ρ₁ ρ₂ κ₁ κ₂} → Pointwise _≈_ vs ws
    → All (λ M → Agree M 0 ρ₁ ρ₂) Ms → κ₁ ≈k κ₂
    → S.tupK vs Ms ρ₁ κ₁ ≈k T.tupK ws (map enclose Ms) ρ₂ κ₂
  getK : ∀ {n} {i : Fin n} {κ₁ κ₂} → κ₁ ≈k κ₂ → S.getK i κ₁ ≈k T.getK i κ₂
  inlK : ∀ {κ₁ κ₂} → κ₁ ≈k κ₂ → S.inlK κ₁ ≈k T.inlK κ₂
  inrK : ∀ {κ₁ κ₂} → κ₁ ≈k κ₂ → S.inrK κ₁ ≈k T.inrK κ₂
  caseK : ∀ {M N ρ₁ ρ₂ κ₁ κ₂} → Agree M 1 ρ₁ ρ₂ → Agree N 1 ρ₁ ρ₂ → κ₁ ≈k κ₂
    → S.caseK M N ρ₁ κ₁ ≈k T.caseK (enclose M) (enclose N) ρ₂ κ₂

data _~_ : S.State → T.State → Set where
  eval~ : ∀ {M ρ₁ ρ₂ κ₁ κ₂} → Agree M 0 ρ₁ ρ₂ → κ₁ ≈k κ₂
    → S.eval M ρ₁ κ₁ ~ T.eval (enclose M) ρ₂ κ₂
  ret~ : ∀ {v w κ₁ κ₂} → v ≈ w → κ₁ ≈k κ₂ → S.ret v κ₁ ~ T.ret w κ₂

{- Related values are observed alike -}
obs≈ : ∀ {v w} → v ≈ w → S.obs v ≡ T.obs w
obs≈-list : ∀ {vs ws} → Pointwise _≈_ vs ws → S.obs-list vs ≡ T.obs-list ws
obs≈ (clo≈ _) = refl
obs≈ const≈ = refl
obs≈ (tup≈ rs) = cong o-tuple (obs≈-list rs)
obs≈ (inl≈ r) = cong o-inl (obs≈ r)
obs≈ (inr≈ r) = cong o-inr (obs≈ r)
obs≈-list [] = refl
obs≈-list (r ∷ rs) = cong₂' (obs≈ r) (obs≈-list rs)
  where cong₂' : ∀ {a b : Obs} {as bs} → a ≡ b → as ≡ bs → a ∷ as ≡ b ∷ bs
        cong₂' refl refl = refl

{- Agreement of environments ---------------------------------------------------}

lookup : ∀ {M k ρ₁ ρ₂} → Agree M k ρ₁ ρ₂ → ∀ x → Uses (k + x) M → Lookup x ρ₁ ρ₂
lookup (agree look _) = look

agree-ext : ∀ {M ρ₁ ρ₂ v w} → v ≈ w → Agree M 1 ρ₁ ρ₂ → Agree M 0 (v ∷ ρ₁) (w ∷ ρ₂)
agree-ext {M} {ρ₁} {ρ₂} {v} {w} r (agree look b) = agree look' b
  where
  look' : ∀ x → Uses x M → Lookup x (v ∷ ρ₁) (w ∷ ρ₂)
  look' zero _ = v , w , refl , refl , r
  look' (suc x) u = look x u

{- a subterm M' of M, under k binders -}
agree-sub : ∀ {k M M' ρ₁ ρ₂} → (∀ x → Uses (k + x) M' → Uses x M)
  → bound M' ≤ k + bound M → Agree M 0 ρ₁ ρ₂ → Agree M' k ρ₁ ρ₂
agree-sub {k} sub b (agree look b₀) = agree (λ x u → look x (sub x u)) (≤-trans b (+-monoʳ-≤ k b₀))

⊔-left : ∀ {m n} → m ≤ m ⊔ n
⊔-left {m} {n} = m≤m⊔n m n

⊔-right : ∀ {k m n} → m ≤ k ⊔ (m ⊔ n)
⊔-right {k} {m} {n} = ≤-trans (m≤m⊔n m n) (m≤n⊔m k _)


agree-args : ∀ {n ρ₁ ρ₂} (args : Args (replicate n ■))
  → (∀ x → UsesArgs x args → Lookup x ρ₁ ρ₂) → bound-args args ≤ length ρ₂
  → All (λ M → Agree M 0 ρ₁ ρ₂) (S.args→list args)
agree-args {zero} Nil look b = []
agree-args {suc n} (M ,, args) look b =
  agree (λ x u → look x (inj₁ u)) (≤-trans (m≤m⊔n _ _) b)
  ∷ agree-args args (λ x u → look x (inj₂ u)) (≤-trans (m≤n⊔m (bound M) _) b)

enc-list : ∀ {n} (args : Args (replicate n ■))
  → T.args→list (enc-args args) ≡ map enclose (S.args→list args)
enc-list {zero} Nil = refl
enc-list {suc n} (M ,, args) = cong (enclose M ∷_) (enc-list args)

body-bind : ∀ m N → T.body m (bind-n-ast m N) ≡ N
body-bind zero N = refl
body-bind (suc m) N = body-bind m N

{- The simulation, for any Clos2 program P -------------------------------------}

module _ (P : C.AST) where

  L₂ = T.sem P

  one : ∀ {s s'} → T.step s ≡ next s' → Plus L₂ s s'
  one eq = plus eq ε

  {- answering a lookup or a projection -}
  ret?-answers : ∀ {mv mw κ₁ κ₂ s₂} → M.Pointwise _≈_ mv mw → κ₁ ≈k κ₂
    → T.step s₂ ≡ T.ret? mw κ₂ → Answers L₂ _~_ (S.ret? mv κ₁) s₂
  ret?-answers (M.just r) κ eq = steps (one eq) (ret~ r κ)
  ret?-answers M.nothing κ eq = stops eq

  lookup-pw : ∀ x ρ₁ ρ₂ → Lookup x ρ₁ ρ₂ → M.Pointwise _≈_ (ρ₁ ‼ x) (ρ₂ ‼ x)
  lookup-pw x ρ₁ ρ₂ (v , w , e₁ , e₂ , r) rewrite e₁ | e₂ = M.just r

  tuple-next~ : ∀ {vs ws Ms ρ₁ ρ₂ κ₁ κ₂} → Pointwise _≈_ vs ws
    → All (λ M → Agree M 0 ρ₁ ρ₂) Ms → κ₁ ≈k κ₂
    → S.tuple-next vs Ms ρ₁ κ₁ ~ T.tuple-next ws (map enclose Ms) ρ₂ κ₂
  tuple-next~ rs [] κ = ret~ (tup≈ (reverse⁺ rs)) κ
  tuple-next~ rs (ag ∷ ags) κ = eval~ ag (tupK rs ags κ)

  {- evaluating the captured variables ` (j - 1) , ... , ` 0 -}
  capture : ∀ j {N vs ρ κ} → j ≤ length ρ
    → Σ[ vs' ∈ List T.Val ]
        Star L₂ (T.clos-next N vs (T.args→list (fv-vars j)) ρ κ) (T.ret (T.clos N vs') κ)
        × length vs' ≡ j + length vs
        × (∀ x → x < j → vs' ‼ x ≡ ρ ‼ x)
        × (∀ x → vs' ‼ (j + x) ≡ vs ‼ x)
  capture zero {vs = vs} j≤ = vs , ε , refl , (λ x ()) , (λ x → refl)
  capture (suc j) {N} {vs} {ρ} {κ} j< with ‼-< ρ j j<
  ... | v , eq with capture j {N} {v ∷ vs} {ρ} {κ} (≤-trans (n≤1+n j) j<)
  ...   | vs' , σ , len , pre , suf =
    vs' , cong (λ mv → T.ret? mv (T.closK N vs (T.args→list (fv-vars j)) ρ κ)) eq ◅ refl ◅ σ , trans len (+-suc j _) , pre' , suf'
    where

    pre' : ∀ x → x < suc j → vs' ‼ x ≡ ρ ‼ x
    pre' x x< with m≤n⇒m<n∨m≡n (≤-pred x<)
    ... | inj₁ x<j = pre x x<j
    ... | inj₂ refl = trans (subst (λ y → vs' ‼ y ≡ just v) (+-identityʳ x) (suf 0)) (sym eq)

    suf' : ∀ x → vs' ‼ (suc j + x) ≡ vs ‼ x
    suf' x = trans (cong (vs' ‼_) (sym (+-suc j x))) (suf (suc x))

  sim : ∀ {s₁ s₂} → s₁ ~ s₂ → Answers L₂ _~_ (S.step s₁) s₂
  sim (eval~ {M = ` x} {ρ₁} {ρ₂} ag κ) = ret?-answers (lookup-pw x ρ₁ ρ₂ (lookup ag x refl)) κ refl
  sim (eval~ {M = lam ⦅ ⟩ N ,, Nil ⦆} {ρ₁} {ρ₂} {κ₁} {κ₂} (agree look b) κ)
    with capture (bound N ∸ 1) {T.body m (bind-n-ast m (enclose N))} {[]} {ρ₂} {κ₂}
                 (≤-trans (m≤m⊔n m 0) b)
    where m = bound N ∸ 1
  ... | vs' , σ , len , pre , suf =
    steps (plus refl σ)
          (subst (λ B → S.ret (S.clo N ρ₁) κ₁ ~ T.ret (T.clos B vs') κ₂)
                 (sym (body-bind (bound N ∸ 1) (enclose N)))
                 (ret~ (clo≈ (agree look' b')) κ))
    where
    look' : ∀ x → Uses (suc x) N → Lookup x ρ₁ vs'
    look' x u with look x (inj₁ u)
    ... | v , w , e₁ , e₂ , r =
      v , w , e₁ , trans (pre x (<-∸1 (uses-bound (suc x) N u))) e₂ , r

    b' : bound N ≤ 1 + length vs'
    b' rewrite len | +-identityʳ (bound N ∸ 1) = m≤n+m∸n (bound N) 1
  sim (eval~ {M = app ⦅ L ,, M ,, Nil ⦆} ag κ) =
    steps (one refl) (eval~ (agree-sub (λ x → inj₁) ⊔-left ag)
                            (appL (agree-sub (λ x u → inj₂ (inj₁ u)) (⊔-right {bound L}) ag) κ))
  sim (eval~ {M = lit B k ⦅ Nil ⦆} ag κ) = steps (one refl) (ret~ const≈ κ)
  sim (eval~ {M = tuple n ⦅ args ⦆} {ρ₁} {ρ₂} {κ₁} {κ₂} (agree look b) κ) =
    steps (one refl)
          (subst (λ Ns → S.tuple-next [] (S.args→list args) ρ₁ κ₁ ~ T.tuple-next [] Ns ρ₂ κ₂)
                 (sym (enc-list args))
                 (tuple-next~ [] (agree-args args look b) κ))
  sim (eval~ {M = get i ⦅ M ,, Nil ⦆} ag κ) =
    steps (one refl) (eval~ (agree-sub (λ x → inj₁) ⊔-left ag) (getK κ))
  sim (eval~ {M = inl-op ⦅ M ,, Nil ⦆} ag κ) =
    steps (one refl) (eval~ (agree-sub (λ x → inj₁) ⊔-left ag) (inlK κ))
  sim (eval~ {M = inr-op ⦅ M ,, Nil ⦆} ag κ) =
    steps (one refl) (eval~ (agree-sub (λ x → inj₁) ⊔-left ag) (inrK κ))
  sim (eval~ {M = case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆} ag κ) =
    steps (one refl)
      (eval~ (agree-sub (λ x → inj₁) ⊔-left ag)
        (caseK (agree-sub (λ x u → inj₂ (inj₁ u))
                          (≤-trans (m≤n+m∸n (bound M) 1) (s≤s (⊔-right {bound L}))) ag)
               (agree-sub (λ x u → inj₂ (inj₂ (inj₁ u)))
                          (≤-trans (m≤n+m∸n (bound N) 1)
                            (s≤s (≤-trans (m≤m⊔n (bound N ∸ 1) 0)
                              (≤-trans (m≤n⊔m (bound M ∸ 1) _) (m≤n⊔m (bound L) _))))) ag)
               κ))
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

{- The end theorem -------------------------------------------------------------}

{- a closed program uses no variables -}
Closed : AST → Set
Closed M = bound M ≡ 0

agree-closed : ∀ M → Closed M → Agree M 0 [] []
agree-closed M c = agree (λ x u → ⊥-elim (x<0 (subst (x <_) c (uses-bound x M u)))) (subst (_≤ 0) (sym c) z≤n)
  where x<0 : ∀ {x} → x < 0 → ⊥
        x<0 ()

enclose-fsim : ∀ M → Closed M → FSim (S.sem M) (T.sem (enclose M))
enclose-fsim M c =
  plus-simulation _~_ (_ , refl , eval~ (agree-closed M c) halt) (sim (enclose M))

enclose-correct : ∀ M → Closed M → Equivalent (S.sem M) (T.sem (enclose M))
enclose-correct M c =
  equivalent (enclose-fsim M c) machine-det machine-progress machine-det machine-progress

{- in particular -}

enclose-const : ∀ M → Closed M → ∀ B k
  → Terminates (S.sem M) (o-const B k) ⇔ Terminates (T.sem (enclose M)) (o-const B k)
enclose-const M c B k = Equivalent.terminates (enclose-correct M c) (o-const B k)

enclose-converges : ∀ M → Closed M
  → Converges (Terminates (S.sem M)) ⇔ Converges (Terminates (T.sem (enclose M)))
enclose-converges M c =
    (λ { (o , a , t) → o , a , proj₁ (Equivalent.terminates E o) t })
  , (λ { (o , a , t) → o , a , proj₂ (Equivalent.terminates E o) t })
  where E = enclose-correct M c

enclose-wrong : ∀ M → Closed M
  → Terminates (S.sem M) o-wrong ⇔ Terminates (T.sem (enclose M)) o-wrong
enclose-wrong M c = Equivalent.terminates (enclose-correct M c) o-wrong

enclose-diverges : ∀ M → Closed M → Diverges (S.sem M) ⇔ Diverges (T.sem (enclose M))
enclose-diverges M c = Equivalent.diverges (enclose-correct M c)

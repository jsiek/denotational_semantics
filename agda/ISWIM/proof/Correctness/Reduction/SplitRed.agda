{-

  Correctness of typed split (Clos3ᵀ → Clos4ᵀ) by a forward simulation
  between their reduction semantics, in lock step.

  The relation on terms (_≈_) relates each variable to itself; it is a
  congruence, closed under substitution (≈-trav), that relates a closure
  to the pack of its code and the tuple of its free variables, and an
  application to a callc. Applying related
  closures substitutes related values in related code.

-}

module ISWIM.proof.Correctness.Reduction.SplitRed where

open import ISWIM.Language.Typed.Type renaming (_≟_ to _≟F_)
open import ISWIM.Language.Typed.Clos3
import ISWIM.Language.Typed.Clos4 as C
open import ISWIM.Compiler.Split
open import Semantics.Observation
open import proof.Framework.Reduction Obs o-error
open import proof.Framework.ReductionVec Obs o-error using (ans-∷)
open import Semantics.Reduction.Smallstep using (Equivalent)
import ISWIM.proof.Semantics.Reduction.Typed.Clos3 as S
import ISWIM.proof.Semantics.Reduction.Typed.Clos4 as T
open T using (Value; value-red)
import Language.Prim as P

open import Data.Bool using (true; false)
import Data.Integer as Z
open import Data.List using (List; []; _∷_)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Vec.Relation.Unary.All using (All; []; _∷_)
open import Data.Vec.Relation.Binary.Pointwise.Inductive using (Pointwise; []; _∷_)
import Data.Vec.Relation.Binary.Pointwise.Inductive as PW
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary using (Dec; yes; no; does)

{- The relation ----------------------------------------------------------------------}

infix 4 _≈_
data _≈_ : ∀ {Γ A} → Tm Γ A → C.Tm Γ A → Set where
  var≈ : ∀ {Γ A} {x : Γ ∋ A} → ` x ≈ C.` x
  clos≈ : ∀ {Γ n} {N N'} {Ms : Vec (Tm Γ Any) n} {Ms'} → N ≈ N' → Pointwise _≈_ Ms Ms'
    → clos N Ms ≈ C.pack (C.code N') (C.tuple Ms')
  app≈ : ∀ {Γ} {L L' M M'} → L ≈ L' → M ≈ M' → app {Γ} L M ≈ C.callc L' M'
  lit≈ : ∀ {Γ B c} → lit {Γ} B c ≈ C.lit B c
  tuple≈ : ∀ {Γ n} {Ms : Vec (Tm Γ Any) n} {Ms'} → Pointwise _≈_ Ms Ms' → tuple Ms ≈ C.tuple Ms'
  get≈ : ∀ {Γ n i} {M : Tm Γ ⟪ tup n ⟫} {M'} → M ≈ M' → get i M ≈ C.get i M'
  inl≈ : ∀ {Γ} {M M'} → M ≈ M' → inl {Γ} M ≈ C.inl M'
  inr≈ : ∀ {Γ} {M M'} → M ≈ M' → inr {Γ} M ≈ C.inr M'
  case≈ : ∀ {Γ} {L L' M M' N N'} → L ≈ L' → M ≈ M' → N ≈ N'
    → case {Γ} L M N ≈ C.case L' M' N'
  prim≈ : ∀ {Γ p} {L L' M M'} → L ≈ L' → M ≈ M' → prim {Γ} p L M ≈ C.prim p L' M'
  let≈ : ∀ {Γ} {M M' N N'} → M ≈ M' → N ≈ N' → let′ {Γ} M N ≈ C.let′ M' N'
  inject≈ : ∀ {Γ G} {M : Tm Γ ⟪ G ⟫} {M'} → M ≈ M' → inject G M ≈ C.inject G M'
  project≈ : ∀ {Γ t} {M M'} → M ≈ M' → project {Γ} t M ≈ C.project t M'

{- The fundamental lemma ------------------------------------------------------------------}

split≈ : ∀ {Γ A} (M : Tm Γ A) → M ≈ split M
splits≈ : ∀ {Γ n} (Ms : Vec (Tm Γ Any) n) → Pointwise _≈_ Ms (splits Ms)
split≈ (` x) = var≈
split≈ (clos N Ms) = clos≈ (split≈ N) (splits≈ Ms)
split≈ (app L M) = app≈ (split≈ L) (split≈ M)
split≈ (lit B c) = lit≈
split≈ (tuple Ms) = tuple≈ (splits≈ Ms)
split≈ (get i M) = get≈ (split≈ M)
split≈ (inl M) = inl≈ (split≈ M)
split≈ (inr M) = inr≈ (split≈ M)
split≈ (case L M N) = case≈ (split≈ L) (split≈ M) (split≈ N)
split≈ (prim p L M) = prim≈ (split≈ L) (split≈ M)
split≈ (let′ M N) = let≈ (split≈ M) (split≈ N)
split≈ (inject G M) = inject≈ (split≈ M)
split≈ (project t M) = project≈ (split≈ M)
splits≈ [] = []
splits≈ (M ∷ Ms) = split≈ M ∷ splits≈ Ms

{- Closure under substitution -------------------------------------------------------------}

OK : ∀ {Γ Γ₂} (𝒦₁ : S.Kit) (𝒦₂ : T.Kit) → S.Sub 𝒦₁ Γ Γ₂ → T.Sub 𝒦₂ Γ Γ₂ → Set
OK 𝒦₁ 𝒦₂ σ τ = ∀ {A} (x : _ ∋ A) → S.Kit.tm 𝒦₁ (σ x) ≈ T.Kit.tm 𝒦₂ (τ x)

record KR (𝒦₁ : S.Kit) (𝒦₂ : T.Kit) : Set where
  field
    rel-vr : ∀ {Γ B} → S.Kit.tm 𝒦₁ (S.Kit.vr 𝒦₁ {B ∷ Γ} Z) ≈ T.Kit.tm 𝒦₂ (T.Kit.vr 𝒦₂ Z)
    rel-wk : ∀ {Γ A B} {a : S.Kit.K 𝒦₁ Γ A} {b} → S.Kit.tm 𝒦₁ a ≈ T.Kit.tm 𝒦₂ b
      → S.Kit.tm 𝒦₁ (S.Kit.wk 𝒦₁ {B = B} a) ≈ T.Kit.tm 𝒦₂ (T.Kit.wk 𝒦₂ b)

module Trav {𝒦₁ 𝒦₂} (K : KR 𝒦₁ 𝒦₂) where
  open KR K

  ok-ext : ∀ {Γ Γ₂ B} {σ : S.Sub 𝒦₁ Γ Γ₂} {τ : T.Sub 𝒦₂ Γ Γ₂} → OK 𝒦₁ 𝒦₂ σ τ
    → OK 𝒦₁ 𝒦₂ (S.exts 𝒦₁ {B = B} σ) (T.exts 𝒦₂ τ)
  ok-ext ok Z = rel-vr
  ok-ext ok (S x) = rel-wk (ok x)

  ≈-trav : ∀ {Γ Γ₂ A} {σ : S.Sub 𝒦₁ Γ Γ₂} {τ : T.Sub 𝒦₂ Γ Γ₂} {M : Tm Γ A} {M'}
    → M ≈ M' → OK 𝒦₁ 𝒦₂ σ τ → S.trav 𝒦₁ σ M ≈ T.trav 𝒦₂ τ M'
  ≈-travs : ∀ {Γ Γ₂ n} {σ : S.Sub 𝒦₁ Γ Γ₂} {τ : T.Sub 𝒦₂ Γ Γ₂}
    {Ms : Vec (Tm Γ Any) n} {Ms' : Vec (C.Tm Γ Any) n}
    → Pointwise _≈_ Ms Ms' → OK 𝒦₁ 𝒦₂ σ τ → Pointwise _≈_ (S.travs 𝒦₁ σ Ms) (T.travs 𝒦₂ τ Ms')
  ≈-trav var≈ ok = ok _
  ≈-trav (clos≈ n rs) ok = clos≈ n (≈-travs rs ok)
  ≈-trav (app≈ r s) ok = app≈ (≈-trav r ok) (≈-trav s ok)
  ≈-trav lit≈ ok = lit≈
  ≈-trav (tuple≈ rs) ok = tuple≈ (≈-travs rs ok)
  ≈-trav (get≈ r) ok = get≈ (≈-trav r ok)
  ≈-trav (inl≈ r) ok = inl≈ (≈-trav r ok)
  ≈-trav (inr≈ r) ok = inr≈ (≈-trav r ok)
  ≈-trav (case≈ r s t) ok = case≈ (≈-trav r ok) (≈-trav s (ok-ext ok)) (≈-trav t (ok-ext ok))
  ≈-trav (prim≈ r s) ok = prim≈ (≈-trav r ok) (≈-trav s ok)
  ≈-trav (let≈ r s) ok = let≈ (≈-trav r ok) (≈-trav s (ok-ext ok))
  ≈-trav (inject≈ r) ok = inject≈ (≈-trav r ok)
  ≈-trav (project≈ r) ok = project≈ (≈-trav r ok)
  ≈-travs [] ok = []
  ≈-travs (r ∷ rs) ok = ≈-trav r ok ∷ ≈-travs rs ok

varKR : KR S.varK T.varK
varKR = record { rel-vr = var≈ ; rel-wk = λ { var≈ → var≈ } }

tmKR : KR S.tmK T.tmK
tmKR = record { rel-vr = var≈ ; rel-wk = λ r → Trav.≈-trav varKR r λ _ → var≈ }

{- The simulation ------------------------------------------------------------------------------}

R : ∀ {A} → Tm [] A → C.Tm [] A → Set
R = _≈_

Ans′ : ∀ {A} → Tm [] A → Red (Tm [] A) → C.Tm [] A → Set
Ans′ = Ans T.red Value R

obs≈ : ∀ {A} {V V'} → R {A} V V' → S.obs V ≡ T.obs V'
obss≈ : ∀ {n} {Vs : Vec _ n} {Vs'} → Pointwise R Vs Vs' → S.obss Vs ≡ T.obss Vs'
obs≈ (var≈ {x = ()})
obs≈ (clos≈ _ _) = refl
obs≈ (app≈ _ _) = refl
obs≈ lit≈ = refl
obs≈ (tuple≈ rs) = cong o-tuple (obss≈ rs)
obs≈ (get≈ _) = refl
obs≈ (inl≈ r) = cong o-inl (obs≈ r)
obs≈ (inr≈ r) = cong o-inr (obs≈ r)
obs≈ (case≈ _ _ _) = refl
obs≈ (prim≈ _ _) = refl
obs≈ (let≈ _ _) = refl
obs≈ (inject≈ r) = obs≈ r
obs≈ (project≈ _) = refl
obss≈ [] = refl
obss≈ (r ∷ rs) = cong₂ _∷_ (obs≈ r) (obss≈ rs)

out≈ : ∀ p n m → R (S.out p n m) (T.out p n m)
out≈ P.sub n m = lit≈
out≈ P.eq n m with does (n Z.≟ m)
... | true = inl≈ (inject≈ (tuple≈ []))
... | false = inr≈ (inject≈ (tuple≈ []))

≈-[] : ∀ {A} {N : Tm (Any ∷ []) A} {N' V V'} → N ≈ N' → R V V' → R (N S.[ V ]) (N' T.[ V' ])
≈-[] n m = Trav.≈-trav tmKR n λ { Z → m ; (S ()) }

sim : ∀ {A} {M M'} → R {A} M M' → Ans′ M (S.red M) M'
sims : ∀ {n} {Ms : Vec _ n} {Ms'} → Pointwise R Ms Ms' → Ans T.reds (All Value) (Pointwise R) Ms (S.reds Ms) Ms'
sim (var≈ {x = ()})
sim (clos≈ {N' = N'} n rs) =
  ans-in (frame-∘ {redU = T.red} {h = C.tuple} {f = C.pack (C.code N')} (frame _ λ _ → refl) (frame _ λ _ → refl))
    (clos≈ n) (sims rs) λ vs ms → val ε (T.pack T.code (T.tuple vs)) (clos≈ n ms)
sim (app≈ r s) =
  ans-in (frame _ λ _ → refl) (λ m → app≈ m s) (sim r)
    λ v m → ans-in (frame {g = C.callc _} _ λ _ → val-in (value-red v)) (app≈ m) (sim s) λ w m' → β-sim v m w m'
  where
  β-sim : ∀ {V V' W W'} → Value V' → R V V' → Value W' → R W W' → Ans′ (app V W) (S.β V W) (C.callc V' W')
  β-sim (T.pack T.code (T.tuple vs)) (clos≈ n ms) w m' =
    to (one (trans (val-in (value-red (T.pack T.code (T.tuple vs)))) (val-in (value-red w))))
       (Trav.≈-trav tmKR n λ { Z → m' ; (S Z) → tuple≈ ms })
sim lit≈ = val ε T.lit lit≈
sim (tuple≈ rs) = ans-in (frame _ λ _ → refl) tuple≈ (sims rs) λ vs ms → val ε (T.tuple vs) (tuple≈ ms)
sim (get≈ {i = i} r) = ans-in (frame _ λ _ → refl) get≈ (sim r)
  λ { (T.tuple vs) (tuple≈ ms) → to (one (val-in (value-red (T.tuple vs)))) (PW.lookup ms i) }
sim (inl≈ r) = ans-in (frame _ λ _ → refl) inl≈ (sim r) λ v m → val ε (T.inl v) (inl≈ m)
sim (inr≈ r) = ans-in (frame _ λ _ → refl) inr≈ (sim r) λ v m → val ε (T.inr v) (inr≈ m)
sim (case≈ r s t) = ans-in (frame _ λ _ → refl) (λ m → case≈ m s t) (sim r)
  λ { (T.inl v) (inl≈ m) → to (one (val-in (value-red (T.inl v)))) (≈-[] s m)
    ; (T.inr v) (inr≈ m) → to (one (val-in (value-red (T.inr v)))) (≈-[] t m) }
sim (prim≈ {p = p} r s) = ans-in (frame _ λ _ → refl) (λ m → prim≈ m s) (sim r)
  λ { T.lit lit≈ → ans-in (frame {g = C.prim p _} _ λ _ → refl) (prim≈ lit≈) (sim s)
    λ { T.lit lit≈ → to (one refl) (out≈ p _ _) } }
sim (let≈ r s) = ans-in (frame _ λ _ → refl) (λ m → let≈ m s) (sim r)
  λ v m → to (one (val-in (value-red v))) (≈-[] s m)
sim (inject≈ r) = ans-in (frame _ λ _ → refl) inject≈ (sim r) λ v m → val ε (T.inject v) (inject≈ m)
sim (project≈ {t = t} r) = ans-in (frame _ λ _ → refl) project≈ (sim r) λ { (T.inject v) (inject≈ m) → proj-sim v m }
  where
  proj-sim : ∀ {G V V'} → Value V' → R V V' → Ans′ (project t (inject G V)) (S.project? t (inject G V)) (C.project t (C.inject G V'))
  proj-sim {G} {V} {V'} v m = pd (G ≟F flat t) (val-in (value-red (T.inject v)))
    where pd : ∀ {H} (d : Dec (G ≡ H)) {X Y} → T.red X ≡ T.proj-dec d V' → Ans′ Y (S.proj-dec d V) X
          pd (yes refl) e = to (one e) m
          pd (no _) e = error ε e
sims [] = val ε [] []
sims (r ∷ rs) = ans-∷ T.reds (λ _ _ → refl) value-red rs (sim r) (sims rs)

{- The end theorem ----------------------------------------------------------------------}

split-correct : ∀ (M : Tm [] Any) → Equivalent (S.sem M) (T.sem (split-program M))
split-correct M = red-equivalent value-red R sim (λ m _ _ → obs≈ m) (split≈ M)

{-

  Correctness of split (EnvClosμ → PairClosμ) by a forward simulation
  between their reduction semantics, in lock step, as for typed split
  (ISWIM/proof/Correctness/Reduction/SplitRed.agda).

  The relation on terms (_≈_) relates each variable to itself; it is a
  congruence, closed under substitution (≈-trav), that relates a closure
  to the pair of its code and the tuple of its free variables, and an
  application to a callc. Applying related
  closures substitutes related values in related code.

-}

module FPC.proof.Correctness.ReductionSemantics.SplitRed where

open import FPC.Language.Type hiding (_[_])
open import FPC.Language.EnvClos
import FPC.Language.PairClos as C
open import FPC.Compiler.Split
open import FPC.Framework.AllUtil using (All; []; _∷_; All₂; lookup₂)
open import Semantics.Observation
open import proof.Framework.Reduction Obs o-error hiding (Each; []; _∷_)
open import FPC.proof.Framework.ReductionAll Obs o-error using (ans-∷; Each; []; _∷_)
open import Semantics.Reduction.Smallstep using (Equivalent)
import FPC.proof.Semantics.ReductionSemantics.EnvClos as S
import FPC.proof.Semantics.ReductionSemantics.PairClos as T
open T using (Value; value-red)
import Language.Prim as P

open import Data.Bool using (true; false)
import Data.Integer as Z
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary using (does)

{- The relation ----------------------------------------------------------------------}

infix 4 _≈_
data _≈_ : ∀ {Γ A} → Tm Γ A → C.Tm Γ A → Set where
  var≈ : ∀ {Γ A} {x : Γ ∋ A} → ` x ≈ C.` x
  clos≈ : ∀ {Γ Θ A B} {N : Tm (A ∷ tup Θ ∷ []) B} {N'} {Ms : All (Tm Γ) Θ} {Ms'} → N ≈ N'
    → All₂ _≈_ Ms Ms' → clos N Ms ≈ C.pair (C.code N') (C.tuple Ms')
  app≈ : ∀ {Γ A B} {L : Tm Γ (A ⇒ B)} {L' M M'} → L ≈ L' → M ≈ M' → app L M ≈ C.callc L' M'
  lit≈ : ∀ {Γ B c} → lit {Γ} B c ≈ C.lit B c
  tuple≈ : ∀ {Γ Θ} {Ms : All (Tm Γ) Θ} {Ms'} → All₂ _≈_ Ms Ms' → tuple Ms ≈ C.tuple Ms'
  get≈ : ∀ {Γ Θ A} {i : Θ ∋ A} {M : Tm Γ (tup Θ)} {M'} → M ≈ M' → get i M ≈ C.get i M'
  inl≈ : ∀ {Γ A B} {M : Tm Γ A} {M'} → M ≈ M' → inl {B = B} M ≈ C.inl M'
  inr≈ : ∀ {Γ A B} {M : Tm Γ B} {M'} → M ≈ M' → inr {A = A} M ≈ C.inr M'
  case≈ : ∀ {Γ A B C} {L : Tm Γ (A ⊹ B)} {L'} {M : Tm (A ∷ Γ) C} {M' N N'} → L ≈ L'
    → M ≈ M' → N ≈ N' → case L M N ≈ C.case L' M' N'
  prim≈ : ∀ {Γ p} {L L' M M'} → L ≈ L' → M ≈ M' → prim {Γ} p L M ≈ C.prim p L' M'
  let≈ : ∀ {Γ A B} {M : Tm Γ A} {M'} {N : Tm (A ∷ Γ) B} {N'} → M ≈ M' → N ≈ N'
    → let′ M N ≈ C.let′ M' N'
  fold≈ : ∀ {Γ A} {M : Tm Γ (unroll A)} {M'} → M ≈ M' → fold {A = A} M ≈ C.fold M'
  unfold≈ : ∀ {Γ A} {M : Tm Γ (μ A)} {M'} → M ≈ M' → unfold M ≈ C.unfold M'

{- The fundamental lemma ------------------------------------------------------------------}

split≈ : ∀ {Γ A} (M : Tm Γ A) → M ≈ split M
splits≈ : ∀ {Γ Θ} (Ms : All (Tm Γ) Θ) → All₂ _≈_ Ms (splits Ms)
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
split≈ (fold M) = fold≈ (split≈ M)
split≈ (unfold M) = unfold≈ (split≈ M)
splits≈ [] = []
splits≈ (M ∷ Ms) = split≈ M ∷ splits≈ Ms

{- Closure under substitution -------------------------------------------------------------}

OK : ∀ {Γ Γ₂} (𝒦₁ : S.Kit) (𝒦₂ : T.Kit) → S.Sub 𝒦₁ Γ Γ₂ → T.Sub 𝒦₂ Γ Γ₂ → Set
OK 𝒦₁ 𝒦₂ σ τ = ∀ {A} (x : _ ∋ A) → S.Kit.tm 𝒦₁ (σ x) ≈ T.Kit.tm 𝒦₂ (τ x)

{- for a kit of each language, which agree on variable 0 and on weakening -}
module Trav {𝒦₁ 𝒦₂}
  (rel-vr : ∀ {Γ B} → S.Kit.tm 𝒦₁ (S.Kit.vr 𝒦₁ {B ∷ Γ} Z) ≈ T.Kit.tm 𝒦₂ (T.Kit.vr 𝒦₂ Z))
  (rel-wk : ∀ {Γ A B} {a : S.Kit.K 𝒦₁ Γ A} {b} → S.Kit.tm 𝒦₁ a ≈ T.Kit.tm 𝒦₂ b
    → S.Kit.tm 𝒦₁ (S.Kit.wk 𝒦₁ {B = B} a) ≈ T.Kit.tm 𝒦₂ (T.Kit.wk 𝒦₂ b)) where

  ok-ext : ∀ {Γ Γ₂ B} {σ : S.Sub 𝒦₁ Γ Γ₂} {τ : T.Sub 𝒦₂ Γ Γ₂} → OK 𝒦₁ 𝒦₂ σ τ
    → OK 𝒦₁ 𝒦₂ (S.exts 𝒦₁ {B = B} σ) (T.exts 𝒦₂ τ)
  ok-ext ok Z = rel-vr
  ok-ext ok (S x) = rel-wk (ok x)

  ≈-trav : ∀ {Γ Γ₂ A} {σ : S.Sub 𝒦₁ Γ Γ₂} {τ : T.Sub 𝒦₂ Γ Γ₂} {M : Tm Γ A} {M'}
    → M ≈ M' → OK 𝒦₁ 𝒦₂ σ τ → S.trav 𝒦₁ σ M ≈ T.trav 𝒦₂ τ M'
  ≈-travs : ∀ {Γ Γ₂ Θ} {σ : S.Sub 𝒦₁ Γ Γ₂} {τ : T.Sub 𝒦₂ Γ Γ₂}
    {Ms : All (Tm Γ) Θ} {Ms' : All (C.Tm Γ) Θ}
    → All₂ _≈_ Ms Ms' → OK 𝒦₁ 𝒦₂ σ τ → All₂ _≈_ (S.travs 𝒦₁ σ Ms) (T.travs 𝒦₂ τ Ms')
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
  ≈-trav (fold≈ r) ok = fold≈ (≈-trav r ok)
  ≈-trav (unfold≈ r) ok = unfold≈ (≈-trav r ok)
  ≈-travs [] ok = []
  ≈-travs (r ∷ rs) ok = ≈-trav r ok ∷ ≈-travs rs ok

module RenT = Trav {S.varK} {T.varK} var≈ (λ { var≈ → var≈ })
module SubT = Trav {S.tmK} {T.tmK} var≈ (λ r → RenT.≈-trav r λ _ → var≈)

{- The simulation ------------------------------------------------------------------------------}

R : ∀ {A} → Tm [] A → C.Tm [] A → Set
R = _≈_

Ans′ : ∀ {A} → Tm [] A → Red (Tm [] A) → C.Tm [] A → Set
Ans′ = Ans T.red Value R

obs≈ : ∀ {A} {V V'} → R {A} V V' → Value V' → S.obs V ≡ T.obs V'
obss≈ : ∀ {Θ} {Vs : All _ Θ} {Vs'} → All₂ R Vs Vs' → Each Value Vs' → S.obss Vs ≡ T.obss Vs'
obs≈ (clos≈ _ _) _ = refl
obs≈ lit≈ _ = refl
obs≈ (tuple≈ rs) (T.tuple vs) = cong o-tuple (obss≈ rs vs)
obs≈ (inl≈ r) (T.inl v) = cong o-inl (obs≈ r v)
obs≈ (inr≈ r) (T.inr v) = cong o-inr (obs≈ r v)
obs≈ (fold≈ r) (T.fold v) = obs≈ r v
obss≈ [] [] = refl
obss≈ (r ∷ rs) (v ∷ vs) = cong₂ _∷_ (obs≈ r v) (obss≈ rs vs)

out≈ : ∀ p n m → R (S.out p n m) (T.out p n m)
out≈ P.sub n m = lit≈
out≈ P.eq n m with does (n Z.≟ m)
... | true = inl≈ (tuple≈ [])
... | false = inr≈ (tuple≈ [])

≈-[] : ∀ {A B} {N : Tm (A ∷ []) B} {N' V V'} → N ≈ N' → R V V' → R (N S.[ V ]) (N' T.[ V' ])
≈-[] n m = SubT.≈-trav n λ { Z → m }

sim : ∀ {A} {M M'} → R {A} M M' → Ans′ M (S.red M) M'
sims : ∀ {Θ} {Ms : All _ Θ} {Ms'} → All₂ R Ms Ms' → Ans T.reds (Each Value) (All₂ R) Ms (S.reds Ms) Ms'
sim (clos≈ {N' = N'} n rs) =
  ans-in (frame-∘ {redU = T.red} {h = C.tuple} {f = C.pair (C.code N')} (frame _ λ _ → refl) (frame _ λ _ → refl))
    (clos≈ n) (sims rs) λ vs ms → val ε (T.pair T.code (T.tuple vs)) (clos≈ n ms)
sim (app≈ r s) =
  ans-in (frame _ λ _ → refl) (λ m → app≈ m s) (sim r)
    λ v m → ans-in (frame {g = C.callc _} _ λ _ → val-in (value-red v)) (app≈ m) (sim s) λ w m' → β-sim v m w m'
  where
  β-sim : ∀ {A B} {V : Tm [] (A ⇒ B)} {V' W W'} → Value V' → R V V' → Value W' → R W W'
    → Ans′ (app V W) (S.β V refl W) (C.callc V' W')
  β-sim (T.pair T.code (T.tuple vs)) (clos≈ n ms) w m' =
    to (one (trans (val-in (value-red (T.pair T.code (T.tuple vs)))) (val-in (value-red w))))
       (SubT.≈-trav n λ { Z → m' ; (S Z) → tuple≈ ms })
sim lit≈ = val ε T.lit lit≈
sim (tuple≈ rs) = ans-in (frame _ λ _ → refl) tuple≈ (sims rs) λ vs ms → val ε (T.tuple vs) (tuple≈ ms)
sim (get≈ {i = i} r) = ans-in (frame _ λ _ → refl) get≈ (sim r)
  λ { (T.tuple vs) (tuple≈ ms) → to (one (val-in (value-red (T.tuple vs)))) (lookup₂ ms i) }
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
sim (fold≈ r) = ans-in (frame _ λ _ → refl) fold≈ (sim r) λ v m → val ε (T.fold v) (fold≈ m)
sim (unfold≈ r) = ans-in (frame _ λ _ → refl) unfold≈ (sim r)
  λ { (T.fold v) (fold≈ m) → to (one (val-in (value-red (T.fold v)))) m }
sims [] = val ε [] []
sims (r ∷ rs) = ans-∷ T.reds (λ _ _ → refl) value-red rs (sim r) (sims rs)

{- The end theorem ----------------------------------------------------------------------}

split-correct : ∀ {A} (M : Tm [] A) → Equivalent (S.sem M) (T.sem (split-program M))
split-correct M = red-equivalent value-red R sim (λ m _ → obs≈ m) (split≈ M)

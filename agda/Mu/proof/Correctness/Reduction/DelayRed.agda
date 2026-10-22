{-

  Correctness of delay (Clos3μ → Clos4μ) by a forward simulation
  between their reduction semantics, in lock step, as for typed delay
  (proof/Correctness/Reduction/DelayRed.agda).

  The relation on terms (_⊢_≈_) relates a variable x to ρ x, for the
  renaming ρ of the pass; it is a congruence, closed under substitution
  (≈-trav), that relates a closure to the pack of its code and the tuple
  of its free variables, and an application to a callc. Applying related
  closures substitutes related values in related code.

-}

module Mu.proof.Correctness.Reduction.DelayRed where

open import Mu.Language.Type hiding (_[_])
open import Mu.Language.Clos3
import Mu.Language.Clos4 as C
open import Mu.Compiler.Delay
open import Mu.Framework.AllUtil using (All; []; _∷_; All₂; lookup₂)
open import Semantics.Observation
open import proof.Framework.Reduction Obs o-error hiding (Each; []; _∷_)
open import Mu.proof.Framework.ReductionAll Obs o-error using (ans-∷; Each; []; _∷_)
open import Semantics.Reduction.Smallstep using (Equivalent)
import Mu.proof.Semantics.Reduction.Clos3 as S
import Mu.proof.Semantics.Reduction.Clos4 as T
open T using (Value; value-red)
import Language.Prim as P

open import Data.Bool using (true; false)
import Data.Integer as Z
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary using (does)

{- The relation ----------------------------------------------------------------------}

infix 4 _⊢_≈_
data _⊢_≈_ : ∀ {Γ Δ A} → Ren Γ Δ → Tm Γ A → C.Tm Δ A → Set where
  var≈ : ∀ {Γ Δ A} {ρ : Ren Γ Δ} {x : Γ ∋ A} {y} → ρ x ≡ y → ρ ⊢ ` x ≈ C.` y
  clos≈ : ∀ {Γ Δ Θ A B} {ρ : Ren Γ Δ} {N : Tm (A ∷ tup Θ ∷ []) B} {N' Ms} {Ms' : All _ Θ} → (λ x → x) ⊢ N ≈ N'
    → All₂ (ρ ⊢_≈_) Ms Ms' → ρ ⊢ clos N Ms ≈ C.pack (C.code N') (C.tuple Ms')
  app≈ : ∀ {Γ Δ A B} {ρ : Ren Γ Δ} {L : Tm Γ (A ⇒ B)} {L' M M'} → ρ ⊢ L ≈ L' → ρ ⊢ M ≈ M' → ρ ⊢ app L M ≈ C.callc L' M'
  lit≈ : ∀ {Γ Δ} {ρ : Ren Γ Δ} {B c} → ρ ⊢ lit B c ≈ C.lit B c
  tuple≈ : ∀ {Γ Δ Θ} {ρ : Ren Γ Δ} {Ms : All _ Θ} {Ms'} → All₂ (ρ ⊢_≈_) Ms Ms' → ρ ⊢ tuple Ms ≈ C.tuple Ms'
  get≈ : ∀ {Γ Δ Θ A} {i : Θ ∋ A} {ρ : Ren Γ Δ} {M : Tm Γ (tup Θ)} {M'} → ρ ⊢ M ≈ M' → ρ ⊢ get i M ≈ C.get i M'
  inl≈ : ∀ {Γ Δ A B} {ρ : Ren Γ Δ} {M : Tm Γ A} {M'} → ρ ⊢ M ≈ M' → ρ ⊢ inl {B = B} M ≈ C.inl M'
  inr≈ : ∀ {Γ Δ A B} {ρ : Ren Γ Δ} {M : Tm Γ B} {M'} → ρ ⊢ M ≈ M' → ρ ⊢ inr {A = A} M ≈ C.inr M'
  case≈ : ∀ {Γ Δ A B C} {ρ : Ren Γ Δ} {L : Tm Γ (A ⊹ B)} {L'} {M : Tm (A ∷ Γ) C} {M' N N'} → ρ ⊢ L ≈ L'
    → ext ρ ⊢ M ≈ M' → ext ρ ⊢ N ≈ N' → ρ ⊢ case L M N ≈ C.case L' M' N'
  prim≈ : ∀ {Γ Δ p} {ρ : Ren Γ Δ} {L L' M M'} → ρ ⊢ L ≈ L' → ρ ⊢ M ≈ M' → ρ ⊢ prim p L M ≈ C.prim p L' M'
  let≈ : ∀ {Γ Δ A B} {ρ : Ren Γ Δ} {M : Tm Γ A} {M'} {N : Tm (A ∷ Γ) B} {N'} → ρ ⊢ M ≈ M' → ext ρ ⊢ N ≈ N'
    → ρ ⊢ let′ M N ≈ C.let′ M' N'
  fold≈ : ∀ {Γ Δ A} {ρ : Ren Γ Δ} {M : Tm Γ (unroll A)} {M'} → ρ ⊢ M ≈ M' → ρ ⊢ fold {A = A} M ≈ C.fold M'
  unfold≈ : ∀ {Γ Δ A} {ρ : Ren Γ Δ} {M : Tm Γ (μ A)} {M'} → ρ ⊢ M ≈ M' → ρ ⊢ unfold M ≈ C.unfold M'

{- The fundamental lemma ------------------------------------------------------------------}

delay≈ : ∀ {Γ Δ A} (ρ : Ren Γ Δ) (M : Tm Γ A) → ρ ⊢ M ≈ delay ρ M
delays≈ : ∀ {Γ Δ Θ} (ρ : Ren Γ Δ) (Ms : All (Tm Γ) Θ) → All₂ (ρ ⊢_≈_) Ms (delays ρ Ms)
delay≈ ρ (` x) = var≈ refl
delay≈ ρ (clos N Ms) = clos≈ (delay≈ (λ x → x) N) (delays≈ ρ Ms)
delay≈ ρ (app L M) = app≈ (delay≈ ρ L) (delay≈ ρ M)
delay≈ ρ (lit B c) = lit≈
delay≈ ρ (tuple Ms) = tuple≈ (delays≈ ρ Ms)
delay≈ ρ (get i M) = get≈ (delay≈ ρ M)
delay≈ ρ (inl M) = inl≈ (delay≈ ρ M)
delay≈ ρ (inr M) = inr≈ (delay≈ ρ M)
delay≈ ρ (case L M N) = case≈ (delay≈ ρ L) (delay≈ (ext ρ) M) (delay≈ (ext ρ) N)
delay≈ ρ (prim p L M) = prim≈ (delay≈ ρ L) (delay≈ ρ M)
delay≈ ρ (let′ M N) = let≈ (delay≈ ρ M) (delay≈ (ext ρ) N)
delay≈ ρ (fold M) = fold≈ (delay≈ ρ M)
delay≈ ρ (unfold M) = unfold≈ (delay≈ ρ M)
delays≈ ρ [] = []
delays≈ ρ (M ∷ Ms) = delay≈ ρ M ∷ delays≈ ρ Ms

{- Closure under substitution -------------------------------------------------------------}

OK : ∀ {Γ Δ Γ₂ Δ₂} (𝒦₁ : S.Kit) (𝒦₂ : T.Kit) → Ren Γ Δ → Ren Γ₂ Δ₂ → S.Sub 𝒦₁ Γ Γ₂ → T.Sub 𝒦₂ Δ Δ₂ → Set
OK 𝒦₁ 𝒦₂ ρ ρ₂ σ τ = ∀ {A} (x : _ ∋ A) → ρ₂ ⊢ S.Kit.tm 𝒦₁ (σ x) ≈ T.Kit.tm 𝒦₂ (τ (ρ x))

record KR (𝒦₁ : S.Kit) (𝒦₂ : T.Kit) : Set where
  field
    rel-vr : ∀ {Γ Δ B} {ρ : Ren Γ Δ} → ext {B = B} ρ ⊢ S.Kit.tm 𝒦₁ (S.Kit.vr 𝒦₁ Z) ≈ T.Kit.tm 𝒦₂ (T.Kit.vr 𝒦₂ Z)
    rel-wk : ∀ {Γ Δ A B} {ρ : Ren Γ Δ} {a : S.Kit.K 𝒦₁ Γ A} {b} → ρ ⊢ S.Kit.tm 𝒦₁ a ≈ T.Kit.tm 𝒦₂ b
      → ext {B = B} ρ ⊢ S.Kit.tm 𝒦₁ (S.Kit.wk 𝒦₁ a) ≈ T.Kit.tm 𝒦₂ (T.Kit.wk 𝒦₂ b)

module Trav {𝒦₁ 𝒦₂} (K : KR 𝒦₁ 𝒦₂) where
  open KR K

  ok-ext : ∀ {Γ Δ Γ₂ Δ₂ B} {ρ : Ren Γ Δ} {ρ₂ : Ren Γ₂ Δ₂} {σ : S.Sub 𝒦₁ Γ Γ₂} {τ : T.Sub 𝒦₂ Δ Δ₂} → OK 𝒦₁ 𝒦₂ ρ ρ₂ σ τ
    → OK 𝒦₁ 𝒦₂ (ext {B = B} ρ) (ext ρ₂) (S.exts 𝒦₁ σ) (T.exts 𝒦₂ τ)
  ok-ext ok Z = rel-vr
  ok-ext ok (S x) = rel-wk (ok x)

  ≈-trav : ∀ {Γ Δ Γ₂ Δ₂ A} {ρ : Ren Γ Δ} {ρ₂ : Ren Γ₂ Δ₂} {σ : S.Sub 𝒦₁ Γ Γ₂} {τ : T.Sub 𝒦₂ Δ Δ₂} {M : Tm Γ A} {M'}
    → ρ ⊢ M ≈ M' → OK 𝒦₁ 𝒦₂ ρ ρ₂ σ τ → ρ₂ ⊢ S.trav 𝒦₁ σ M ≈ T.trav 𝒦₂ τ M'
  ≈-travs : ∀ {Γ Δ Γ₂ Δ₂ Θ} {ρ : Ren Γ Δ} {ρ₂ : Ren Γ₂ Δ₂} {σ : S.Sub 𝒦₁ Γ Γ₂} {τ : T.Sub 𝒦₂ Δ Δ₂}
    {Ms : All (Tm Γ) Θ} {Ms' : All (C.Tm Δ) Θ}
    → All₂ (ρ ⊢_≈_) Ms Ms' → OK 𝒦₁ 𝒦₂ ρ ρ₂ σ τ → All₂ (ρ₂ ⊢_≈_) (S.travs 𝒦₁ σ Ms) (T.travs 𝒦₂ τ Ms')
  ≈-trav (var≈ refl) ok = ok _
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

varKR : KR S.varK T.varK
varKR = record { rel-vr = var≈ refl ; rel-wk = λ { (var≈ e) → var≈ (cong S e) } }

tmKR : KR S.tmK T.tmK
tmKR = record { rel-vr = var≈ refl ; rel-wk = λ r → Trav.≈-trav varKR r λ _ → var≈ refl }

{- The simulation ------------------------------------------------------------------------------}

module _ {ρ₀ : Ren [] []} where

  R : ∀ {A} → Tm [] A → C.Tm [] A → Set
  R = ρ₀ ⊢_≈_

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

  ≈-[] : ∀ {A B} {N : Tm (A ∷ []) B} {N' V V'} → ext ρ₀ ⊢ N ≈ N' → R V V' → R (N S.[ V ]) (N' T.[ V' ])
  ≈-[] n m = Trav.≈-trav tmKR n λ { Z → m ; (S ()) }

  sim : ∀ {A} {M M'} → R {A} M M' → Ans′ M (S.red M) M'
  sims : ∀ {Θ} {Ms : All _ Θ} {Ms'} → All₂ R Ms Ms' → Ans T.reds (Each Value) (All₂ R) Ms (S.reds Ms) Ms'
  sim (var≈ {x = ()} _)
  sim (clos≈ {N' = N'} n rs) =
    ans-in (frame-∘ {redU = T.red} {h = C.tuple} {f = C.pack (C.code N')} (frame _ λ _ → refl) (frame _ λ _ → refl))
      (clos≈ n) (sims rs) λ vs ms → val ε (T.pack T.code (T.tuple vs)) (clos≈ n ms)
  sim (app≈ r s) =
    ans-in (frame _ λ _ → refl) (λ m → app≈ m s) (sim r)
      λ v m → ans-in (frame {g = C.callc _} _ λ _ → val-in (value-red v)) (app≈ m) (sim s) λ w m' → β-sim v m w m'
    where
    β-sim : ∀ {A B} {V : Tm [] (A ⇒ B)} {V' W W'} → Value V' → R V V' → Value W' → R W W'
      → Ans′ (app V W) (S.β V refl W) (C.callc V' W')
    β-sim (T.pack T.code (T.tuple vs)) (clos≈ n ms) w m' =
      to (one (trans (val-in (value-red (T.pack T.code (T.tuple vs)))) (val-in (value-red w))))
         (Trav.≈-trav tmKR n λ { Z → m' ; (S Z) → tuple≈ ms })
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

delay-correct : ∀ {A} (M : Tm [] A) → Equivalent (S.sem M) (T.sem (delay-program M))
delay-correct M = red-equivalent value-red R sim (λ m _ → obs≈ m) (delay≈ _ M)

{-

  Correctness of enclose (ISWIMμ → Clos2μ) by a forward simulation
  between their reduction semantics, in lock step, as for typed enclose
  (proof/Correctness/Reduction/EncloseRed.agda).

  The relation on terms (_≈_) is a congruence, closed under substitution
  (≈-trav, for both kits), except for functions. Substitution goes into
  an ISWIMμ function, but not into the code of a Clos2μ closure, only
  into the terms it captures. So a function lam (sub (exts σ) N) is
  related to a closure of code N' related to N that captures terms Fs
  related to σ. Applying them substitutes related values in N and N'
  (exts-[]). A closure captures variables or values (VV), so in a closed
  term it captures values and is a value.

-}

module Mu.proof.Correctness.Reduction.EncloseRed where

open import Mu.Language.Type hiding (_[_])
open import Mu.Language.ISWIM
import Mu.Language.Clos2 as C
open import Mu.Compiler.Enclose using (enclose; encs)
open import Mu.Framework.AllUtil using (All; []; _∷_; lookup; tab; All₂; lookup₂)
open import Semantics.Observation
open import proof.Framework.Reduction Obs o-error hiding (Each; []; _∷_)
open import Mu.proof.Framework.ReductionAll Obs o-error using (ans-∷; Each; []; _∷_; each-lookup)
open import Semantics.Reduction.Smallstep using (Equivalent)
import Mu.proof.Semantics.Reduction.ISWIM as S
import Mu.proof.Semantics.Reduction.Clos2 as T
open T using (Value; value-red)
import Language.Prim as P

open import Data.Bool using (true; false)
import Data.Integer as Z
open import Data.List using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary using (does)

{- The relation --------------------------------------------------------------}

{- what a closure captures: a variable or a value -}
data VV {Γ} : ∀ {A} → C.Tm Γ A → Set where
  var : ∀ {A} (x : Γ ∋ A) → VV (C.` x)
  val : ∀ {A} {V : C.Tm Γ A} → Value V → VV V

infix 4 _≈_
data _≈_ : ∀ {Γ A} → Tm Γ A → C.Tm Γ A → Set where
  var≈ : ∀ {Γ A} {x : Γ ∋ A} → ` x ≈ C.` x
  lam≈ : ∀ {Γ Δ A B} {N : Tm (A ∷ Δ) B} {N'} {σ : ∀ {C} → Δ ∋ C → Tm Γ C} {Fs : All (C.Tm Γ) Δ}
    → N ≈ N' → (∀ {C} (i : Δ ∋ C) → σ i ≈ lookup Fs i) → Each VV Fs
    → lam (S.sub (S.exts S.tmK σ) N) ≈ C.clos N' Fs
  app≈ : ∀ {Γ A B} {L : Tm Γ (A ⇒ B)} {L' M M'} → L ≈ L' → M ≈ M' → app L M ≈ C.app L' M'
  lit≈ : ∀ {Γ B c} → lit {Γ} B c ≈ C.lit B c
  tuple≈ : ∀ {Γ Δ} {Ms : All (Tm Γ) Δ} {Ms'} → All₂ _≈_ Ms Ms' → tuple Ms ≈ C.tuple Ms'
  get≈ : ∀ {Γ Δ A} {i : Δ ∋ A} {M : Tm Γ (tup Δ)} {M'} → M ≈ M' → get i M ≈ C.get i M'
  inl≈ : ∀ {Γ A B} {M : Tm Γ A} {M'} → M ≈ M' → inl {B = B} M ≈ C.inl M'
  inr≈ : ∀ {Γ A B} {M : Tm Γ B} {M'} → M ≈ M' → inr {A = A} M ≈ C.inr M'
  case≈ : ∀ {Γ A B C} {L : Tm Γ (A ⊹ B)} {L'} {M : Tm (A ∷ Γ) C} {M' N N'} → L ≈ L' → M ≈ M' → N ≈ N'
    → case L M N ≈ C.case L' M' N'
  prim≈ : ∀ {Γ p} {L : Tm Γ _} {L' M M'} → L ≈ L' → M ≈ M' → prim p L M ≈ C.prim p L' M'
  let≈ : ∀ {Γ A B} {M : Tm Γ A} {M'} {N : Tm (A ∷ Γ) B} {N'} → M ≈ M' → N ≈ N' → let′ M N ≈ C.let′ M' N'
  fold≈ : ∀ {Γ A} {M : Tm Γ (unroll A)} {M'} → M ≈ M' → fold {A = A} M ≈ C.fold M'
  unfold≈ : ∀ {Γ A} {M : Tm Γ (μ A)} {M'} → M ≈ M' → unfold M ≈ C.unfold M'

{- The fundamental lemma -------------------------------------------------------}

vv-tab : ∀ {Γ Δ} (g : ∀ {C} → Δ ∋ C → Γ ∋ C) → Each VV (tab {P = C.Tm Γ} (λ i → C.` g i))
vv-tab {Δ = []} g = []
vv-tab {Δ = _ ∷ Δ} g = var _ ∷ vv-tab (λ i → g (S i))

lookup-tab : ∀ {Γ Δ C} (g : ∀ {C} → Δ ∋ C → Γ ∋ C) (i : Δ ∋ C) → lookup (tab {P = C.Tm Γ} (λ x → C.` g x)) i ≡ C.` g i
lookup-tab g Z = refl
lookup-tab g (S i) = lookup-tab (λ x → g (S x)) i

enc : ∀ {Γ A} (M : Tm Γ A) → M ≈ enclose M
encs≈ : ∀ {Γ Δ} (Ms : All (Tm Γ) Δ) → All₂ _≈_ Ms (encs Ms)
enc (` x) = var≈
enc (lam N) = subst (λ X → lam X ≈ C.clos (enclose N) (tab C.`_)) (S.sub-id (λ { Z → refl ; (S x) → refl }) N)
  (lam≈ {σ = `_} (enc N) (λ i → subst (` i ≈_) (sym (lookup-tab (λ x → x) i)) var≈) (vv-tab (λ i → i)))
enc (app L M) = app≈ (enc L) (enc M)
enc (lit B c) = lit≈
enc (tuple Ms) = tuple≈ (encs≈ Ms)
enc (get i M) = get≈ (enc M)
enc (inl M) = inl≈ (enc M)
enc (inr M) = inr≈ (enc M)
enc (case L M N) = case≈ (enc L) (enc M) (enc N)
enc (prim p L M) = prim≈ (enc L) (enc M)
enc (let′ M N) = let≈ (enc M) (enc N)
enc (fold M) = fold≈ (enc M)
enc (unfold M) = unfold≈ (enc M)
encs≈ [] = []
encs≈ (M ∷ Ms) = enc M ∷ encs≈ Ms

{- Closure under substitution ----------------------------------------------------}

{- a kit of each language, which agree -}
record KR (𝒦₁ : S.Kit) (𝒦₂ : T.Kit) : Set where
  module K₁ = S.Kit 𝒦₁
  module K₂ = T.Kit 𝒦₂
  field
    laws : S.Laws 𝒦₁
    rel-vr : ∀ {Γ A} (x : Γ ∋ A) → K₁.tm (K₁.vr x) ≈ K₂.tm (K₂.vr x)
    rel-wk : ∀ {Γ A B} {a : K₁.K Γ A} {b} → K₁.tm a ≈ K₂.tm b → K₁.tm (K₁.wk {B = B} a) ≈ K₂.tm (K₂.wk b)
    vv-vr : ∀ {Γ A} (x : Γ ∋ A) → VV (K₂.tm (K₂.vr x))
    vv-wk : ∀ {Γ A B} {b : K₂.K Γ A} → VV (K₂.tm b) → VV (K₂.tm (K₂.wk {B = B} b))

module Trav {𝒦₁ 𝒦₂} (K : KR 𝒦₁ 𝒦₂) where
  open KR K
  open S.Laws laws

  OK : ∀ {Γ Δ} → S.Sub 𝒦₁ Γ Δ → T.Sub 𝒦₂ Γ Δ → Set
  OK σ τ = ∀ {A} (x : _ ∋ A) → K₁.tm (σ x) ≈ K₂.tm (τ x)

  VK : ∀ {Γ Δ} → T.Sub 𝒦₂ Γ Δ → Set
  VK τ = ∀ {A} (x : _ ∋ A) → VV (K₂.tm (τ x))

  ≈-trav : ∀ {Γ Δ A} {σ : S.Sub 𝒦₁ Γ Δ} {τ : T.Sub 𝒦₂ Γ Δ} {M : Tm Γ A} {M'} → M ≈ M'
    → OK σ τ → VK τ → S.trav 𝒦₁ σ M ≈ T.trav 𝒦₂ τ M'
  ≈-travs : ∀ {Γ Δ Δ'} {σ : S.Sub 𝒦₁ Γ Δ} {τ : T.Sub 𝒦₂ Γ Δ} {Ms : All (Tm Γ) Δ'} {Ms'} → All₂ _≈_ Ms Ms'
    → OK σ τ → VK τ → All₂ _≈_ (S.travs 𝒦₁ σ Ms) (T.travs 𝒦₂ τ Ms')
  vvs-trav : ∀ {Γ Δ Δ'} {τ : T.Sub 𝒦₂ Γ Δ} {Fs : All (C.Tm Γ) Δ'} → Each VV Fs → VK τ → Each VV (T.travs 𝒦₂ τ Fs)
  ok-exts : ∀ {Γ Δ B} {σ : S.Sub 𝒦₁ Γ Δ} {τ : T.Sub 𝒦₂ Γ Δ} → OK σ τ → OK (S.exts 𝒦₁ {B = B} σ) (T.exts 𝒦₂ τ)
  ok-exts h Z = rel-vr Z
  ok-exts h (S x) = rel-wk (h x)
  vv-exts : ∀ {Γ Δ B} {τ : T.Sub 𝒦₂ Γ Δ} → VK τ → VK (T.exts 𝒦₂ {B = B} τ)
  vv-exts h Z = vv-vr Z
  vv-exts h (S x) = vv-wk (h x)

  ≈-trav var≈ ok vk = ok _
  ≈-trav {σ = σ} {τ} (lam≈ {N = N} {σ = ρ} {Fs} n h vv) ok vk =
    subst (λ X → lam X ≈ C.clos _ (T.travs 𝒦₂ τ Fs))
          (sym (S.trav-sub laws (λ { Z → tm-vr Z ; (S y) → exts-ren σ (ρ y) }) N))
          (lam≈ n (λ i → subst (_ ≈_) (sym (T.lookup-travs τ Fs i)) (≈-trav (h i) ok vk)) (vvs-trav vv vk))
  ≈-trav (app≈ r s) ok vk = app≈ (≈-trav r ok vk) (≈-trav s ok vk)
  ≈-trav lit≈ ok vk = lit≈
  ≈-trav (tuple≈ rs) ok vk = tuple≈ (≈-travs rs ok vk)
  ≈-trav (get≈ r) ok vk = get≈ (≈-trav r ok vk)
  ≈-trav (inl≈ r) ok vk = inl≈ (≈-trav r ok vk)
  ≈-trav (inr≈ r) ok vk = inr≈ (≈-trav r ok vk)
  ≈-trav (case≈ r s t) ok vk = case≈ (≈-trav r ok vk) (≈-trav s (ok-exts ok) (vv-exts vk)) (≈-trav t (ok-exts ok) (vv-exts vk))
  ≈-trav (prim≈ r s) ok vk = prim≈ (≈-trav r ok vk) (≈-trav s ok vk)
  ≈-trav (let≈ r s) ok vk = let≈ (≈-trav r ok vk) (≈-trav s (ok-exts ok) (vv-exts vk))
  ≈-trav (fold≈ r) ok vk = fold≈ (≈-trav r ok vk)
  ≈-trav (unfold≈ r) ok vk = unfold≈ (≈-trav r ok vk)
  ≈-travs [] ok vk = []
  ≈-travs (r ∷ rs) ok vk = ≈-trav r ok vk ∷ ≈-travs rs ok vk
  vvs-trav [] vk = []
  vvs-trav (var x ∷ vv) vk = vk x ∷ vvs-trav vv vk
  vvs-trav (val v ∷ vv) vk = val (T.value-trav v) ∷ vvs-trav vv vk

varKR : KR S.varK T.varK
varKR = record { laws = S.varL ; rel-vr = λ _ → var≈ ; rel-wk = λ { var≈ → var≈ } ; vv-vr = var ; vv-wk = λ _ → var _ }

tmKR : KR S.tmK T.tmK
tmKR = record { laws = S.tmL ; rel-vr = λ _ → var≈ ; rel-wk = λ r → Trav.≈-trav varKR r (λ _ → var≈) (λ _ → var _)
              ; vv-vr = var ; vv-wk = λ { (var x) → var _ ; (val v) → val (T.value-trav v) } }

{- substituting a value for the variable of a binder -}
≈-[] : ∀ {A B} {N : Tm (A ∷ []) B} {N' V V'} → N ≈ N' → V ≈ V' → Value V' → (N S.[ V ]) ≈ (N' T.[ V' ])
≈-[] n m v = Trav.≈-trav tmKR n (λ { Z → m }) (λ { Z → val v })

{- The simulation ------------------------------------------------------------------}

Ans′ : ∀ {A} → Tm [] A → Red (Tm [] A) → C.Tm [] A → Set
Ans′ = Ans T.red Value _≈_

vvs-values : ∀ {Δ} {Fs : All (C.Tm []) Δ} → Each VV Fs → Each Value Fs
vvs-values [] = []
vvs-values (var () ∷ vv)
vvs-values (val v ∷ vv) = v ∷ vvs-values vv

obs≈ : ∀ {A} {V : Tm [] A} {V'} → V ≈ V' → Value V' → S.obs V ≡ T.obs V'
obss≈ : ∀ {Δ} {Vs : All (Tm []) Δ} {Vs'} → All₂ _≈_ Vs Vs' → Each Value Vs' → S.obss Vs ≡ T.obss Vs'
obs≈ (lam≈ _ _ _) _ = refl
obs≈ lit≈ _ = refl
obs≈ (tuple≈ rs) (T.tuple vs) = cong o-tuple (obss≈ rs vs)
obs≈ (inl≈ r) (T.inl v) = cong o-inl (obs≈ r v)
obs≈ (inr≈ r) (T.inr v) = cong o-inr (obs≈ r v)
obs≈ (fold≈ r) (T.fold v) = obs≈ r v
obss≈ [] [] = refl
obss≈ (r ∷ rs) (v ∷ vs) = cong₂ _∷_ (obs≈ r v) (obss≈ rs vs)

out≈ : ∀ p n m → S.out {[]} p n m ≈ T.out p n m
out≈ P.sub n m = lit≈
out≈ P.eq n m with does (n Z.≟ m)
... | true = inl≈ (tuple≈ [])
... | false = inr≈ (tuple≈ [])

sim : ∀ {A} {M : Tm [] A} {M'} → M ≈ M' → Ans′ M (S.red M) M'
sims : ∀ {Δ} {Ms : All (Tm []) Δ} {Ms'} → All₂ _≈_ Ms Ms' → Ans T.reds (Each Value) (All₂ _≈_) Ms (S.reds Ms) Ms'
sim (var≈ {x = ()})
sim m@(lam≈ _ _ vv) = val ε (T.clos (vvs-values vv)) m
sim (app≈ r s) =
  ans-in (frame _ λ _ → refl) (λ m → app≈ m s) (sim r)
    λ v m → ans-in (frame {g = C.app _} _ λ _ → val-in (value-red v)) (app≈ m) (sim s) λ w m' → β-sim v m w m'
  where
  β-sim : ∀ {A B} {V : Tm [] (A ⇒ B)} {V' W W'} → Value V' → V ≈ V' → Value W' → W ≈ W'
    → Ans′ (app V W) (S.β V refl W) (C.app V' W')
  β-sim (T.clos vs) (lam≈ {N = N} {σ = σ} n h vv) w m' =
    to (one (trans (val-in (value-red (T.clos vs))) (val-in (value-red w))))
       (subst (_≈ _) (sym (S.exts-[] σ _ N))
              (Trav.≈-trav tmKR n (λ { Z → m' ; (S i) → h i }) (λ { Z → val w ; (S i) → each-lookup vv i })))
sim lit≈ = val ε T.lit lit≈
sim (tuple≈ rs) = ans-in (frame _ λ _ → refl) tuple≈ (sims rs) λ vs ms → val ε (T.tuple vs) (tuple≈ ms)
sim (get≈ {i = i} r) = ans-in (frame _ λ _ → refl) get≈ (sim r)
  λ { (T.tuple vs) (tuple≈ ms) → to (one (val-in (value-red (T.tuple vs)))) (lookup₂ ms i) }
sim (inl≈ r) = ans-in (frame _ λ _ → refl) inl≈ (sim r) λ v m → val ε (T.inl v) (inl≈ m)
sim (inr≈ r) = ans-in (frame _ λ _ → refl) inr≈ (sim r) λ v m → val ε (T.inr v) (inr≈ m)
sim (case≈ r s t) = ans-in (frame _ λ _ → refl) (λ m → case≈ m s t) (sim r)
  λ { (T.inl v) (inl≈ m) → to (one (val-in (value-red (T.inl v)))) (≈-[] s m v)
    ; (T.inr v) (inr≈ m) → to (one (val-in (value-red (T.inr v)))) (≈-[] t m v) }
sim (prim≈ {p = p} r s) = ans-in (frame _ λ _ → refl) (λ m → prim≈ m s) (sim r)
  λ { T.lit lit≈ → ans-in (frame {g = C.prim p _} _ λ _ → refl) (prim≈ lit≈) (sim s)
    λ { T.lit lit≈ → to (one refl) (out≈ p _ _) } }
sim (let≈ r s) = ans-in (frame _ λ _ → refl) (λ m → let≈ m s) (sim r)
  λ v m → to (one (val-in (value-red v))) (≈-[] s m v)
sim (fold≈ r) = ans-in (frame _ λ _ → refl) fold≈ (sim r) λ v m → val ε (T.fold v) (fold≈ m)
sim (unfold≈ r) = ans-in (frame _ λ _ → refl) unfold≈ (sim r)
  λ { (T.fold v) (fold≈ m) → to (one (val-in (value-red (T.fold v)))) m }
sims [] = val ε [] []
sims (r ∷ rs) = ans-∷ T.reds (λ _ _ → refl) value-red rs (sim r) (sims rs)

{- The end theorem -------------------------------------------------------------}

enclose-correct : ∀ {A} (M : Tm [] A) → Equivalent (S.sem M) (T.sem (enclose M))
enclose-correct M = red-equivalent value-red _≈_ sim (λ m _ → obs≈ m) (enc M)

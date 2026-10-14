{-

  Correctness of typed enclose (ISWIMᵀ → Clos2ᵀ) by a forward simulation
  between their reduction semantics, in lock step.

  The relation on terms (_≈_) is a congruence, closed under substitution
  (≈-trav, for both kits), except for functions. Substitution goes into
  an ISWIMᵀ function, but not into the code of a Clos2ᵀ closure, only
  into the terms it captures. So a function lam (sub (exts σ) N) is
  related to a closure of code N' related to N that captures terms Fs
  related to σ. Applying them substitutes related values in N and N'
  (exts-[]). A closure captures variables or values (VV), so in a closed
  term it captures values and is a value.

-}

module proof.Correctness.Typed.Reduction.EncloseRed where

open import Language.Typed.Type renaming (_≟_ to _≟F_)
open import Language.Typed.ISWIM
import Language.Typed.Clos2 as C
open import Compiler.Typed.Enclose using (enclose; encs)
open import Semantics.Observation
open import proof.Framework.Reduction Obs o-error
open import proof.Framework.ReductionVec Obs o-error using (ans-∷; all-lookup)
open import Semantics.Reduction.Smallstep using (Equivalent)
import proof.Semantics.Reduction.Typed.ISWIM as S
import proof.Semantics.Reduction.Typed.Clos2 as T
open T using (Value; value-red)
import Language.Prim as P

open import Data.Bool using (true; false)
open import Data.Fin using (Fin; zero; suc)
import Data.Integer as Z
open import Data.List using (_∷_)
open import Data.Nat using (ℕ; suc)
open import Data.Vec using (Vec; []; _∷_; lookup; tabulate)
open import Data.Vec.Properties using (lookup∘tabulate)
open import Data.Vec.Relation.Unary.All using (All; []; _∷_)
import Data.Vec.Relation.Unary.All as All
open import Data.Vec.Relation.Binary.Pointwise.Inductive using (Pointwise; []; _∷_)
import Data.Vec.Relation.Binary.Pointwise.Inductive as PW
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary using (Dec; yes; no; does)

{- The relation --------------------------------------------------------------}

{- what a closure captures: a variable or a value -}
data VV {k} : C.Tm k Any → Set where
  var : ∀ x → VV (C.` x)
  val : ∀ {V} → Value V → VV V

infix 4 _≈_
data _≈_ : ∀ {k A} → Tm k A → C.Tm k A → Set where
  var≈ : ∀ {k} {x : Fin k} → ` x ≈ C.` x
  lam≈ : ∀ {k j N N'} {σ : Fin j → Tm k Any} {Fs} → N ≈ N' → (∀ i → σ i ≈ lookup Fs i) → All VV Fs
    → lam (S.sub (S.exts S.tmK σ) N) ≈ C.clos N' Fs
  app≈ : ∀ {k} {L : Tm k _} {L' M M'} → L ≈ L' → M ≈ M' → app L M ≈ C.app L' M'
  lit≈ : ∀ {k B c} → lit {k} B c ≈ C.lit B c
  tuple≈ : ∀ {k n} {Ms : Vec (Tm k Any) n} {Ms'} → Pointwise _≈_ Ms Ms' → tuple Ms ≈ C.tuple Ms'
  get≈ : ∀ {k n i} {M : Tm k ⟪ tup n ⟫} {M'} → M ≈ M' → get i M ≈ C.get i M'
  inl≈ : ∀ {k} {M : Tm k Any} {M'} → M ≈ M' → inl M ≈ C.inl M'
  inr≈ : ∀ {k} {M : Tm k Any} {M'} → M ≈ M' → inr M ≈ C.inr M'
  case≈ : ∀ {k} {L : Tm k _} {L' M M' N N'} → L ≈ L' → M ≈ M' → N ≈ N' → case L M N ≈ C.case L' M' N'
  prim≈ : ∀ {k p} {L : Tm k _} {L' M M'} → L ≈ L' → M ≈ M' → prim p L M ≈ C.prim p L' M'
  let≈ : ∀ {k} {M : Tm k _} {M' N N'} → M ≈ M' → N ≈ N' → let′ M N ≈ C.let′ M' N'
  inject≈ : ∀ {k G} {M : Tm k ⟪ G ⟫} {M'} → M ≈ M' → inject G M ≈ C.inject G M'
  project≈ : ∀ {k t} {M : Tm k Any} {M'} → M ≈ M' → project t M ≈ C.project t M'

{- The fundamental lemma -------------------------------------------------------}

vv-tab : ∀ {k n} (g : Fin n → Fin k) → All VV (tabulate (λ i → C.` g i))
vv-tab {n = 0} g = []
vv-tab {n = suc n} g = var _ ∷ vv-tab (λ i → g (suc i))

enc : ∀ {k A} (M : Tm k A) → M ≈ enclose M
encs≈ : ∀ {k n} (Ms : Vec (Tm k Any) n) → Pointwise _≈_ Ms (encs Ms)
enc (` x) = var≈
enc (lam N) = subst (λ X → lam X ≈ C.clos (enclose N) (tabulate C.`_)) (S.sub-id (λ { zero → refl ; (suc x) → refl }) N)
  (lam≈ {σ = `_} (enc N) (λ i → subst (` i ≈_) (sym (lookup∘tabulate C.`_ i)) var≈) (vv-tab (λ i → i)))
enc (app L M) = app≈ (enc L) (enc M)
enc (lit B c) = lit≈
enc (tuple Ms) = tuple≈ (encs≈ Ms)
enc (get i M) = get≈ (enc M)
enc (inl M) = inl≈ (enc M)
enc (inr M) = inr≈ (enc M)
enc (case L M N) = case≈ (enc L) (enc M) (enc N)
enc (prim p L M) = prim≈ (enc L) (enc M)
enc (let′ M N) = let≈ (enc M) (enc N)
enc (inject G M) = inject≈ (enc M)
enc (project t M) = project≈ (enc M)
encs≈ [] = []
encs≈ (M ∷ Ms) = enc M ∷ encs≈ Ms

{- Closure under substitution ----------------------------------------------------}

{- a kit of each language, which agree -}
record KR (𝒦₁ : S.Kit) (𝒦₂ : T.Kit) : Set where
  module K₁ = S.Kit 𝒦₁
  module K₂ = T.Kit 𝒦₂
  field
    laws : S.Laws 𝒦₁
    rel-vr : ∀ {k} (x : Fin k) → K₁.tm (K₁.vr x) ≈ K₂.tm (K₂.vr x)
    rel-wk : ∀ {k a b} → K₁.tm {k} a ≈ K₂.tm b → K₁.tm (K₁.wk a) ≈ K₂.tm (K₂.wk b)
    vv-vr : ∀ {k} (x : Fin k) → VV (K₂.tm (K₂.vr x))
    vv-wk : ∀ {k b} → VV (K₂.tm {k} b) → VV (K₂.tm (K₂.wk b))

module Trav {𝒦₁ 𝒦₂} (K : KR 𝒦₁ 𝒦₂) where
  open KR K
  open S.Laws laws

  ≈-trav : ∀ {k j A} {σ : S.Sub 𝒦₁ k j} {τ : T.Sub 𝒦₂ k j} {M : Tm k A} {M'} → M ≈ M'
    → (∀ x → K₁.tm (σ x) ≈ K₂.tm (τ x)) → (∀ x → VV (K₂.tm (τ x))) → S.trav 𝒦₁ σ M ≈ T.trav 𝒦₂ τ M'
  ≈-travs : ∀ {k j n} {σ : S.Sub 𝒦₁ k j} {τ : T.Sub 𝒦₂ k j} {Ms : Vec (Tm k Any) n} {Ms' : Vec (C.Tm k Any) n} → Pointwise _≈_ Ms Ms'
    → (∀ x → K₁.tm (σ x) ≈ K₂.tm (τ x)) → (∀ x → VV (K₂.tm (τ x))) → Pointwise _≈_ (S.travs 𝒦₁ σ Ms) (T.travs 𝒦₂ τ Ms')
  vvs-trav : ∀ {k j n} {τ : T.Sub 𝒦₂ k j} {Fs : Vec (C.Tm k Any) n} → All VV Fs → (∀ x → VV (K₂.tm (τ x)))
    → All VV (T.travs 𝒦₂ τ Fs)
  ok-exts : ∀ {k j} {σ : S.Sub 𝒦₁ k j} {τ : T.Sub 𝒦₂ k j} → (∀ x → K₁.tm (σ x) ≈ K₂.tm (τ x))
    → ∀ x → K₁.tm (S.exts 𝒦₁ σ x) ≈ K₂.tm (T.exts 𝒦₂ τ x)
  ok-exts h zero = rel-vr zero
  ok-exts h (suc x) = rel-wk (h x)
  vv-exts : ∀ {k j} {τ : T.Sub 𝒦₂ k j} → (∀ x → VV (K₂.tm (τ x))) → ∀ x → VV (K₂.tm (T.exts 𝒦₂ τ x))
  vv-exts h zero = vv-vr zero
  vv-exts h (suc x) = vv-wk (h x)

  ≈-trav var≈ ok vk = ok _
  ≈-trav {σ = σ} {τ} (lam≈ {N = N} {σ = ρ} {Fs} n h vv) ok vk =
    subst (λ X → lam X ≈ C.clos _ (T.travs 𝒦₂ τ Fs))
          (sym (S.trav-sub laws (λ { zero → tm-vr zero ; (suc y) → exts-ren σ (ρ y) }) N))
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
  ≈-trav (inject≈ r) ok vk = inject≈ (≈-trav r ok vk)
  ≈-trav (project≈ r) ok vk = project≈ (≈-trav r ok vk)
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
≈-[] : ∀ {A} {N : Tm 1 A} {N' V V'} → N ≈ N' → V ≈ V' → Value V' → (N S.[ V ]) ≈ (N' T.[ V' ])
≈-[] n m v = Trav.≈-trav tmKR n (λ _ → m) (λ _ → val v)

{- The simulation ------------------------------------------------------------------}

Ans′ : ∀ {A} → Tm 0 A → Red (Tm 0 A) → C.Tm 0 A → Set
Ans′ = Ans T.red Value _≈_

vvs-values : ∀ {n} {Fs : Vec (C.Tm 0 Any) n} → All VV Fs → All Value Fs
vvs-values [] = []
vvs-values (var () ∷ vv)
vvs-values (val v ∷ vv) = v ∷ vvs-values vv

obs≈ : ∀ {A} {V : Tm 0 A} {V'} → V ≈ V' → S.obs V ≡ T.obs V'
obss≈ : ∀ {n} {Vs : Vec (Tm 0 Any) n} {Vs'} → Pointwise _≈_ Vs Vs' → S.obss Vs ≡ T.obss Vs'
obs≈ (lam≈ _ _ _) = refl
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

out≈ : ∀ p n m → S.out {0} p n m ≈ T.out p n m
out≈ P.sub n m = lit≈
out≈ P.eq n m with does (n Z.≟ m)
... | true = inl≈ (inject≈ (tuple≈ []))
... | false = inr≈ (inject≈ (tuple≈ []))

sim : ∀ {A} {M : Tm 0 A} {M'} → M ≈ M' → Ans′ M (S.red M) M'
sims : ∀ {n} {Ms : Vec (Tm 0 Any) n} {Ms'} → Pointwise _≈_ Ms Ms' → Ans T.reds (All Value) (Pointwise _≈_) Ms (S.reds Ms) Ms'
sim (var≈ {x = ()})
sim m@(lam≈ _ _ vv) = val ε (T.clos (vvs-values vv)) m
sim (app≈ r s) =
  ans-in (frame _ λ _ → refl) (λ m → app≈ m s) (sim r)
    λ v m → ans-in (frame {g = C.app _} _ λ _ → val-in (value-red v)) (app≈ m) (sim s) λ w m' → β-sim v m w m'
  where
  β-sim : ∀ {V V' W W'} → Value V' → V ≈ V' → Value W' → W ≈ W' → Ans′ (app V W) (S.β V W) (C.app V' W')
  β-sim (T.clos vs) (lam≈ {N = N} {σ = σ} n h vv) w m' =
    to (one (trans (val-in (value-red (T.clos vs))) (val-in (value-red w))))
       (subst (_≈ _) (sym (S.exts-[] σ _ N))
              (Trav.≈-trav tmKR n (λ { zero → m' ; (suc i) → h i }) (λ { zero → val w ; (suc i) → all-lookup vv i })))
sim lit≈ = val ε T.lit lit≈
sim (tuple≈ rs) = ans-in (frame _ λ _ → refl) tuple≈ (sims rs) λ vs ms → val ε (T.tuple vs) (tuple≈ ms)
sim (get≈ {i = i} r) = ans-in (frame _ λ _ → refl) get≈ (sim r)
  λ { (T.tuple vs) (tuple≈ ms) → to (one (val-in (value-red (T.tuple vs)))) (PW.lookup ms i) }
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
sim (inject≈ r) = ans-in (frame _ λ _ → refl) inject≈ (sim r) λ v m → val ε (T.inject v) (inject≈ m)
sim (project≈ {t = t} r) = ans-in (frame _ λ _ → refl) project≈ (sim r) λ { (T.inject v) (inject≈ m) → proj-sim v m }
  where
  proj-sim : ∀ {G V V'} → Value V' → V ≈ V' → Ans′ (project t (inject G V)) (S.project? t (inject G V)) (C.project t (C.inject G V'))
  proj-sim {G} {V} {V'} v m = pd (G ≟F flat t) (val-in (value-red (T.inject v)))
    where pd : ∀ {H} (d : Dec (G ≡ H)) {X Y} → T.red X ≡ T.proj-dec d V' → Ans′ Y (S.proj-dec d V) X
          pd (yes refl) e = to (one e) m
          pd (no _) e = error ε e
sims [] = val ε [] []
sims (r ∷ rs) = ans-∷ T.reds (λ _ _ → refl) value-red rs (sim r) (sims rs)

{- The end theorem -------------------------------------------------------------}

enclose-correct : ∀ (M : Tm 0 Any) → Equivalent (S.sem M) (T.sem (enclose M))
enclose-correct M = red-equivalent value-red _≈_ sim (λ m _ _ → obs≈ m) (enc M)

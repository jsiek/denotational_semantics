{-

  Correctness of typed split (Clos3ᵀ → Clos4ᵀ) by a forward simulation
  between their reduction semantics, in lock step.

  The relation on terms (_⊢_≈_) relates a variable x to ρ x, for the
  renaming ρ of the pass; it is a congruence, closed under substitution
  (≈-trav), that relates a closure to the pack of its code and the tuple
  of its free variables, and an application to a callc. Applying related
  closures substitutes related values in related code.

-}

module proof.Correctness.Reduction.SplitRed where

open import Language.Typed.Type renaming (_≟_ to _≟F_)
open import Language.Typed.Clos3
import Language.Typed.Clos4 as C
open import Compiler.Split
open import Semantics.Observation
open import proof.Framework.Reduction Obs o-error
open import proof.Framework.ReductionVec Obs o-error using (ans-∷)
open import Semantics.Reduction.Smallstep using (Equivalent)
import proof.Semantics.Reduction.Typed.Clos3 as S
import proof.Semantics.Reduction.Typed.Clos4 as T
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

infix 4 _⊢_≈_
data _⊢_≈_ : ∀ {Γ Δ A} → Ren Γ Δ → Tm Γ A → C.Tm Δ A → Set where
  var≈ : ∀ {Γ Δ A} {ρ : Ren Γ Δ} {x : Γ ∋ A} {y} → ρ x ≡ y → ρ ⊢ ` x ≈ C.` y
  clos≈ : ∀ {Γ Δ n} {ρ : Ren Γ Δ} {N N' Ms} {Ms' : Vec _ n} → (λ x → x) ⊢ N ≈ N' → Pointwise (ρ ⊢_≈_) Ms Ms'
    → ρ ⊢ clos N Ms ≈ C.pack (C.code N') (C.tuple Ms')
  app≈ : ∀ {Γ Δ} {ρ : Ren Γ Δ} {L L' M M'} → ρ ⊢ L ≈ L' → ρ ⊢ M ≈ M' → ρ ⊢ app L M ≈ C.callc L' M'
  lit≈ : ∀ {Γ Δ} {ρ : Ren Γ Δ} {B c} → ρ ⊢ lit B c ≈ C.lit B c
  tuple≈ : ∀ {Γ Δ n} {ρ : Ren Γ Δ} {Ms : Vec _ n} {Ms'} → Pointwise (ρ ⊢_≈_) Ms Ms' → ρ ⊢ tuple Ms ≈ C.tuple Ms'
  get≈ : ∀ {Γ Δ n i} {ρ : Ren Γ Δ} {M : Tm Γ ⟪ tup n ⟫} {M'} → ρ ⊢ M ≈ M' → ρ ⊢ get i M ≈ C.get i M'
  inl≈ : ∀ {Γ Δ} {ρ : Ren Γ Δ} {M M'} → ρ ⊢ M ≈ M' → ρ ⊢ inl M ≈ C.inl M'
  inr≈ : ∀ {Γ Δ} {ρ : Ren Γ Δ} {M M'} → ρ ⊢ M ≈ M' → ρ ⊢ inr M ≈ C.inr M'
  case≈ : ∀ {Γ Δ} {ρ : Ren Γ Δ} {L L' M M' N N'} → ρ ⊢ L ≈ L' → ext ρ ⊢ M ≈ M' → ext ρ ⊢ N ≈ N'
    → ρ ⊢ case L M N ≈ C.case L' M' N'
  prim≈ : ∀ {Γ Δ p} {ρ : Ren Γ Δ} {L L' M M'} → ρ ⊢ L ≈ L' → ρ ⊢ M ≈ M' → ρ ⊢ prim p L M ≈ C.prim p L' M'
  let≈ : ∀ {Γ Δ} {ρ : Ren Γ Δ} {M M' N N'} → ρ ⊢ M ≈ M' → ext ρ ⊢ N ≈ N' → ρ ⊢ let′ M N ≈ C.let′ M' N'
  inject≈ : ∀ {Γ Δ G} {ρ : Ren Γ Δ} {M : Tm Γ ⟪ G ⟫} {M'} → ρ ⊢ M ≈ M' → ρ ⊢ inject G M ≈ C.inject G M'
  project≈ : ∀ {Γ Δ t} {ρ : Ren Γ Δ} {M M'} → ρ ⊢ M ≈ M' → ρ ⊢ project t M ≈ C.project t M'

{- The fundamental lemma ------------------------------------------------------------------}

split≈ : ∀ {Γ Δ A} (ρ : Ren Γ Δ) (M : Tm Γ A) → ρ ⊢ M ≈ split ρ M
splits≈ : ∀ {Γ Δ n} (ρ : Ren Γ Δ) (Ms : Vec (Tm Γ Any) n) → Pointwise (ρ ⊢_≈_) Ms (splits ρ Ms)
split≈ ρ (` x) = var≈ refl
split≈ ρ (clos N Ms) = clos≈ (split≈ (λ x → x) N) (splits≈ ρ Ms)
split≈ ρ (app L M) = app≈ (split≈ ρ L) (split≈ ρ M)
split≈ ρ (lit B c) = lit≈
split≈ ρ (tuple Ms) = tuple≈ (splits≈ ρ Ms)
split≈ ρ (get i M) = get≈ (split≈ ρ M)
split≈ ρ (inl M) = inl≈ (split≈ ρ M)
split≈ ρ (inr M) = inr≈ (split≈ ρ M)
split≈ ρ (case L M N) = case≈ (split≈ ρ L) (split≈ (ext ρ) M) (split≈ (ext ρ) N)
split≈ ρ (prim p L M) = prim≈ (split≈ ρ L) (split≈ ρ M)
split≈ ρ (let′ M N) = let≈ (split≈ ρ M) (split≈ (ext ρ) N)
split≈ ρ (inject G M) = inject≈ (split≈ ρ M)
split≈ ρ (project t M) = project≈ (split≈ ρ M)
splits≈ ρ [] = []
splits≈ ρ (M ∷ Ms) = split≈ ρ M ∷ splits≈ ρ Ms

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
  ≈-travs : ∀ {Γ Δ Γ₂ Δ₂ n} {ρ : Ren Γ Δ} {ρ₂ : Ren Γ₂ Δ₂} {σ : S.Sub 𝒦₁ Γ Γ₂} {τ : T.Sub 𝒦₂ Δ Δ₂}
    {Ms : Vec (Tm Γ Any) n} {Ms' : Vec (C.Tm Δ Any) n}
    → Pointwise (ρ ⊢_≈_) Ms Ms' → OK 𝒦₁ 𝒦₂ ρ ρ₂ σ τ → Pointwise (ρ₂ ⊢_≈_) (S.travs 𝒦₁ σ Ms) (T.travs 𝒦₂ τ Ms')
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
  ≈-trav (inject≈ r) ok = inject≈ (≈-trav r ok)
  ≈-trav (project≈ r) ok = project≈ (≈-trav r ok)
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

  obs≈ : ∀ {A} {V V'} → R {A} V V' → S.obs V ≡ T.obs V'
  obss≈ : ∀ {n} {Vs : Vec _ n} {Vs'} → Pointwise R Vs Vs' → S.obss Vs ≡ T.obss Vs'
  obs≈ (var≈ {x = ()} _)
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

  ≈-[] : ∀ {A} {N : Tm (Any ∷ []) A} {N' V V'} → ext ρ₀ ⊢ N ≈ N' → R V V' → R (N S.[ V ]) (N' T.[ V' ])
  ≈-[] n m = Trav.≈-trav tmKR n λ { Z → m ; (S ()) }

  sim : ∀ {A} {M M'} → R {A} M M' → Ans′ M (S.red M) M'
  sims : ∀ {n} {Ms : Vec _ n} {Ms'} → Pointwise R Ms Ms' → Ans T.reds (All Value) (Pointwise R) Ms (S.reds Ms) Ms'
  sim (var≈ {x = ()} _)
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
split-correct M = red-equivalent value-red R sim (λ m _ _ → obs≈ m) (split≈ _ M)

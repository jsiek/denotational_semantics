{-

  Correctness of typed concretize (Clos2ᵀ → Clos3ᵀ) by a forward
  simulation between their reduction semantics.

  The relation on terms (_⊢_≈_) relates a variable x to where it lives,
  φ x (a variable, or a component of a tuple in a variable); it is a
  congruence, closed under substitution (≈-trav), for closures too,
  since in both languages substitution enters only a closure's free
  variables. Applying related closures substitutes, for the free
  variables of the target's code, the tuple of their values: a free
  variable of the code is then get i of that tuple, related to the
  value of the source's free variable (get≈), and the target reaches
  that value in one step, where the source has it already.

-}

module proof.Correctness.Typed.Reduction.ConcretizeRed where

open import Language.Typed.Type renaming (_≟_ to _≟F_)
open import Language.Typed.Clos2
import Language.Typed.Clos3 as C
open import Compiler.Typed.Concretize
open import Semantics.Observation
open import proof.Framework.Reduction Obs o-error
open import proof.Framework.ReductionVec Obs o-error using (ans-∷; all-lookup)
open import Semantics.Reduction.Smallstep using (Equivalent)
import proof.Semantics.Reduction.Typed.Clos2 as S
import proof.Semantics.Reduction.Typed.Clos3 as T
open T using (Value; value-red)
import Language.Prim as P

open import Data.Bool using (true; false)
open import Data.Fin using (Fin; zero; suc)
import Data.Integer as Z
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; suc)
open import Data.Vec using (Vec; []; _∷_; lookup)
open import Data.Vec.Relation.Unary.All using (All; []; _∷_)
open import Data.Vec.Relation.Binary.Pointwise.Inductive using (Pointwise; []; _∷_)
import Data.Vec.Relation.Binary.Pointwise.Inductive as PW
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary using (Dec; yes; no; does)

{- The relation -------------------------------------------------------------------}

infix 4 _⊢_≈_
data _⊢_≈_ : ∀ {k Γ A} → (Fin k → Ref Γ) → Tm k A → C.Tm Γ A → Set where
  var≈ : ∀ {k Γ} {φ : Fin k → Ref Γ} {x} → φ ⊢ ` x ≈ ref-tm (φ x)
  get≈ : ∀ {k Γ n} {φ : Fin k → Ref Γ} {V Vs'} {i : Fin n} → S.Value V → φ ⊢ V ≈ lookup Vs' i → All Value Vs'
    → φ ⊢ V ≈ C.get i (C.tuple Vs')
  clos≈ : ∀ {k Γ n} {φ : Fin k → Ref Γ} {N N' Ms} {Ms' : Vec _ n} → fv-ref ⊢ N ≈ N' → Pointwise (φ ⊢_≈_) Ms Ms'
    → φ ⊢ clos N Ms ≈ C.clos N' Ms'
  app≈ : ∀ {k Γ} {φ : Fin k → Ref Γ} {L L' M M'} → φ ⊢ L ≈ L' → φ ⊢ M ≈ M' → φ ⊢ app L M ≈ C.app L' M'
  lit≈ : ∀ {k Γ} {φ : Fin k → Ref Γ} {B c} → φ ⊢ lit B c ≈ C.lit B c
  tuple≈ : ∀ {k Γ n} {φ : Fin k → Ref Γ} {Ms : Vec _ n} {Ms'} → Pointwise (φ ⊢_≈_) Ms Ms' → φ ⊢ tuple Ms ≈ C.tuple Ms'
  getᵢ≈ : ∀ {k Γ n i} {φ : Fin k → Ref Γ} {M : Tm k ⟪ tup n ⟫} {M'} → φ ⊢ M ≈ M' → φ ⊢ get i M ≈ C.get i M'
  inl≈ : ∀ {k Γ} {φ : Fin k → Ref Γ} {M M'} → φ ⊢ M ≈ M' → φ ⊢ inl M ≈ C.inl M'
  inr≈ : ∀ {k Γ} {φ : Fin k → Ref Γ} {M M'} → φ ⊢ M ≈ M' → φ ⊢ inr M ≈ C.inr M'
  case≈ : ∀ {k Γ} {φ : Fin k → Ref Γ} {L L' M M' N N'} → φ ⊢ L ≈ L' → ext-ref φ ⊢ M ≈ M' → ext-ref φ ⊢ N ≈ N'
    → φ ⊢ case L M N ≈ C.case L' M' N'
  prim≈ : ∀ {k Γ p} {φ : Fin k → Ref Γ} {L L' M M'} → φ ⊢ L ≈ L' → φ ⊢ M ≈ M' → φ ⊢ prim p L M ≈ C.prim p L' M'
  let≈ : ∀ {k Γ} {φ : Fin k → Ref Γ} {M M' N N'} → φ ⊢ M ≈ M' → ext-ref φ ⊢ N ≈ N' → φ ⊢ let′ M N ≈ C.let′ M' N'
  inject≈ : ∀ {k Γ G} {φ : Fin k → Ref Γ} {M : Tm k ⟪ G ⟫} {M'} → φ ⊢ M ≈ M' → φ ⊢ inject G M ≈ C.inject G M'
  project≈ : ∀ {k Γ t} {φ : Fin k → Ref Γ} {M M'} → φ ⊢ M ≈ M' → φ ⊢ project t M ≈ C.project t M'

{- The fundamental lemma -------------------------------------------------------------}

conc≈ : ∀ {k Γ A} (φ : Fin k → Ref Γ) (M : Tm k A) → φ ⊢ M ≈ concretize φ M
concs≈ : ∀ {k Γ n} (φ : Fin k → Ref Γ) (Ms : Vec (Tm k Any) n) → Pointwise (φ ⊢_≈_) Ms (concs φ Ms)
conc≈ φ (` x) = var≈
conc≈ φ (clos N Ms) = clos≈ (conc≈ fv-ref N) (concs≈ φ Ms)
conc≈ φ (app L M) = app≈ (conc≈ φ L) (conc≈ φ M)
conc≈ φ (lit B c) = lit≈
conc≈ φ (tuple Ms) = tuple≈ (concs≈ φ Ms)
conc≈ φ (get i M) = getᵢ≈ (conc≈ φ M)
conc≈ φ (inl M) = inl≈ (conc≈ φ M)
conc≈ φ (inr M) = inr≈ (conc≈ φ M)
conc≈ φ (case L M N) = case≈ (conc≈ φ L) (conc≈ (ext-ref φ) M) (conc≈ (ext-ref φ) N)
conc≈ φ (prim p L M) = prim≈ (conc≈ φ L) (conc≈ φ M)
conc≈ φ (let′ M N) = let≈ (conc≈ φ M) (conc≈ (ext-ref φ) N)
conc≈ φ (inject G M) = inject≈ (conc≈ φ M)
conc≈ φ (project t M) = project≈ (conc≈ φ M)
concs≈ φ [] = []
concs≈ φ (M ∷ Ms) = conc≈ φ M ∷ concs≈ φ Ms

{- Closure under substitution -----------------------------------------------------------}

OK : ∀ {k Γ j Δ} (𝒦₁ : S.Kit) (𝒦₂ : T.Kit) → (Fin k → Ref Γ) → (Fin j → Ref Δ) → S.Sub 𝒦₁ k j → T.Sub 𝒦₂ Γ Δ → Set
OK 𝒦₁ 𝒦₂ φ φ₂ σ τ = ∀ x → φ₂ ⊢ S.Kit.tm 𝒦₁ (σ x) ≈ T.trav 𝒦₂ τ (ref-tm (φ x))

shift-ren : ∀ {Γ A} (r : Ref Γ) → ref-tm (shift-ref {A = A} r) ≡ T.ren S (ref-tm r)
shift-ren (var x) = refl
shift-ren (prj i x) = refl

record KR (𝒦₁ : S.Kit) (𝒦₂ : T.Kit) : Set where
  field
    rel-vr : ∀ {k Γ} {φ : Fin k → Ref Γ} → ext-ref φ ⊢ S.Kit.tm 𝒦₁ (S.Kit.vr 𝒦₁ zero) ≈ T.Kit.tm 𝒦₂ (T.Kit.vr 𝒦₂ Z)
    shift-trav : ∀ {Γ Δ} {τ : T.Sub 𝒦₂ Γ Δ} (r : Ref Γ)
      → T.trav 𝒦₂ (T.exts 𝒦₂ {B = Any} τ) (ref-tm (shift-ref r)) ≡ T.ren S (T.trav 𝒦₂ τ (ref-tm r))
    rel-wk : ∀ {k Γ} {φ : Fin k → Ref Γ} {a X} → φ ⊢ S.Kit.tm 𝒦₁ a ≈ X → ext-ref φ ⊢ S.Kit.tm 𝒦₁ (S.Kit.wk 𝒦₁ a) ≈ T.ren S X

module Trav {𝒦₁ 𝒦₂} (K : KR 𝒦₁ 𝒦₂) where
  open KR K

  ok-ext : ∀ {k Γ j Δ} {φ : Fin k → Ref Γ} {φ₂ : Fin j → Ref Δ} {σ : S.Sub 𝒦₁ k j} {τ : T.Sub 𝒦₂ Γ Δ} → OK 𝒦₁ 𝒦₂ φ φ₂ σ τ
    → OK 𝒦₁ 𝒦₂ (ext-ref φ) (ext-ref φ₂) (S.exts 𝒦₁ σ) (T.exts 𝒦₂ τ)
  ok-ext ok zero = rel-vr
  ok-ext {φ = φ} ok (suc x) = subst (_ ⊢ _ ≈_) (sym (shift-trav (φ x))) (rel-wk (ok x))

  ≈-trav : ∀ {k Γ j Δ A} {φ : Fin k → Ref Γ} {φ₂ : Fin j → Ref Δ} {σ : S.Sub 𝒦₁ k j} {τ : T.Sub 𝒦₂ Γ Δ} {M : Tm k A} {M'} → φ ⊢ M ≈ M'
    → OK 𝒦₁ 𝒦₂ φ φ₂ σ τ → φ₂ ⊢ S.trav 𝒦₁ σ M ≈ T.trav 𝒦₂ τ M'
  ≈-travs : ∀ {k Γ j Δ n} {φ : Fin k → Ref Γ} {φ₂ : Fin j → Ref Δ} {σ : S.Sub 𝒦₁ k j} {τ : T.Sub 𝒦₂ Γ Δ} {Ms : Vec (Tm k Any) n} {Ms' : Vec (C.Tm Γ Any) n}
    → Pointwise (φ ⊢_≈_) Ms Ms' → OK 𝒦₁ 𝒦₂ φ φ₂ σ τ → Pointwise (φ₂ ⊢_≈_) (S.travs 𝒦₁ σ Ms) (T.travs 𝒦₂ τ Ms')
  ≈-trav var≈ ok = ok _
  ≈-trav {τ = τ} (get≈ {Vs' = Vs'} {i} v r vs) ok =
    get≈ (S.value-trav v) (subst (_ ⊢ _ ≈_) (sym (T.lookup-travs τ Vs' i)) (≈-trav r ok)) (T.values-trav vs)
  ≈-trav (clos≈ n rs) ok = clos≈ n (≈-travs rs ok)
  ≈-trav (app≈ r s) ok = app≈ (≈-trav r ok) (≈-trav s ok)
  ≈-trav lit≈ ok = lit≈
  ≈-trav (tuple≈ rs) ok = tuple≈ (≈-travs rs ok)
  ≈-trav (getᵢ≈ r) ok = getᵢ≈ (≈-trav r ok)
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
varKR = record { rel-vr = var≈ ; shift-trav = λ { (var x) → refl ; (prj i x) → refl }
               ; rel-wk = λ { {φ = φ} {a} var≈ → subst (_ ⊢ _ ≈_) (shift-ren (φ a)) var≈ ; (get≈ () _ _) } }

tmKR : KR S.tmK T.tmK
tmKR = record { rel-vr = var≈ ; shift-trav = λ { (var x) → refl ; (prj i x) → refl }
              ; rel-wk = λ r → Trav.≈-trav varKR r λ x → subst (_ ⊢ _ ≈_) (shift-ren _) var≈ }

{- The simulation --------------------------------------------------------------------------}

module _ {φ₀ : Fin 0 → Ref []} where

 R : ∀ {A} → Tm 0 A → C.Tm [] A → Set
 R = φ₀ ⊢_≈_

 Ans′ : ∀ {A} → Tm 0 A → Red (Tm 0 A) → C.Tm [] A → Set
 Ans′ = Ans T.red Value R

 {- the source of a value is a value -}
 ≈-value : ∀ {A} {V V'} → R {A} V V' → Value V' → S.Value V
 ≈-values : ∀ {n} {Vs : Vec _ n} {Vs'} → Pointwise R Vs Vs' → All Value Vs' → All S.Value Vs
 ≈-value (clos≈ n rs) (T.clos vs) = S.clos (≈-values rs vs)
 ≈-value lit≈ T.lit = S.lit
 ≈-value (tuple≈ rs) (T.tuple vs) = S.tuple (≈-values rs vs)
 ≈-value (inl≈ r) (T.inl v) = S.inl (≈-value r v)
 ≈-value (inr≈ r) (T.inr v) = S.inr (≈-value r v)
 ≈-value (inject≈ r) (T.inject v) = S.inject (≈-value r v)
 ≈-values [] [] = []
 ≈-values (r ∷ rs) (v ∷ vs) = ≈-value r v ∷ ≈-values rs vs

 obs≈ : ∀ {A} {V V'} → R {A} V V' → Value V' → S.obs V ≡ T.obs V'
 obss≈ : ∀ {n} {Vs : Vec _ n} {Vs'} → Pointwise R Vs Vs' → All Value Vs' → S.obss Vs ≡ T.obss Vs'
 obs≈ (clos≈ _ _) _ = refl
 obs≈ lit≈ _ = refl
 obs≈ (tuple≈ rs) (T.tuple vs) = cong o-tuple (obss≈ rs vs)
 obs≈ (inl≈ r) (T.inl v) = cong o-inl (obs≈ r v)
 obs≈ (inr≈ r) (T.inr v) = cong o-inr (obs≈ r v)
 obs≈ (inject≈ r) (T.inject v) = obs≈ r v
 obss≈ [] [] = refl
 obss≈ (r ∷ rs) (v ∷ vs) = cong₂ _∷_ (obs≈ r v) (obss≈ rs vs)

 out≈ : ∀ p n m → R (S.out p n m) (T.out p n m)
 out≈ P.sub n m = lit≈
 out≈ P.eq n m with does (n Z.≟ m)
 ... | true = inl≈ (inject≈ (tuple≈ []))
 ... | false = inr≈ (inject≈ (tuple≈ []))

 ≈-[] : ∀ {A} {N : Tm 1 A} {N' V V'} → ext-ref φ₀ ⊢ N ≈ N' → R V V' → R (N S.[ V ]) (N' T.[ V' ])
 ≈-[] n m = Trav.≈-trav tmKR n λ { zero → m }

 sim : ∀ {A} {M M'} → R {A} M M' → Ans′ M (S.red M) M'
 sims : ∀ {n} {Ms : Vec _ n} {Ms'} → Pointwise R Ms Ms' → Ans T.reds (All Value) (Pointwise R) Ms (S.reds Ms) Ms'
 sim (var≈ {x = ()})
 sim (get≈ {V = V} {Vs'} {i} v r vs) =
   subst (λ x → Ans′ V x (C.get i (C.tuple Vs'))) (sym (S.value-red v))
         (val (val-in (T.value-red (T.tuple vs)) ◅ ε) (all-lookup vs i) r)
 sim (clos≈ n rs) = ans-in (frame _ λ _ → refl) (clos≈ n) (sims rs) λ vs ms → val ε (T.clos vs) (clos≈ n ms)
 sim (app≈ r s) =
   ans-in (frame _ λ _ → refl) (λ m → app≈ m s) (sim r)
     λ v m → ans-in (frame {g = C.app _} _ λ _ → val-in (value-red v)) (app≈ m) (sim s) λ w m' → β-sim v m w m'
   where
   β-sim : ∀ {V V' W W'} → Value V' → R V V' → Value W' → R W W' → Ans′ (app V W) (S.β V W) (C.app V' W')
   β-sim (T.clos vs) (clos≈ n ms) w m' =
     to (one (trans (val-in (value-red (T.clos vs))) (val-in (value-red w))))
        (Trav.≈-trav tmKR n λ { zero → m' ; (suc i) → get≈ (all-lookup (≈-values ms vs) i) (PW.lookup ms i) vs })
 sim lit≈ = val ε T.lit lit≈
 sim (tuple≈ rs) = ans-in (frame _ λ _ → refl) tuple≈ (sims rs) λ vs ms → val ε (T.tuple vs) (tuple≈ ms)
 sim (getᵢ≈ {i = i} r) = ans-in (frame _ λ _ → refl) getᵢ≈ (sim r)
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

concretize-correct : ∀ (M : Tm 0 Any) → Equivalent (S.sem M) (T.sem (concretize-program M))
concretize-correct M = red-equivalent value-red R sim (λ m _ v → obs≈ m v) (conc≈ _ M)

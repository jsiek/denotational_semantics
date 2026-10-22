{-

  Correctness of concretize (Clos2μ → Clos3μ) by a forward simulation
  between their reduction semantics, as for typed concretize
  (proof/Correctness/Reduction/ConcretizeRed.agda).

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

module Mu.proof.Correctness.Reduction.ConcretizeRed where

open import Mu.Language.Type hiding (_[_])
open import Mu.Language.Clos2
import Mu.Language.Clos3 as C
open import Mu.Compiler.Concretize
open import Mu.Framework.AllUtil using (All; []; _∷_; lookup; All₂; lookup₂)
open import Semantics.Observation
open import proof.Framework.Reduction Obs o-error hiding (Each; []; _∷_)
open import Mu.proof.Framework.ReductionAll Obs o-error using (ans-∷; Each; []; _∷_; each-lookup)
open import Semantics.Reduction.Smallstep using (Equivalent)
import Mu.proof.Semantics.Reduction.Clos2 as S
import Mu.proof.Semantics.Reduction.Clos3 as T
open T using (Value; value-red)
import Language.Prim as P

open import Data.Bool using (true; false)
import Data.Integer as Z
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary using (does)

{- The relation -------------------------------------------------------------------}

infix 4 _⊢_≈_
data _⊢_≈_ : ∀ {Γ Γ' A} → Refs Γ Γ' → Tm Γ A → C.Tm Γ' A → Set where
  var≈ : ∀ {Γ Γ' A} {φ : Refs Γ Γ'} {x : Γ ∋ A} {M'} → ref-tm (φ x) ≡ M' → φ ⊢ ` x ≈ M'
  get≈ : ∀ {Γ Γ' Δ A} {φ : Refs Γ Γ'} {V : Tm Γ A} {Vs' : All (C.Tm Γ') Δ} {i : Δ ∋ A} → S.Value V → φ ⊢ V ≈ lookup Vs' i
    → Each Value Vs' → φ ⊢ V ≈ C.get i (C.tuple Vs')
  clos≈ : ∀ {Γ Γ' Δ A B} {φ : Refs Γ Γ'} {N : Tm (A ∷ Δ) B} {N' Ms Ms'} → fv-ref ⊢ N ≈ N' → All₂ (φ ⊢_≈_) Ms Ms'
    → φ ⊢ clos N Ms ≈ C.clos N' Ms'
  app≈ : ∀ {Γ Γ' A B} {φ : Refs Γ Γ'} {L : Tm Γ (A ⇒ B)} {L' M M'} → φ ⊢ L ≈ L' → φ ⊢ M ≈ M' → φ ⊢ app L M ≈ C.app L' M'
  lit≈ : ∀ {Γ Γ'} {φ : Refs Γ Γ'} {B c} → φ ⊢ lit B c ≈ C.lit B c
  tuple≈ : ∀ {Γ Γ' Δ} {φ : Refs Γ Γ'} {Ms : All (Tm Γ) Δ} {Ms'} → All₂ (φ ⊢_≈_) Ms Ms' → φ ⊢ tuple Ms ≈ C.tuple Ms'
  getᵢ≈ : ∀ {Γ Γ' Δ A} {i : Δ ∋ A} {φ : Refs Γ Γ'} {M : Tm Γ (tup Δ)} {M'} → φ ⊢ M ≈ M' → φ ⊢ get i M ≈ C.get i M'
  inl≈ : ∀ {Γ Γ' A B} {φ : Refs Γ Γ'} {M : Tm Γ A} {M'} → φ ⊢ M ≈ M' → φ ⊢ inl {B = B} M ≈ C.inl M'
  inr≈ : ∀ {Γ Γ' A B} {φ : Refs Γ Γ'} {M : Tm Γ B} {M'} → φ ⊢ M ≈ M' → φ ⊢ inr {A = A} M ≈ C.inr M'
  case≈ : ∀ {Γ Γ' A B C} {φ : Refs Γ Γ'} {L : Tm Γ (A ⊹ B)} {L'} {M : Tm (A ∷ Γ) C} {M' N N'} → φ ⊢ L ≈ L'
    → ext-ref φ ⊢ M ≈ M' → ext-ref φ ⊢ N ≈ N' → φ ⊢ case L M N ≈ C.case L' M' N'
  prim≈ : ∀ {Γ Γ' p} {φ : Refs Γ Γ'} {L L' M M'} → φ ⊢ L ≈ L' → φ ⊢ M ≈ M' → φ ⊢ prim p L M ≈ C.prim p L' M'
  let≈ : ∀ {Γ Γ' A B} {φ : Refs Γ Γ'} {M : Tm Γ A} {M'} {N : Tm (A ∷ Γ) B} {N'} → φ ⊢ M ≈ M' → ext-ref φ ⊢ N ≈ N'
    → φ ⊢ let′ M N ≈ C.let′ M' N'
  fold≈ : ∀ {Γ Γ' A} {φ : Refs Γ Γ'} {M : Tm Γ (unroll A)} {M'} → φ ⊢ M ≈ M' → φ ⊢ fold {A = A} M ≈ C.fold M'
  unfold≈ : ∀ {Γ Γ' A} {φ : Refs Γ Γ'} {M : Tm Γ (μ A)} {M'} → φ ⊢ M ≈ M' → φ ⊢ unfold M ≈ C.unfold M'

{- The fundamental lemma -------------------------------------------------------------}

conc≈ : ∀ {Γ Γ' A} (φ : Refs Γ Γ') (M : Tm Γ A) → φ ⊢ M ≈ concretize φ M
concs≈ : ∀ {Γ Γ' Δ} (φ : Refs Γ Γ') (Ms : All (Tm Γ) Δ) → All₂ (φ ⊢_≈_) Ms (concs φ Ms)
conc≈ φ (` x) = var≈ refl
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
conc≈ φ (fold M) = fold≈ (conc≈ φ M)
conc≈ φ (unfold M) = unfold≈ (conc≈ φ M)
concs≈ φ [] = []
concs≈ φ (M ∷ Ms) = conc≈ φ M ∷ concs≈ φ Ms

{- Closure under substitution -----------------------------------------------------------}

OK : ∀ {Γ Γ' Δ Δ'} (𝒦₁ : S.Kit) (𝒦₂ : T.Kit) → Refs Γ Γ' → Refs Δ Δ' → S.Sub 𝒦₁ Γ Δ → T.Sub 𝒦₂ Γ' Δ' → Set
OK 𝒦₁ 𝒦₂ φ φ₂ σ τ = ∀ {A} (x : _ ∋ A) → φ₂ ⊢ S.Kit.tm 𝒦₁ (σ x) ≈ T.trav 𝒦₂ τ (ref-tm (φ x))

shift-ren : ∀ {Γ A B} (r : Ref Γ A) → ref-tm (shift-ref {B = B} r) ≡ T.ren S (ref-tm r)
shift-ren (var x) = refl
shift-ren (prj i x) = refl

{- for a kit of each language, which agree on variable 0 and on weakening -}
module Trav {𝒦₁ 𝒦₂}
  (rel-vr : ∀ {Γ Γ' B} {φ : Refs Γ Γ'} → ext-ref {B = B} φ ⊢ S.Kit.tm 𝒦₁ (S.Kit.vr 𝒦₁ Z) ≈ T.Kit.tm 𝒦₂ (T.Kit.vr 𝒦₂ Z))
  (shift-trav : ∀ {Γ Δ A B} {τ : T.Sub 𝒦₂ Γ Δ} (r : Ref Γ A)
    → T.trav 𝒦₂ (T.exts 𝒦₂ {B = B} τ) (ref-tm (shift-ref r)) ≡ T.ren S (T.trav 𝒦₂ τ (ref-tm r)))
  (rel-wk : ∀ {Γ Γ' A B} {φ : Refs Γ Γ'} {a : S.Kit.K 𝒦₁ Γ A} {X} → φ ⊢ S.Kit.tm 𝒦₁ a ≈ X
    → ext-ref {B = B} φ ⊢ S.Kit.tm 𝒦₁ (S.Kit.wk 𝒦₁ a) ≈ T.ren S X) where

  ok-ext : ∀ {Γ Γ' Δ Δ' B} {φ : Refs Γ Γ'} {φ₂ : Refs Δ Δ'} {σ : S.Sub 𝒦₁ Γ Δ} {τ : T.Sub 𝒦₂ Γ' Δ'} → OK 𝒦₁ 𝒦₂ φ φ₂ σ τ
    → OK 𝒦₁ 𝒦₂ (ext-ref {B = B} φ) (ext-ref φ₂) (S.exts 𝒦₁ σ) (T.exts 𝒦₂ τ)
  ok-ext ok Z = rel-vr
  ok-ext {φ = φ} ok (S x) = subst (_ ⊢ _ ≈_) (sym (shift-trav (φ x))) (rel-wk (ok x))

  ≈-trav : ∀ {Γ Γ' Δ Δ' A} {φ : Refs Γ Γ'} {φ₂ : Refs Δ Δ'} {σ : S.Sub 𝒦₁ Γ Δ} {τ : T.Sub 𝒦₂ Γ' Δ'} {M : Tm Γ A} {M'}
    → φ ⊢ M ≈ M' → OK 𝒦₁ 𝒦₂ φ φ₂ σ τ → φ₂ ⊢ S.trav 𝒦₁ σ M ≈ T.trav 𝒦₂ τ M'
  ≈-travs : ∀ {Γ Γ' Δ Δ' Θ} {φ : Refs Γ Γ'} {φ₂ : Refs Δ Δ'} {σ : S.Sub 𝒦₁ Γ Δ} {τ : T.Sub 𝒦₂ Γ' Δ'}
    {Ms : All (Tm Γ) Θ} {Ms'} → All₂ (φ ⊢_≈_) Ms Ms' → OK 𝒦₁ 𝒦₂ φ φ₂ σ τ
    → All₂ (φ₂ ⊢_≈_) (S.travs 𝒦₁ σ Ms) (T.travs 𝒦₂ τ Ms')
  ≈-trav (var≈ refl) ok = ok _
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
  ≈-trav (fold≈ r) ok = fold≈ (≈-trav r ok)
  ≈-trav (unfold≈ r) ok = unfold≈ (≈-trav r ok)
  ≈-travs [] ok = []
  ≈-travs (r ∷ rs) ok = ≈-trav r ok ∷ ≈-travs rs ok

module RenT = Trav {S.varK} {T.varK} (var≈ refl) (λ { (var x) → refl ; (prj i x) → refl })
  (λ { {φ = φ} {a} (var≈ refl) → var≈ (shift-ren (φ a)) })
module SubT = Trav {S.tmK} {T.tmK} (var≈ refl) (λ { (var x) → refl ; (prj i x) → refl })
  (λ r → RenT.≈-trav r λ x → var≈ (shift-ren _))

{- The simulation --------------------------------------------------------------------------}

module _ {φ₀ : Refs [] []} where

 R : ∀ {A} → Tm [] A → C.Tm [] A → Set
 R = φ₀ ⊢_≈_

 Ans′ : ∀ {A} → Tm [] A → Red (Tm [] A) → C.Tm [] A → Set
 Ans′ = Ans T.red Value R

 {- the source of a value is a value -}
 ≈-value : ∀ {A} {V V'} → R {A} V V' → Value V' → S.Value V
 ≈-values : ∀ {Δ} {Vs : All _ Δ} {Vs'} → All₂ R Vs Vs' → Each Value Vs' → Each S.Value Vs
 ≈-value (clos≈ n rs) (T.clos vs) = S.clos (≈-values rs vs)
 ≈-value lit≈ T.lit = S.lit
 ≈-value (tuple≈ rs) (T.tuple vs) = S.tuple (≈-values rs vs)
 ≈-value (inl≈ r) (T.inl v) = S.inl (≈-value r v)
 ≈-value (inr≈ r) (T.inr v) = S.inr (≈-value r v)
 ≈-value (fold≈ r) (T.fold v) = S.fold (≈-value r v)
 ≈-values [] [] = []
 ≈-values (r ∷ rs) (v ∷ vs) = ≈-value r v ∷ ≈-values rs vs

 obs≈ : ∀ {A} {V V'} → R {A} V V' → Value V' → S.obs V ≡ T.obs V'
 obss≈ : ∀ {Δ} {Vs : All _ Δ} {Vs'} → All₂ R Vs Vs' → Each Value Vs' → S.obss Vs ≡ T.obss Vs'
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

 ≈-[] : ∀ {A B} {N : Tm (A ∷ []) B} {N' V V'} → ext-ref φ₀ ⊢ N ≈ N' → R V V' → R (N S.[ V ]) (N' T.[ V' ])
 ≈-[] n m = SubT.≈-trav n λ { Z → m }

 sim : ∀ {A} {M M'} → R {A} M M' → Ans′ M (S.red M) M'
 sims : ∀ {Δ} {Ms : All _ Δ} {Ms'} → All₂ R Ms Ms' → Ans T.reds (Each Value) (All₂ R) Ms (S.reds Ms) Ms'
 sim (get≈ {V = V} {Vs'} {i} v r vs) =
   subst (λ x → Ans′ V x (C.get i (C.tuple Vs'))) (sym (S.value-red v))
         (val (val-in (T.value-red (T.tuple vs)) ◅ ε) (each-lookup vs i) r)
 sim (clos≈ n rs) = ans-in (frame _ λ _ → refl) (clos≈ n) (sims rs) λ vs ms → val ε (T.clos vs) (clos≈ n ms)
 sim (app≈ r s) =
   ans-in (frame _ λ _ → refl) (λ m → app≈ m s) (sim r)
     λ v m → ans-in (frame {g = C.app _} _ λ _ → val-in (value-red v)) (app≈ m) (sim s) λ w m' → β-sim v m w m'
   where
   β-sim : ∀ {A B} {V : Tm [] (A ⇒ B)} {V' W W'} → Value V' → R V V' → Value W' → R W W'
     → Ans′ (app V W) (S.β V refl W) (C.app V' W')
   β-sim (T.clos vs) (clos≈ n ms) w m' =
     to (one (trans (val-in (value-red (T.clos vs))) (val-in (value-red w))))
        (SubT.≈-trav n λ { Z → m' ; (S i) → get≈ (each-lookup (≈-values ms vs) i) (lookup₂ ms i) vs })
 sim lit≈ = val ε T.lit lit≈
 sim (tuple≈ rs) = ans-in (frame _ λ _ → refl) tuple≈ (sims rs) λ vs ms → val ε (T.tuple vs) (tuple≈ ms)
 sim (getᵢ≈ {i = i} r) = ans-in (frame _ λ _ → refl) getᵢ≈ (sim r)
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

concretize-correct : ∀ {A} (M : Tm [] A) → Equivalent (S.sem M) (T.sem (concretize-program M))
concretize-correct M = red-equivalent value-red R sim (λ m _ v → obs≈ m v) (conc≈ _ M)

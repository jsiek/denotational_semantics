{-

  Correctness of typed optimize (Clos2ᵀ → Clos2ᵀ) by a forward simulation
  of the Clos2ᵀ reduction semantics by itself, in lock step.

  The pass renames variables: the relation on terms (_⊢_≈_) relates a
  variable x to ρ x, for a partial map ρ (a free variable that a closure
  drops has no variable in the closure's code). It is a congruence,
  closed under substitution (≈-trav), except for closures: a closure of
  code N and free variables Ms is related to one of code N' and free
  variables Ms' when N is related to N' by the map of the kept variables
  (ρfl fl), and Ms' are the free variables that fl keeps, related, while
  the others are variables or values (Caps), so in a closed term values,
  which the source evaluates in no step. Applying related closures
  substitutes related values in related code (caps-lookup).

-}

module proof.Correctness.Typed.Reduction.OptimizeRed where

open import Language.Typed.Type renaming (_≟_ to _≟F_)
open import Language.Typed.Clos2
open import Compiler.Typed.Optimize
open import Framework.VecSelect
open import proof.Framework.VecSelect using (subL; subR)
open import Semantics.Observation
open import proof.Framework.Reduction Obs o-error
open import proof.Framework.ReductionVec Obs o-error using (ans-∷; all-lookup)
open import Semantics.Reduction.Smallstep using (Equivalent)
import proof.Semantics.Reduction.Typed.Clos2 as T
open T using (Kit; varK; tmK; trav; travs; Value; value-red)
import Language.Prim as P

open import Data.Bool using (Bool; true; false; T)
open import Data.Fin using (Fin; zero; suc)
open import Data.Fin.Properties using () renaming (_≟_ to _Fin≟_)
import Data.Integer as Z
open import Data.List using (_∷_)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe as Mb
open import Data.Nat using (ℕ; suc)
open import Data.Vec using (Vec; []; _∷_; lookup)
open import Data.Vec.Relation.Unary.All using (All; []; _∷_)
open import Data.Vec.Relation.Binary.Pointwise.Inductive using (Pointwise; []; _∷_)
import Data.Vec.Relation.Binary.Pointwise.Inductive as PW
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary using (Dec; yes; no; does)

{- The relation ----------------------------------------------------------------}

VM : ℕ → ℕ → Set
VM k k' = Fin k → Maybe (Fin k')

extρ : ∀ {k k'} → VM k k' → VM (suc k) (suc k')
extρ ρ zero = just zero
extρ ρ (suc x) = Mb.map suc (ρ x)

{- the variables of a closure's code that fl keeps, where squeeze sends them -}
ρfl : ∀ {n} (fl : Vec Bool n) → VM (suc n) (suc (count fl))
ρfl fl zero = just zero
ρfl (true ∷ fl) (suc zero) = just (suc zero)
ρfl (true ∷ fl) (suc (suc i)) = Mb.map (ext suc) (ρfl fl (suc i))
ρfl (false ∷ fl) (suc zero) = nothing
ρfl (false ∷ fl) (suc (suc i)) = ρfl fl (suc i)

{- a variable or a value -}
data VV {k} : Tm k Any → Set where
  var : ∀ x → VV (` x)
  val : ∀ {V} → Value V → VV V

infix 4 _⊢_≈_
data _⊢_≈_ : ∀ {k k' A} → VM k k' → Tm k A → Tm k' A → Set
data Caps {k k'} (ρ : VM k k') : ∀ {n} (fl : Vec Bool n) → Vec (Tm k Any) n → Vec (Tm k' Any) (count fl) → Set

data _⊢_≈_ where
  var≈ : ∀ {k k'} {ρ : VM k k'} {x y} → ρ x ≡ just y → ρ ⊢ ` x ≈ ` y
  clos≈ : ∀ {k k' n} {ρ : VM k k'} {N : Tm (suc n) Any} {Ms} (fl : Vec Bool n) {N' Ms'} → ρfl fl ⊢ N ≈ N' → Caps ρ fl Ms Ms'
    → ρ ⊢ clos N Ms ≈ clos N' Ms'
  app≈ : ∀ {k k'} {ρ : VM k k'} {L L' M M'} → ρ ⊢ L ≈ L' → ρ ⊢ M ≈ M' → ρ ⊢ app L M ≈ app L' M'
  lit≈ : ∀ {k k'} {ρ : VM k k'} {B c} → ρ ⊢ lit B c ≈ lit B c
  tuple≈ : ∀ {k k' n} {ρ : VM k k'} {Ms : Vec _ n} {Ms'} → Pointwise (ρ ⊢_≈_) Ms Ms' → ρ ⊢ tuple Ms ≈ tuple Ms'
  get≈ : ∀ {k k' n i} {ρ : VM k k'} {M : Tm k ⟪ tup n ⟫} {M'} → ρ ⊢ M ≈ M' → ρ ⊢ get i M ≈ get i M'
  inl≈ : ∀ {k k'} {ρ : VM k k'} {M M'} → ρ ⊢ M ≈ M' → ρ ⊢ inl M ≈ inl M'
  inr≈ : ∀ {k k'} {ρ : VM k k'} {M M'} → ρ ⊢ M ≈ M' → ρ ⊢ inr M ≈ inr M'
  case≈ : ∀ {k k'} {ρ : VM k k'} {L L' M M' N N'} → ρ ⊢ L ≈ L' → extρ ρ ⊢ M ≈ M' → extρ ρ ⊢ N ≈ N'
    → ρ ⊢ case L M N ≈ case L' M' N'
  prim≈ : ∀ {k k' p} {ρ : VM k k'} {L L' M M'} → ρ ⊢ L ≈ L' → ρ ⊢ M ≈ M' → ρ ⊢ prim p L M ≈ prim p L' M'
  let≈ : ∀ {k k'} {ρ : VM k k'} {M M' N N'} → ρ ⊢ M ≈ M' → extρ ρ ⊢ N ≈ N' → ρ ⊢ let′ M N ≈ let′ M' N'
  inject≈ : ∀ {k k' G} {ρ : VM k k'} {M : Tm k ⟪ G ⟫} {M'} → ρ ⊢ M ≈ M' → ρ ⊢ inject G M ≈ inject G M'
  project≈ : ∀ {k k' t} {ρ : VM k k'} {M M'} → ρ ⊢ M ≈ M' → ρ ⊢ project t M ≈ project t M'

data Caps ρ where
  [] : Caps ρ [] [] []
  keep : ∀ {n fl M M'} {Ms : Vec _ n} {Ms'} → ρ ⊢ M ≈ M' → Caps ρ fl Ms Ms' → Caps ρ (true ∷ fl) (M ∷ Ms) (M' ∷ Ms')
  drop : ∀ {n fl M} {Ms : Vec _ n} {Ms'} → VV M → Caps ρ fl Ms Ms' → Caps ρ (false ∷ fl) (M ∷ Ms) Ms'

{- The fundamental lemma ----------------------------------------------------------}

ρfl-kept : ∀ {n} (fl : Vec Bool n) x → Kept fl x → ρfl fl x ≡ just (squeeze fl x)
ρfl-kept fl zero _ = refl
ρfl-kept (true ∷ fl) (suc zero) _ = refl
ρfl-kept (true ∷ fl) (suc (suc i)) k = cong (Mb.map (ext suc)) (ρfl-kept fl (suc i) k)
ρfl-kept (false ∷ fl) (suc (suc i)) k = ρfl-kept fl (suc i) k

Hyp : ∀ {k k'} → (Fin k → Bool) → VM k k' → (Fin k → Fin k') → Set
Hyp u ρ r = ∀ x → T (u x) → ρ x ≡ just (r x)

opt≈ : ∀ {k k' A} {ρ : VM k k'} {r} (M : Tm k A) → Hyp (uses M) ρ r → ρ ⊢ M ≈ opt r M
opts≈ : ∀ {k k' n} {ρ : VM k k'} {r} (Ms : Vec (Tm k Any) n) → Hyp (usesV Ms) ρ r → Pointwise (ρ ⊢_≈_) Ms (opts r Ms)
caps≈ : ∀ {k k' n} {ρ : VM k k'} {r} (u : Fin n → Bool) (Ms : Vec (Tm k Any) n) → Hyp (usesV Ms) ρ r
  → Caps ρ (flags u Ms) Ms (select (flags u Ms) (opts r Ms))
under : ∀ {k k' u} {ρ : VM k k'} {r} → Hyp (λ x → u (suc x)) ρ r → Hyp u (extρ ρ) (ext r)
under h zero _ = refl
under h (suc x) t rewrite h x t = refl
opt≈ (` x) h = var≈ (h x (lemma x))
  where lemma : ∀ {k} (x : Fin k) → T (uses (` x) x)
        lemma x with x Fin≟ x
        ... | yes _ = _
        ... | no ne = ne refl
opt≈ (clos N Ms) h =
  clos≈ (keeps N Ms) (opt≈ N λ x t → ρfl-kept _ x (covers {N = N} {Ms = Ms} (flags-ok (λ i → uses N (suc i)) Ms) x t)) (caps≈ _ Ms h)
opt≈ (app L M) h = app≈ (opt≈ L (subL {u = uses L} h)) (opt≈ M (subR {u = uses L} h))
opt≈ (lit B c) h = lit≈
opt≈ (tuple Ms) h = tuple≈ (opts≈ Ms h)
opt≈ (get i M) h = get≈ (opt≈ M h)
opt≈ (inl M) h = inl≈ (opt≈ M h)
opt≈ (inr M) h = inr≈ (opt≈ M h)
opt≈ (case L M N) h = case≈ (opt≈ L (subL {u = uses L} h)) (opt≈ M (under (subL {u = λ x → uses M (suc x)} (subR {u = uses L} h))))
  (opt≈ N (under (subR {u = λ x → uses M (suc x)} (subR {u = uses L} h))))
opt≈ (prim p L M) h = prim≈ (opt≈ L (subL {u = uses L} h)) (opt≈ M (subR {u = uses L} h))
opt≈ (let′ M N) h = let≈ (opt≈ M (subL {u = uses M} h)) (opt≈ N (under (subR {u = uses M} h)))
opt≈ (inject G M) h = inject≈ (opt≈ M h)
opt≈ (project t M) h = project≈ (opt≈ M h)
opts≈ [] h = []
opts≈ (M ∷ Ms) h = opt≈ M (subL {u = uses M} h) ∷ opts≈ Ms (subR {u = uses M} h)
caps≈ u [] h = []
caps≈ u (M ∷ Ms) h with keep? M (u zero) | flags-ok u (M ∷ Ms) zero
... | true | kept = keep (opt≈ M (subL {u = uses M} h)) (caps≈ (λ i → u (suc i)) Ms (subR {u = uses M} h))
... | false | var _ = drop (var _) (caps≈ (λ i → u (suc i)) Ms (subR {u = uses M} h))

{- Closure under substitution ------------------------------------------------------}

OK : ∀ {k k' j j'} (𝒦 : Kit) → VM k k' → VM j j' → T.Sub 𝒦 k j → T.Sub 𝒦 k' j' → Set
OK 𝒦 ρ ρ₂ σ τ = ∀ x {y} → ρ x ≡ just y → ρ₂ ⊢ Kit.tm 𝒦 (σ x) ≈ Kit.tm 𝒦 (τ y)

record KR (𝒦 : Kit) : Set where
  field
    rel-vr : ∀ {k k'} {ρ : VM k k'} → extρ ρ ⊢ Kit.tm 𝒦 (Kit.vr 𝒦 zero) ≈ Kit.tm 𝒦 (Kit.vr 𝒦 zero)
    vv-vr : ∀ {k} → VV {suc k} (Kit.tm 𝒦 (Kit.vr 𝒦 zero))
    rel-wk : ∀ {k k'} {ρ : VM k k'} {a b} → ρ ⊢ Kit.tm 𝒦 a ≈ Kit.tm 𝒦 b → extρ ρ ⊢ Kit.tm 𝒦 (Kit.wk 𝒦 a) ≈ Kit.tm 𝒦 (Kit.wk 𝒦 b)
    vv-wk : ∀ {k a} → VV {k} (Kit.tm 𝒦 a) → VV (Kit.tm 𝒦 (Kit.wk 𝒦 a))

module Trav {𝒦} (K : KR 𝒦) where
  open KR K

  ok-ext : ∀ {k k' j j'} {ρ : VM k k'} {ρ₂ : VM j j'} {σ τ} → OK 𝒦 ρ ρ₂ σ τ
    → OK 𝒦 (extρ ρ) (extρ ρ₂) (T.exts 𝒦 σ) (T.exts 𝒦 τ)
  ok-ext ok zero refl = rel-vr
  ok-ext {ρ = ρ} ok (suc x) e with ρ x in eq | e
  ... | just y | refl = rel-wk (ok x eq)

  vv-ext : ∀ {k j} {σ : T.Sub 𝒦 k j} → (∀ x → VV (Kit.tm 𝒦 (σ x))) → ∀ x → VV (Kit.tm 𝒦 (T.exts 𝒦 σ x))
  vv-ext h zero = vv-vr
  vv-ext h (suc x) = vv-wk (h x)

  ≈-trav : ∀ {k k' j j' A} {ρ : VM k k'} {ρ₂ : VM j j'} {σ τ} {M : Tm k A} {M'} → ρ ⊢ M ≈ M'
    → OK 𝒦 ρ ρ₂ σ τ → (∀ x → VV (Kit.tm 𝒦 (σ x))) → ρ₂ ⊢ trav 𝒦 σ M ≈ trav 𝒦 τ M'
  ≈-travs : ∀ {k k' j j' n} {ρ : VM k k'} {ρ₂ : VM j j'} {σ τ} {Ms : Vec (Tm k Any) n} {Ms'} → Pointwise (ρ ⊢_≈_) Ms Ms'
    → OK 𝒦 ρ ρ₂ σ τ → (∀ x → VV (Kit.tm 𝒦 (σ x))) → Pointwise (ρ₂ ⊢_≈_) (travs 𝒦 σ Ms) (travs 𝒦 τ Ms')
  caps-trav : ∀ {k k' j j' n} {ρ : VM k k'} {ρ₂ : VM j j'} {σ τ} {fl : Vec Bool n} {Ms Ms'} → Caps ρ fl Ms Ms'
    → OK 𝒦 ρ ρ₂ σ τ → (∀ x → VV (Kit.tm 𝒦 (σ x))) → Caps ρ₂ fl (travs 𝒦 σ Ms) (travs 𝒦 τ Ms')
  ≈-trav (var≈ e) ok vv = ok _ e
  ≈-trav (clos≈ fl n cs) ok vv = clos≈ fl n (caps-trav cs ok vv)
  ≈-trav (app≈ r s) ok vv = app≈ (≈-trav r ok vv) (≈-trav s ok vv)
  ≈-trav lit≈ ok vv = lit≈
  ≈-trav (tuple≈ rs) ok vv = tuple≈ (≈-travs rs ok vv)
  ≈-trav (get≈ r) ok vv = get≈ (≈-trav r ok vv)
  ≈-trav (inl≈ r) ok vv = inl≈ (≈-trav r ok vv)
  ≈-trav (inr≈ r) ok vv = inr≈ (≈-trav r ok vv)
  ≈-trav (case≈ r s t) ok vv = case≈ (≈-trav r ok vv) (≈-trav s (ok-ext ok) (vv-ext vv)) (≈-trav t (ok-ext ok) (vv-ext vv))
  ≈-trav (prim≈ r s) ok vv = prim≈ (≈-trav r ok vv) (≈-trav s ok vv)
  ≈-trav (let≈ r s) ok vv = let≈ (≈-trav r ok vv) (≈-trav s (ok-ext ok) (vv-ext vv))
  ≈-trav (inject≈ r) ok vv = inject≈ (≈-trav r ok vv)
  ≈-trav (project≈ r) ok vv = project≈ (≈-trav r ok vv)
  ≈-travs [] ok vv = []
  ≈-travs (r ∷ rs) ok vv = ≈-trav r ok vv ∷ ≈-travs rs ok vv
  caps-trav [] ok vv = []
  caps-trav (keep r cs) ok vv = keep (≈-trav r ok vv) (caps-trav cs ok vv)
  caps-trav (drop (var x) cs) ok vv = drop (vv x) (caps-trav cs ok vv)
  caps-trav (drop (val v) cs) ok vv = drop (val (T.value-trav v)) (caps-trav cs ok vv)

varKR : KR varK
varKR = record { rel-vr = var≈ refl ; vv-vr = var _ ; rel-wk = λ { (var≈ e) → var≈ (cong (Mb.map suc) e) } ; vv-wk = λ _ → var _ }

tmKR : KR tmK
tmKR = record { rel-vr = var≈ refl ; vv-vr = var _ ; rel-wk = λ r → Trav.≈-trav varKR r (λ _ e → var≈ (cong (Mb.map suc) e)) (λ _ → var _)
              ; vv-wk = λ { (var x) → var _ ; (val v) → val (T.value-trav v) } }

{- The simulation ----------------------------------------------------------------------}

ρ₀ : VM 0 0
ρ₀ ()

R : ∀ {A} → Tm 0 A → Tm 0 A → Set
R = ρ₀ ⊢_≈_

Ans′ : ∀ {A} → Tm 0 A → Red (Tm 0 A) → Tm 0 A → Set
Ans′ = Ans T.red Value R

{- a closed variable or value is a value -}
vv-value : ∀ {V : Tm 0 Any} → VV V → Value V
vv-value (var ())
vv-value (val v) = v

{- the source of a value is a value -}
≈-value : ∀ {A} {V V' : Tm 0 A} → R V V' → Value V' → Value V
≈-values : ∀ {n} {Vs Vs' : Vec (Tm 0 Any) n} → Pointwise R Vs Vs' → All Value Vs' → All Value Vs
caps-values : ∀ {n} {fl : Vec Bool n} {Vs Vs'} → Caps ρ₀ fl Vs Vs' → All Value Vs' → All Value Vs
≈-value (clos≈ fl n cs) (T.clos vs) = T.clos (caps-values cs vs)
≈-value lit≈ T.lit = T.lit
≈-value (tuple≈ rs) (T.tuple vs) = T.tuple (≈-values rs vs)
≈-value (inl≈ r) (T.inl v) = T.inl (≈-value r v)
≈-value (inr≈ r) (T.inr v) = T.inr (≈-value r v)
≈-value (inject≈ r) (T.inject v) = T.inject (≈-value r v)
≈-values [] [] = []
≈-values (r ∷ rs) (v ∷ vs) = ≈-value r v ∷ ≈-values rs vs
caps-values [] [] = []
caps-values (keep r cs) (v ∷ vs) = ≈-value r v ∷ caps-values cs vs
caps-values (drop vv cs) vs = vv-value vv ∷ caps-values cs vs

{- the variables of the code of related closures, applied to related values -}
caps-lookup : ∀ {n} {fl : Vec Bool n} {Vs Vs' W W'} → Caps ρ₀ fl Vs Vs' → R W W'
  → OK tmK (ρfl fl) ρ₀ (lookup (W ∷ Vs)) (lookup (W' ∷ Vs'))
caps-lookup cs m zero refl = m
caps-lookup (keep r cs) m (suc zero) refl = r
caps-lookup {fl = true ∷ fl} (keep r cs) m (suc (suc i)) e with ρfl fl (suc i) in eq | e
... | just zero | refl = caps-lookup cs m (suc i) eq
... | just (suc j) | refl = caps-lookup cs m (suc i) eq
caps-lookup (drop vv cs) m (suc (suc i)) e = caps-lookup cs m (suc i) e

obs≈ : ∀ {A} {V : Tm 0 A} {V'} → R V V' → T.obs V ≡ T.obs V'
obss≈ : ∀ {n} {Vs : Vec (Tm 0 Any) n} {Vs'} → Pointwise R Vs Vs' → T.obss Vs ≡ T.obss Vs'
obs≈ (clos≈ _ _ _) = refl
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

out≈ : ∀ p n m → R (T.out p n m) (T.out p n m)
out≈ P.sub n m = lit≈
out≈ P.eq n m with does (n Z.≟ m)
... | true = inl≈ (inject≈ (tuple≈ []))
... | false = inr≈ (inject≈ (tuple≈ []))

{- substituting a value for the variable of a binder -}
≈-[] : ∀ {A} {N N' : Tm 1 A} {V V'} → extρ ρ₀ ⊢ N ≈ N' → R V V' → Value V → R (N T.[ V ]) (N' T.[ V' ])
≈-[] n m v = Trav.≈-trav tmKR n (λ { zero refl → m }) (λ _ → val v)

sim : ∀ {A} {M M' : Tm 0 A} → R M M' → Ans′ M (T.red M) M'
sims : ∀ {n} {Ms Ms' : Vec (Tm 0 Any) n} → Pointwise R Ms Ms' → Ans T.reds (All Value) (Pointwise R) Ms (T.reds Ms) Ms'
caps-sim : ∀ {n} {fl : Vec Bool n} {Ms Ms'} → Caps ρ₀ fl Ms Ms' → Ans T.reds (All Value) (Caps ρ₀ fl) Ms (T.reds Ms) Ms'
sim (var≈ {x = ()} _)
sim (clos≈ fl n cs) = ans-in (frame _ λ _ → refl) (clos≈ fl n) (caps-sim cs) λ vs ms → val ε (T.clos vs) (clos≈ fl n ms)
sim (app≈ r s) =
  ans-in (frame _ λ _ → refl) (λ m → app≈ m s) (sim r)
    λ v m → ans-in (frame {g = app _} _ λ _ → val-in (value-red v)) (app≈ m) (sim s)
      λ { w m' → β-sim v m w m' }
  where
  β-sim : ∀ {V V' W W'} → Value V' → R V V' → Value W' → R W W' → Ans′ (app V W) (T.β V W) (app V' W')
  β-sim (T.clos vs) (clos≈ fl n cs) w m' =
    to (one (trans (val-in (value-red (T.clos vs))) (val-in (value-red w))))
       (Trav.≈-trav tmKR n (caps-lookup cs m')
          λ { zero → val (≈-value m' w) ; (suc i) → val (all-lookup (caps-values cs vs) i) })
sim lit≈ = val ε T.lit lit≈
sim (tuple≈ rs) = ans-in (frame _ λ _ → refl) tuple≈ (sims rs) λ vs ms → val ε (T.tuple vs) (tuple≈ ms)
sim (get≈ {i = i} r) = ans-in (frame _ λ _ → refl) get≈ (sim r)
  λ { (T.tuple vs) (tuple≈ ms) → to (one (val-in (value-red (T.tuple vs)))) (PW.lookup ms i) }
sim (inl≈ r) = ans-in (frame _ λ _ → refl) inl≈ (sim r) λ v m → val ε (T.inl v) (inl≈ m)
sim (inr≈ r) = ans-in (frame _ λ _ → refl) inr≈ (sim r) λ v m → val ε (T.inr v) (inr≈ m)
sim (case≈ r s t) = ans-in (frame _ λ _ → refl) (λ m → case≈ m s t) (sim r)
  λ { (T.inl v) (inl≈ m) → to (one (val-in (value-red (T.inl v)))) (≈-[] s m (≈-value m v))
    ; (T.inr v) (inr≈ m) → to (one (val-in (value-red (T.inr v)))) (≈-[] t m (≈-value m v)) }
sim (prim≈ {p = p} r s) = ans-in (frame _ λ _ → refl) (λ m → prim≈ m s) (sim r)
  λ { T.lit lit≈ → ans-in (frame {g = prim p _} _ λ _ → refl) (prim≈ lit≈) (sim s)
    λ { T.lit lit≈ → to (one refl) (out≈ p _ _) } }
sim (let≈ r s) = ans-in (frame _ λ _ → refl) (λ m → let≈ m s) (sim r)
  λ v m → to (one (val-in (value-red v))) (≈-[] s m (≈-value m v))
sim (inject≈ r) = ans-in (frame _ λ _ → refl) inject≈ (sim r) λ v m → val ε (T.inject v) (inject≈ m)
sim (project≈ {t = t} r) = ans-in (frame _ λ _ → refl) project≈ (sim r) λ { (T.inject v) (inject≈ m) → proj-sim v m }
  where
  proj-sim : ∀ {G V V'} → Value V' → R V V' → Ans′ (project t (inject G V)) (T.project? t (inject G V)) (project t (inject G V'))
  proj-sim {G} {V} {V'} v m = pd (G ≟F flat t) (val-in (value-red (T.inject v)))
    where pd : ∀ {H} (d : Dec (G ≡ H)) {X Y} → T.red X ≡ T.proj-dec d V' → Ans′ Y (T.proj-dec d V) X
          pd (yes refl) e = to (one e) m
          pd (no _) e = error ε e
sims [] = val ε [] []
sims (r ∷ rs) = ans-∷ T.reds (λ _ _ → refl) value-red rs (sim r) (sims rs)
caps-sim [] = val ε [] []
caps-sim (keep r cs) =
  ans-in (frame _ λ _ → refl) (λ m → keep m cs) (sim r)
    λ v m → ans-in (frame {g = λ Xs → _ ∷ Xs} _ λ _ → val-in (value-red v)) (keep m) (caps-sim cs)
      λ vs ms → val ε (v ∷ vs) (keep m ms)
caps-sim (drop vv cs) =
  ans-skip (value-red (vv-value vv)) (ans-in frame-id (drop vv) (caps-sim cs) λ vs ms → val ε vs (drop vv ms))

{- The end theorem ---------------------------------------------------------------}

optimize-correct : ∀ (M : Tm 0 Any) → Equivalent (T.sem M) (T.sem (optimize-program M))
optimize-correct M = red-equivalent value-red R sim (λ m _ _ → obs≈ m) (opt≈ M λ ())

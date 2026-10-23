{-

  Correctness of optimize (Closμ → Closμ) by a forward simulation of
  the Closμ reduction semantics by itself, in lock step, as for typed
  optimize (proof/Correctness/Reduction/OptimizeRed.agda).

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

module Mu.proof.Correctness.ReductionSemantics.OptimizeRed where

open import Mu.Language.Type hiding (_[_])
open import Mu.Language.Clos
open import Mu.Compiler.Optimize
open import Mu.Framework.AllUtil using (All; []; _∷_; lookup; All₂; lookup₂; Flags; kept; select; Kept; squeeze; sq; ∨-l; ∨-r)
open import Semantics.Observation
open import proof.Framework.Reduction Obs o-error hiding (Each; []; _∷_)
open import Mu.proof.Framework.ReductionAll Obs o-error using (ans-∷; Each; []; _∷_; each-lookup)
open import Semantics.Reduction.Smallstep using (Equivalent)
import Mu.proof.Semantics.ReductionSemantics.Clos as T
open T using (Kit; varK; tmK; trav; travs; Value; value-red; VV; var; val; vv-wk; vv-value)
import Language.Prim as P

open import Data.Bool using (Bool; true; false; T)
import Data.Integer as Z
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe as Mb
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary using (does)
open import Relation.Nullary.Decidable using (fromWitness)

{- The relation ----------------------------------------------------------------}

VM : Ctx → Ctx → Set
VM Γ Γ' = ∀ {A} → Γ ∋ A → Maybe (Γ' ∋ A)

extρ : ∀ {Γ Γ' B} → VM Γ Γ' → VM (B ∷ Γ) (B ∷ Γ')
extρ ρ Z = just Z
extρ ρ (S x) = Mb.map S (ρ x)

{- the free variables that fl keeps, where they go -}
ρsq : ∀ {Δ} (fl : Flags Δ) → VM Δ (kept fl)
ρsq (true ∷ fl) Z = just Z
ρsq (true ∷ fl) (S i) = Mb.map S (ρsq fl i)
ρsq (false ∷ fl) Z = nothing
ρsq (false ∷ fl) (S i) = ρsq fl i

{- the variables of a closure's code: the argument and the kept ones -}
ρfl : ∀ {Δ A} (fl : Flags Δ) → VM (A ∷ Δ) (A ∷ kept fl)
ρfl fl Z = just Z
ρfl fl (S i) = Mb.map S (ρsq fl i)

infix 4 _⊢_≈_
data _⊢_≈_ : ∀ {Γ Γ' A} → VM Γ Γ' → Tm Γ A → Tm Γ' A → Set
data Caps {Γ Γ'} (ρ : VM Γ Γ') : ∀ {Δ} (fl : Flags Δ) → All (Tm Γ) Δ → All (Tm Γ') (kept fl) → Set

data _⊢_≈_ where
  var≈ : ∀ {Γ Γ' A} {ρ : VM Γ Γ'} {x : Γ ∋ A} {y} → ρ x ≡ just y → ρ ⊢ ` x ≈ ` y
  clos≈ : ∀ {Γ Γ' Δ A B} {ρ : VM Γ Γ'} {N : Tm (A ∷ Δ) B} {Ms} (fl : Flags Δ) {N' Ms'} → ρfl fl ⊢ N ≈ N' → Caps ρ fl Ms Ms'
    → ρ ⊢ clos N Ms ≈ clos N' Ms'
  app≈ : ∀ {Γ Γ' A B} {ρ : VM Γ Γ'} {L : Tm Γ (A ⇒ B)} {L' M M'} → ρ ⊢ L ≈ L' → ρ ⊢ M ≈ M' → ρ ⊢ app L M ≈ app L' M'
  lit≈ : ∀ {Γ Γ'} {ρ : VM Γ Γ'} {B c} → ρ ⊢ lit B c ≈ lit B c
  tuple≈ : ∀ {Γ Γ' Δ} {ρ : VM Γ Γ'} {Ms : All (Tm Γ) Δ} {Ms'} → All₂ (ρ ⊢_≈_) Ms Ms' → ρ ⊢ tuple Ms ≈ tuple Ms'
  get≈ : ∀ {Γ Γ' Δ A} {i : Δ ∋ A} {ρ : VM Γ Γ'} {M : Tm Γ (tup Δ)} {M'} → ρ ⊢ M ≈ M' → ρ ⊢ get i M ≈ get i M'
  inl≈ : ∀ {Γ Γ' A B} {ρ : VM Γ Γ'} {M : Tm Γ A} {M'} → ρ ⊢ M ≈ M' → ρ ⊢ inl {B = B} M ≈ inl M'
  inr≈ : ∀ {Γ Γ' A B} {ρ : VM Γ Γ'} {M : Tm Γ B} {M'} → ρ ⊢ M ≈ M' → ρ ⊢ inr {A = A} M ≈ inr M'
  case≈ : ∀ {Γ Γ' A B C} {ρ : VM Γ Γ'} {L : Tm Γ (A ⊹ B)} {L'} {M : Tm (A ∷ Γ) C} {M' N N'} → ρ ⊢ L ≈ L'
    → extρ ρ ⊢ M ≈ M' → extρ ρ ⊢ N ≈ N' → ρ ⊢ case L M N ≈ case L' M' N'
  prim≈ : ∀ {Γ Γ' p} {ρ : VM Γ Γ'} {L L' M M'} → ρ ⊢ L ≈ L' → ρ ⊢ M ≈ M' → ρ ⊢ prim p L M ≈ prim p L' M'
  let≈ : ∀ {Γ Γ' A B} {ρ : VM Γ Γ'} {M : Tm Γ A} {M'} {N : Tm (A ∷ Γ) B} {N'} → ρ ⊢ M ≈ M' → extρ ρ ⊢ N ≈ N'
    → ρ ⊢ let′ M N ≈ let′ M' N'
  fold≈ : ∀ {Γ Γ' A} {ρ : VM Γ Γ'} {M : Tm Γ (unroll A)} {M'} → ρ ⊢ M ≈ M' → ρ ⊢ fold {A = A} M ≈ fold M'
  unfold≈ : ∀ {Γ Γ' A} {ρ : VM Γ Γ'} {M : Tm Γ (μ A)} {M'} → ρ ⊢ M ≈ M' → ρ ⊢ unfold M ≈ unfold M'

data Caps ρ where
  [] : Caps ρ [] [] []
  keep : ∀ {Δ A fl} {M : Tm _ A} {M'} {Ms : All _ Δ} {Ms'} → ρ ⊢ M ≈ M' → Caps ρ fl Ms Ms' → Caps ρ (true ∷ fl) (M ∷ Ms) (M' ∷ Ms')
  drop : ∀ {Δ A fl} {M : Tm _ A} {Ms : All _ Δ} {Ms'} → VV M → Caps ρ fl Ms Ms' → Caps ρ (false ∷ fl) (M ∷ Ms) Ms'

{- The fundamental lemma ----------------------------------------------------------}

ρfl-kept : ∀ {Δ A C} (fl : Flags Δ) (x : (A ∷ Δ) ∋ C) (k : Kept fl x) → ρfl fl x ≡ just (squeeze fl x k)
ρfl-kept fl Z _ = refl
ρfl-kept fl (S i) k = cong (Mb.map S) (ρsq-kept fl i k)
  where ρsq-kept : ∀ {Δ C} (fl : Flags Δ) (i : Δ ∋ C) (k : T (lookup fl i)) → ρsq fl i ≡ just (sq fl i k)
        ρsq-kept (true ∷ fl) Z k = refl
        ρsq-kept (true ∷ fl) (S i) k = cong (Mb.map S) (ρsq-kept fl i k)
        ρsq-kept (false ∷ fl) (S i) k = ρsq-kept fl i k

Hyp : ∀ {Γ Γ'} (u : ∀ {C} → Γ ∋ C → Bool) → VM Γ Γ' → Ren u Γ' → Set
Hyp u ρ r = ∀ {C} (x : _ ∋ C) (t : T (u x)) → ρ x ≡ just (r x t)

opt≈ : ∀ {Γ Γ' A} {ρ : VM Γ Γ'} (M : Tm Γ A) {r : Ren (uses M) Γ'} → Hyp (uses M) ρ r → ρ ⊢ M ≈ opt M r
opts≈ : ∀ {Γ Γ' Δ} {ρ : VM Γ Γ'} (Ms : All (Tm Γ) Δ) {r : Ren (usesA Ms) Γ'} → Hyp (usesA Ms) ρ r → All₂ (ρ ⊢_≈_) Ms (opts Ms r)
caps≈ : ∀ {Γ Γ' Δ} {ρ : VM Γ Γ'} (u : ∀ {C} → Δ ∋ C → Bool) (Ms : All (Tm Γ) Δ) {r : Ren (usesA Ms) Γ'} → Hyp (usesA Ms) ρ r
  → Caps ρ (flags u Ms) Ms (select (flags u Ms) (opts Ms r))
under : ∀ {Γ Γ' B} {u : ∀ {C} → (B ∷ Γ) ∋ C → Bool} {ρ : VM Γ Γ'} {r : Ren (λ x → u (S x)) Γ'} → Hyp (λ x → u (S x)) ρ r → Hyp u (extρ ρ) (ext {u = u} r)
under h Z _ = refl
under h (S x) t rewrite h x t = refl
opt≈ (` x) h = var≈ (h x (fromWitness refl))
opt≈ (clos N Ms) h = clos≈ (keeps N Ms) (opt≈ N λ x t → ρfl-kept _ x (covers N Ms x t)) (caps≈ _ Ms h)
opt≈ (app L M) h = app≈ (opt≈ L λ x t → h x (∨-l _ t)) (opt≈ M λ x t → h x (∨-r (uses L x) t))
opt≈ (lit B c) h = lit≈
opt≈ (tuple Ms) h = tuple≈ (opts≈ Ms h)
opt≈ (get i M) h = get≈ (opt≈ M h)
opt≈ (inl M) h = inl≈ (opt≈ M h)
opt≈ (inr M) h = inr≈ (opt≈ M h)
opt≈ (case L M N) h = case≈ (opt≈ L λ x t → h x (∨-l _ t))
  (opt≈ M (under {u = uses M} λ x t → h x (∨-r (uses L x) (∨-l (uses N (S x)) t))))
  (opt≈ N (under {u = uses N} λ x t → h x (∨-r (uses L x) (∨-r (uses M (S x)) t))))
opt≈ (prim p L M) h = prim≈ (opt≈ L λ x t → h x (∨-l _ t)) (opt≈ M λ x t → h x (∨-r (uses L x) t))
opt≈ (let′ M N) h = let≈ (opt≈ M λ x t → h x (∨-l _ t)) (opt≈ N (under {u = uses N} λ x t → h x (∨-r (uses M x) t)))
opt≈ (fold M) h = fold≈ (opt≈ M h)
opt≈ (unfold M) h = unfold≈ (opt≈ M h)
opts≈ [] h = []
opts≈ (M ∷ Ms) h = opt≈ M (λ x t → h x (∨-l _ t)) ∷ opts≈ Ms λ x t → h x (∨-r (uses M x) t)
caps≈ u [] h = []
caps≈ u (M ∷ Ms) h with keep? M (u Z) | fl-ok M (u Z)
... | true | kept-fv = keep (opt≈ M λ x t → h x (∨-l _ t)) (caps≈ (λ i → u (S i)) Ms λ x t → h x (∨-r (uses M x) t))
... | false | var-fv = drop (var _) (caps≈ (λ i → u (S i)) Ms λ x t → h x (∨-r (uses M x) t))

{- Closure under substitution ------------------------------------------------------}

OK : ∀ {Γ Γ' Δ Δ'} (𝒦 : Kit) → VM Γ Γ' → VM Δ Δ' → T.Sub 𝒦 Γ Δ → T.Sub 𝒦 Γ' Δ' → Set
OK 𝒦 ρ ρ₂ σ τ = ∀ {A} (x : _ ∋ A) {y} → ρ x ≡ just y → ρ₂ ⊢ Kit.tm 𝒦 (σ x) ≈ Kit.tm 𝒦 (τ y)

VK : ∀ {Γ Δ} (𝒦 : Kit) → T.Sub 𝒦 Γ Δ → Set
VK 𝒦 σ = ∀ {A} (x : _ ∋ A) → VV (Kit.tm 𝒦 (σ x))

{- for a kit whose variable 0 is related to itself and is a variable or a
   value, and whose weakening keeps both -}
module Trav {𝒦}
  (rel-vr : ∀ {Γ Γ' B} {ρ : VM Γ Γ'} → extρ {B = B} ρ ⊢ Kit.tm 𝒦 (Kit.vr 𝒦 Z) ≈ Kit.tm 𝒦 (Kit.vr 𝒦 Z))
  (vv-vr : ∀ {Γ B} → VV {B ∷ Γ} (Kit.tm 𝒦 (Kit.vr 𝒦 Z)))
  (rel-wk : ∀ {Γ Γ' A B} {ρ : VM Γ Γ'} {a : Kit.K 𝒦 Γ A} {b} → ρ ⊢ Kit.tm 𝒦 a ≈ Kit.tm 𝒦 b
    → extρ {B = B} ρ ⊢ Kit.tm 𝒦 (Kit.wk 𝒦 a) ≈ Kit.tm 𝒦 (Kit.wk 𝒦 b))
  (vv-wk : ∀ {Γ A B} {a : Kit.K 𝒦 Γ A} → VV (Kit.tm 𝒦 a) → VV (Kit.tm 𝒦 (Kit.wk 𝒦 {B = B} a))) where

  ok-ext : ∀ {Γ Γ' Δ Δ' B} {ρ : VM Γ Γ'} {ρ₂ : VM Δ Δ'} {σ : T.Sub 𝒦 Γ Δ} {τ : T.Sub 𝒦 Γ' Δ'} → OK 𝒦 ρ ρ₂ σ τ
    → OK 𝒦 (extρ {B = B} ρ) (extρ ρ₂) (T.exts 𝒦 σ) (T.exts 𝒦 τ)
  ok-ext ok Z refl = rel-vr
  ok-ext {ρ = ρ} ok (S x) e with ρ x in eq | e
  ... | just y | refl = rel-wk (ok x eq)

  vv-ext : ∀ {Γ Δ B} {σ : T.Sub 𝒦 Γ Δ} → VK 𝒦 σ → VK 𝒦 (T.exts 𝒦 {B = B} σ)
  vv-ext h Z = vv-vr
  vv-ext h (S x) = vv-wk (h x)

  ≈-trav : ∀ {Γ Γ' Δ Δ' A} {ρ : VM Γ Γ'} {ρ₂ : VM Δ Δ'} {σ : T.Sub 𝒦 Γ Δ} {τ : T.Sub 𝒦 Γ' Δ'} {M : Tm Γ A} {M'} → ρ ⊢ M ≈ M'
    → OK 𝒦 ρ ρ₂ σ τ → VK 𝒦 σ → ρ₂ ⊢ trav 𝒦 σ M ≈ trav 𝒦 τ M'
  ≈-travs : ∀ {Γ Γ' Δ Δ' Θ} {ρ : VM Γ Γ'} {ρ₂ : VM Δ Δ'} {σ : T.Sub 𝒦 Γ Δ} {τ : T.Sub 𝒦 Γ' Δ'} {Ms : All (Tm Γ) Θ} {Ms'} → All₂ (ρ ⊢_≈_) Ms Ms'
    → OK 𝒦 ρ ρ₂ σ τ → VK 𝒦 σ → All₂ (ρ₂ ⊢_≈_) (travs 𝒦 σ Ms) (travs 𝒦 τ Ms')
  caps-trav : ∀ {Γ Γ' Δ Δ' Θ} {ρ : VM Γ Γ'} {ρ₂ : VM Δ Δ'} {σ : T.Sub 𝒦 Γ Δ} {τ : T.Sub 𝒦 Γ' Δ'} {fl : Flags Θ} {Ms Ms'} → Caps ρ fl Ms Ms'
    → OK 𝒦 ρ ρ₂ σ τ → VK 𝒦 σ → Caps ρ₂ fl (travs 𝒦 σ Ms) (travs 𝒦 τ Ms')
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
  ≈-trav (fold≈ r) ok vv = fold≈ (≈-trav r ok vv)
  ≈-trav (unfold≈ r) ok vv = unfold≈ (≈-trav r ok vv)
  ≈-travs [] ok vv = []
  ≈-travs (r ∷ rs) ok vv = ≈-trav r ok vv ∷ ≈-travs rs ok vv
  caps-trav [] ok vv = []
  caps-trav (keep r cs) ok vv = keep (≈-trav r ok vv) (caps-trav cs ok vv)
  caps-trav (drop (var x) cs) ok vv = drop (vv x) (caps-trav cs ok vv)
  caps-trav (drop (val v) cs) ok vv = drop (val (T.value-trav v)) (caps-trav cs ok vv)

module RenT = Trav {varK} (var≈ refl) (var _) (λ { (var≈ e) → var≈ (cong (Mb.map S) e) }) (λ _ → var _)
module SubT = Trav {tmK} (var≈ refl) (var _) (λ r → RenT.≈-trav r (λ _ e → var≈ (cong (Mb.map S) e)) (λ _ → var _)) vv-wk

{- The simulation ----------------------------------------------------------------------}

ρ₀ : VM [] []
ρ₀ ()

R : ∀ {A} → Tm [] A → Tm [] A → Set
R = ρ₀ ⊢_≈_

Ans′ : ∀ {A} → Tm [] A → Red (Tm [] A) → Tm [] A → Set
Ans′ = Ans T.red Value R

{- a closed variable or value is a value -}

{- the source of a value is a value -}
≈-value : ∀ {A} {V V' : Tm [] A} → R V V' → Value V' → Value V
≈-values : ∀ {Δ} {Vs Vs' : All (Tm []) Δ} → All₂ R Vs Vs' → Each Value Vs' → Each Value Vs
caps-values : ∀ {Δ} {fl : Flags Δ} {Vs Vs'} → Caps ρ₀ fl Vs Vs' → Each Value Vs' → Each Value Vs
≈-value (clos≈ fl n cs) (T.clos vs) = T.clos (caps-values cs vs)
≈-value lit≈ T.lit = T.lit
≈-value (tuple≈ rs) (T.tuple vs) = T.tuple (≈-values rs vs)
≈-value (inl≈ r) (T.inl v) = T.inl (≈-value r v)
≈-value (inr≈ r) (T.inr v) = T.inr (≈-value r v)
≈-value (fold≈ r) (T.fold v) = T.fold (≈-value r v)
≈-values [] [] = []
≈-values (r ∷ rs) (v ∷ vs) = ≈-value r v ∷ ≈-values rs vs
caps-values [] [] = []
caps-values (keep r cs) (v ∷ vs) = ≈-value r v ∷ caps-values cs vs
caps-values (drop vv cs) vs = vv-value vv ∷ caps-values cs vs

{- the variables of the code of related closures, applied to related values -}
caps-lookup : ∀ {Δ A} {fl : Flags Δ} {Vs Vs'} {W W' : Tm [] A} → Caps ρ₀ fl Vs Vs' → R W W'
  → OK tmK (ρfl fl) ρ₀ (W T.• lookup Vs) (W' T.• lookup Vs')
caps-lookup cs m Z refl = m
caps-lookup {fl = fl} cs m (S i) e with ρsq fl i in eq | e
... | just y | refl = go cs i eq
  where go : ∀ {Δ C} {fl : Flags Δ} {Vs Vs'} → Caps ρ₀ fl Vs Vs' → (i : Δ ∋ C) {y : _ ∋ C}
          → ρsq fl i ≡ just y → R (lookup Vs i) (lookup Vs' y)
        go (keep r cs) Z refl = r
        go {fl = true ∷ fl} (keep r cs) (S i) e with ρsq fl i in eq | e
        ... | just y | refl = go cs i eq
        go (drop vv cs) (S i) e = go cs i e

obs≈ : ∀ {A} {V : Tm [] A} {V'} → R V V' → Value V' → T.obs V ≡ T.obs V'
obss≈ : ∀ {Δ} {Vs : All (Tm []) Δ} {Vs'} → All₂ R Vs Vs' → Each Value Vs' → T.obss Vs ≡ T.obss Vs'
obs≈ (clos≈ _ _ _) _ = refl
obs≈ lit≈ _ = refl
obs≈ (tuple≈ rs) (T.tuple vs) = cong o-tuple (obss≈ rs vs)
obs≈ (inl≈ r) (T.inl v) = cong o-inl (obs≈ r v)
obs≈ (inr≈ r) (T.inr v) = cong o-inr (obs≈ r v)
obs≈ (fold≈ r) (T.fold v) = obs≈ r v
obss≈ [] [] = refl
obss≈ (r ∷ rs) (v ∷ vs) = cong₂ _∷_ (obs≈ r v) (obss≈ rs vs)

out≈ : ∀ p n m → R (T.out p n m) (T.out p n m)
out≈ P.sub n m = lit≈
out≈ P.eq n m with does (n Z.≟ m)
... | true = inl≈ (tuple≈ [])
... | false = inr≈ (tuple≈ [])

{- substituting a value for the variable of a binder -}
≈-[] : ∀ {A B} {N N' : Tm (A ∷ []) B} {V V'} → extρ ρ₀ ⊢ N ≈ N' → R V V' → Value V → R (N T.[ V ]) (N' T.[ V' ])
≈-[] n m v = SubT.≈-trav n (λ { Z refl → m }) (λ { Z → val v })

sim : ∀ {A} {M M' : Tm [] A} → R M M' → Ans′ M (T.red M) M'
sims : ∀ {Δ} {Ms Ms' : All (Tm []) Δ} → All₂ R Ms Ms' → Ans T.reds (Each Value) (All₂ R) Ms (T.reds Ms) Ms'
caps-sim : ∀ {Δ} {fl : Flags Δ} {Ms Ms'} → Caps ρ₀ fl Ms Ms' → Ans T.reds (Each Value) (Caps ρ₀ fl) Ms (T.reds Ms) Ms'
sim (clos≈ fl n cs) = ans-in (frame _ λ _ → refl) (clos≈ fl n) (caps-sim cs) λ vs ms → val ε (T.clos vs) (clos≈ fl n ms)
sim (app≈ r s) =
  ans-in (frame _ λ _ → refl) (λ m → app≈ m s) (sim r)
    λ v m → ans-in (frame {g = app _} _ λ _ → val-in (value-red v)) (app≈ m) (sim s)
      λ { w m' → β-sim v m w m' }
  where
  β-sim : ∀ {A B} {V V' : Tm [] (A ⇒ B)} {W W'} → Value V' → R V V' → Value W' → R W W'
    → Ans′ (app V W) (T.β V refl W) (app V' W')
  β-sim (T.clos vs) (clos≈ fl n cs) w m' =
    to (one (trans (val-in (value-red (T.clos vs))) (val-in (value-red w))))
       (SubT.≈-trav n (caps-lookup cs m')
          λ { Z → val (≈-value m' w) ; (S i) → val (each-lookup (caps-values cs vs) i) })
sim lit≈ = val ε T.lit lit≈
sim (tuple≈ rs) = ans-in (frame _ λ _ → refl) tuple≈ (sims rs) λ vs ms → val ε (T.tuple vs) (tuple≈ ms)
sim (get≈ {i = i} r) = ans-in (frame _ λ _ → refl) get≈ (sim r)
  λ { (T.tuple vs) (tuple≈ ms) → to (one (val-in (value-red (T.tuple vs)))) (lookup₂ ms i) }
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
sim (fold≈ r) = ans-in (frame _ λ _ → refl) fold≈ (sim r) λ v m → val ε (T.fold v) (fold≈ m)
sim (unfold≈ r) = ans-in (frame _ λ _ → refl) unfold≈ (sim r)
  λ { (T.fold v) (fold≈ m) → to (one (val-in (value-red (T.fold v)))) m }
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

optimize-correct : ∀ {A} (M : Tm [] A) → Equivalent (T.sem M) (T.sem (optimize-program M))
optimize-correct M = red-equivalent value-red R sim (λ m _ → obs≈ m) (opt≈ M λ ())

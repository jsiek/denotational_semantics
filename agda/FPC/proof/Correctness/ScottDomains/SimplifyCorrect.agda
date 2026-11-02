{-

  Correctness of the simplify pass (FPC → FPC) in Scott domains
  (Mu/Semantics/ScottDomains/FPC.agda), as in the graph model
  (Mu/proof/Correctness/GraphModel/SimplifyCorrect.agda), with equality of
  values in place of equality of sets.

  The main lemma (simp-ok): if what simp knows of each variable x is true
  of the source's environment γ in the target's γ' (Desc: γ x is denoted
  in γ' by the term that replaces x, and by what x is known to be), then
  what simp E M says of M is true. A known function λ N denotes
  ⟦ λ N ⟧ γf for a source environment γf of which its Facts are true
  (KDesc), so an inlined call is a call of ⟦ λ N ⟧ γf: β and inlining
  share let-ok.

  The transformations rest on β for a value: a function value applied to
  a defined argument d means its body at d (app-Λ-defined), and so does
  a case of an injection of d. A value denotes a defined element in an
  environment that is defined (sv-defined), so only the target's
  environment need be defined; consistency is not needed. Fold and
  unfold are the identity, so an unfold of a known fold V denotes V.

  What differs in the proof's structure: the graph proof's tests by
  `with` inside the recursive lemmas (simp-app, simp-let, simp-call,
  simp-case) are, here, auxiliary lemmas that take the test's result as
  an argument, with the result of the pass stated by a copy of its
  clauses (app-res, let-res, call-res, case-res) that agrees with it
  (app-eq, ...), proved by `with` on syntax only; the lemmas on known
  values (get-ok, prim-ok, unfold-ok) do the same, outside the
  recursion. (A `with` while values of 𝔻 or environments are in scope
  is very slow to check: get-ok by `with`, as in the graph model, does
  not check in 45 minutes, and neither does a `with` on simp-get whose
  Desc is about a variable, in 4 minutes.) kfun states D ＝ ⟦ L ⟧ γ
  for a term L ≡ λ N: with D ＝ ⟦ λ N ⟧ γ, as in the graph model, the
  module does not check in 6 minutes.

-}

open import MLTT.Spartan hiding (inl; inr; cases; _+_)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons
open import UF.Base using (ap₂; happly)

open import Framework.Primitives using (Int)
import Language.Prim as Pr
open import Mu.Language.Type
open import Mu.Language.FPC
open import Mu.Language.FPCSubst using (ren; exts; varK; travs)
open import Mu.Framework.AllUtil using (All; []; _∷_; lookup; pos)
open import Mu.proof.Compiler.SimplifyFacts as P
  using (Info; _∣_; term; known; Known; val; fun; Facts; self; info; under; known-as; shift-info; shift-known;
         simp; simps; simp-app; Lam?; lam?; is-lam; other; simp-call; simp-let; size; inline-size; inline-fuel;
         simp-get; simp-case; simp-prim; simp-unfold; simplify; small; value; component; branch; unfolded; int-of;
         prim-term; SV; SVs; value-sv; small-sv; sv-ren; prim-term-sv; svs-lookup; int-inv; comp-inv;
         branch-inl; branch-inr; unfold-inv)
open import Framework.abt.GSubst using (_•_)

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Fin using (Fin; zero; suc)
open import Data.Integer using (ℤ; _≟_)
open import Data.List using (List; []; _∷_; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (_≤ᵇ_)
import Data.Product as DP
open DP using () renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Relation.Nullary using (does)

module Mu.proof.Correctness.ScottDomains.SimplifyCorrect
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : propext 𝓤₀)
       where

open import Framework.Scott.Base pt fe
open import proof.Framework.Scott.Ops pt fe pe hiding (component; branch; case; unroll) renaming (app to appᵈ; inl to inlᵈ; inr to inrᵈ; tuple to tupleᵈ)
open import proof.Framework.Scott.Semantics pt fe pe
open import Semantics.Scott.Prim pt fe pe using (primD; out)
open import Mu.Semantics.ScottDomains.FPC pt fe pe

{- Renaming ---------------------------------------------------------------------}

ren-＝ : ∀ {Γ Δ A} (r : ∀ {B} → Γ ∋ B → Δ ∋ B) (M : Tm Γ A) {ρ ρ' : ⟨ Env ⟩}
  → (∀ {B} (x : Γ ∋ B) → ρ' (idx (r x)) ＝ ρ (idx x)) → ⟦ ren r M ⟧ · ρ' ＝ ⟦ M ⟧ · ρ
rens-nth : ∀ {Γ Δ Δ'} (r : ∀ {B} → Γ ∋ B → Δ ∋ B) (Ms : All (Tm Γ) Δ') {ρ ρ' : ⟨ Env ⟩}
  → (∀ {B} (x : Γ ∋ B) → ρ' (idx (r x)) ＝ ρ (idx x)) → ∀ i → (⟦ travs varK r Ms ⟧s · ρ') i ＝ (⟦ Ms ⟧s · ρ) i
ren-ext : ∀ {Γ Δ C} (r : ∀ {B} → Γ ∋ B → Δ ∋ B) {ρ ρ' : ⟨ Env ⟩} {d : ⟨ 𝔻 ⟩} → (∀ {B} (x : Γ ∋ B) → ρ' (idx (r x)) ＝ ρ (idx x))
  → ∀ {B} (x : (C ∷ Γ) ∋ B) → (d • ρ') (idx (exts varK r x)) ＝ (d • ρ) (idx x)
ren-ext r h Z = refl
ren-ext r h (S x) = h x
ren-＝ r (` x) h = h x
ren-＝ r (lam N) {ρ} {ρ'} h = lamᶜ-cong ⟦ ren (exts varK r) N ⟧ ⟦ N ⟧ ρ' ρ (λ d _ → ren-＝ (exts varK r) N (ren-ext r h))
ren-＝ r (app L M) h = ap₂ (λ a b → appᵈ · a · b) (ren-＝ r L h) (ren-＝ r M h)
ren-＝ r (lit B c) h = refl
ren-＝ r (tuple {Δ} Ms) h = ap (tupleᵈ (length Δ) ·_) (dfunext fe (rens-nth r Ms h))
ren-＝ r (get i M) h = ap (proj (pos i) ·_) (ren-＝ r M h)
ren-＝ r (inl M) h = ap (inlᵈ ·_) (ren-＝ r M h)
ren-＝ r (inr M) h = ap (inrᵈ ·_) (ren-＝ r M h)
ren-＝ r (case L M N) {ρ} {ρ'} h =
  caseᶜ-cong ⟦ ren r L ⟧ ⟦ L ⟧ ⟦ ren (exts varK r) M ⟧ ⟦ M ⟧ ⟦ ren (exts varK r) N ⟧ ⟦ N ⟧ ρ' ρ (ren-＝ r L h)
    (λ d _ → ren-＝ (exts varK r) M (ren-ext r h)) (λ d _ → ren-＝ (exts varK r) N (ren-ext r h))
ren-＝ r (prim p L M) h = ap₂ (λ a b → primD p · a · b) (ren-＝ r L h) (ren-＝ r M h)
ren-＝ r (let′ M N) {ρ} {ρ'} h =
  letᶜ-cong ⟦ ren r M ⟧ ⟦ M ⟧ ⟦ ren (exts varK r) N ⟧ ⟦ N ⟧ ρ' ρ (ren-＝ r M h) (λ d _ → ren-＝ (exts varK r) N (ren-ext r h))
ren-＝ r (fold M) h = ren-＝ r M h
ren-＝ r (unfold M) h = ren-＝ r M h
rens-nth r (M ∷ Ms) h zero = ren-＝ r M h
rens-nth r (M ∷ Ms) h (suc i) = rens-nth r Ms h i

shift-＝ : ∀ {Γ A B} (M : Tm Γ A) (d : ⟨ 𝔻 ⟩) (γ : ⟨ Env ⟩) → ⟦ ren (S {b = B}) M ⟧ · (d • γ) ＝ ⟦ M ⟧ · γ
shift-＝ M d γ = ren-＝ S M (λ x → refl)

{- β for a defined value -}
let-β : (N : Den Env) (γ : ⟨ Env ⟩) (d : ⟨ 𝔻 ⟩) → defined d → appᵈ · (lamᶜ N · γ) · d ＝ N · (d • γ)
let-β N γ d p = app-Λ-defined (abs N · γ) d p

{- What simp knows, and what it means ----------------------------------------}

{- I is true of D in γ': its term denotes D, and so does what it is known
   to be (KDesc): a value, or a function λ N closed in a source
   environment γ of which its Facts are true -}
record Desc {Γ A} (D : ⟨ 𝔻 ⟩) (I : Info Γ A) (γ' : ⟨ Env ⟩) : 𝓤₁ ̇
data KDesc {Γ} (D : ⟨ 𝔻 ⟩) : ∀ {A} → Known Γ A → ⟨ Env ⟩ → 𝓤₁ ̇

Ok : ∀ {Δ Γ} → Facts Δ Γ → ⟨ Env ⟩ → ⟨ Env ⟩ → 𝓤₁ ̇
Ok {Δ} E γ γ' = ∀ {A} (x : Δ ∋ A) → Desc (γ (idx x)) (E x) γ'

record Desc D I γ' where
  inductive
  constructor desc
  field
    tm : D ＝ ⟦ term I ⟧ · γ'
    kn : ∀ {K} → known I ≡ just K → KDesc D K γ'
open Desc

data KDesc {Γ} D where
  kval : ∀ {A} {K : Tm Γ A} {γ'} → SV K → D ＝ ⟦ K ⟧ · γ' → KDesc D (val K) γ'
  kfun : ∀ {Δ A B} {N : Tm (A ∷ Δ) B} {E : Facts Δ Γ} {γ'} (γ : ⟨ Env ⟩) (L : Tm Δ (A ⇒ B)) → L ≡ lam N → Ok E γ γ' → D ＝ ⟦ L ⟧ · γ
    → KDesc D (fun N E) γ'

kv : ∀ {Γ A D} {K : Tm Γ A} {γ'} → KDesc D (val K) γ' → SV K × (D ＝ ⟦ K ⟧ · γ')
kv (kval v eq) = v , eq

kdesc-＝ : ∀ {Γ A} (K : Known Γ A) {D D' : ⟨ 𝔻 ⟩} {γ'} → KDesc D K γ' → D' ＝ D → KDesc D' K γ'
kdesc-＝ (val K) (kval v K＝) eq = kval v (eq ∙ K＝)
kdesc-＝ (fun N E) (kfun γ L e ok F＝) eq = kfun γ L e ok (eq ∙ F＝)

desc-＝ : ∀ {Γ A} {D D' : ⟨ 𝔻 ⟩} {I : Info Γ A} {γ'} → Desc D I γ' → D' ＝ D → Desc D' I γ'
desc-＝ d eq = desc (eq ∙ tm d) (λ e → kdesc-＝ _ (kn d e) eq)

desc-self : ∀ {Γ A} {D : ⟨ 𝔻 ⟩} {V : Tm Γ A} {γ'} → SV V → D ＝ ⟦ V ⟧ · γ' → Desc D (self V) γ'
desc-self v eq = desc eq (λ { Eq.refl → kval v eq })

desc-info : ∀ {Γ A} {D : ⟨ 𝔻 ⟩} {M : Tm Γ A} {γ'} → D ＝ ⟦ M ⟧ · γ' → Desc D (info M) γ'
desc-info {Γ} {A} {D} {M} {γ'} eq = desc eq (info-kn (value M) Eq.refl)
  where
  info-kn : ∀ (b : Bool) → value M ≡ b → ∀ {K} → (if b then just (val M) else nothing) ≡ just K → KDesc D K γ'
  info-kn true e Eq.refl = kval (value-sv M e) eq
  info-kn false e ()

{- under one more binder, in the target -}
desc-shift : ∀ {Γ A B} (I : Info Γ A) {D : ⟨ 𝔻 ⟩} {γ'} (X : ⟨ 𝔻 ⟩) → Desc D I γ' → Desc D (shift-info {B = B} I) (X • γ')
kdesc-shift : ∀ {Γ A B} (K : Known Γ A) {D : ⟨ 𝔻 ⟩} {γ'} (X : ⟨ 𝔻 ⟩) → KDesc D K γ' → KDesc D (shift-known {B = B} K) (X • γ')
desc-shift (M ∣ nothing) {γ' = γ'} X d = desc (tm d ∙ (shift-＝ M X γ' ⁻¹)) (λ ())
desc-shift (M ∣ just K) {γ' = γ'} X d = desc (tm d ∙ (shift-＝ M X γ' ⁻¹)) (λ { Eq.refl → kdesc-shift K X (kn d Eq.refl) })
kdesc-shift (val K) {γ' = γ'} X (kval v K＝) = kval (sv-ren S v) (K＝ ∙ (shift-＝ K X γ' ⁻¹))
kdesc-shift (fun N E) X (kfun γ L e ok F＝) = kfun γ L e (λ x → desc-shift (E x) X (ok x)) F＝

ok-under : ∀ {Δ Γ B} {E : Facts Δ Γ} {γ γ' : ⟨ Env ⟩} (X : ⟨ 𝔻 ⟩) → Ok E γ γ' → Ok (under {B = B} E) (X • γ) (X • γ')
ok-under X ok Z = desc-self (P.var Z) refl
ok-under {E = E} X ok (S x) = desc-shift (E x) X (ok x)

ok-• : ∀ {Δ Γ B} {E : Facts Δ Γ} {I : Info Γ B} {γ γ' : ⟨ Env ⟩} {D : ⟨ 𝔻 ⟩} → Desc D I γ' → Ok E γ γ' → Ok (I P.• E) (D • γ) γ'
ok-• d ok Z = d
ok-• d ok (S x) = ok x

ok-known-as : ∀ {Δ Γ B} {E : Facts Δ Γ} (I : Info Γ B) {γ γ' : ⟨ Env ⟩} {D : ⟨ 𝔻 ⟩} (V : ⟨ 𝔻 ⟩) → D ＝ V → Desc D I γ' → Ok E γ γ'
  → Ok (known-as I E) (D • γ) (V • γ')
ok-known-as I V eq d ok Z = desc eq (kn (desc-shift I V d))
ok-known-as {E = E} I V eq d ok (S x) = desc-shift (E x) V (ok x)

{- Values denote defined elements ------------------------------------------------}

sv-defined : ∀ {Γ A} {V : Tm Γ A} {γ : ⟨ Env ⟩} → SV V → defined-env γ → defined (⟦ V ⟧ · γ)
svs-defined : ∀ {Γ Δ} {Ms : All (Tm Γ) Δ} {γ : ⟨ Env ⟩} → SVs Ms → defined-env γ → ∀ i → defined ((⟦ Ms ⟧s · γ) i)
sv-defined (P.var x) ne = ne (idx x)
sv-defined {V = lam N} {γ} P.lam ne = Λ-defined (abs ⟦ N ⟧ · γ)
sv-defined (P.lit {B} {c}) ne = const-defined B c
sv-defined {V = tuple {Δ} Ms} {γ} (P.tuple vs) ne = tuple-defined (length Δ) (⟦ Ms ⟧s · γ) (svs-defined vs ne)
sv-defined {V = inl M} {γ} (P.inl v) ne = inl-defined (⟦ M ⟧ · γ) (sv-defined v ne)
sv-defined {V = inr M} {γ} (P.inr v) ne = inr-defined (⟦ M ⟧ · γ) (sv-defined v ne)
sv-defined (P.fold v) ne = sv-defined v ne
svs-defined (v P.∷ vs) ne zero = sv-defined v ne
svs-defined (v P.∷ vs) ne (suc i) = svs-defined vs ne i

{- Known tuples, integers and folds -----------------------------------------------}

nth-lookup : ∀ {Γ Δ A} (Ks : All (Tm Γ) Δ) (i : Δ ∋ A) (γ : ⟨ Env ⟩) → (⟦ Ks ⟧s · γ) (pos i) ＝ ⟦ lookup Ks i ⟧ · γ
nth-lookup (K ∷ Ks) Z γ = refl
nth-lookup (K ∷ Ks) (S i) γ = nth-lookup Ks i γ

tuple-sv : ∀ {Γ Δ} {Ks : All (Tm Γ) Δ} → SV (tuple Ks) → SVs Ks
tuple-sv (P.tuple vs) = vs

{- a known value, inspected: its term T, or K itself if K is small -}
known-small : ∀ {Γ A} (K T : Tm Γ A) {D γ'} → D ＝ ⟦ T ⟧ · γ' → SV K → D ＝ ⟦ K ⟧ · γ'
  → (b : Bool) → Desc D (if b then self K else (T ∣ just (val K))) γ'
known-small K T T＝ v K＝ true = desc-self v K＝
known-small K T T＝ v K＝ false = desc T＝ (λ { Eq.refl → kval v K＝ })

{- a component of a known tuple -}
component-ok : ∀ {Γ Δ A} (i : Δ ∋ A) (k : Maybe (Known Γ (tup Δ))) {K γ' D} → defined-env γ'
  → (∀ {Kt} → k ≡ just Kt → KDesc D Kt γ')
  → DP.Σ (All (Tm Γ) Δ) (λ Ks → (k ≡ just (val (tuple Ks))) DP.× (lookup Ks i ≡ K))
  → SV K × (proj (pos i) · D ＝ ⟦ K ⟧ · γ')
component-ok {Δ = Δ} i k {γ' = γ'} ne h ⟨ Ks , ⟨ Eq.refl , Eq.refl ⟩ ⟩ =
  svs-lookup vs i ,
  (ap (proj (pos i) ·_) (pr₂ c) ∙ proj-tuple (length Δ) (⟦ Ks ⟧s · γ') (svs-defined vs ne) (pos i) ∙ nth-lookup Ks i γ')
  where
  c = kv (h Eq.refl)
  vs = tuple-sv (pr₁ c)

get-res : ∀ {Γ Δ A} → Δ ∋ A → Info Γ (tup Δ) → Maybe (Tm Γ A) → Info Γ A
get-res i I (just K) = if small K then self K else (get i (term I) ∣ just (val K))
get-res i I nothing = get i (term I) ∣ nothing

get-eq : ∀ {Γ Δ A} (i : Δ ∋ A) (I : Info Γ (tup Δ)) → simp-get i I ≡ get-res i I (component i (known I) Eq.refl)
get-eq i I with component i (known I) Eq.refl
... | just K = Eq.refl
... | nothing = Eq.refl

get-ok-aux : ∀ {Γ Δ A} (i : Δ ∋ A) (I : Info Γ (tup Δ)) {γ' D} → defined-env γ' → Desc D I γ'
  → (c : Maybe (Tm Γ A)) → component i (known I) Eq.refl ≡ c → Desc (proj (pos i) · D) (get-res i I c) γ'
get-ok-aux i I ne d nothing e = desc (ap (proj (pos i) ·_) (tm d)) (λ ())
get-ok-aux i I ne d (just K) e = known-small K (get i (term I)) (ap (proj (pos i) ·_) (tm d)) (pr₁ c) (pr₂ c) (small K)
  where c = component-ok i (known I) ne (kn d) (comp-inv i (known I) Eq.refl e)

get-ok : ∀ {Γ Δ A} (i : Δ ∋ A) (I : Info Γ (tup Δ)) {γ' D} → defined-env γ' → Desc D I γ' → Desc (proj (pos i) · D) (simp-get i I) γ'
get-ok i I {γ'} {D} ne d =
  Eq.subst (λ J → Desc (proj (pos i) · D) J γ') (Eq.sym (get-eq i I)) (get-ok-aux i I ne d (component i (known I) Eq.refl) Eq.refl)

{- a known integer -}
int-ok : ∀ {Γ} (k : Maybe (Known Γ (base Int))) {n γ' D} → (∀ {K} → k ≡ just K → KDesc D K γ')
  → DP.Σ (base Int ≡ base Int) (λ e → k ≡ just (val (Eq.subst (Tm Γ) e (lit Int n)))) → D ＝ const Int n
int-ok k h ⟨ Eq.refl , Eq.refl ⟩ = pr₂ (kv (h Eq.refl))

{- the result of a primitive -}
prim-eq-＝ : ∀ {Γ} (b : Bool) (γ : ⟨ Env ⟩)
  → out (Pr.bool b) ＝ ⟦ (if b then inl {Γ} {B = tup []} (tuple []) else inr (tuple [])) ⟧ · γ
prim-eq-＝ true γ = ap (λ - → inlᵈ · (tupleᵈ 0 · -)) (dfunext fe (λ ()))
prim-eq-＝ false γ = ap (λ - → inrᵈ · (tupleᵈ 0 · -)) (dfunext fe (λ ()))

prim-term-＝ : ∀ {Γ} p n m (γ : ⟨ Env ⟩) → out (Pr.δ p n m) ＝ ⟦ prim-term {Γ} p n m ⟧ · γ
prim-term-＝ Pr.sub n m γ = refl
prim-term-＝ Pr.eq n m γ = prim-eq-＝ (does (n ≟ m)) γ

prim-res : ∀ {Γ} p → Info Γ (base Int) → Info Γ (base Int) → Maybe ℤ → Maybe ℤ → Info Γ (out-ty p)
prim-res p I J (just n) (just m) = self (prim-term p n m)
prim-res p I J (just n) nothing = prim p (term I) (term J) ∣ nothing
prim-res p I J nothing _ = prim p (term I) (term J) ∣ nothing

prim-eq : ∀ {Γ} p (I J : Info Γ (base Int)) → simp-prim p I J ≡ prim-res p I J (int-of (known I)) (int-of (known J))
prim-eq p I J with int-of (known I)
... | nothing = Eq.refl
... | just n with int-of (known J)
...   | nothing = Eq.refl
...   | just m = Eq.refl

prim-ok-aux : ∀ {Γ} p (I J : Info Γ (base Int)) {γ' DI DJ} → Desc DI I γ' → Desc DJ J γ'
  → (a b : Maybe ℤ) → int-of (known I) ≡ a → int-of (known J) ≡ b → Desc (primD p · DI · DJ) (prim-res p I J a b) γ'
prim-ok-aux p I J {γ'} dI dJ (just n) (just m) e₁ e₂ =
  desc-self (prim-term-sv p n m)
    (ap₂ (λ a b → primD p · a · b) (int-ok (known I) (kn dI) (int-inv (known I) e₁)) (int-ok (known J) (kn dJ) (int-inv (known J) e₂))
     ∙ primD-const p n m ∙ prim-term-＝ p n m γ')
prim-ok-aux p I J dI dJ (just n) nothing e₁ e₂ = desc (ap₂ (λ a b → primD p · a · b) (tm dI) (tm dJ)) (λ ())
prim-ok-aux p I J dI dJ nothing b e₁ e₂ = desc (ap₂ (λ a b → primD p · a · b) (tm dI) (tm dJ)) (λ ())

prim-ok : ∀ {Γ} p (I J : Info Γ (base Int)) {γ' DI DJ} → Desc DI I γ' → Desc DJ J γ' → Desc (primD p · DI · DJ) (simp-prim p I J) γ'
prim-ok p I J {γ'} {DI} {DJ} dI dJ =
  Eq.subst (λ R → Desc (primD p · DI · DJ) R γ') (Eq.sym (prim-eq p I J))
    (prim-ok-aux p I J dI dJ (int-of (known I)) (int-of (known J)) Eq.refl Eq.refl)

{- a known fold -}
fold-sv : ∀ {Γ A} {K : Tm Γ (unroll A)} → SV (fold {A = A} K) → SV K
fold-sv (P.fold v) = v

unfold-res : ∀ {Γ A} → Info Γ (μ A) → Maybe (Tm Γ (unroll A)) → Info Γ (unroll A)
unfold-res I (just K) = if small K then self K else (unfold (term I) ∣ just (val K))
unfold-res I nothing = unfold (term I) ∣ nothing

unfold-eq : ∀ {Γ A} (I : Info Γ (μ A)) → simp-unfold I ≡ unfold-res I (unfolded (known I) Eq.refl)
unfold-eq I with unfolded (known I) Eq.refl
... | just K = Eq.refl
... | nothing = Eq.refl

unfold-ok-aux : ∀ {Γ A} (I : Info Γ (μ A)) {γ' D} → Desc D I γ'
  → (u : Maybe (Tm Γ (unroll A))) → unfolded (known I) Eq.refl ≡ u → Desc D (unfold-res I u) γ'
unfold-ok-aux I d nothing e = desc (tm d) (λ ())
unfold-ok-aux I d (just K) e = known-small K (unfold (term I)) (tm d) (fold-sv (pr₁ c)) (pr₂ c) (small K)
  where c = kv (kn d (unfold-inv (known I) Eq.refl e))

unfold-ok : ∀ {Γ A} (I : Info Γ (μ A)) {γ' D} → Desc D I γ' → Desc D (simp-unfold I) γ'
unfold-ok I {γ'} {D} d =
  Eq.subst (λ J → Desc D J γ') (Eq.sym (unfold-eq I)) (unfold-ok-aux I d (unfolded (known I) Eq.refl) Eq.refl)

{- a known injection: the value it injects -}
inl-sv : ∀ {Γ A B} {K : Tm Γ A} → SV (inl {B = B} K) → SV K
inl-sv (P.inl v) = v

inr-sv : ∀ {Γ A B} {K : Tm Γ B} → SV (inr {A = A} K) → SV K
inr-sv (P.inr v) = v

branch-inl-ok : ∀ {Γ A B} (I : Info Γ (A ⊹ B)) {K γ' D} → branch (known I) Eq.refl ≡ just (inj₁ K)
  → Desc D I γ' → SV K × (D ＝ inlᵈ · (⟦ K ⟧ · γ'))
branch-inl-ok I e d = inl-sv (pr₁ c) , pr₂ c
  where c = kv (kn d (DP.proj₁ (branch-inl (known I) Eq.refl e)))

branch-inr-ok : ∀ {Γ A B} (I : Info Γ (A ⊹ B)) {K γ' D} → branch (known I) Eq.refl ≡ just (inj₂ K)
  → Desc D I γ' → SV K × (D ＝ inrᵈ · (⟦ K ⟧ · γ'))
branch-inr-ok I e d = inr-sv (pr₁ c) , pr₂ c
  where c = kv (kn d (DP.proj₁ (branch-inr (known I) Eq.refl e)))

{- The tests of the pass, by their results ----------------------------------------}

app-res : ∀ {Δ Γ A B} → ℕ → Facts Δ Γ → (L : Tm Δ (A ⇒ B)) → Info Γ A → Lam? L → Info Γ B
app-res f E .(lam N) I (is-lam N) = simp-let f E N I
app-res f E L I other = simp-call f (simp f E L) I

app-eq : ∀ {Δ Γ A B} f (E : Facts Δ Γ) (L : Tm Δ (A ⇒ B)) I → simp-app f E L I ≡ app-res f E L I (lam? L)
app-eq f E L I with lam? L
... | is-lam N = Eq.refl
... | other = Eq.refl

call-res : ∀ {Δ Γ A B} → ℕ → Tm Γ (A ⇒ B) → Tm (A ∷ Δ) B → Facts Δ Γ → Info Γ A → Bool → Info Γ B
call-res f T N E I true = simp-let f E N I
call-res f T N E I false = app T (term I) ∣ nothing

call-eq : ∀ {Δ Γ A B} f T (N : Tm (A ∷ Δ) B) (E : Facts Δ Γ) I
  → simp-call (succ f) (T ∣ just (fun N E)) I ≡ call-res f T N E I (size (term (simp-let f E N I)) ≤ᵇ inline-size)
call-eq f T N E I with size (term (simp-let f E N I)) ≤ᵇ inline-size
... | true = Eq.refl
... | false = Eq.refl

let-res : ∀ {Δ Γ A B} → ℕ → Facts Δ Γ → Tm (A ∷ Δ) B → Info Γ A → Bool → Bool → Info Γ B
let-res f E N I true _ = simp f (I P.• E) N
let-res f E N I false true = let′ (term I) (term (simp f (known-as I E) N)) ∣ nothing
let-res f E N I false false = let′ (term I) (term (simp f (under E) N)) ∣ nothing

let-eq : ∀ {Δ Γ A B} f (E : Facts Δ Γ) (N : Tm (A ∷ Δ) B) I → simp-let f E N I ≡ let-res f E N I (small (term I)) (value (term I))
let-eq f E N I with small (term I) | value (term I)
... | true | _ = Eq.refl
... | false | true = Eq.refl
... | false | false = Eq.refl

case-res : ∀ {Δ Γ A B C} → ℕ → Facts Δ Γ → Info Γ (A ⊹ B) → Tm (A ∷ Δ) C → Tm (B ∷ Δ) C → Maybe (Tm Γ A ⊎ Tm Γ B) → Info Γ C
case-res f E I M N (just (inj₁ K)) = simp f (self K P.• E) M
case-res f E I M N (just (inj₂ K)) = simp f (self K P.• E) N
case-res f E I M N nothing = case (term I) (term (simp f (under E) M)) (term (simp f (under E) N)) ∣ nothing

case-eq : ∀ {Δ Γ A B C} f (E : Facts Δ Γ) (I : Info Γ (A ⊹ B)) (M : Tm (A ∷ Δ) C) N
  → simp-case f E I M N ≡ case-res f E I M N (branch (known I) Eq.refl)
case-eq f E I M N with branch (known I) Eq.refl
... | just (inj₁ K) = Eq.refl
... | just (inj₂ K) = Eq.refl
... | nothing = Eq.refl

{- The main lemma ------------------------------------------------------------------}

simp-ok : ∀ {Δ Γ A} fl (M : Tm Δ A) {E : Facts Δ Γ} {γ γ'} → Ok E γ γ' → defined-env γ' → Desc (⟦ M ⟧ · γ) (simp fl E M) γ'
simps-ok : ∀ {Δ Γ Δ'} fl (Ms : All (Tm Δ) Δ') {E : Facts Δ Γ} {γ γ'} → Ok E γ γ' → defined-env γ'
  → ∀ i → (⟦ Ms ⟧s · γ) i ＝ (⟦ simps fl E Ms ⟧s · γ') i
under-ok : ∀ {Δ Γ A B} fl (N : Tm (A ∷ Δ) B) {E : Facts Δ Γ} {γ γ'} → Ok E γ γ' → defined-env γ'
  → (d : ⟨ 𝔻 ⟩) → defined d → ⟦ N ⟧ · (d • γ) ＝ ⟦ term (simp fl (under E) N) ⟧ · (d • γ')
app-ok : ∀ {Δ Γ A B} fl (L : Tm Δ (A ⇒ B)) (M : Tm Δ A) {E : Facts Δ Γ} {γ γ' I} → Ok E γ γ' → defined-env γ'
  → Desc (⟦ M ⟧ · γ) I γ' → (l : Lam? L) → Desc (⟦ app L M ⟧ · γ) (app-res fl E L I l) γ'
call-ok : ∀ {Γ A B} fl (J : Info Γ (A ⇒ B)) I {γ' F D} → defined-env γ' → Desc F J γ' → Desc D I γ'
  → Desc (appᵈ · F · D) (simp-call fl J I) γ'
call-ok-aux : ∀ {Δ Γ A B} fl T (N : Tm (A ∷ Δ) B) (E : Facts Δ Γ) I {γ' F D} → defined-env γ'
  → Desc F (T ∣ just (fun N E)) γ' → Desc D I γ' → (b : Bool) → KDesc F (fun N E) γ' → Desc (appᵈ · F · D) (call-res fl T N E I b) γ'
let-ok : ∀ {Δ Γ A B} fl (N : Tm (A ∷ Δ) B) {E : Facts Δ Γ} {γ γ' I D} → Ok E γ γ' → defined-env γ'
  → Desc D I γ' → Desc (appᵈ · (⟦ lam N ⟧ · γ) · D) (simp-let fl E N I) γ'
let-ok-aux : ∀ {Δ Γ A B} fl (N : Tm (A ∷ Δ) B) {E : Facts Δ Γ} {γ γ' I D} → Ok E γ γ' → defined-env γ'
  → Desc D I γ' → (b₁ b₂ : Bool) → small (term I) ≡ b₁ → value (term I) ≡ b₂
  → Desc (appᵈ · (⟦ lam N ⟧ · γ) · D) (let-res fl E N I b₁ b₂) γ'
case-ok : ∀ {Δ Γ A B C} fl (L : Tm Δ (A ⊹ B)) (M : Tm (A ∷ Δ) C) N {E : Facts Δ Γ} {γ γ' I} → Ok E γ γ'
  → defined-env γ' → Desc (⟦ L ⟧ · γ) I γ' → (b : Maybe (Tm Γ A ⊎ Tm Γ B)) → branch (known I) Eq.refl ≡ b
  → Desc (⟦ case L M N ⟧ · γ) (case-res fl E I M N b) γ'

under-ok fl N {γ' = γ'} ok ne d p = tm (simp-ok fl N (ok-under d ok) (•-defined d γ' p ne))

simp-ok fl (` x) ok ne = ok x
simp-ok fl (lam N) {E} {γ} {γ'} ok ne =
  desc (lamᶜ-cong ⟦ N ⟧ ⟦ term (simp fl (under E) N) ⟧ γ γ' (under-ok fl N ok ne)) (λ { Eq.refl → kfun γ (lam N) Eq.refl ok refl })
simp-ok fl (app L M) {E} {γ} {γ'} ok ne =
  Eq.subst (λ J → Desc (⟦ app L M ⟧ · γ) J γ') (Eq.sym (app-eq fl E L (simp fl E M))) (app-ok fl L M ok ne (simp-ok fl M ok ne) (lam? L))
simp-ok fl (lit B c) ok ne = desc-self P.lit refl
simp-ok fl (tuple {Δ'} Ms) ok ne = desc-info (ap (tupleᵈ (length Δ') ·_) (dfunext fe (simps-ok fl Ms ok ne)))
simp-ok fl (get i L) {E} ok ne = get-ok i (simp fl E L) ne (simp-ok fl L ok ne)
simp-ok fl (inl M) ok ne = desc-info (ap (inlᵈ ·_) (tm (simp-ok fl M ok ne)))
simp-ok fl (inr M) ok ne = desc-info (ap (inrᵈ ·_) (tm (simp-ok fl M ok ne)))
simp-ok fl (case L M N) {E} {γ} {γ'} ok ne =
  Eq.subst (λ J → Desc (⟦ case L M N ⟧ · γ) J γ') (Eq.sym (case-eq fl E (simp fl E L) M N))
    (case-ok fl L M N ok ne (simp-ok fl L ok ne) (branch (known (simp fl E L)) Eq.refl) Eq.refl)
simp-ok fl (prim p L M) {E} ok ne = prim-ok p (simp fl E L) (simp fl E M) (simp-ok fl L ok ne) (simp-ok fl M ok ne)
simp-ok fl (let′ M N) ok ne = let-ok fl N ok ne (simp-ok fl M ok ne)
simp-ok fl (fold M) ok ne = desc-info (tm (simp-ok fl M ok ne))
simp-ok fl (unfold L) {E} ok ne = unfold-ok (simp fl E L) (simp-ok fl L ok ne)

simps-ok fl (M ∷ Ms) ok ne zero = tm (simp-ok fl M ok ne)
simps-ok fl (M ∷ Ms) ok ne (suc i) = simps-ok fl Ms ok ne i

{- an application: β if the operator is a function, and otherwise a call -}
app-ok fl (lam N) M ok ne d (is-lam .N) = let-ok fl N ok ne d
app-ok fl L M {E} ok ne d other = call-ok fl (simp fl E L) _ ne (simp-ok fl L ok ne) d

{- a call of a known function: its body, bound to the operand -}
call-ok zero J I ne dJ dI = desc (ap₂ (λ a b → appᵈ · a · b) (tm dJ) (tm dI)) (λ ())
call-ok (succ fl) (T ∣ nothing) I ne dJ dI = desc (ap₂ (λ a b → appᵈ · a · b) (tm dJ) (tm dI)) (λ ())
call-ok (succ fl) (T ∣ just (val K)) I ne dJ dI = desc (ap₂ (λ a b → appᵈ · a · b) (tm dJ) (tm dI)) (λ ())
call-ok (succ fl) (T ∣ just (fun N E)) I {γ'} {F} {D} ne dJ dI =
  Eq.subst (λ J → Desc (appᵈ · F · D) J γ') (Eq.sym (call-eq fl T N E I))
    (call-ok-aux fl T N E I ne dJ dI (size (term (simp-let fl E N I)) ≤ᵇ inline-size) (kn dJ Eq.refl))

call-ok-aux fl T N E I {D = D} ne dJ dI true (kfun γ L Eq.refl ok F＝) = desc-＝ (let-ok fl N ok ne dI) (ap (λ a → appᵈ · a · D) F＝)
call-ok-aux fl T N E I ne dJ dI false k = desc (ap₂ (λ a b → appᵈ · a · b) (tm dJ) (tm dI)) (λ ())

{- the body N of a function, bound to the operand: a small value is
   substituted, another value stays bound and known, anything else stays
   bound -}
let-ok fl N {E} {γ} {γ'} {I} {D} ok ne d =
  Eq.subst (λ J → Desc (appᵈ · (⟦ lam N ⟧ · γ) · D) J γ') (Eq.sym (let-eq fl E N I))
    (let-ok-aux fl N ok ne d (small (term I)) (value (term I)) Eq.refl Eq.refl)

let-ok-aux fl N {γ = γ} {I = I} {D} ok ne d true _ s v =
  desc-＝ (simp-ok fl N (ok-• d ok) ne) (let-β ⟦ N ⟧ γ D (transport defined (tm d ⁻¹) (sv-defined (small-sv (term I) s) ne)))
let-ok-aux fl N {E} {γ} {γ'} {I} {D} ok ne d false true s v =
  desc (let-β ⟦ N ⟧ γ D (transport defined (tm d ⁻¹) pV)
        ∙ tm (simp-ok fl N (ok-known-as I V (tm d) d ok) (•-defined V γ' pV ne))
        ∙ (let-β ⟦ term (simp fl (known-as I E) N) ⟧ γ' V pV ⁻¹))
       (λ ())
  where
  V = ⟦ term I ⟧ · γ'
  pV = sv-defined (value-sv (term I) v) ne
let-ok-aux fl N {E} {γ} {γ'} ok ne d false false s v =
  desc (ap₂ (λ a b → appᵈ · a · b) (lamᶜ-cong ⟦ N ⟧ ⟦ term (simp fl (under E) N) ⟧ γ γ' (under-ok fl N ok ne)) (tm d)) (λ ())

{- a case on a known injection takes its branch -}
case-ok fl L M N {E} {γ} {γ'} {I} ok ne d nothing e =
  desc (caseᶜ-cong ⟦ L ⟧ ⟦ term I ⟧ ⟦ M ⟧ ⟦ term (simp fl (under E) M) ⟧ ⟦ N ⟧ ⟦ term (simp fl (under E) N) ⟧ γ γ'
          (tm d) (under-ok fl M ok ne) (under-ok fl N ok ne))
       (λ ())
case-ok fl L M N {γ = γ} {γ'} {I} ok ne d (just (inj₁ K)) e =
  desc-＝ (simp-ok fl M (ok-• (desc-self (pr₁ h) refl) ok) ne) (caseᶜ-inl ⟦ L ⟧ ⟦ M ⟧ ⟦ N ⟧ γ (⟦ K ⟧ · γ') (pr₂ h) (sv-defined (pr₁ h) ne))
  where h = branch-inl-ok I e d
case-ok fl L M N {γ = γ} {γ'} {I} ok ne d (just (inj₂ K)) e =
  desc-＝ (simp-ok fl N (ok-• (desc-self (pr₁ h) refl) ok) ne) (caseᶜ-inr ⟦ L ⟧ ⟦ M ⟧ ⟦ N ⟧ γ (⟦ K ⟧ · γ') (pr₂ h) (sv-defined (pr₁ h) ne))
  where h = branch-inr-ok I e d

{- The end theorem: every closed program -}
simplify-correct : ∀ {A} (M : Tm [] A) → ⟦ M ⟧ · ρ₀ ＝ ⟦ simplify M ⟧ · ρ₀
simplify-correct M = tm (simp-ok inline-fuel M (λ ()) ρ₀-defined)

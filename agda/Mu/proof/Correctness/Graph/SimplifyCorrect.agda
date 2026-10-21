{-

  Correctness of the simplify pass (ISWIMμ → ISWIMμ) in the graph model,
  as for the untyped simplify (proof/Correctness/Graph/SimplifyCorrect.agda).

  The main lemma (simp-ok): if what simp knows of each variable x is true
  of the source's environment γ in the target's γ' (Desc: γ x is denoted
  in γ' by the term that replaces x, and by what x is known to be), then
  what simp E M says of M is true: ⟦ M ⟧ γ is denoted in γ' by its term,
  and by what it is known to be. A known function λ N denotes ⟦ λ N ⟧ γf for a
  source environment γf of which its Facts are true (KDesc), so an
  inlined call is a call of ⟦ λ N ⟧ γf: β and inlining share let-ok.

  The transformations rest on β for a value (let-β, case-inl, case-inr):
  a function body applied to an operand whose denotation D is nonempty
  and consistent means ⟦ N ⟧ (D • γ). The binders Λ and 𝒞 bind only
  finite, nonempty, consistent sets, and D is a union of those: by
  continuity, an element of ⟦ N ⟧ (D • γ) needs only a finite part of D,
  which is consistent because D is (consistent environments give
  consistent denotations, so the environments are kept consistent, and
  nonempty, Wf). A value denotes a nonempty set (sv-ne). Fold and
  unfold are the identity, so an unfold of a known fold V denotes V.

  Unlike untyped ISWIM, whose renaming and continuity come with the
  syntax of any signature, ISWIMμ's renaming needs its lemma here
  (ren-≃), and its continuity is Mu/proof/Semantics/Graph/ISWIM.agda's.

-}

module Mu.proof.Correctness.Graph.SimplifyCorrect where

open import Framework.Primitives using (Int)
open import proof.Framework.GraphModel.Prelude hiding (ρ₀)
open import Mu.Semantics.Graph.Closed using (ρ₀)
open import proof.Framework.GraphModel.Ops renaming (inl to inlD; inr to inrD)
open import proof.Framework.GraphModel.TypedOkBase using (fin₁)
open import proof.Framework.GraphModel.TypedGraph using (𝒯-intro; proj-𝒯)
open import proof.Framework.GraphModel.Env using (Env; nonempty-env; extend-nonempty-env; •-~)
open import proof.Semantics.Graph.Prim
open import Language.Prim using (Prim; Out; int; bool; δ)
import Language.Prim as Pr
open import Mu.Language.Type
open import Mu.Language.ISWIM
open import Mu.Language.ISWIMSubst using (ren; exts; varK; travs)
open import Mu.proof.Semantics.Graph.ISWIM
open import Mu.proof.Semantics.Graph.Binders using (Body-≃; lam-≃; let-≃; case-≃; body-mono)
open import Mu.Framework.AllUtil using (All; []; _∷_; lookup; pos)
open import Mu.proof.Compiler.SimplifyFacts as P
  using (Info; _∣_; term; known; Known; val; fun; Facts; self; info; under; known-as; shift-info; shift-known;
         simp; simps; simp-app; lam?; is-lam; other; simp-call; simp-let; size; inline-size; inline-fuel;
         simp-get; simp-case; simp-prim; simp-unfold; simplify; small; value; component; branch; unfolded; int-of;
         prim-term; SV; SVs; value-sv; small-sv; sv-ren; prim-term-sv; svs-lookup; int-inv; comp-inv;
         branch-inl; branch-inr; unfold-inv)

open import Data.Bool using (true; false)
open import Data.Fin using (Fin; zero; suc)
open import Data.Integer using (_≟_)
open import Data.List using (List; []; _∷_; length; replicate)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _≤ᵇ_)
open import Data.Product using (_×_; Σ-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong)
open import Relation.Nullary using (does)

{- Renaming ---------------------------------------------------------------------}

ren-≃ : ∀ {Γ Δ A} (r : ∀ {B} → Γ ∋ B → Δ ∋ B) (M : Tm Γ A) {ρ ρ'}
  → (∀ {B} (x : Γ ∋ B) → ρ' (idx (r x)) ≃ ρ (idx x)) → ⟦ ren r M ⟧ ρ' ≃ ⟦ M ⟧ ρ
rens-nth : ∀ {Γ Δ Δ'} (r : ∀ {B} → Γ ∋ B → Δ ∋ B) (Ms : All (Tm Γ) Δ') {ρ ρ'}
  → (∀ {B} (x : Γ ∋ B) → ρ' (idx (r x)) ≃ ρ (idx x)) → ∀ i → nthD (⟦ travs varK r Ms ⟧s ρ') i ≃ nthD (⟦ Ms ⟧s ρ) i
ren-ext : ∀ {Γ Δ C} (r : ∀ {B} → Γ ∋ B → Δ ∋ B) {ρ ρ' X} → (∀ {B} (x : Γ ∋ B) → ρ' (idx (r x)) ≃ ρ (idx x))
  → ∀ {B} (x : (C ∷ Γ) ∋ B) → (X • ρ') (idx (exts varK r x)) ≃ (X • ρ) (idx x)
ren-ext r h Z = ≃-refl
ren-ext r h (S x) = h x
ren-≃ r (` x) h = h x
ren-≃ r (lam N) {ρ} {ρ'} h = lam-≃ λ X _ _ → ren-≃ (exts varK r) N {X • ρ} {X • ρ'} (ren-ext r h)
ren-≃ r (app L M) h = ⋆-≃ (ren-≃ r L h) (ren-≃ r M h)
ren-≃ r (lit B c) h = ≃-refl
ren-≃ r (tuple {Δ} Ms) h = 𝒯-≃ (length Δ) (rens-nth r Ms h)
ren-≃ r (get i M) h = proj-≃ (pos i) (ren-≃ r M h)
ren-≃ r (inl M) h = inl-≃ (ren-≃ r M h)
ren-≃ r (inr M) h = inr-≃ (ren-≃ r M h)
ren-≃ r (case L M N) {ρ} {ρ'} h = case-≃ (ren-≃ r L h)
  (λ X _ _ → ren-≃ (exts varK r) M {X • ρ} {X • ρ'} (ren-ext r h)) (λ X _ _ → ren-≃ (exts varK r) N {X • ρ} {X • ρ'} (ren-ext r h))
ren-≃ r (prim p L M) h = primD-≃ p (ren-≃ r L h) (ren-≃ r M h)
ren-≃ r (let′ M N) {ρ} {ρ'} h = let-≃ (ren-≃ r M h) λ X _ _ → ren-≃ (exts varK r) N {X • ρ} {X • ρ'} (ren-ext r h)
ren-≃ r (fold M) h = ren-≃ r M h
ren-≃ r (unfold M) h = ren-≃ r M h
rens-nth r (M ∷ Ms) h zero = ren-≃ r M h
rens-nth r (M ∷ Ms) h (suc i) = rens-nth r Ms h i

shift-≃ : ∀ {Γ A B} (M : Tm Γ A) X γ → ⟦ ren (S {b = B}) M ⟧ (X • γ) ≃ ⟦ M ⟧ γ
shift-≃ M X γ = ren-≃ S M (λ x → ≃-refl)

{- β for a value ------------------------------------------------------------------}

let-β : ∀ {Γ A B} (N : Tm (A ∷ Γ) B) γ D → nonempty-env γ → nonempty D → Con D
  → ⋆ ⟨ ⟦ lam N ⟧ γ , ⟨ D , ptt ⟩ ⟩ ≃ ⟦ N ⟧ (D • γ)
let-β N γ D ne neD cD = Λ-β (body-mono (ok N) γ) (fin₁ (ok N) ne neD) cD

case-inl : ∀ {Γ A B C} (L : Tm Γ (A ⊹ B)) (M : Tm (A ∷ Γ) C) N γ D → ⟦ L ⟧ γ ≃ inlD ⟨ D , ptt ⟩ → nonempty-env γ → nonempty D → Con D
  → ⟦ case L M N ⟧ γ ≃ ⟦ M ⟧ (D • γ)
case-inl L M N γ D L≃ ne neD cD =
  ≃-trans (𝒞-≃ {F = F} {F} {G} {G} L≃ (λ _ _ _ → ≃-refl) (λ _ _ _ → ≃-refl))
          (𝒞-inl-β {D} {F} {G} (body-mono (ok M) γ) (fin₁ (ok M) ne neD) cD)
  where F = λ X → ⟦ M ⟧ (X • γ)
        G = λ X → ⟦ N ⟧ (X • γ)

case-inr : ∀ {Γ A B C} (L : Tm Γ (A ⊹ B)) (M : Tm (A ∷ Γ) C) N γ D → ⟦ L ⟧ γ ≃ inrD ⟨ D , ptt ⟩ → nonempty-env γ → nonempty D → Con D
  → ⟦ case L M N ⟧ γ ≃ ⟦ N ⟧ (D • γ)
case-inr L M N γ D L≃ ne neD cD =
  ≃-trans (𝒞-≃ {F = F} {F} {G} {G} L≃ (λ _ _ _ → ≃-refl) (λ _ _ _ → ≃-refl))
          (𝒞-inr-β {D} {F} {G} (body-mono (ok N) γ) (fin₁ (ok N) ne neD) cD)
  where F = λ X → ⟦ M ⟧ (X • γ)
        G = λ X → ⟦ N ⟧ (X • γ)

{- What simp knows, and what it means ----------------------------------------}

{- the environments: nonempty and consistent -}
Wf : Env Value → Set
Wf γ = nonempty-env γ × Con-env γ

wf-• : ∀ {D γ} → Wf γ → nonempty D → Con D → Wf (D • γ)
wf-• ⟨ ne , c ⟩ neD cD = ⟨ extend-nonempty-env ne neD , Con-• cD c ⟩

{- I is true of D in γ': its term denotes D, and so does what it is known
   to be (KDesc): a value, or a function λ N closed in a source
   environment γ of which its Facts are true -}
record Desc {Γ A} (D : 𝒫 Value) (I : Info Γ A) (γ' : Env Value) : Set₁
data KDesc {Γ} : ∀ {A} → 𝒫 Value → Known Γ A → Env Value → Set₁

Ok : ∀ {Δ Γ} → Facts Δ Γ → Env Value → Env Value → Set₁
Ok {Δ} E γ γ' = ∀ {A} (x : Δ ∋ A) → Desc (γ (idx x)) (E x) γ'

record Desc D I γ' where
  inductive
  constructor desc
  field
    tm : D ≃ ⟦ term I ⟧ γ'
    kn : ∀ {K} → known I ≡ just K → KDesc D K γ'
open Desc

data KDesc {Γ} where
  kval : ∀ {A D} {K : Tm Γ A} {γ'} → SV K → D ≃ ⟦ K ⟧ γ' → KDesc D (val K) γ'
  kfun : ∀ {Δ A B D} {N : Tm (A ∷ Δ) B} {E : Facts Δ Γ} {γ'} γ → Wf γ → Ok E γ γ' → D ≃ ⟦ lam N ⟧ γ → KDesc D (fun N E) γ'

kv : ∀ {Γ A D} {K : Tm Γ A} {γ'} → KDesc D (val K) γ' → SV K × D ≃ ⟦ K ⟧ γ'
kv (kval v eq) = ⟨ v , eq ⟩

desc-≃ : ∀ {Γ A D D'} {I : Info Γ A} {γ'} → Desc D I γ' → D' ≃ D → Desc D' I γ'
desc-≃ {γ' = γ'} d eq = desc (≃-trans eq (tm d)) (λ e → G _ (kn d e))
  where
  G : ∀ {A} (K : Known _ A) → KDesc _ K γ' → KDesc _ K γ'
  G (val K) (kval v K≃) = kval v (≃-trans eq K≃)
  G (fun N E) (kfun γ wf ok F≃) = kfun γ wf ok (≃-trans eq F≃)

desc-self : ∀ {Γ A D} {V : Tm Γ A} {γ'} → SV V → D ≃ ⟦ V ⟧ γ' → Desc D (self V) γ'
desc-self v eq = desc eq (λ { refl → kval v eq })

desc-info : ∀ {Γ A D} {M : Tm Γ A} {γ'} → D ≃ ⟦ M ⟧ γ' → Desc D (info M) γ'
desc-info {M = M} eq with value M in e
... | true = desc eq (λ { refl → kval (value-sv M e) eq })
... | false = desc eq (λ ())

{- under one more binder, in the target -}
desc-shift : ∀ {Γ A B} (I : Info Γ A) {D γ'} X → Desc D I γ' → Desc D (shift-info {B = B} I) (X • γ')
kdesc-shift : ∀ {Γ A B} (K : Known Γ A) {D γ'} X → KDesc D K γ' → KDesc D (shift-known {B = B} K) (X • γ')
desc-shift (M ∣ nothing) {γ' = γ'} X d = desc (≃-trans (tm d) (≃-sym (shift-≃ M X γ'))) (λ ())
desc-shift (M ∣ just K) {γ' = γ'} X d = desc (≃-trans (tm d) (≃-sym (shift-≃ M X γ'))) (λ { refl → kdesc-shift K X (kn d refl) })
kdesc-shift (val K) {γ' = γ'} X (kval v K≃) = kval (sv-ren S v) (≃-trans K≃ (≃-sym (shift-≃ K X γ')))
kdesc-shift (fun N E) X (kfun γ wf ok F≃) = kfun γ wf (λ x → desc-shift (E x) X (ok x)) F≃

ok-under : ∀ {Δ Γ B} {E : Facts Δ Γ} {γ γ'} X → Ok E γ γ' → Ok (under {B = B} E) (X • γ) (X • γ')
ok-under X ok Z = desc-self (P.var Z) ≃-refl
ok-under {E = E} X ok (S x) = desc-shift (E x) X (ok x)

{- Values denote nonempty sets ------------------------------------------------}

sv-ne : ∀ {Γ A} {V : Tm Γ A} {γ} → SV V → nonempty-env γ → nonempty (⟦ V ⟧ γ)
svs-ne : ∀ {Γ Δ} {Ms : All (Tm Γ) Δ} {γ} → SVs Ms → nonempty-env γ → ∀ i → nonempty (nthD (⟦ Ms ⟧s γ) i)
sv-ne (P.var x) ne = ne (idx x)
sv-ne P.lam ne = ⟨ ν , tt ⟩
sv-ne (P.lit {c = c}) ne = ⟨ const c , ⟨ refl , refl ⟩ ⟩
sv-ne (P.tuple {Δ} vs) ne = 𝒯-intro (length Δ) (svs-ne vs ne)
sv-ne (P.inl v) ne with sv-ne v ne
... | ⟨ d , d∈ ⟩ = ⟨ left d , d∈ ⟩
sv-ne (P.inr v) ne with sv-ne v ne
... | ⟨ d , d∈ ⟩ = ⟨ right d , d∈ ⟩
sv-ne (P.fold v) ne = sv-ne v ne
svs-ne (v P.∷ vs) ne zero = sv-ne v ne
svs-ne (v P.∷ vs) ne (suc i) = svs-ne vs ne i

{- Known tuples, integers and folds -----------------------------------------------}

nth-lookup : ∀ {Γ Δ A} (Ks : All (Tm Γ) Δ) (i : Δ ∋ A) γ → nthD (⟦ Ks ⟧s γ) (pos i) ≡ ⟦ lookup Ks i ⟧ γ
nth-lookup (K ∷ Ks) Z γ = refl
nth-lookup (K ∷ Ks) (S i) γ = nth-lookup Ks i γ

{- a component of a known tuple -}
component-ok : ∀ {Γ Δ A} (i : Δ ∋ A) (k : Maybe (Known Γ (tup Δ))) {K γ' D} → component i k refl ≡ just K → nonempty-env γ'
  → (∀ {Kt} → k ≡ just Kt → KDesc D Kt γ') → SV K × proj (pos i) ⟨ D , ptt ⟩ ≃ ⟦ K ⟧ γ'
component-ok {Δ = Δ} i k {γ' = γ'} e ne h with comp-inv i k refl e
... | ⟨ Ks , ⟨ refl , refl ⟩ ⟩ with kv (h refl)
...   | ⟨ P.tuple vs , Kt≃ ⟩ =
  ⟨ svs-lookup vs i , ≃-trans (proj-≃ (pos i) Kt≃)
                       (≃-trans (proj-𝒯 (length Δ) (svs-ne vs ne) (pos i)) (≃-reflexive (nth-lookup Ks i γ'))) ⟩

{- a known integer -}
int-ok : ∀ {Γ} (k : Maybe (Known Γ (base Int))) {n γ' D} → int-of k ≡ just n → (∀ {K} → k ≡ just K → KDesc D K γ')
  → D ≃ ⟦ lit {Γ} Int n ⟧ γ'
int-ok k e h with int-inv k e
... | ⟨ refl , refl ⟩ = proj₂ (kv (h refl))

{- the result of a primitive -}
prim-term-≃ : ∀ {Γ} p n m γ → ⌈ out (δ p n m) ⌉ ≃ ⟦ prim-term {Γ} p n m ⟧ γ
prim-term-≃ Pr.sub n m γ = ⟨ (λ { _ refl → ⟨ refl , refl ⟩ }) , (λ { (const {Int} n') ⟨ refl , refl ⟩ → refl }) ⟩
prim-term-≃ Pr.eq n m γ with does (n ≟ m)
... | true = ⟨ (λ { _ refl → tt }) , (λ { (left ⟨⟩) tt → refl }) ⟩
... | false = ⟨ (λ { _ refl → tt }) , (λ { (right ⟨⟩) tt → refl }) ⟩

prim-fold : ∀ p n m → primD p ⟨ ℬ Int n ptt , ⟨ ℬ Int m ptt , ptt ⟩ ⟩ ≃ ⌈ out (δ p n m) ⌉
prim-fold p n m =
  ⟨ (λ { _ ⟨ n' , ⟨ m' , ⟨ ⟨ refl , refl ⟩ , ⟨ ⟨ refl , refl ⟩ , refl ⟩ ⟩ ⟩ ⟩ → refl })
  , (λ { _ refl → ⟨ n , ⟨ m , ⟨ ⟨ refl , refl ⟩ , ⟨ ⟨ refl , refl ⟩ , refl ⟩ ⟩ ⟩ ⟩ }) ⟩

{- The main lemma ------------------------------------------------------------------}

simp-ok : ∀ {Δ Γ A} fl (M : Tm Δ A) {E : Facts Δ Γ} {γ γ'} → Wf γ → Wf γ' → Ok E γ γ' → Desc (⟦ M ⟧ γ) (simp fl E M) γ'
simps-ok : ∀ {Δ Γ Δ'} fl (Ms : All (Tm Δ) Δ') {E : Facts Δ Γ} {γ γ'} → Wf γ → Wf γ' → Ok E γ γ'
  → ∀ i → nthD (⟦ Ms ⟧s γ) i ≃ nthD (⟦ simps fl E Ms ⟧s γ') i
app-ok : ∀ {Δ Γ A B} fl (L : Tm Δ (A ⇒ B)) (M : Tm Δ A) {E : Facts Δ Γ} {γ γ' I} → Wf γ → Wf γ' → Ok E γ γ' → Desc (⟦ M ⟧ γ) I γ'
  → Desc (⟦ app L M ⟧ γ) (simp-app fl E L I) γ'
let-ok : ∀ {Δ Γ A B} fl (N : Tm (A ∷ Δ) B) {E : Facts Δ Γ} {γ γ' I D} → Wf γ → Wf γ' → Ok E γ γ' → Desc D I γ' → Con D
  → Desc (⋆ ⟨ ⟦ lam N ⟧ γ , ⟨ D , ptt ⟩ ⟩) (simp-let fl E N I) γ'
call-ok : ∀ {Γ A B} fl (J : Info Γ (A ⇒ B)) I {γ' F D} → Wf γ' → Desc F J γ' → Desc D I γ' → Con D
  → Desc (⋆ ⟨ F , ⟨ D , ptt ⟩ ⟩) (simp-call fl J I) γ'
case-ok : ∀ {Δ Γ A B C} fl (L : Tm Δ (A ⊹ B)) (M : Tm (A ∷ Δ) C) N {E : Facts Δ Γ} {γ γ' I} → Wf γ → Wf γ' → Ok E γ γ'
  → Desc (⟦ L ⟧ γ) I γ' → Desc (⟦ case L M N ⟧ γ) (simp-case fl E I M N) γ'

{- a body under a binder that stays -}
under-ok : ∀ {Δ Γ A B} fl (N : Tm (A ∷ Δ) B) {E : Facts Δ Γ} {γ γ'} → Wf γ → Wf γ' → Ok E γ γ'
  → Body-≃ (λ X → ⟦ N ⟧ (X • γ)) (λ X → ⟦ term (simp fl (under E) N) ⟧ (X • γ'))
under-ok fl N wf wf' ok X ne c = tm (simp-ok fl N (wf-• wf ne c) (wf-• wf' ne c) (ok-under X ok))

simp-ok fl (` x) wf wf' ok = ok x
simp-ok fl (lam N) {γ = γ} wf wf' ok =
  desc (lam-≃ (under-ok fl N wf wf' ok)) (λ { refl → kfun γ wf ok ≃-refl })
simp-ok fl (app L M) wf wf' ok = app-ok fl L M wf wf' ok (simp-ok fl M wf wf' ok)
simp-ok fl (lit B c) wf wf' ok = desc-self P.lit ≃-refl
simp-ok fl (tuple {Δ'} Ms) wf wf' ok = desc-info (𝒯-≃ (length Δ') (simps-ok fl Ms wf wf' ok))
simp-ok fl (get i L) {E} {γ' = γ'} wf wf' ok = get-ok (simp fl E L) (simp-ok fl L wf wf' ok)
  where
  get-ok : ∀ I → Desc (⟦ L ⟧ _) I γ' → Desc (⟦ get i L ⟧ _) (simp-get i I) γ'
  get-ok I d with component i (known I) refl in e
  ... | nothing = desc (proj-≃ (pos i) (tm d)) (λ ())
  ... | just K with component-ok i (known I) e (proj₁ wf') (kn d) | small K
  ...   | ⟨ v , K≃ ⟩ | true = desc-self v K≃
  ...   | ⟨ v , K≃ ⟩ | false = desc (proj-≃ (pos i) (tm d)) (λ { refl → kval v K≃ })
simp-ok fl (inl M) wf wf' ok = desc-info (inl-≃ (tm (simp-ok fl M wf wf' ok)))
simp-ok fl (inr M) wf wf' ok = desc-info (inr-≃ (tm (simp-ok fl M wf wf' ok)))
simp-ok fl (case L M N) wf wf' ok = case-ok fl L M N wf wf' ok (simp-ok fl L wf wf' ok)
simp-ok fl (prim p L M) {E} {γ = γ} {γ'} wf wf' ok =
  prim-ok (simp fl E L) (simp fl E M) (simp-ok fl L wf wf' ok) (simp-ok fl M wf wf' ok)
  where
  dflt : ∀ {I J} → Desc (⟦ L ⟧ γ) I γ' → Desc (⟦ M ⟧ γ) J γ'
    → Desc (⟦ prim p L M ⟧ γ) (prim p (term I) (term J) ∣ nothing) γ'
  dflt dI dJ = desc (primD-≃ p (tm dI) (tm dJ)) (λ ())
  prim-ok : ∀ I J → Desc (⟦ L ⟧ γ) I γ' → Desc (⟦ M ⟧ γ) J γ' → Desc (⟦ prim p L M ⟧ γ) (simp-prim p I J) γ'
  prim-ok I J dI dJ with int-of (known I) in e₁
  ... | nothing = dflt dI dJ
  ... | just n with int-of (known J) in e₂
  ...   | nothing = dflt dI dJ
  ...   | just m =
    desc-self (prim-term-sv p n m)
      (≃-trans (≃-trans (primD-≃ p (int-ok (known I) e₁ (kn dI)) (int-ok (known J) e₂ (kn dJ))) (prim-fold p n m))
        (prim-term-≃ p n m γ'))
simp-ok fl (let′ M N) wf wf' ok =
  let-ok fl N wf wf' ok (simp-ok fl M wf wf' ok) (con M (proj₂ wf))
simp-ok fl (fold M) wf wf' ok = desc-info (tm (simp-ok fl M wf wf' ok))
simp-ok fl (unfold L) {E} {γ' = γ'} wf wf' ok = unfold-ok (simp fl E L) (simp-ok fl L wf wf' ok)
  where
  unfold-ok : ∀ I → Desc (⟦ L ⟧ _) I γ' → Desc (⟦ unfold L ⟧ _) (simp-unfold I) γ'
  unfold-ok I d with unfolded (known I) refl in e
  ... | nothing = desc (tm d) (λ ())
  ... | just K with kv (kn d (unfold-inv (known I) refl e)) | small K
  ...   | ⟨ P.fold v , K≃ ⟩ | true = desc-self v K≃
  ...   | ⟨ P.fold v , K≃ ⟩ | false = desc (tm d) (λ { refl → kval v K≃ })

simps-ok fl (M ∷ Ms) wf wf' ok zero = tm (simp-ok fl M wf wf' ok)
simps-ok fl (M ∷ Ms) wf wf' ok (suc i) = simps-ok fl Ms wf wf' ok i

{- an application: β if the operator is a function, and otherwise a call -}
app-ok fl L M wf wf' ok d with lam? L
... | is-lam N = let-ok fl N wf wf' ok d (con M (proj₂ wf))
... | other = call-ok fl _ _ wf' (simp-ok fl L wf wf' ok) d (con M (proj₂ wf))

{- a call of a known function: its body, bound to the operand -}
call-ok (suc fl) (T ∣ just (fun N E)) I wf' dJ dI cD with size (term (simp-let fl E N I)) ≤ᵇ inline-size | kn dJ refl
... | true | kfun γ wf ok F≃ = desc-≃ (let-ok fl N wf wf' ok dI cD) (⋆-≃ F≃ ≃-refl)
... | false | _ = desc (⋆-≃ (tm dJ) (tm dI)) (λ ())
call-ok zero J I wf' dJ dI cD = desc (⋆-≃ (tm dJ) (tm dI)) (λ ())
call-ok (suc fl) (T ∣ nothing) I wf' dJ dI cD = desc (⋆-≃ (tm dJ) (tm dI)) (λ ())
call-ok (suc fl) (T ∣ just (val K)) I wf' dJ dI cD = desc (⋆-≃ (tm dJ) (tm dI)) (λ ())

{- the body N of a function, bound to the operand: a small value is
   substituted, another value stays bound and known, anything else stays
   bound -}
let-ok fl N {E} {γ} {γ'} {I} {D} wf wf' ok d cD with small (term I) in s | value (term I) in v
... | true | _ = desc-≃ (simp-ok fl N (wf-• wf neD cD) wf' ok') (let-β N γ D (proj₁ wf) neD cD)
  where
  neD = ⟨ _ , proj₂ (tm d) _ (proj₂ (sv-ne (small-sv (term I) s) (proj₁ wf'))) ⟩
  ok' : Ok (I P.• E) (D • γ) γ'
  ok' Z = d
  ok' (S x) = ok x
... | false | true =
  desc (≃-trans (let-β N γ D (proj₁ wf) neD cD)
          (≃-trans (tm (simp-ok fl N (wf-• wf neD cD) (wf-• wf' neV cV) ok')) (≃-sym (let-β N' γ' _ (proj₁ wf') neV cV))))
       (λ ())
  where
  N' = term (simp fl (known-as I E) N)
  neV = sv-ne (value-sv (term I) v) (proj₁ wf')
  cV = con (term I) (proj₂ wf')
  neD = ⟨ _ , proj₂ (tm d) _ (proj₂ neV) ⟩
  ok' : Ok (known-as I E) (D • γ) (⟦ term I ⟧ γ' • γ')
  ok' Z = desc (tm d) (kn (desc-shift I _ d))
  ok' (S x) = desc-shift (E x) _ (ok x)
... | false | false =
  desc (let-≃ (tm d) (under-ok fl N wf wf' ok)) (λ ())

{- a case on a known injection takes its branch -}
case-ok fl L M N {E} {γ} {γ'} {I} wf wf' ok d with branch (known I) refl in e
... | nothing =
  desc (case-≃ (tm d) (under-ok fl M wf wf' ok) (under-ok fl N wf wf' ok)) (λ ())
... | just (inj₁ K) with branch-inl (known I) refl e
...   | ⟨ k , _ ⟩ with kv (kn d k)
...     | ⟨ P.inl v , Kt≃ ⟩ =
  desc-≃ (simp-ok fl M (wf-• wf neK cK) wf' ok') (case-inl L M N γ _ Kt≃ (proj₁ wf) neK cK)
  where
  neK = sv-ne v (proj₁ wf')
  cK = con K (proj₂ wf')
  ok' : Ok (self K P.• E) (⟦ K ⟧ γ' • γ) γ'
  ok' Z = desc-self v ≃-refl
  ok' (S x) = ok x
case-ok fl L M N {E} {γ} {γ'} {I} wf wf' ok d | just (inj₂ K) with branch-inr (known I) refl e
...   | ⟨ k , _ ⟩ with kv (kn d k)
...     | ⟨ P.inr v , Kt≃ ⟩ =
  desc-≃ (simp-ok fl N (wf-• wf neK cK) wf' ok') (case-inr L M N γ _ Kt≃ (proj₁ wf) neK cK)
  where
  neK = sv-ne v (proj₁ wf')
  cK = con K (proj₂ wf')
  ok' : Ok (self K P.• E) (⟦ K ⟧ γ' • γ) γ'
  ok' Z = desc-self v ≃-refl
  ok' (S x) = ok x

{- The end theorem: every closed program -}
simplify-correct : ∀ {A} (M : Tm [] A) → ⟦ M ⟧ ρ₀ ≃ ⟦ simplify M ⟧ ρ₀
simplify-correct M = tm (simp-ok inline-fuel M wf₀ wf₀ (λ ()))
  where wf₀ = ⟨ (λ _ → ⟨ ⟨⟩ , refl ⟩) , (λ _ → Con-⌈⌉ ⟨⟩) ⟩

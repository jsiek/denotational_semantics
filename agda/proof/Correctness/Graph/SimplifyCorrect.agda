{-

  Correctness of the simplify pass (ISWIM → ISWIM) in the graph model.

  The main lemma (simp-ok): if what simp knows of each variable x is true
  of the source's environment γ in the target's γ' (Desc: the term that
  replaces x, and the value x is known to be, denote γ x in γ'), then
  what simp E M says of M is true: its term, and its known value,
  denote ⟦ M ⟧ γ in γ'.

  The transformations rest on β for a value (beta, case-inl, case-inr):
  a function body applied to an operand whose denotation D is nonempty
  and consistent means ⟦ N ⟧ (D • γ). The binders Λ and 𝒞 bind only
  finite, nonempty, consistent sets, and D is a union of those: by
  continuity, an element of ⟦ N ⟧ (D • γ) needs only a finite part of D,
  which is consistent because D is (consistent environments give
  consistent denotations, so the environments are kept consistent, and
  nonempty, Wf). A value denotes a nonempty set (sv-ne).

-}

module proof.Correctness.Graph.SimplifyCorrect where

open import Framework.Primitives using (Int)
open import Framework.Syntax.SyntaxUtil
open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.Domain
open import proof.Framework.GraphModel.Ops
open import proof.Semantics.Graph.Prim
open import Language.ISWIM
open import Language.Prim using (Prim; Out; int; bool; δ)
open import proof.Semantics.Graph.ISWIM
open import proof.Semantics.Graph.ISWIMContinuous using (body-continuous)
open import proof.Compiler.SimplifyFacts as P
  using (Info; _∣_; term; known; Facts; self; info; under; shift-info; simp; simp-args; simp-app; simp-let;
         simp-get; simp-case; simp-prim; simplify; small; value; component; branch; int-of; prim-term;
         SV; SVs; value-sv; small-sv; sv-rename; prim-term-sv; int-of-just; component-just)
open import proof.Framework.GraphModel.Env using (Env; nonempty-env; extend-nonempty-env; _⊆ₑ_)
open import proof.Framework.GraphModel.RenameSem Op sig using (shift-≃)
open import proof.Correctness.Graph.ConcretizeCorrect using (⋆-≃; 𝒯-≃; proj-≃; inl-≃; inr-≃; 𝒞-≃; primD-≃)
open import Framework.ListUtil using (args→list; has-length) renaming (proj to proj-list)
open import Framework.Syntax.Rename Op sig using (shift)

open import Data.Bool using (true; false)
open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_; replicate)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe
open import Data.Maybe.Properties using (just-injective)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; Σ-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)

Λ-≃ : ∀ {F F'} → (∀ V → V ≢ [] → V ≈ V → F (mem V) ≃ F' (mem V)) → Λ ⟨ F , ptt ⟩ ≃ Λ ⟨ F' , ptt ⟩
Λ-≃ {F} {F'} eq = ⟨ G (λ V ne c → proj₁ (eq V ne c)) , G (λ V ne c → proj₂ (eq V ne c)) ⟩
  where
  G : ∀ {A B : 𝒫 Value → 𝒫 Value} → (∀ V → V ≢ [] → V ≈ V → A (mem V) ⊆ B (mem V))
    → Λ ⟨ A , ptt ⟩ ⊆ Λ ⟨ B , ptt ⟩
  G A⊆ ν tt = tt
  G A⊆ (V ↦ w) ⟨ w∈ , ne ⟩ = ⟨ A⊆ V (proj₁ ne) (proj₂ ne) w w∈ , ne ⟩

{- What simp knows, and what it means ----------------------------------------}

{- the environments: nonempty and consistent -}
Wf : Env Value → Set
Wf γ = nonempty-env γ × Con-env γ

wf-• : ∀ {D γ} → Wf γ → nonempty D → Con D → Wf (D • γ)
wf-• ⟨ ne , c ⟩ neD cD = ⟨ extend-nonempty-env ne neD , Con-• cD c ⟩

{- I is true of D in γ': its term, and its known value, denote D -}
record Desc (I : Info) (γ' : Env Value) (D : 𝒫 Value) : Set where
  constructor desc
  field
    tm : ⟦ term I ⟧ γ' ≃ D
    kn : ∀ {K} → known I ≡ just K → SV K × ⟦ K ⟧ γ' ≃ D
open Desc

Ok : Facts → Env Value → Env Value → Set
Ok E γ γ' = ∀ x → Desc (E x) γ' (γ x)

desc-≃ : ∀ {I γ' D D'} → Desc I γ' D → D ≃ D' → Desc I γ' D'
desc-≃ (desc t k) eq = desc (≃-trans t eq) (λ e → ⟨ proj₁ (k e) , ≃-trans (proj₂ (k e)) eq ⟩)

desc-self : ∀ {V γ' D} → SV V → ⟦ V ⟧ γ' ≃ D → Desc (self V) γ' D
desc-self v eq = desc eq (λ { refl → ⟨ v , eq ⟩ })

desc-info : ∀ {M γ' D} → ⟦ M ⟧ γ' ≃ D → Desc (info M) γ' D
desc-info {M} eq with value M in e
... | true = desc eq (λ { refl → ⟨ value-sv M e , eq ⟩ })
... | false = desc eq (λ ())

desc-shift : ∀ {I γ' D X} → Desc I γ' D → Desc (shift-info I) (X • γ') D
desc-shift {M ∣ k} {γ'} {X = X} (desc t kn) = desc (≃-trans (shift-≃ M X γ') t) (G k kn)
  where
  G : ∀ k → (∀ {K} → k ≡ just K → SV K × ⟦ K ⟧ γ' ≃ _)
    → ∀ {K} → Data.Maybe.map shift k ≡ just K → SV K × ⟦ K ⟧ (X • γ') ≃ _
  G (just K) h refl = ⟨ sv-rename suc (proj₁ (h refl)) , ≃-trans (shift-≃ K X γ') (proj₂ (h refl)) ⟩

ok-under : ∀ {E γ γ'} X → Ok E γ γ' → Ok (under E) (X • γ) (X • γ')
ok-under X ok zero = desc-self (P.var 0) ≃-refl
ok-under {E} X ok (suc x) = desc-shift {E x} (ok x)

{- Values denote nonempty sets ------------------------------------------------}

sv-ne : ∀ {V γ} → SV V → nonempty-env γ → nonempty (⟦ V ⟧ γ)
svs-ne : ∀ {n} {as : Args (replicate n ■)} {γ} → SVs as → nonempty-env γ
  → ∀ i → nonempty (nthD (⟦ as ⟧₊ γ) i)
sv-ne (P.var x) ne = ne x
sv-ne P.lam ne = ⟨ ν , tt ⟩
sv-ne (P.lit {k = k}) ne = ⟨ const k , ⟨ refl , refl ⟩ ⟩
sv-ne (P.tuple {zero} vs) ne = ⟨ ⟨⟩ , tt ⟩
sv-ne (P.tuple {suc n} vs) ne with svs-ne vs ne zero
... | ⟨ d , d∈ ⟩ = ⟨ tup[ zero ] d , ⟨ refl , ⟨ d∈ , svs-ne vs ne ⟩ ⟩ ⟩
sv-ne (P.inl v) ne with sv-ne v ne
... | ⟨ d , d∈ ⟩ = ⟨ left d , d∈ ⟩
sv-ne (P.inr v) ne with sv-ne v ne
... | ⟨ d , d∈ ⟩ = ⟨ right d , d∈ ⟩
svs-ne (v P.∷ vs) ne zero = sv-ne v ne
svs-ne (v P.∷ vs) ne (suc i) = svs-ne vs ne i

{- β for a value ----------------------------------------------------------------}

{- an element of a body on D needs a finite, nonempty, consistent part of D -}
body : ∀ N γ D → nonempty-env γ → nonempty D → Con D → ∀ w → w ∈ ⟦ N ⟧ (D • γ)
  → Σ[ V ∈ List Value ] V ≢ [] × V ≈ V × mem V ⊆ D × w ∈ ⟦ N ⟧ (mem V • γ)
body N γ D ne neD cD w w∈ with body-continuous N γ ne D neD w w∈
... | ⟨ V , ⟨ V≢ , ⟨ V⊆ , w∈' ⟩ ⟩ ⟩ = ⟨ V , ⟨ V≢ , ⟨ Con⇒≈ V cD V⊆ , ⟨ V⊆ , w∈' ⟩ ⟩ ⟩ ⟩

part : ∀ {V : List Value} {D : 𝒫 Value} {γ : Env Value} → mem V ⊆ D → (mem V • γ) ⊆ₑ (D • γ)
part V⊆ zero = V⊆
part V⊆ (suc x) d d∈ = d∈

beta : ∀ N M γ → nonempty-env γ → nonempty (⟦ M ⟧ γ) → Con (⟦ M ⟧ γ)
  → ⟦ app ⦅ lam ⦅ ⟩ N ,, Nil ⦆ ,, M ,, Nil ⦆ ⟧ γ ≃ ⟦ N ⟧ (⟦ M ⟧ γ • γ)
beta N M γ ne neM cM = ⟨ G , H ⟩
  where
  G : _
  G w ⟨ V , ⟨ ⟨ w∈ , _ ⟩ , ⟨ V⊆ , _ ⟩ ⟩ ⟩ = ⟦⟧-monotone {ρ = mem V • γ} {ρ′ = ⟦ M ⟧ γ • γ} N (part V⊆) w w∈
  H : _
  H w w∈ with body N γ _ ne neM cM w w∈
  ... | ⟨ V , ⟨ V≢ , ⟨ c , ⟨ V⊆ , w∈' ⟩ ⟩ ⟩ ⟩ = ⟨ V , ⟨ ⟨ w∈' , ⟨ V≢ , c ⟩ ⟩ , ⟨ V⊆ , V≢ ⟩ ⟩ ⟩

case-inl : ∀ L M N γ D → ⟦ L ⟧ γ ≃ inl ⟨ D , ptt ⟩ → nonempty-env γ → nonempty D → Con D
  → ⟦ case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆ ⟧ γ ≃ ⟦ M ⟧ (D • γ)
case-inl L M N γ D L≃ ne neD cD = ⟨ G , H ⟩
  where
  G : _
  G w (inj₁ ⟨ v , ⟨ V , ⟨ ls , ⟨ w∈ , _ ⟩ ⟩ ⟩ ⟩) = ⟦⟧-monotone {ρ = mem (v ∷ V) • γ} {ρ′ = D • γ} M (part (λ d d∈ → proj₁ L≃ (left d) (ls d d∈))) w w∈
  G w (inj₂ ⟨ v , ⟨ V , ⟨ rs , _ ⟩ ⟩ ⟩) = ⊥-elim (proj₁ L≃ (right v) (rs v (here refl)))
  H : _
  H w w∈ with body M γ D ne neD cD w w∈
  ... | ⟨ [] , ⟨ V≢ , _ ⟩ ⟩ = ⊥-elim (V≢ refl)
  ... | ⟨ v ∷ V , ⟨ _ , ⟨ c , ⟨ V⊆ , w∈' ⟩ ⟩ ⟩ ⟩ =
    inj₁ ⟨ v , ⟨ V , ⟨ (λ d d∈ → proj₂ L≃ (left d) (V⊆ d d∈)) , ⟨ w∈' , c ⟩ ⟩ ⟩ ⟩

case-inr : ∀ L M N γ D → ⟦ L ⟧ γ ≃ inr ⟨ D , ptt ⟩ → nonempty-env γ → nonempty D → Con D
  → ⟦ case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆ ⟧ γ ≃ ⟦ N ⟧ (D • γ)
case-inr L M N γ D L≃ ne neD cD = ⟨ G , H ⟩
  where
  G : _
  G w (inj₁ ⟨ v , ⟨ V , ⟨ ls , _ ⟩ ⟩ ⟩) = ⊥-elim (proj₁ L≃ (left v) (ls v (here refl)))
  G w (inj₂ ⟨ v , ⟨ V , ⟨ rs , ⟨ w∈ , _ ⟩ ⟩ ⟩ ⟩) = ⟦⟧-monotone {ρ = mem (v ∷ V) • γ} {ρ′ = D • γ} N (part (λ d d∈ → proj₁ L≃ (right d) (rs d d∈))) w w∈
  H : _
  H w w∈ with body N γ D ne neD cD w w∈
  ... | ⟨ [] , ⟨ V≢ , _ ⟩ ⟩ = ⊥-elim (V≢ refl)
  ... | ⟨ v ∷ V , ⟨ _ , ⟨ c , ⟨ V⊆ , w∈' ⟩ ⟩ ⟩ ⟩ =
    inj₂ ⟨ v , ⟨ V , ⟨ (λ d d∈ → proj₂ L≃ (right d) (V⊆ d d∈)) , ⟨ w∈' , c ⟩ ⟩ ⟩ ⟩

{- Known tuples and integers ------------------------------------------------------}

has-length-≡ : ∀ n {m} (Ks : Args (replicate m ■)) → has-length n (args→list Ks) ≡ true → n ≡ m
has-length-≡ zero {zero} Nil _ = refl
has-length-≡ zero {suc m} (K ,, Ks) ()
has-length-≡ (suc n) {suc m} (K ,, Ks) e = cong suc (has-length-≡ n Ks e)

{- a component of a known tuple -}
proj-nth : ∀ {n} (i : Fin n) {m} (Ks : Args (replicate m ■)) {K} γ → proj-list i (args→list Ks) ≡ just K
  → Σ[ e ∈ n ≡ m ] nthD (⟦ Ks ⟧₊ γ) (subst Fin e i) ≡ ⟦ K ⟧ γ
proj-nth {suc n} zero {suc m} (K₀ ,, Ks) γ e with has-length n (args→list Ks) in h
proj-nth {suc n} zero {suc m} (K₀ ,, Ks) γ refl | true with has-length-≡ n Ks h
... | refl = ⟨ refl , refl ⟩
proj-nth (suc i) {suc m} (K₀ ,, Ks) γ e with proj-nth i Ks γ e
... | ⟨ refl , eq ⟩ = ⟨ refl , eq ⟩

tuple-proj : ∀ {n} (i : Fin n) (Ks : Args (replicate n ■)) {K} γ → SVs Ks → nonempty-env γ
  → nthD (⟦ Ks ⟧₊ γ) i ≡ ⟦ K ⟧ γ → proj i ⟨ ⟦ tuple n ⦅ Ks ⦆ ⟧ γ , ptt ⟩ ≃ ⟦ K ⟧ γ
tuple-proj {suc n} i Ks γ vs ne eq =
  ⟨ (λ { d ⟨ refl , ⟨ d∈ , _ ⟩ ⟩ → subst (d ∈_) eq d∈ })
  , (λ d d∈ → ⟨ refl , ⟨ subst (d ∈_) (sym eq) d∈ , svs-ne vs ne ⟩ ⟩) ⟩

component-ok : ∀ {n} (i : Fin n) k {K γ' D} → component i k ≡ just K → nonempty-env γ'
  → (∀ {Kt} → k ≡ just Kt → SV Kt × ⟦ Kt ⟧ γ' ≃ D) → SV K × ⟦ K ⟧ γ' ≃ proj i ⟨ D , ptt ⟩
component-ok i (just Kt) {K} {γ'} e ne h with h refl
... | ⟨ P.tuple {m} {Ks} vs , Kt≃ ⟩ with proj-nth i Ks γ' e
...   | ⟨ refl , eq ⟩ =
  ⟨ component-just i vs e , ≃-trans (≃-sym (tuple-proj i Ks {K} γ' vs ne eq)) (proj-≃ i Kt≃) ⟩

{- a known integer -}
int-ok : ∀ k {n γ' D} → int-of k ≡ just n → (∀ {K} → k ≡ just K → SV K × ⟦ K ⟧ γ' ≃ D)
  → ⟦ lit Int n ⦅ Nil ⦆ ⟧ γ' ≃ D
int-ok (just K) {γ' = γ'} e h with int-of-just (proj₁ (h refl)) e
... | refl = proj₂ (h refl)

{- the result of a primitive -}
prim-term-≃ : ∀ o γ → ⟦ prim-term o ⟧ γ ≃ ⌈ out o ⌉
prim-term-≃ (int n) γ = ⟨ (λ { (const {Int} n') ⟨ refl , refl ⟩ → refl }) , (λ { _ refl → ⟨ refl , refl ⟩ }) ⟩
prim-term-≃ (bool true) γ = ⟨ (λ { (left ⟨⟩) tt → refl }) , (λ { _ refl → tt }) ⟩
prim-term-≃ (bool false) γ = ⟨ (λ { (right ⟨⟩) tt → refl }) , (λ { _ refl → tt }) ⟩

prim-fold : ∀ p n m γ → primD p ⟨ ⟦ lit Int n ⦅ Nil ⦆ ⟧ γ , ⟨ ⟦ lit Int m ⦅ Nil ⦆ ⟧ γ , ptt ⟩ ⟩ ≃ ⌈ out (δ p n m) ⌉
prim-fold p n m γ =
  ⟨ (λ { _ ⟨ n' , ⟨ m' , ⟨ ⟨ refl , refl ⟩ , ⟨ ⟨ refl , refl ⟩ , refl ⟩ ⟩ ⟩ ⟩ → refl })
  , (λ { _ refl → ⟨ n , ⟨ m , ⟨ ⟨ refl , refl ⟩ , ⟨ ⟨ refl , refl ⟩ , refl ⟩ ⟩ ⟩ ⟩ }) ⟩

{- The main lemma ------------------------------------------------------------------}

simp-ok : ∀ M {E γ γ'} → Wf γ → Wf γ' → Ok E γ γ' → Desc (simp E M) γ' (⟦ M ⟧ γ)
simp-args-ok : ∀ {n} (as : Args (replicate n ■)) {E γ γ'} → Wf γ → Wf γ' → Ok E γ γ'
  → ∀ i → nthD (⟦ simp-args E as ⟧₊ γ') i ≃ nthD (⟦ as ⟧₊ γ) i
app-ok : ∀ L M {E γ γ' I} → Wf γ → Wf γ' → Ok E γ γ' → Desc I γ' (⟦ M ⟧ γ)
  → Desc (simp-app E L I) γ' (⟦ app ⦅ L ,, M ,, Nil ⦆ ⟧ γ)
let-ok : ∀ N M {E γ γ' I} → Wf γ → Wf γ' → Ok E γ γ' → Desc I γ' (⟦ M ⟧ γ)
  → Desc (simp-let E N I) γ' (⟦ app ⦅ lam ⦅ ⟩ N ,, Nil ⦆ ,, M ,, Nil ⦆ ⟧ γ)
case-ok : ∀ L M N {E γ γ' I} → Wf γ → Wf γ' → Ok E γ γ' → Desc I γ' (⟦ L ⟧ γ)
  → Desc (simp-case E I M N) γ' (⟦ case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆ ⟧ γ)

{- a body under a binder that stays -}
under-ok : ∀ N {E γ γ'} → Wf γ → Wf γ' → Ok E γ γ' → ∀ V → V ≢ [] → V ≈ V
  → ⟦ term (simp (under E) N) ⟧ (mem V • γ') ≃ ⟦ N ⟧ (mem V • γ)
under-ok N wf wf' ok V ne c =
  tm (simp-ok N (wf-• wf (E≢[]⇒nonempty-mem ne) (≈⇒Con c)) (wf-• wf' (E≢[]⇒nonempty-mem ne) (≈⇒Con c))
                 (ok-under (mem V) ok))

simp-ok (` x) wf wf' ok = ok x
simp-ok (lam ⦅ ⟩ N ,, Nil ⦆) wf wf' ok = desc-self P.lam (Λ-≃ (under-ok N wf wf' ok))
simp-ok (app ⦅ L ,, M ,, Nil ⦆) wf wf' ok = app-ok L M wf wf' ok (simp-ok M wf wf' ok)
simp-ok (lit B k ⦅ Nil ⦆) wf wf' ok = desc-self P.lit ≃-refl
simp-ok (tuple n ⦅ as ⦆) wf wf' ok = desc-info (𝒯-≃ n (simp-args-ok as wf wf' ok))
simp-ok (get i ⦅ L ,, Nil ⦆) {E} {γ' = γ'} wf wf' ok = get-ok (simp E L) (simp-ok L wf wf' ok)
  where
  get-ok : ∀ I → Desc I γ' (⟦ L ⟧ _) → Desc (simp-get i I) γ' (⟦ get i ⦅ L ,, Nil ⦆ ⟧ _)
  get-ok I d with component i (known I) in e
  ... | nothing = desc (proj-≃ i (tm d)) (λ ())
  ... | just K with component-ok i (known I) e (proj₁ wf') (kn d) | small K
  ...   | ⟨ v , K≃ ⟩ | true = desc-self v K≃
  ...   | ⟨ v , K≃ ⟩ | false = desc (proj-≃ i (tm d)) (λ { refl → ⟨ v , K≃ ⟩ })
simp-ok (inl-op ⦅ M ,, Nil ⦆) wf wf' ok = desc-info (inl-≃ (tm (simp-ok M wf wf' ok)))
simp-ok (inr-op ⦅ M ,, Nil ⦆) wf wf' ok = desc-info (inr-≃ (tm (simp-ok M wf wf' ok)))
simp-ok (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) wf wf' ok = case-ok L M N wf wf' ok (simp-ok L wf wf' ok)
simp-ok (prim p ⦅ L ,, M ,, Nil ⦆) {E} {γ = γ} {γ'} wf wf' ok =
  prim-ok (simp E L) (simp E M) (simp-ok L wf wf' ok) (simp-ok M wf wf' ok)
  where
  dflt : ∀ {I J} → Desc I γ' (⟦ L ⟧ γ) → Desc J γ' (⟦ M ⟧ γ)
    → Desc (prim p ⦅ term I ,, term J ,, Nil ⦆ ∣ nothing) γ' (⟦ prim p ⦅ L ,, M ,, Nil ⦆ ⟧ γ)
  dflt dI dJ = desc (primD-≃ p (tm dI) (tm dJ)) (λ ())
  prim-ok : ∀ I J → Desc I γ' (⟦ L ⟧ γ) → Desc J γ' (⟦ M ⟧ γ) → Desc (simp-prim p I J) γ' (⟦ prim p ⦅ L ,, M ,, Nil ⦆ ⟧ γ)
  prim-ok I J dI dJ with int-of (known I) in e₁
  ... | nothing = dflt dI dJ
  ... | just n with int-of (known J) in e₂
  ...   | nothing = dflt dI dJ
  ...   | just m =
    desc-self (prim-term-sv _)
      (≃-trans (prim-term-≃ (δ p n m) γ')
        (≃-sym (≃-trans (primD-≃ p (≃-sym (int-ok (known I) e₁ (kn dI))) (≃-sym (int-ok (known J) e₂ (kn dJ))))
                        (prim-fold p n m γ'))))

simp-args-ok {suc n} (M ,, as) wf wf' ok zero = tm (simp-ok M wf wf' ok)
simp-args-ok {suc n} (M ,, as) wf wf' ok (suc i) = simp-args-ok as wf wf' ok i

{- an application whose operator is not a function stays -}
app-ok (lam ⦅ ⟩ N ,, Nil ⦆) M wf wf' ok d = let-ok N M wf wf' ok d
app-ok (` x) M wf wf' ok d = desc (⋆-≃ (tm (simp-ok (` x) wf wf' ok)) (tm d)) (λ ())
app-ok L@(app ⦅ _ ⦆) M wf wf' ok d = desc (⋆-≃ (tm (simp-ok L wf wf' ok)) (tm d)) (λ ())
app-ok L@(lit B k ⦅ _ ⦆) M wf wf' ok d = desc (⋆-≃ (tm (simp-ok L wf wf' ok)) (tm d)) (λ ())
app-ok L@(tuple n ⦅ _ ⦆) M wf wf' ok d = desc (⋆-≃ (tm (simp-ok L wf wf' ok)) (tm d)) (λ ())
app-ok L@(get i ⦅ _ ⦆) M wf wf' ok d = desc (⋆-≃ (tm (simp-ok L wf wf' ok)) (tm d)) (λ ())
app-ok L@(inl-op ⦅ _ ⦆) M wf wf' ok d = desc (⋆-≃ (tm (simp-ok L wf wf' ok)) (tm d)) (λ ())
app-ok L@(inr-op ⦅ _ ⦆) M wf wf' ok d = desc (⋆-≃ (tm (simp-ok L wf wf' ok)) (tm d)) (λ ())
app-ok L@(case-op ⦅ _ ⦆) M wf wf' ok d = desc (⋆-≃ (tm (simp-ok L wf wf' ok)) (tm d)) (λ ())
app-ok L@(prim p ⦅ _ ⦆) M wf wf' ok d = desc (⋆-≃ (tm (simp-ok L wf wf' ok)) (tm d)) (λ ())

{- β: the operand is substituted if it is small, and stays bound, and
   known, if it is another value -}
let-ok N M {E} {γ} {γ'} {I} wf wf' ok d with small (term I) in s | value (term I) in v
... | true | _ = desc-≃ (simp-ok N (wf-• wf neM cM) wf' ok') (≃-sym (beta N M γ (proj₁ wf) neM cM))
  where
  sv = small-sv (term I) s
  neM = ⟨ _ , proj₁ (tm d) _ (proj₂ (sv-ne sv (proj₁ wf'))) ⟩
  cM = ISWIM-con-env M (proj₂ wf)
  ok' : Ok (self (term I) • E) (⟦ M ⟧ γ • γ) γ'
  ok' zero = desc-self sv (tm d)
  ok' (suc x) = ok x
... | false | true =
  desc (≃-trans (beta N' (term I) γ' (proj₁ wf') neM' cM')
          (≃-trans (tm (simp-ok N (wf-• wf neM cM) (wf-• wf' neM' cM') ok')) (≃-sym (beta N M γ (proj₁ wf) neM cM))))
       (λ ())
  where
  sv = value-sv (term I) v
  N' = term (simp (((` 0) ∣ just (shift (term I))) • (λ x → shift-info (E x))) N)
  neM' = sv-ne sv (proj₁ wf')
  cM' = ISWIM-con-env (term I) (proj₂ wf')
  neM = ⟨ _ , proj₁ (tm d) _ (proj₂ neM') ⟩
  cM = ISWIM-con-env M (proj₂ wf)
  ok' : Ok (((` 0) ∣ just (shift (term I))) • (λ x → shift-info (E x))) (⟦ M ⟧ γ • γ) (⟦ term I ⟧ γ' • γ')
  ok' zero = desc (tm d) (λ { refl → ⟨ sv-rename suc sv , ≃-trans (shift-≃ (term I) _ γ') (tm d) ⟩ })
  ok' (suc x) = desc-shift {E x} (ok x)
... | false | false = desc (⋆-≃ (Λ-≃ {λ X → ⟦ term (simp (under E) N) ⟧ (X • γ')} {λ X → ⟦ N ⟧ (X • γ)} (under-ok N wf wf' ok)) (tm d)) (λ ())

{- a case on a known injection takes its branch -}
case-ok L M N {E} {γ} {γ'} {I} wf wf' ok d with branch (known I) in e
... | nothing =
  desc (𝒞-≃ {F = λ X → ⟦ term (simp (under E) M) ⟧ (X • γ')} {λ X → ⟦ M ⟧ (X • γ)}
             {λ X → ⟦ term (simp (under E) N) ⟧ (X • γ')} {λ X → ⟦ N ⟧ (X • γ)}
             (tm d) (λ v V c → under-ok M wf wf' ok (v ∷ V) (λ ()) c) (λ v V c → under-ok N wf wf' ok (v ∷ V) (λ ()) c))
       (λ ())
... | just ⟨ true , K ⟩ = taken (known I) e (kn d)
  where
  taken : ∀ k → branch k ≡ just ⟨ true , K ⟩ → (∀ {Kt} → k ≡ just Kt → SV Kt × ⟦ Kt ⟧ γ' ≃ ⟦ L ⟧ γ)
    → Desc (simp (self K • E) M) γ' (⟦ case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆ ⟧ γ)
  taken (just Kt) e h with h refl
  taken (just Kt) e h | ⟨ P.inl {K₀} v , Kt≃ ⟩ with small K₀ | e
  taken (just Kt) e h | ⟨ P.inl {K₀} v , Kt≃ ⟩ | true | refl =
    desc-≃ (simp-ok M (wf-• wf neK cK) wf' ok') (≃-sym (case-inl L M N γ _ (≃-sym Kt≃) (proj₁ wf) neK cK))
    where
    neK = sv-ne v (proj₁ wf')
    cK = ISWIM-con-env K (proj₂ wf')
    ok' : Ok (self K • E) (⟦ K ⟧ γ' • γ) γ'
    ok' zero = desc-self v ≃-refl
    ok' (suc x) = ok x
  taken (just Kt) e h | ⟨ P.inl {K₀} v , Kt≃ ⟩ | false | ()
  taken (just Kt) e h | ⟨ P.inr {K₀} v , _ ⟩ with small K₀ | e
  taken (just Kt) e h | ⟨ P.inr {K₀} v , _ ⟩ | true | ()
  taken (just Kt) e h | ⟨ P.inr {K₀} v , _ ⟩ | false | ()
... | just ⟨ false , K ⟩ = taken (known I) e (kn d)
  where
  taken : ∀ k → branch k ≡ just ⟨ false , K ⟩ → (∀ {Kt} → k ≡ just Kt → SV Kt × ⟦ Kt ⟧ γ' ≃ ⟦ L ⟧ γ)
    → Desc (simp (self K • E) N) γ' (⟦ case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆ ⟧ γ)
  taken (just Kt) e h with h refl
  taken (just Kt) e h | ⟨ P.inr {K₀} v , Kt≃ ⟩ with small K₀ | e
  taken (just Kt) e h | ⟨ P.inr {K₀} v , Kt≃ ⟩ | true | refl =
    desc-≃ (simp-ok N (wf-• wf neK cK) wf' ok') (≃-sym (case-inr L M N γ _ (≃-sym Kt≃) (proj₁ wf) neK cK))
    where
    neK = sv-ne v (proj₁ wf')
    cK = ISWIM-con-env K (proj₂ wf')
    ok' : Ok (self K • E) (⟦ K ⟧ γ' • γ) γ'
    ok' zero = desc-self v ≃-refl
    ok' (suc x) = ok x
  taken (just Kt) e h | ⟨ P.inr {K₀} v , Kt≃ ⟩ | false | ()
  taken (just Kt) e h | ⟨ P.inl {K₀} v , _ ⟩ with small K₀ | e
  taken (just Kt) e h | ⟨ P.inl {K₀} v , _ ⟩ | true | ()
  taken (just Kt) e h | ⟨ P.inl {K₀} v , _ ⟩ | false | ()

{- The end theorem: every program, in the environment where every variable
   means {ω} -}
ρ₀ : Env Value
ρ₀ = λ _ → ⌈ ω ⌉

simplify-correct : ∀ M → ⟦ M ⟧ ρ₀ ≃ ⟦ simplify M ⟧ ρ₀
simplify-correct M = ≃-sym (tm (simp-ok M wf₀ wf₀ (λ x → desc-self (P.var x) ≃-refl)))
  where wf₀ = ⟨ (λ _ → ⟨ ω , refl ⟩) , (λ _ → Con-⌈⌉ ω) ⟩

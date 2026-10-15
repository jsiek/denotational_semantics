{-

  Correctness of the simplify pass (ISWIM → ISWIM) in the graph model.

  The main lemma (simp-ok): if what simp knows of each variable x is true
  of the source's environment γ in the target's γ' (Desc: γ x is denoted
  in γ' by the term that replaces x, and by what x is known to be), then
  what simp E M says of M is true: ⟦ M ⟧ γ is denoted in γ' by its term,
  and by what it is known to be. A known function λ N denotes ⟦ λ N ⟧ γf for a
  source environment γf of which its Facts are true (KDesc), so an
  inlined call is a call of ⟦ λ N ⟧ γf: β and inlining share let-ok.

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
open import proof.Framework.GraphModel.Prelude
open import proof.Framework.GraphModel.Ops
open import proof.Semantics.Graph.Prim
open import Language.ISWIM
open import Language.Prim using (Prim; Out; int; bool; δ)
open import proof.Semantics.Graph.ISWIM
open import proof.Compiler.SimplifyFacts as P
  using (Info; _∣_; term; known; Known; val; fun; Facts; self; info; under; known-as; shift-info; shift-known;
         simp; simp-args; simp-app; lam?; is-lam; other; simp-call; simp-let; size; inline-size; inline-fuel;
         simp-get; simp-case; simp-prim; simplify; small; value; component; branch; int-of; prim-term;
         SV; SVs; value-sv; small-sv; sv-rename; prim-term-sv; int-of-just; component-just)
open import proof.Framework.GraphModel.Env using (Env; nonempty-env; extend-nonempty-env; •-~)
open import proof.Framework.GraphModel.RenameSem Op sig using (shift-≃)
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
open import Data.Nat using (ℕ; zero; suc; _≤ᵇ_)
open import Data.Product using (_×_; Σ-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)

{- What simp knows, and what it means ----------------------------------------}

{- the environments: nonempty and consistent -}
Wf : Env Value → Set
Wf γ = nonempty-env γ × Con-env γ

wf-• : ∀ {D γ} → Wf γ → nonempty D → Con D → Wf (D • γ)
wf-• ⟨ ne , c ⟩ neD cD = ⟨ extend-nonempty-env ne neD , Con-• cD c ⟩

{- I is true of D in γ': its term denotes D, and so does what it is known
   to be (KDesc): a value, or a function λ N closed in a source
   environment γ of which its Facts are true -}
record Desc (D : 𝒫 Value) (I : Info) (γ' : Env Value) : Set₁
data KDesc : 𝒫 Value → Known → Env Value → Set₁

Ok : Facts → Env Value → Env Value → Set₁
Ok E γ γ' = ∀ x → Desc (γ x) (E x) γ'

record Desc D I γ' where
  inductive
  constructor desc
  field
    tm : D ≃ ⟦ term I ⟧ γ'
    kn : ∀ {K} → known I ≡ just K → KDesc D K γ'
open Desc

data KDesc where
  kval : ∀ {D K γ'} → SV K → D ≃ ⟦ K ⟧ γ' → KDesc D (val K) γ'
  kfun : ∀ {D N E γ'} γ → Wf γ → Ok E γ γ' → D ≃ ⟦ lam ⦅ ⟩ N ,, Nil ⦆ ⟧ γ → KDesc D (fun N E) γ'

kv : ∀ {D K γ'} → KDesc D (val K) γ' → SV K × D ≃ ⟦ K ⟧ γ'
kv (kval v eq) = ⟨ v , eq ⟩

desc-≃ : ∀ {D D' I γ'} → Desc D I γ' → D' ≃ D → Desc D' I γ'
desc-≃ {I = I} {γ'} d eq = desc (≃-trans eq (tm d)) (λ e → G _ (kn d e))
  where
  G : ∀ K → KDesc _ K γ' → KDesc _ K γ'
  G (val K) (kval v K≃) = kval v (≃-trans eq K≃)
  G (fun N E) (kfun γ wf ok F≃) = kfun γ wf ok (≃-trans eq F≃)

desc-self : ∀ {D V γ'} → SV V → D ≃ ⟦ V ⟧ γ' → Desc D (self V) γ'
desc-self v eq = desc eq (λ { refl → kval v eq })

desc-info : ∀ {D M γ'} → D ≃ ⟦ M ⟧ γ' → Desc D (info M) γ'
desc-info {M = M} eq with value M in e
... | true = desc eq (λ { refl → kval (value-sv M e) eq })
... | false = desc eq (λ ())

{- under one more binder, in the target -}
desc-shift : ∀ I {D γ'} X → Desc D I γ' → Desc D (shift-info I) (X • γ')
kdesc-shift : ∀ K {D γ'} X → KDesc D K γ' → KDesc D (shift-known K) (X • γ')
desc-shift (M ∣ nothing) {γ' = γ'} X d = desc (≃-trans (tm d) (≃-sym (shift-≃ M X γ'))) (λ ())
desc-shift (M ∣ just K) {γ' = γ'} X d = desc (≃-trans (tm d) (≃-sym (shift-≃ M X γ'))) (λ { refl → kdesc-shift K X (kn d refl) })
kdesc-shift (val K) {γ' = γ'} X (kval v K≃) = kval (sv-rename suc v) (≃-trans K≃ (≃-sym (shift-≃ K X γ')))
kdesc-shift (fun N E) X (kfun γ wf ok F≃) = kfun γ wf (λ x → desc-shift (E x) X (ok x)) F≃

ok-under : ∀ {E γ γ'} X → Ok E γ γ' → Ok (under E) (X • γ) (X • γ')
ok-under X ok zero = desc-self (P.var 0) ≃-refl
ok-under {E} X ok (suc x) = desc-shift (E x) X (ok x)

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

case-inl : ∀ L M N γ D → ⟦ L ⟧ γ ≃ inl ⟨ D , ptt ⟩ → nonempty-env γ → nonempty D → Con D
  → ⟦ case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆ ⟧ γ ≃ ⟦ M ⟧ (D • γ)
case-inl L M N γ D L≃ ne neD cD =
  ≃-trans (𝒞-≃ {F = F} {F} {G} {G} L≃ (λ _ _ _ → ≃-refl) (λ _ _ _ → ≃-refl))
          (𝒞-inl-β {D} {F} {G} (body-mono M γ) (body-continuous M γ ne D neD) cD)
  where F = λ X → ⟦ M ⟧ (X • γ)
        G = λ X → ⟦ N ⟧ (X • γ)

case-inr : ∀ L M N γ D → ⟦ L ⟧ γ ≃ inr ⟨ D , ptt ⟩ → nonempty-env γ → nonempty D → Con D
  → ⟦ case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆ ⟧ γ ≃ ⟦ N ⟧ (D • γ)
case-inr L M N γ D L≃ ne neD cD =
  ≃-trans (𝒞-≃ {F = F} {F} {G} {G} L≃ (λ _ _ _ → ≃-refl) (λ _ _ _ → ≃-refl))
          (𝒞-inr-β {D} {F} {G} (body-mono N γ) (body-continuous N γ ne D neD) cD)
  where F = λ X → ⟦ M ⟧ (X • γ)
        G = λ X → ⟦ N ⟧ (X • γ)

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
  → (∀ {Kt} → k ≡ just Kt → KDesc D Kt γ') → SV K × proj i ⟨ D , ptt ⟩ ≃ ⟦ K ⟧ γ'
component-ok i (just (val Kt)) {K} {γ'} e ne h with kv (h refl)
... | ⟨ P.tuple {m} {Ks} vs , Kt≃ ⟩ with proj-nth i Ks γ' e
...   | ⟨ refl , eq ⟩ =
  ⟨ component-just i vs e , ≃-trans (proj-≃ i Kt≃) (tuple-proj i Ks {K} γ' vs ne eq) ⟩

{- a known integer -}
int-ok : ∀ k {n γ' D} → int-of k ≡ just n → (∀ {K} → k ≡ just K → KDesc D K γ')
  → D ≃ ⟦ lit Int n ⦅ Nil ⦆ ⟧ γ'
int-ok (just (val K)) {γ' = γ'} e h with int-of-just (proj₁ (kv (h refl))) e
... | refl = proj₂ (kv (h refl))

{- the result of a primitive -}
prim-term-≃ : ∀ o γ → ⌈ out o ⌉ ≃ ⟦ prim-term o ⟧ γ
prim-term-≃ (int n) γ = ⟨ (λ { _ refl → ⟨ refl , refl ⟩ }) , (λ { (const {Int} n') ⟨ refl , refl ⟩ → refl }) ⟩
prim-term-≃ (bool true) γ = ⟨ (λ { _ refl → tt }) , (λ { (left ⟨⟩) tt → refl }) ⟩
prim-term-≃ (bool false) γ = ⟨ (λ { _ refl → tt }) , (λ { (right ⟨⟩) tt → refl }) ⟩

prim-fold : ∀ p n m γ → primD p ⟨ ⟦ lit Int n ⦅ Nil ⦆ ⟧ γ , ⟨ ⟦ lit Int m ⦅ Nil ⦆ ⟧ γ , ptt ⟩ ⟩ ≃ ⌈ out (δ p n m) ⌉
prim-fold p n m γ =
  ⟨ (λ { _ ⟨ n' , ⟨ m' , ⟨ ⟨ refl , refl ⟩ , ⟨ ⟨ refl , refl ⟩ , refl ⟩ ⟩ ⟩ ⟩ → refl })
  , (λ { _ refl → ⟨ n , ⟨ m , ⟨ ⟨ refl , refl ⟩ , ⟨ ⟨ refl , refl ⟩ , refl ⟩ ⟩ ⟩ ⟩ }) ⟩

{- The main lemma ------------------------------------------------------------------}

simp-ok : ∀ fl M {E γ γ'} → Wf γ → Wf γ' → Ok E γ γ' → Desc (⟦ M ⟧ γ) (simp fl E M) γ'
simp-args-ok : ∀ fl {n} (as : Args (replicate n ■)) {E γ γ'} → Wf γ → Wf γ' → Ok E γ γ'
  → ∀ i → nthD (⟦ as ⟧₊ γ) i ≃ nthD (⟦ simp-args fl E as ⟧₊ γ') i
app-ok : ∀ fl L M {E γ γ' I} → Wf γ → Wf γ' → Ok E γ γ' → Desc (⟦ M ⟧ γ) I γ'
  → Desc (⟦ app ⦅ L ,, M ,, Nil ⦆ ⟧ γ) (simp-app fl E L I) γ'
let-ok : ∀ fl N {E γ γ' I D} → Wf γ → Wf γ' → Ok E γ γ' → Desc D I γ' → Con D
  → Desc (⋆ ⟨ ⟦ lam ⦅ ⟩ N ,, Nil ⦆ ⟧ γ , ⟨ D , ptt ⟩ ⟩) (simp-let fl E N I) γ'
call-ok : ∀ fl J I {γ' F D} → Wf γ' → Desc F J γ' → Desc D I γ' → Con D
  → Desc (⋆ ⟨ F , ⟨ D , ptt ⟩ ⟩) (simp-call fl J I) γ'
case-ok : ∀ fl L M N {E γ γ' I} → Wf γ → Wf γ' → Ok E γ γ' → Desc (⟦ L ⟧ γ) I γ'
  → Desc (⟦ case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆ ⟧ γ) (simp-case fl E I M N) γ'

{- a body under a binder that stays -}
under-ok : ∀ fl N {E γ γ'} → Wf γ → Wf γ' → Ok E γ γ' → ∀ V → V ≢ [] → V ≈ V
  → ⟦ N ⟧ (mem V • γ) ≃ ⟦ term (simp fl (under E) N) ⟧ (mem V • γ')
under-ok fl N wf wf' ok V ne c =
  tm (simp-ok fl N (wf-• wf (E≢[]⇒nonempty-mem ne) (≈⇒Con c)) (wf-• wf' (E≢[]⇒nonempty-mem ne) (≈⇒Con c))
                 (ok-under (mem V) ok))

simp-ok fl (` x) wf wf' ok = ok x
simp-ok fl (lam ⦅ ⟩ N ,, Nil ⦆) {γ = γ} wf wf' ok =
  desc (Λ-≃ (under-ok fl N wf wf' ok)) (λ { refl → kfun γ wf ok ≃-refl })
simp-ok fl (app ⦅ L ,, M ,, Nil ⦆) wf wf' ok = app-ok fl L M wf wf' ok (simp-ok fl M wf wf' ok)
simp-ok fl (lit B k ⦅ Nil ⦆) wf wf' ok = desc-self P.lit ≃-refl
simp-ok fl (tuple n ⦅ as ⦆) wf wf' ok = desc-info (𝒯-≃ n (simp-args-ok fl as wf wf' ok))
simp-ok fl (get i ⦅ L ,, Nil ⦆) {E} {γ' = γ'} wf wf' ok = get-ok (simp fl E L) (simp-ok fl L wf wf' ok)
  where
  get-ok : ∀ I → Desc (⟦ L ⟧ _) I γ' → Desc (⟦ get i ⦅ L ,, Nil ⦆ ⟧ _) (simp-get i I) γ'
  get-ok I d with component i (known I) in e
  ... | nothing = desc (proj-≃ i (tm d)) (λ ())
  ... | just K with component-ok i (known I) e (proj₁ wf') (kn d) | small K
  ...   | ⟨ v , K≃ ⟩ | true = desc-self v K≃
  ...   | ⟨ v , K≃ ⟩ | false = desc (proj-≃ i (tm d)) (λ { refl → kval v K≃ })
simp-ok fl (inl-op ⦅ M ,, Nil ⦆) wf wf' ok = desc-info (inl-≃ (tm (simp-ok fl M wf wf' ok)))
simp-ok fl (inr-op ⦅ M ,, Nil ⦆) wf wf' ok = desc-info (inr-≃ (tm (simp-ok fl M wf wf' ok)))
simp-ok fl (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) wf wf' ok = case-ok fl L M N wf wf' ok (simp-ok fl L wf wf' ok)
simp-ok fl (prim p ⦅ L ,, M ,, Nil ⦆) {E} {γ = γ} {γ'} wf wf' ok =
  prim-ok (simp fl E L) (simp fl E M) (simp-ok fl L wf wf' ok) (simp-ok fl M wf wf' ok)
  where
  dflt : ∀ {I J} → Desc (⟦ L ⟧ γ) I γ' → Desc (⟦ M ⟧ γ) J γ'
    → Desc (⟦ prim p ⦅ L ,, M ,, Nil ⦆ ⟧ γ) (prim p ⦅ term I ,, term J ,, Nil ⦆ ∣ nothing) γ'
  dflt dI dJ = desc (primD-≃ p (tm dI) (tm dJ)) (λ ())
  prim-ok : ∀ I J → Desc (⟦ L ⟧ γ) I γ' → Desc (⟦ M ⟧ γ) J γ' → Desc (⟦ prim p ⦅ L ,, M ,, Nil ⦆ ⟧ γ) (simp-prim p I J) γ'
  prim-ok I J dI dJ with int-of (known I) in e₁
  ... | nothing = dflt dI dJ
  ... | just n with int-of (known J) in e₂
  ...   | nothing = dflt dI dJ
  ...   | just m =
    desc-self (prim-term-sv _)
      (≃-trans (≃-trans (primD-≃ p (int-ok (known I) e₁ (kn dI)) (int-ok (known J) e₂ (kn dJ))) (prim-fold p n m γ'))
        (prim-term-≃ (δ p n m) γ'))

simp-ok fl (let-op ⦅ M ,, ⟩ N ,, Nil ⦆) wf wf' ok =
  let-ok fl N wf wf' ok (simp-ok fl M wf wf' ok) (ISWIM-con-env M (proj₂ wf))

simp-args-ok fl {suc n} (M ,, as) wf wf' ok zero = tm (simp-ok fl M wf wf' ok)
simp-args-ok fl {suc n} (M ,, as) wf wf' ok (suc i) = simp-args-ok fl as wf wf' ok i

{- an application: β if the operator is a function, and otherwise a call -}
app-ok fl L M wf wf' ok d with lam? L
... | is-lam N = let-ok fl N wf wf' ok d (ISWIM-con-env M (proj₂ wf))
... | other = call-ok fl _ _ wf' (simp-ok fl L wf wf' ok) d (ISWIM-con-env M (proj₂ wf))

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
  ok' : Ok (I • E) (D • γ) γ'
  ok' zero = d
  ok' (suc x) = ok x
... | false | true =
  desc (≃-trans (let-β N γ D (proj₁ wf) neD cD)
          (≃-trans (tm (simp-ok fl N (wf-• wf neD cD) (wf-• wf' neV cV) ok')) (≃-sym (let-β N' γ' _ (proj₁ wf') neV cV))))
       (λ ())
  where
  N' = term (simp fl (known-as I E) N)
  neV = sv-ne (value-sv (term I) v) (proj₁ wf')
  cV = ISWIM-con-env (term I) (proj₂ wf')
  neD = ⟨ _ , proj₂ (tm d) _ (proj₂ neV) ⟩
  ok' : Ok (known-as I E) (D • γ) (⟦ term I ⟧ γ' • γ')
  ok' zero = desc (tm d) (kn (desc-shift I _ d))
  ok' (suc x) = desc-shift (E x) _ (ok x)
... | false | false =
  desc (⋆-≃ (Λ-≃ {λ X → ⟦ N ⟧ (X • γ)} {λ X → ⟦ term (simp fl (under E) N) ⟧ (X • γ')} (under-ok fl N wf wf' ok)) (tm d)) (λ ())

{- a case on a known injection takes its branch -}
case-ok fl L M N {E} {γ} {γ'} {I} wf wf' ok d with branch (known I) in e
... | nothing =
  desc (𝒞-≃ {F = λ X → ⟦ M ⟧ (X • γ)} {λ X → ⟦ term (simp fl (under E) M) ⟧ (X • γ')}
             {λ X → ⟦ N ⟧ (X • γ)} {λ X → ⟦ term (simp fl (under E) N) ⟧ (X • γ')}
             (tm d) (λ v V c → under-ok fl M wf wf' ok (v ∷ V) (λ ()) c) (λ v V c → under-ok fl N wf wf' ok (v ∷ V) (λ ()) c))
       (λ ())
... | just ⟨ true , K ⟩ = taken (known I) e (kn d)
  where
  taken : ∀ k → branch k ≡ just ⟨ true , K ⟩ → (∀ {Kt} → k ≡ just Kt → KDesc (⟦ L ⟧ γ) Kt γ')
    → Desc (⟦ case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆ ⟧ γ) (simp fl (self K • E) M) γ'
  taken (just (val Kt)) e h with kv (h refl)
  taken (just (val Kt)) e h | ⟨ P.inl {K₀} v , Kt≃ ⟩ with small K₀ | e
  taken (just (val Kt)) e h | ⟨ P.inl {K₀} v , Kt≃ ⟩ | true | refl =
    desc-≃ (simp-ok fl M (wf-• wf neK cK) wf' ok') (case-inl L M N γ _ Kt≃ (proj₁ wf) neK cK)
    where
    neK = sv-ne v (proj₁ wf')
    cK = ISWIM-con-env K (proj₂ wf')
    ok' : Ok (self K • E) (⟦ K ⟧ γ' • γ) γ'
    ok' zero = desc-self v ≃-refl
    ok' (suc x) = ok x
  taken (just (val Kt)) e h | ⟨ P.inl {K₀} v , Kt≃ ⟩ | false | ()
  taken (just (val Kt)) e h | ⟨ P.inr {K₀} v , _ ⟩ with small K₀ | e
  taken (just (val Kt)) e h | ⟨ P.inr {K₀} v , _ ⟩ | true | ()
  taken (just (val Kt)) e h | ⟨ P.inr {K₀} v , _ ⟩ | false | ()
... | just ⟨ false , K ⟩ = taken (known I) e (kn d)
  where
  taken : ∀ k → branch k ≡ just ⟨ false , K ⟩ → (∀ {Kt} → k ≡ just Kt → KDesc (⟦ L ⟧ γ) Kt γ')
    → Desc (⟦ case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆ ⟧ γ) (simp fl (self K • E) N) γ'
  taken (just (val Kt)) e h with kv (h refl)
  taken (just (val Kt)) e h | ⟨ P.inr {K₀} v , Kt≃ ⟩ with small K₀ | e
  taken (just (val Kt)) e h | ⟨ P.inr {K₀} v , Kt≃ ⟩ | true | refl =
    desc-≃ (simp-ok fl N (wf-• wf neK cK) wf' ok') (case-inr L M N γ _ Kt≃ (proj₁ wf) neK cK)
    where
    neK = sv-ne v (proj₁ wf')
    cK = ISWIM-con-env K (proj₂ wf')
    ok' : Ok (self K • E) (⟦ K ⟧ γ' • γ) γ'
    ok' zero = desc-self v ≃-refl
    ok' (suc x) = ok x
  taken (just (val Kt)) e h | ⟨ P.inr {K₀} v , Kt≃ ⟩ | false | ()
  taken (just (val Kt)) e h | ⟨ P.inl {K₀} v , _ ⟩ with small K₀ | e
  taken (just (val Kt)) e h | ⟨ P.inl {K₀} v , _ ⟩ | true | ()
  taken (just (val Kt)) e h | ⟨ P.inl {K₀} v , _ ⟩ | false | ()

{- The end theorem: every program, in the environment where every variable
   means {ω} -}
simplify-correct : ∀ M → ⟦ M ⟧ ρ₀ ≃ ⟦ simplify M ⟧ ρ₀
simplify-correct M = tm (simp-ok inline-fuel M wf₀ wf₀ (λ x → desc-self (P.var x) ≃-refl))
  where wf₀ = ⟨ (λ _ → ⟨ ω , refl ⟩) , (λ _ → Con-⌈⌉ ω) ⟩

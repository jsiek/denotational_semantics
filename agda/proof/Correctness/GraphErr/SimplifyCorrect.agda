{-

  Correctness of the simplify pass (ISWIM → ISWIM) in the graph model with
  errors (Semantics/GraphErr/ISWIM.agda).

  The proof is that of the graph model (proof/Correctness/Graph/
  SimplifyCorrect.agda), with environments that also hold no ω (Wf):
  simplify duplicates and drops values only, and a variable stands for a
  value, so the variables must not stand for errors. That holds under
  the binders, which bind no ω, but not in ρ₀, where a variable not in
  scope means {ω}: so the end theorem is for closed programs, which mean
  the same in every environment (proof/Framework/GraphModel/
  SemanticsUses.agda). (For an open program, simplify can drop an error:
  let y = x in 0 becomes 0, while x is an error in ρ₀. The machine, too,
  stops with an error on a free variable, and the operational proofs are
  for closed programs.)

  The transformations rest on β for a value (let, case, projection, and
  constant folding), whose operand denotes a nonempty, consistent set of
  values without ω; an error in an operand that simplify keeps is kept
  by congruence.

-}

module proof.Correctness.GraphErr.SimplifyCorrect where

open import Framework.Primitives using (Int)
open import Framework.Syntax.SyntaxUtil
open import proof.Framework.GraphModel.ErrorPrelude
open import proof.Framework.GraphModel.Ops using (𝒯-mono; inl; inr)
open import Level using (lower)
open import proof.Semantics.GraphErr.Prim
open import Language.ISWIM
open import Language.Prim using (Prim; Out; int; bool; δ)
open import proof.Semantics.GraphErr.ISWIM
open import proof.Compiler.SimplifyFacts as P
  using (Info; _∣_; term; known; Known; val; fun; Facts; self; info; under; known-as; shift-info; shift-known;
         simp; simp-args; simp-app; lam?; is-lam; other; simp-call; simp-let; size; inline-size; inline-fuel;
         simp-get; simp-case; simp-prim; simplify; small; value; component; branch; int-of; prim-term;
         SV; SVs; value-sv; small-sv; sv-rename; prim-term-sv; int-of-just; component-just)
open import proof.Compiler.SimplifyScope using (simplify-closed)
open import Compiler.CaptureScope using (Closed)
open import proof.Framework.GraphModel.Env using (Env; nonempty-env; extend-nonempty-env; •-~)
open import proof.Framework.GraphModel.RenameSem Op sig using (shift-≃)
open import proof.Framework.GraphModel.SemanticsUses Op sig using (⟦⟧-closed₀)
open import proof.Framework.Syntax.Uses Op sig using (Uses; uses-bound)
open import Framework.ListUtil using (args→list; has-length) renaming (proj to proj-list)

open import Data.Bool using (true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_; replicate)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _≤ᵇ_)
open import Data.Nat.Properties using (n≮0)
open import Data.Product using (_×_; Σ-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)

{- What simp knows, and what it means ----------------------------------------}

{- the environments: nonempty, consistent, and without errors -}
Wf : Env Value → Set
Wf γ = nonempty-env γ × Con-env γ × (∀ x → Clean (γ x))

wf-• : ∀ {D γ} → Wf γ → Con D → Val D → Wf (D • γ)
wf-• ⟨ ne , ⟨ c , cl ⟩ ⟩ cD ⟨ clD , neD ⟩ =
  ⟨ extend-nonempty-env ne neD , ⟨ Con-• cD c , (λ { zero → clD ; (suc x) → cl x }) ⟩ ⟩

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

desc-≃ : ∀ {D D' I γ'} → D ≃ D' → Desc D' I γ' → Desc D I γ'
desc-≃ {I = I} {γ'} eq d = desc (≃-trans eq (tm d)) (λ e → G _ (kn d e))
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

desc-shift : ∀ I {D γ'} X → Desc D I γ' → Desc D (shift-info I) (X • γ')
kdesc-shift : ∀ K {D γ'} X → KDesc D K γ' → KDesc D (shift-known K) (X • γ')
desc-shift (M ∣ nothing) {γ' = γ'} X d = desc (≃-trans (tm d) (≃-sym (shift-≃ M X γ'))) (λ ())
desc-shift (M ∣ just K) {γ' = γ'} X d = desc (≃-trans (tm d) (≃-sym (shift-≃ M X γ'))) (λ { refl → kdesc-shift K X (kn d refl) })
kdesc-shift (val K) {γ' = γ'} X (kval v K≃) = kval (sv-rename suc v) (≃-trans K≃ (≃-sym (shift-≃ K X γ')))
kdesc-shift (fun N E) X (kfun γ wf ok F≃) = kfun γ wf (λ x → desc-shift (E x) X (ok x)) F≃

ok-under : ∀ {E γ γ'} X → Ok E γ γ' → Ok (under E) (X • γ) (X • γ')
ok-under X ok zero = desc-self (P.var 0) ≃-refl
ok-under {E} X ok (suc x) = desc-shift (E x) X (ok x)

{- Values denote sets of values without errors --------------------------------}

sv-val : ∀ {V γ} → SV V → Wf γ → Val (⟦ V ⟧ γ)
svs-val : ∀ {n} {as : Args (replicate n ■)} {γ} → SVs as → Wf γ → AllVal n (⟦ as ⟧₊ γ)
sv-val (P.var x) ⟨ ne , ⟨ _ , cl ⟩ ⟩ = ⟨ cl x , ne x ⟩
sv-val P.lam wf = ⟨ Λᵐ-clean , ⟨ ν , ⟨ tt , tt ⟩ ⟩ ⟩
sv-val P.lit wf = ⟨ (λ { .ω () refl }) , ⟨ _ , ⟨ refl , refl ⟩ ⟩ ⟩
sv-val (P.tuple {n} vs) wf = 𝒯ᵐ-val n (svs-val vs wf)
sv-val (P.inl v) wf = inlᵐ-val (sv-val v wf)
sv-val (P.inr v) wf = inrᵐ-val (sv-val v wf)
svs-val (v P.∷ vs) wf zero = sv-val v wf
svs-val (v P.∷ vs) wf (suc i) = svs-val vs wf i

{- β for a value ----------------------------------------------------------------}

let-β : ∀ N γ D → Wf γ → Con D → Val D
  → letᵐ ⟨ D , ⟨ (λ X → ⟦ N ⟧ (X • γ)) , ptt ⟩ ⟩ ≃ ⟦ N ⟧ (D • γ)
let-β N γ D wf cD vD = letᵐ-β (body-mono N γ) (body-continuous N γ (proj₁ wf) D (proj₂ vD)) cD vD

case-inl : ∀ L M N γ D → ⟦ L ⟧ γ ≃ inlᵐ ⟨ D , ptt ⟩ → Wf γ → Con D → Val D
  → ⟦ case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆ ⟧ γ ≃ ⟦ M ⟧ (D • γ)
case-inl L M N γ D L≃ wf cD vD =
  ≃-trans (𝒞ᵐ-≃ {F = F} {F} {G} {G} L≃ (λ _ _ _ _ → ≃-refl) (λ _ _ _ _ → ≃-refl))
          (𝒞ᵐ-inl-β {D} {F} {G} (body-mono M γ) (body-continuous M γ (proj₁ wf) D (proj₂ vD)) cD vD)
  where F = λ X → ⟦ M ⟧ (X • γ)
        G = λ X → ⟦ N ⟧ (X • γ)

case-inr : ∀ L M N γ D → ⟦ L ⟧ γ ≃ inrᵐ ⟨ D , ptt ⟩ → Wf γ → Con D → Val D
  → ⟦ case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆ ⟧ γ ≃ ⟦ N ⟧ (D • γ)
case-inr L M N γ D L≃ wf cD vD =
  ≃-trans (𝒞ᵐ-≃ {F = F} {F} {G} {G} L≃ (λ _ _ _ _ → ≃-refl) (λ _ _ _ _ → ≃-refl))
          (𝒞ᵐ-inr-β {D} {F} {G} (body-mono N γ) (body-continuous N γ (proj₁ wf) D (proj₂ vD)) cD vD)
  where F = λ X → ⟦ M ⟧ (X • γ)
        G = λ X → ⟦ N ⟧ (X • γ)

{- Known tuples and integers ------------------------------------------------------}

has-length-≡ : ∀ n {m} (Ks : Args (replicate m ■)) → has-length n (args→list Ks) ≡ true → n ≡ m
has-length-≡ zero {zero} Nil _ = refl
has-length-≡ zero {suc m} (K ,, Ks) ()
has-length-≡ (suc n) {suc m} (K ,, Ks) e = cong suc (has-length-≡ n Ks e)

proj-nth : ∀ {n} (i : Fin n) {m} (Ks : Args (replicate m ■)) {K} γ → proj-list i (args→list Ks) ≡ just K
  → Σ[ e ∈ n ≡ m ] nthD (⟦ Ks ⟧₊ γ) (subst Fin e i) ≡ ⟦ K ⟧ γ
proj-nth {suc n} zero {suc m} (K₀ ,, Ks) γ e with has-length n (args→list Ks) in h
proj-nth {suc n} zero {suc m} (K₀ ,, Ks) γ refl | true with has-length-≡ n Ks h
... | refl = ⟨ refl , refl ⟩
proj-nth (suc i) {suc m} (K₀ ,, Ks) γ e with proj-nth i Ks γ e
... | ⟨ refl , eq ⟩ = ⟨ refl , eq ⟩

component-ok : ∀ {n} (i : Fin n) k {D K γ'} → component i k ≡ just K → Wf γ'
  → (∀ {Kt} → k ≡ just Kt → KDesc D Kt γ') → SV K × projᵐ i ⟨ D , ptt ⟩ ≃ ⟦ K ⟧ γ'
component-ok i (just (val Kt)) {K = K} {γ'} e wf h with kv (h refl)
... | ⟨ P.tuple {m} {Ks} vs , Kt≃ ⟩ with proj-nth i Ks γ' e
...   | ⟨ refl , eq ⟩ =
  ⟨ component-just i vs e
  , ≃-trans (projᵐ-≃ i Kt≃)
      (≃-trans (projᵐ-𝒯ᵐ _ (⟦ Ks ⟧₊ γ') (svs-val vs wf) i) (≃-reflexive eq)) ⟩

int-ok : ∀ k {n D γ'} → int-of k ≡ just n → (∀ {K} → k ≡ just K → KDesc D K γ')
  → D ≃ ⟦ lit Int n ⦅ Nil ⦆ ⟧ γ'
int-ok (just (val K)) {γ' = γ'} e h with int-of-just (proj₁ (kv (h refl))) e
... | refl = proj₂ (kv (h refl))

lit-≃ : ∀ n γ → ⟦ lit Int n ⦅ Nil ⦆ ⟧ γ ≃ ⌈ const {Int} n ⌉
lit-≃ n γ = ⟨ (λ { (const {Int} n') ⟨ refl , refl ⟩ → refl }) , (λ { _ refl → ⟨ refl , refl ⟩ }) ⟩

prim-term-≃ : ∀ o γ → ⟦ prim-term o ⟧ γ ≃ ⌈ out o ⌉
prim-term-≃ (int n) γ = lit-≃ n γ
prim-term-≃ (bool true) γ =
  ⟨ (λ { (left ⟨⟩) (inj₂ ⟨ _ , _ ⟩) → refl ; ω (inj₁ ⟨ _ , () ⟩) })
  , (λ { _ refl → inj₂ ⟨ ⟨ ⟨⟩ , ⟨ tt , (λ ()) ⟩ ⟩ , ⟨ tt , (λ ()) ⟩ ⟩ }) ⟩
prim-term-≃ (bool false) γ =
  ⟨ (λ { (right ⟨⟩) (inj₂ ⟨ _ , _ ⟩) → refl ; ω (inj₁ ⟨ _ , () ⟩) })
  , (λ { _ refl → inj₂ ⟨ ⟨ ⟨⟩ , ⟨ tt , (λ ()) ⟩ ⟩ , ⟨ tt , (λ ()) ⟩ ⟩ }) ⟩

{- The main lemma ------------------------------------------------------------------}

simp-ok : ∀ fl M {E γ γ'} → Wf γ → Wf γ' → Ok E γ γ' → Desc (⟦ M ⟧ γ) (simp fl E M) γ'
simp-args-ok : ∀ fl {n} (as : Args (replicate n ■)) {E γ γ'} → Wf γ → Wf γ' → Ok E γ γ'
  → ∀ i → nthD (⟦ as ⟧₊ γ) i ≃ nthD (⟦ simp-args fl E as ⟧₊ γ') i
app-ok : ∀ fl L M {E γ γ' I} → Wf γ → Wf γ' → Ok E γ γ' → Desc (⟦ M ⟧ γ) I γ'
  → Desc (⟦ app ⦅ L ,, M ,, Nil ⦆ ⟧ γ) (simp-app fl E L I) γ'
let-ok : ∀ fl N {E γ γ' I D} → Wf γ → Wf γ' → Ok E γ γ' → Desc D I γ' → Con D
  → Desc (⋆ᵐ ⟨ ⟦ lam ⦅ ⟩ N ,, Nil ⦆ ⟧ γ , ⟨ D , ptt ⟩ ⟩) (simp-let fl E N I) γ'
call-ok : ∀ fl J I {γ' F D} → Wf γ' → Desc F J γ' → Desc D I γ' → Con D
  → Desc (⋆ᵐ ⟨ F , ⟨ D , ptt ⟩ ⟩) (simp-call fl J I) γ'
case-ok : ∀ fl L M N {E γ γ' I} → Wf γ → Wf γ' → Ok E γ γ' → Desc (⟦ L ⟧ γ) I γ'
  → Desc (⟦ case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆ ⟧ γ) (simp-case fl E I M N) γ'

{- a body under a binder that stays -}
under-ok : ∀ fl N {E γ γ'} → Wf γ → Wf γ' → Ok E γ γ' → ∀ V → V ≢ [] → V ≈ V → NoErr V
  → ⟦ N ⟧ (mem V • γ) ≃ ⟦ term (simp fl (under E) N) ⟧ (mem V • γ')
under-ok fl N wf wf' ok V ne c n =
  tm (simp-ok fl N (wf-• wf (≈⇒Con c) (noerr-val V ne n)) (wf-• wf' (≈⇒Con c) (noerr-val V ne n))
                 (ok-under (mem V) ok))

simp-ok fl (` x) wf wf' ok = ok x
simp-ok fl (lam ⦅ ⟩ N ,, Nil ⦆) {γ = γ} wf wf' ok =
  desc (Λᵐ-≃ (under-ok fl N wf wf' ok)) (λ { refl → kfun γ wf ok ≃-refl })
simp-ok fl (app ⦅ L ,, M ,, Nil ⦆) wf wf' ok = app-ok fl L M wf wf' ok (simp-ok fl M wf wf' ok)
simp-ok fl (lit B k ⦅ Nil ⦆) wf wf' ok = desc-self P.lit ≃-refl
simp-ok fl (tuple n ⦅ as ⦆) wf wf' ok = desc-info (𝒯ᵐ-≃ n (simp-args-ok fl as wf wf' ok))
simp-ok fl (get i ⦅ L ,, Nil ⦆) {E} {γ' = γ'} wf wf' ok = get-ok (simp fl E L) (simp-ok fl L wf wf' ok)
  where
  get-ok : ∀ I → Desc (⟦ L ⟧ _) I γ' → Desc (⟦ get i ⦅ L ,, Nil ⦆ ⟧ _) (simp-get i I) γ'
  get-ok I d with component i (known I) in e
  ... | nothing = desc (projᵐ-≃ i (tm d)) (λ ())
  ... | just K with component-ok i (known I) e wf' (kn d) | small K
  ...   | ⟨ v , K≃ ⟩ | true = desc-self v K≃
  ...   | ⟨ v , K≃ ⟩ | false = desc (projᵐ-≃ i (tm d)) (λ { refl → kval v K≃ })
simp-ok fl (inl-op ⦅ M ,, Nil ⦆) wf wf' ok = desc-info (inlᵐ-≃ (tm (simp-ok fl M wf wf' ok)))
simp-ok fl (inr-op ⦅ M ,, Nil ⦆) wf wf' ok = desc-info (inrᵐ-≃ (tm (simp-ok fl M wf wf' ok)))
simp-ok fl (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) wf wf' ok = case-ok fl L M N wf wf' ok (simp-ok fl L wf wf' ok)
simp-ok fl (prim p ⦅ L ,, M ,, Nil ⦆) {E} {γ = γ} {γ'} wf wf' ok =
  prim-ok (simp fl E L) (simp fl E M) (simp-ok fl L wf wf' ok) (simp-ok fl M wf wf' ok)
  where
  dflt : ∀ {I J} → Desc (⟦ L ⟧ γ) I γ' → Desc (⟦ M ⟧ γ) J γ'
    → Desc (⟦ prim p ⦅ L ,, M ,, Nil ⦆ ⟧ γ) (prim p ⦅ term I ,, term J ,, Nil ⦆ ∣ nothing) γ'
  dflt dI dJ = desc (primᵐ-≃ p (tm dI) (tm dJ)) (λ ())
  prim-ok : ∀ I J → Desc (⟦ L ⟧ γ) I γ' → Desc (⟦ M ⟧ γ) J γ' → Desc (⟦ prim p ⦅ L ,, M ,, Nil ⦆ ⟧ γ) (simp-prim p I J) γ'
  prim-ok I J dI dJ with int-of (known I) in e₁
  ... | nothing = dflt dI dJ
  ... | just n with int-of (known J) in e₂
  ...   | nothing = dflt dI dJ
  ...   | just m =
    desc-self (prim-term-sv _)
      (≃-trans (primᵐ-≃ p (≃-trans (int-ok (known I) e₁ (kn dI)) (lit-≃ n γ'))
                          (≃-trans (int-ok (known J) e₂ (kn dJ)) (lit-≃ m γ')))
        (≃-trans (primᵐ-fold p n m) (≃-sym (prim-term-≃ (δ p n m) γ'))))

simp-ok fl (let-op ⦅ M ,, ⟩ N ,, Nil ⦆) wf wf' ok =
  let-ok fl N wf wf' ok (simp-ok fl M wf wf' ok) (ISWIMᵐ-con-env M (proj₁ (proj₂ wf)))

simp-args-ok fl {suc n} (M ,, as) wf wf' ok zero = tm (simp-ok fl M wf wf' ok)
simp-args-ok fl {suc n} (M ,, as) wf wf' ok (suc i) = simp-args-ok fl as wf wf' ok i

app-ok fl L M wf wf' ok d with lam? L
... | is-lam N = let-ok fl N wf wf' ok d (ISWIMᵐ-con-env M (proj₁ (proj₂ wf)))
... | other = call-ok fl _ _ wf' (simp-ok fl L wf wf' ok) d (ISWIMᵐ-con-env M (proj₁ (proj₂ wf)))

{- a call of a known function: its body, bound to the operand -}
call-ok (suc fl) (T ∣ just (fun N E)) I wf' dJ dI cD with size (term (simp-let fl E N I)) ≤ᵇ inline-size | kn dJ refl
... | true | kfun γ wf ok F≃ = desc-≃ (⋆ᵐ-≃ F≃ ≃-refl) (let-ok fl N wf wf' ok dI cD)
... | false | _ = desc (⋆ᵐ-≃ (tm dJ) (tm dI)) (λ ())
call-ok zero J I wf' dJ dI cD = desc (⋆ᵐ-≃ (tm dJ) (tm dI)) (λ ())
call-ok (suc fl) (T ∣ nothing) I wf' dJ dI cD = desc (⋆ᵐ-≃ (tm dJ) (tm dI)) (λ ())
call-ok (suc fl) (T ∣ just (val K)) I wf' dJ dI cD = desc (⋆ᵐ-≃ (tm dJ) (tm dI)) (λ ())

let-ok fl N {E} {γ} {γ'} {I} {D} wf wf' ok d cD with small (term I) in s | value (term I) in v
... | true | _ = desc-≃ (let-β N γ D wf cD vD) (simp-ok fl N (wf-• wf cD vD) wf' ok')
  where
  vD = Val-≃ (≃-sym (tm d)) (sv-val (small-sv (term I) s) wf')
  ok' : Ok (I • E) (D • γ) γ'
  ok' zero = d
  ok' (suc x) = ok x
... | false | true =
  desc (≃-trans (let-β N γ D wf cD vD)
          (≃-trans (tm (simp-ok fl N (wf-• wf cD vD) (wf-• wf' cV vV) ok')) (≃-sym (let-β N' γ' _ wf' cV vV))))
       (λ ())
  where
  N' = term (simp fl (known-as I E) N)
  vV = sv-val (value-sv (term I) v) wf'
  cV = ISWIMᵐ-con-env (term I) (proj₁ (proj₂ wf'))
  vD = Val-≃ (≃-sym (tm d)) vV
  ok' : Ok (known-as I E) (D • γ) (⟦ term I ⟧ γ' • γ')
  ok' zero = desc (tm d) (kn (desc-shift I _ d))
  ok' (suc x) = desc-shift (E x) _ (ok x)
... | false | false =
  desc (⋆ᵐ-≃ (Λᵐ-≃ {λ X → ⟦ N ⟧ (X • γ)} {λ X → ⟦ term (simp fl (under E) N) ⟧ (X • γ')} (under-ok fl N wf wf' ok)) (tm d)) (λ ())

{- a case on a known injection takes its branch -}
case-ok fl L M N {E} {γ} {γ'} {I} wf wf' ok d with branch (known I) in e
... | nothing =
  desc (𝒞ᵐ-≃ {F = λ X → ⟦ M ⟧ (X • γ)} {λ X → ⟦ term (simp fl (under E) M) ⟧ (X • γ')}
              {λ X → ⟦ N ⟧ (X • γ)} {λ X → ⟦ term (simp fl (under E) N) ⟧ (X • γ')}
              (tm d) (under-ok fl M wf wf' ok)
              (under-ok fl N wf wf' ok))
       (λ ())
... | just ⟨ true , K ⟩ = taken (known I) e (kn d)
  where
  taken : ∀ k → branch k ≡ just ⟨ true , K ⟩ → (∀ {Kt} → k ≡ just Kt → KDesc (⟦ L ⟧ γ) Kt γ')
    → Desc (⟦ case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆ ⟧ γ) (simp fl (self K • E) M) γ'
  taken (just (val Kt)) e h with kv (h refl)
  taken (just (val Kt)) e h | ⟨ P.inl {K₀} v , Kt≃ ⟩ with small K₀ | e
  taken (just (val Kt)) e h | ⟨ P.inl {K₀} v , Kt≃ ⟩ | true | refl =
    desc-≃ (case-inl L M N γ _ Kt≃ wf cK vK) (simp-ok fl M (wf-• wf cK vK) wf' ok')
    where
    vK = sv-val v wf'
    cK = ISWIMᵐ-con-env K (proj₁ (proj₂ wf'))
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
    desc-≃ (case-inr L M N γ _ Kt≃ wf cK vK) (simp-ok fl N (wf-• wf cK vK) wf' ok')
    where
    vK = sv-val v wf'
    cK = ISWIMᵐ-con-env K (proj₁ (proj₂ wf'))
    ok' : Ok (self K • E) (⟦ K ⟧ γ' • γ) γ'
    ok' zero = desc-self v ≃-refl
    ok' (suc x) = ok x
  taken (just (val Kt)) e h | ⟨ P.inr {K₀} v , Kt≃ ⟩ | false | ()
  taken (just (val Kt)) e h | ⟨ P.inl {K₀} v , _ ⟩ with small K₀ | e
  taken (just (val Kt)) e h | ⟨ P.inl {K₀} v , _ ⟩ | true | ()
  taken (just (val Kt)) e h | ⟨ P.inl {K₀} v , _ ⟩ | false | ()

{- The end theorem: closed programs, in the environment where every
   variable means {ω} -}

{- an environment of values, with which to compare -}
ρ₁ : Env Value
ρ₁ = λ _ → ⌈ ν ⌉

wf₁ : Wf ρ₁
wf₁ = ⟨ (λ _ → ⟨ ν , refl ⟩) , ⟨ (λ _ → Con-⌈⌉ ν) , (λ { _ _ refl () }) ⟩ ⟩

simplify-correct : ∀ M → Closed M → ⟦ M ⟧ ρ₀ ≃ ⟦ simplify M ⟧ ρ₀
simplify-correct M c =
  ≃-trans (⟦⟧-closed₀ M c ρ₀ ρ₁)
    (≃-trans (tm (simp-ok inline-fuel M wf₁ wf₁ (λ x → desc-self (P.var x) ≃-refl)))
             (⟦⟧-closed₀ (simplify M) (simplify-closed M c) ρ₁ ρ₀))

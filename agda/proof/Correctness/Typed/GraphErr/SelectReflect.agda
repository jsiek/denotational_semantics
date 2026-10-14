{-

  CFGᵀ with the X86 checks (SelectCheck.agda) reflects into CFGᵀ: each
  value of the first is related (⊑, SelectRel.agda) to the meaning of
  the second, for every CFGᵀ program.

  A slot of a flat type holds, in CFGᵀ, only values of its kind (SR), so
  the checks of the first never fire on related values, and its
  operators are those of CFGᵀ on them; a slot of code type is related by
  what its code does (Code). A call opens a closure whose code is
  related on environments of the kind its pairs say. CFGᵀ binds the
  whole set where the first binds finite parts of it, and contains them,
  since CFGᵀ is continuous (proof/Semantics/GraphErr/Typed/CFG.agda).

-}

module proof.Correctness.Typed.GraphErr.SelectReflect where

open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.Domain
open import proof.Framework.GraphModel.DomainUtilBase using (Nth; Lefts; Rights)
open import proof.Framework.GraphModel.DOpSig using (Results)
open import proof.Framework.GraphModel.OpsBase using (nthD; Mono₁; Finitary; ℬ)
open import proof.Framework.GraphModel.Ops using (⋆; pair; car; cdr; proj; 𝒯; 𝒞; ⋆-mono) renaming (inl to inlᴰ; inr to inrᴰ)
open import proof.Framework.GraphModel.ErrorMonad
open import proof.Framework.GraphModel.Env using (Env; nonempty-env; extend-nonempty-env; •-~)
open import proof.Framework.GraphModel.TypedOk using (Ok; fin₁; fin₂)
open import proof.Framework.GraphModel.TypedBinders using (ΛΛᵐ-call; callcᵈ)
open import proof.Semantics.Graph.Prim using (primD; out)
open import proof.Semantics.GraphErr.Typed.Clos5 using (tbl; ok; con)
open import proof.Semantics.GraphErr.Typed.Imp using (letᵗ-≫=)
open import proof.Semantics.GraphErr.Typed.CFG using (tail-ok; blocks-ok; run-ok; drop-ok)
open import Semantics.GraphErr.Typed.Ops using (init; caseᵗ; projectᵠ; keep; hit; kindᶠ; checkedᵠ; primᵗ; getᵗ)
open import Semantics.GraphErr.Prim using (primᵐ)
open import Semantics.GraphErr.Typed.Clos4 using (kind₄)
open import Semantics.GraphErr.Typed.Imp using (⌞_⌟; letᵗ)
open import Semantics.GraphErr.Typed.CFG using (Table; 𝒜; 𝒮; BEnv; drop; ⟦_⟧ᵗ; blocks; run; codeᶜ; ⟦_⟧ᶜ)
open import Semantics.GraphErr.Typed.Clos5 using (⟦_⟧[_]; ⟦_⟧s[_])
open import proof.Correctness.Typed.GraphErr.SelectCheck
open import proof.Correctness.Typed.GraphErr.SelectRel
open import Framework.Primitives using (Int)
open import Framework.Membership using (here⊑; there⊑; ⊑-∋) renaming (_⊑_ to _≤ₗ_)
open import proof.Framework.Lookup using (lvl-<)
open import Language.Prim using (Prim; sub; eq; δ; int; bool)
open import Language.Typed.Type hiding (_≟_)
import Language.Typed.Mon as M
open import Language.Typed.Imp using (Atm; var; lit; ref; Simple; atm; pack; callc; tuple; get; inl; inr; prim; inject; project)
open import Language.Typed.CFG using (Tail; return; seq; goto; case; Blocks; _▷_; Body; body; Program; program)

open import Data.Bool using (true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_; length; replicate)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (ℕ; zero; suc; _≟_)
open import Data.Nat.Properties using (<⇒≢; ≤-refl; n<1+n)
open import Data.Product using (_×_; proj₁; proj₂; Σ-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Data.Vec using (Vec; []; _∷_)
open import Level using (lift; lower)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst; subst₂)
open import Relation.Nullary using (yes; no)

{- the values of a flat type, as project sees their kinds, or an error -}
Kd : Flat → Value → Set
Kd G d = d ≡ ω ⊎ kind₄ (kind d) ≡ kindᶠ G

{- the relation of a slot of type A: CFGᵀ with checks on the left, CFGᵀ on the right -}
SR : Ty → 𝒫 Value → 𝒫 Value → Set₁
SR Any Dᶜ D = Lifted _⊑_ Dᶜ D
SR ⟪ G ⟫ Dᶜ D = Lifted _⊑_ Dᶜ (D ⇂ Kd G)
SR (code n) Cᶜ C = ∀ u → u ∈ Cᶜ → Code (tup n) u C

record ER {Δ : Ctx} (ρᶜ ρ : Env Value) : Set₁ where
  field
    rel : ∀ {A} (x : Δ ∋ A) → SR A (ρᶜ (idx x)) (ρ (idx x))
    valᶜ : ∀ {A} (x : Δ ∋ A) → Val (ρᶜ (idx x))
    conᶜ : ∀ {A} (x : Δ ∋ A) → Con (ρᶜ (idx x))
    clean : ∀ {A} (x : Δ ∋ A) → Clean (ρ (idx x))
open ER

{- Lemmas ----------------------------------------------------------------------------}

ℬ-val : ∀ {B c} → Val (ℬ B c ptt)
ℬ-val {c = c} = ⟨ (λ { _ d∈ refl → ⊥-elim d∈ }) , ⟨ const c , ⟨ refl , refl ⟩ ⟩ ⟩

βᵛ : ∀ {D F} → Val D → (D ≫= F) ⊆ F ⌊ D ⌋
βᵛ {D} {F} v = proj₁ (≫=-val-β {D} {F} v)

βᵛ⁻ : ∀ {D F} → Val D → F ⌊ D ⌋ ⊆ (D ≫= F)
βᵛ⁻ {D} {F} v = proj₂ (≫=-val-β {D} {F} v)

⌊⌋⊇ : ∀ {D} → Clean D → D ⊆ ⌊ D ⌋
⌊⌋⊇ = ⌊⌋-clean

kind₄-prod : ∀ {k} → kind₄ k ≡ fun → k ≡ prod
kind₄-prod {prod} refl = refl
kind₄-prod {fun} ()
kind₄-prod {inj} ()
kind₄-prod {error} ()
kind₄-prod {tup _} ()
kind₄-prod {base _} ()

{- the kind of a value related to a set of a flat type -}
⊑-kok : ∀ d {D G} → d ⊑ (D ⇂ Kd G) → d ≢ ω → kind₄ (kind d) ≡ kindᶠ G
⊑-kok d r d≢ with ⊑-wit d r d≢
... | ⟨ e , ⟨ ⟨ _ , inj₂ k ⟩ , ke ⟩ ⟩ = trans (cong kind₄ (sym ke)) k
... | ⟨ e , ⟨ ⟨ _ , inj₁ refl ⟩ , ke ⟩ ⟩ = ⊥-elim (d≢ (kind-ω (sym ke)))

⊑-Kd : ∀ d {D G} → kind₄ (kind d) ≡ kindᶠ G → d ⊑ D → d ⊑ (D ⇂ Kd G)
⊑-Kd d k = ⊑-⇂ d (λ e e∈ ke → inj₂ (trans (cong kind₄ ke) k))

⊑*-∈ : ∀ {V D v} → V ⊑* D → v ∈ mem V → v ⊑ D
⊑*-∈ ⟨ r , _ ⟩ (here refl) = r
⊑*-∈ ⟨ _ , rs ⟩ (there v∈) = ⊑*-∈ rs v∈

⊑*-from : ∀ V {D} → (∀ v → v ∈ mem V → v ⊑ D) → V ⊑* D
⊑*-from [] h = ptt
⊑*-from (v ∷ V) h = ⟨ h v (here refl) , ⊑*-from V (λ u u∈ → h u (there u∈)) ⟩

code-fun : ∀ k u {C} → Code k u C → kind u ≡ fun
code-fun k ν c = refl
code-fun k (V ↦ w) c = refl
code-fun k (const _) (lift ())
code-fun k ω (lift ())
code-fun k ⦅ _ , _ ⦆ (lift ())
code-fun k (tup[ _ ] _) (lift ())
code-fun k (left _) (lift ())
code-fun k (right _) (lift ())
code-fun k ⟨⟩ (lift ())

{- the first element of a pair related to a set -}
car-≢ : ∀ {u v D} → ⦅ u , v ⦆ ⊑ D → u ≢ ω
car-≢ {ω} ⟨ lift () , _ ⟩
car-≢ {const _} r ()
car-≢ {_ ↦ _} r ()
car-≢ {ν} r ()
car-≢ {⦅ _ , _ ⦆} r ()
car-≢ {tup[ _ ] _} r ()
car-≢ {left _} r ()
car-≢ {right _} r ()
car-≢ {⟨⟩} r ()

{- an output of a primitive -}
out-⊑ : ∀ p n m {D} → out (δ p n m) ∈ D → out (δ p n m) ⊑ (D ⇂ Kd (out-flat p))
out-⊑ sub n m o∈ = lift ⟨ o∈ , inj₂ refl ⟩
out-⊑ eq n m o∈ with does′ (n Data.Integer.≟ m)
  where open import Relation.Nullary using () renaming (does to does′)
        import Data.Integer
... | true = ⟨ lift (λ ()) , lift ⟨ o∈ , inj₂ refl ⟩ ⟩
... | false = ⟨ lift (λ ()) , lift ⟨ o∈ , inj₂ refl ⟩ ⟩

{- the payloads of the lefts (rights) of a consistent set are consistent -}
lefts-con : ∀ {D} → Con D → Con (λ d → left d ∈ D)
lefts-con c a b a∈ b∈ = c _ _ a∈ b∈

rights-con : ∀ {D} → Con D → Con (λ d → right d ∈ D)
rights-con c a b a∈ b∈ = c _ _ a∈ b∈

cdrs-con : ∀ {D} → Con D → Con (Cdrs D)
cdrs-con c a b ⟨ x , a∈ ⟩ ⟨ y , b∈ ⟩ = proj₂ (c _ _ a∈ b∈)

{- CFGᵀ contains its binders on whole sets, as it is continuous -}
𝒞ˡ-⊇ : ∀ {X F G} {Y : 𝒫 Value} → Con Y → Finitary F Y → (∀ d → Y d → left d ∈ X) → F Y ⊆ 𝒞 ⟨ X , ⟨ F , ⟨ G , ptt ⟩ ⟩ ⟩
𝒞ˡ-⊇ cY fin Y⊆ w w∈ with fin w w∈
... | ⟨ [] , ⟨ ne , _ ⟩ ⟩ = ⊥-elim (ne refl)
... | ⟨ v ∷ V , ⟨ _ , ⟨ V⊆ , w∈′ ⟩ ⟩ ⟩ = inj₁ ⟨ v , ⟨ V , ⟨ (λ d d∈ → Y⊆ d (V⊆ d d∈)) , ⟨ w∈′ , Con⇒≈ (v ∷ V) cY V⊆ ⟩ ⟩ ⟩ ⟩

𝒞ʳ-⊇ : ∀ {X F G} {Y : 𝒫 Value} → Con Y → Finitary G Y → (∀ d → Y d → right d ∈ X) → G Y ⊆ 𝒞 ⟨ X , ⟨ F , ⟨ G , ptt ⟩ ⟩ ⟩
𝒞ʳ-⊇ cY fin Y⊆ w w∈ with fin w w∈
... | ⟨ [] , ⟨ ne , _ ⟩ ⟩ = ⊥-elim (ne refl)
... | ⟨ v ∷ V , ⟨ _ , ⟨ V⊆ , w∈′ ⟩ ⟩ ⟩ = inj₂ ⟨ v , ⟨ V , ⟨ (λ d d∈ → Y⊆ d (V⊆ d d∈)) , ⟨ w∈′ , Con⇒≈ (v ∷ V) cY V⊆ ⟩ ⟩ ⟩ ⟩

drop-idx : ∀ {Δ' Δ A} (p : Δ' ≤ₗ Δ) (σ : Env Value) (y : Δ' ∋ A) → drop p σ (idx y) ≡ σ (idx (⊑-∋ p y))
drop-idx here⊑ σ y = refl
drop-idx (there⊑ p) σ y = drop-idx p (λ i → σ (suc i)) y

drop-con : ∀ {Δ' Δ} (p : Δ' ≤ₗ Δ) {σ} → Con-env σ → Con-env (drop p σ)
drop-con here⊑ c = c
drop-con (there⊑ p) c = drop-con p (λ i → c (suc i))

drop-ne : ∀ {Δ' Δ} (p : Δ' ≤ₗ Δ) {σ : Env Value} → nonempty-env σ → nonempty-env (drop p σ)
drop-ne here⊑ c = c
drop-ne (there⊑ p) c = drop-ne p (λ i → c (suc i))

kind₄-tup : ∀ {k n} → kind₄ k ≡ tup n → k ≡ tup n
kind₄-tup {tup _} refl = refl
kind₄-tup {fun} ()
kind₄-tup {inj} ()
kind₄-tup {prod} ()
kind₄-tup {error} ()
kind₄-tup {base _} ()

kind₄-base : ∀ {k B} → kind₄ k ≡ base B → k ≡ base B
kind₄-base {base _} refl = refl
kind₄-base {fun} ()
kind₄-base {inj} ()
kind₄-base {prod} ()
kind₄-base {error} ()
kind₄-base {tup _} ()

kind₄-inj : ∀ {k} → kind₄ k ≡ inj → k ≡ inj
kind₄-inj {inj} refl = refl
kind₄-inj {fun} ()
kind₄-inj {base _} ()
kind₄-inj {prod} ()
kind₄-inj {error} ()
kind₄-inj {tup _} ()

pair-elim : ∀ {X Y d} → d ∈ pair ⟨ X , ⟨ Y , ptt ⟩ ⟩ → Σ[ u ∈ Value ] Σ[ v ∈ Value ] d ≡ ⦅ u , v ⦆ × u ∈ X × v ∈ Y
pair-elim {d = ⦅ u , v ⦆} ⟨ u∈ , v∈ ⟩ = ⟨ u , ⟨ v , ⟨ refl , ⟨ u∈ , v∈ ⟩ ⟩ ⟩ ⟩

inl-elim : ∀ {X d} → d ∈ inlᴰ ⟨ X , ptt ⟩ → Σ[ x ∈ Value ] d ≡ left x × x ∈ X
inl-elim {d = left x} x∈ = ⟨ x , ⟨ refl , x∈ ⟩ ⟩

inr-elim : ∀ {X d} → d ∈ inrᴰ ⟨ X , ptt ⟩ → Σ[ x ∈ Value ] d ≡ right x × x ∈ X
inr-elim {d = right x} x∈ = ⟨ x , ⟨ refl , x∈ ⟩ ⟩

ℬ-r : ∀ {B c} → Lifted _⊑_ (ℬ B c ptt) (ℬ B c ptt ⇂ Kd (base B))
ℬ-r (const k) ⟨ refl , refl ⟩ = lift ⟨ ⟨ refl , refl ⟩ , inj₂ refl ⟩

{- a check that does not fire -}
no-bad : ∀ {k X A} → (∀ d → d ∈ X → kind d ≡ k) → checked k X A ⊆ A
no-bad ok w (inj₁ ⟨ _ , ⟨ d , ⟨ d∈ , dk ⟩ ⟩ ⟩) = ⊥-elim (dk (ok d d∈))
no-bad ok w (inj₂ w∈) = w∈

{- the components of a vector of atoms -}
nth-atm : ∀ {Σ Δ n} (as : Vec (Atm Σ Δ Any) n) T ρ i → nthD (⟦ M.⌜ as ⌝ᵛ ⟧s[ T ] ρ) i ≡ 𝒜 (Data.Vec.lookup as i) T ρ
nth-atm (a ∷ as) T ρ zero = refl
nth-atm (a ∷ as) T ρ (suc i) = nth-atm as T ρ i

{- a tuple of related components -}
𝒯-r : ∀ n {Xs Xs'} → (∀ i → Clean (nthD Xs i)) → (∀ i → Lifted _⊑_ (nthD Xs i) (nthD Xs' i)) → Lifted _⊑_ (𝒯 n Xs) (𝒯 n Xs')
𝒯-r zero cl r ⟨⟩ _ = lift tt
𝒯-r (suc n) cl r (tup[_]_ i d) ⟨ refl , ⟨ d∈ , ne ⟩ ⟩ =
  ⟨ lift (cl i d d∈) , ⊑-mono d (λ e e∈ → ⟨ refl , ⟨ e∈ , (λ j → let ⟨ x , x∈ ⟩ = ne j in ⊑-ne x (r j x x∈)) ⟩ ⟩) (r i d d∈) ⟩

{- the elements of a tuple of values have its kind -}
𝒯ᵐ-kok : ∀ n {Ds} d → d ∈ 𝒯ᵐ n Ds → Kd (tup n) d
𝒯ᵐ-kok n {Ds} d d∈ = binds-P n (λ Xs d d∈ → inj₂ (cong kind₄ (𝒯-kind n Xs d d∈))) d d∈
  where
  𝒯-kind : ∀ n Xs d → d ∈ 𝒯 n Xs → kind d ≡ tup n
  𝒯-kind zero Xs ⟨⟩ _ = refl
  𝒯-kind (suc n) Xs (tup[ i ] e) ⟨ refl , _ ⟩ = refl
  𝒯-kind zero Xs (const _) ()
  𝒯-kind zero Xs (_ ↦ _) ()
  𝒯-kind zero Xs ν ()
  𝒯-kind zero Xs ω ()
  𝒯-kind zero Xs ⦅ _ , _ ⦆ ()
  𝒯-kind zero Xs (tup[ _ ] _) ()
  𝒯-kind zero Xs (left _) ()
  𝒯-kind zero Xs (right _) ()
  𝒯-kind (suc n) Xs (const _) ()
  𝒯-kind (suc n) Xs (_ ↦ _) ()
  𝒯-kind (suc n) Xs ν ()
  𝒯-kind (suc n) Xs ω ()
  𝒯-kind (suc n) Xs ⦅ _ , _ ⦆ ()
  𝒯-kind (suc n) Xs (left _) ()
  𝒯-kind (suc n) Xs (right _) ()
  𝒯-kind (suc n) Xs ⟨⟩ ()

  binds-P : ∀ k {Es : Results (𝒫 Value) (replicate k ■)} {K} → (∀ Xs d → d ∈ K Xs → Kd (tup n) d) → ∀ d → d ∈ binds k Es K → Kd (tup n) d
  binds-P zero h d d∈ = h ptt d d∈
  binds-P (suc k) h d (inj₁ ⟨ refl , _ ⟩) = inj₁ refl
  binds-P (suc k) {⟨ E , Es ⟩} {K} h d (inj₂ ⟨ _ , d∈ ⟩) = binds-P k (λ Xs → h ⟨ ⌊ E ⌋ , Xs ⟩) d d∈


{- a primitive on integers -}
prim-r : ∀ p {A B A' B'} → Val A → Val B → Val A' → Val B'
  → (∀ d → d ∈ ⌊ A ⌋ → kind d ≡ base Int) → (∀ d → d ∈ ⌊ B ⌋ → kind d ≡ base Int)
  → (∀ k → const {Int} k ∈ A → const {Int} k ∈ A') → (∀ k → const {Int} k ∈ B → const {Int} k ∈ B')
  → Lifted _⊑_ (primᵐ p ⟨ A , ⟨ B , ptt ⟩ ⟩) (primᵗ p A' B' ⇂ Kd (out-flat p))
prim-r p {A} {B} {A'} {B'} vA vB vA' vB' oka okb ia ib w w∈
  with no-bad {base Int} {⌊ B ⌋} {primD p ⟨ ⌊ A ⌋ , ⟨ ⌊ B ⌋ , ptt ⟩ ⟩} okb w
         (no-bad {base Int} {⌊ A ⌋} {checked (base Int) ⌊ B ⌋ (primD p ⟨ ⌊ A ⌋ , ⟨ ⌊ B ⌋ , ptt ⟩ ⟩)} oka w


         (βᵛ {B} {λ Y → checked (base Int) ⌊ A ⌋ (checked (base Int) Y (primD p ⟨ ⌊ A ⌋ , ⟨ Y , ptt ⟩ ⟩))} vB w
           (βᵛ {A} {λ X → B ≫= λ Y → checked (base Int) X (checked (base Int) Y (primD p ⟨ X , ⟨ Y , ptt ⟩ ⟩))} vA w w∈)))
... | ⟨ n , ⟨ m , ⟨ n∈ , ⟨ m∈ , refl ⟩ ⟩ ⟩ ⟩ =
  out-⊑ p n m (βᵛ⁻ {A'} {λ X → B' ≫= λ Y → primD p ⟨ X , ⟨ Y , ptt ⟩ ⟩} vA' _
                 (βᵛ⁻ {B'} {λ Y → primD p ⟨ ⌊ A' ⌋ , ⟨ Y , ptt ⟩ ⟩} vB' _
                    ⟨ n , ⟨ m , ⟨ ⌊⌋⊇ (proj₁ vA') _ (ia n (proj₁ n∈)) , ⟨ ⌊⌋⊇ (proj₁ vB') _ (ib m (proj₁ m∈)) , refl ⟩ ⟩ ⟩ ⟩))

{- project: an error of the test is a value of the wrong kind -}
test-bad : ∀ t {A A'} → Val A → Lifted _⊑_ A A' → ω ∈ test t A → Σ[ d ∈ Value ] d ∈ ⌊ A ⌋ × kind₄ (kind d) ≢ kindᶠ (flat t)
test-bad tint {A} vA r ω∈ with βᵛ {ℬ Int (Data.Integer.+ 0) ptt} {λ Y → checked (base Int) ⌊ A ⌋ (checked (base Int) Y (primD sub ⟨ ⌊ A ⌋ , ⟨ Y , ptt ⟩ ⟩))} ℬ-val ω
  (βᵛ {A} {λ X → ℬ Int (Data.Integer.+ 0) ptt ≫= λ Y → checked (base Int) X (checked (base Int) Y (primD sub ⟨ X , ⟨ Y , ptt ⟩ ⟩))} vA ω ω∈)
  where import Data.Integer
... | inj₁ ⟨ _ , ⟨ d , ⟨ d∈ , dk ⟩ ⟩ ⟩ = ⟨ d , ⟨ d∈ , (λ e → dk (kind₄-base e)) ⟩ ⟩
... | inj₂ (inj₁ ⟨ _ , ⟨ const _ , ⟨ ⟨ ⟨ refl , refl ⟩ , _ ⟩ , dk ⟩ ⟩ ⟩) = ⊥-elim (dk refl)
... | inj₂ (inj₂ ⟨ _ , ⟨ _ , ⟨ _ , ⟨ _ , () ⟩ ⟩ ⟩ ⟩)
test-bad tsum {A} vA r ω∈ with βᵛ {A} {λ X → checked inj X (isinlD X)} vA ω ω∈
... | inj₁ ⟨ _ , ⟨ d , ⟨ d∈ , dk ⟩ ⟩ ⟩ = ⟨ d , ⟨ d∈ , (λ e → dk (kind₄-inj e)) ⟩ ⟩
... | inj₂ (inj₁ ⟨ _ , ⟨ _ , () ⟩ ⟩)
... | inj₂ (inj₂ ⟨ _ , ⟨ _ , () ⟩ ⟩)
test-bad tfun {A} {A'} vA r ω∈ with βᵛ {A} {λ X → checked prod X (car ⟨ X , ptt ⟩)} vA ω ω∈
... | inj₁ ⟨ _ , ⟨ d , ⟨ d∈ , dk ⟩ ⟩ ⟩ = ⟨ d , ⟨ d∈ , (λ e → dk (kind₄-prod e)) ⟩ ⟩
... | inj₂ ⟨ v , p∈ ⟩ = ⊥-elim (car-≢ {ω} {v} {A'} (r ⦅ ω , v ⦆ (proj₁ p∈)) refl)
test-bad (ttup n i) {A} vA r ω∈ with βᵛ {A} {λ X → checked (tup (suc n)) X (proj i ⟨ X , ptt ⟩)} vA ω ω∈
... | inj₁ ⟨ _ , ⟨ d , ⟨ d∈ , dk ⟩ ⟩ ⟩ = ⟨ d , ⟨ d∈ , (λ e → dk (kind₄-tup e)) ⟩ ⟩
... | inj₂ t∈ = ⊥-elim (lower (proj₁ (r _ (proj₁ t∈))) refl)

{- a value of the test: a value of the right kind, and what the typed test needs -}
test-ok : ∀ t {A A'} → Val A → Clean A' → Lifted _⊑_ A A' → Conv (test t A)
  → Σ[ d ∈ Value ] d ∈ ⌊ A ⌋ × kind₄ (kind d) ≡ kindᶠ (flat t) × hit t ⌊ A' ⌋
test-ok tint {A} vA cl r ⟨ v , ⟨ v∈ , v≢ ⟩ ⟩
  with βᵛ {ℬ Int (Data.Integer.+ 0) ptt} {λ Y → checked (base Int) ⌊ A ⌋ (checked (base Int) Y (primD sub ⟨ ⌊ A ⌋ , ⟨ Y , ptt ⟩ ⟩))} ℬ-val v
  (βᵛ {A} {λ X → ℬ Int (Data.Integer.+ 0) ptt ≫= λ Y → checked (base Int) X (checked (base Int) Y (primD sub ⟨ X , ⟨ Y , ptt ⟩ ⟩))} vA v v∈)
  where import Data.Integer
... | inj₁ ⟨ refl , _ ⟩ = ⊥-elim (v≢ refl)
... | inj₂ (inj₁ ⟨ refl , _ ⟩) = ⊥-elim (v≢ refl)
... | inj₂ (inj₂ ⟨ n , ⟨ _ , ⟨ n∈ , _ ⟩ ⟩ ⟩) = ⟨ const n , ⟨ n∈ , ⟨ refl , tt ⟩ ⟩ ⟩
test-ok tsum {A} vA cl r ⟨ v , ⟨ v∈ , v≢ ⟩ ⟩ with βᵛ {A} {λ X → checked inj X (isinlD X)} vA v v∈
... | inj₁ ⟨ refl , _ ⟩ = ⊥-elim (v≢ refl)
... | inj₂ (inj₁ ⟨ u , ⟨ u∈ , _ ⟩ ⟩) = ⟨ left u , ⟨ u∈ , ⟨ refl , tt ⟩ ⟩ ⟩
... | inj₂ (inj₂ ⟨ u , ⟨ u∈ , _ ⟩ ⟩) = ⟨ right u , ⟨ u∈ , ⟨ refl , tt ⟩ ⟩ ⟩
test-ok tfun {A} vA cl r ⟨ v , ⟨ v∈ , v≢ ⟩ ⟩ with βᵛ {A} {λ X → checked prod X (car ⟨ X , ptt ⟩)} vA v v∈
... | inj₁ ⟨ refl , _ ⟩ = ⊥-elim (v≢ refl)
... | inj₂ ⟨ e , p∈ ⟩ = ⟨ ⦅ v , e ⦆ , ⟨ p∈ , ⟨ refl , tt ⟩ ⟩ ⟩
test-ok (ttup n i) {A} {A'} vA cl r ⟨ v , ⟨ v∈ , v≢ ⟩ ⟩ with βᵛ {A} {λ X → checked (tup (suc n)) X (proj i ⟨ X , ptt ⟩)} vA v v∈
... | inj₁ ⟨ refl , _ ⟩ = ⊥-elim (v≢ refl)
... | inj₂ t∈ = ⟨ tup[ i ] v , ⟨ t∈ , ⟨ refl , hit′ ⟩ ⟩ ⟩
  where
  hit′ : Σ[ e ∈ Value ] (tup[ i ] e) ∈ ⌊ A' ⌋
  hit′ = let ⟨ e , e∈ ⟩ = ⊑-ne v (proj₂ (r _ (proj₁ t∈))) in ⟨ e , ⟨ e∈ , cl _ e∈ ⟩ ⟩

project-r : ∀ t {A A'} → Val A → Con A → Val A' → Lifted _⊑_ A A'
  → Lifted _⊑_ (strictᵐ (test t A) A) (projectᵠ kind₄ t A' ⇂ Kd (flat t))
project-r t {A} {A'} vA cA vA' r .ω (inj₁ ⟨ refl , ω∈ ⟩) with test-bad t vA r ω∈
... | ⟨ d , ⟨ d∈ , dk ⟩ ⟩ with ⊑-wit d (r d (proj₁ d∈)) (proj₂ d∈)
...   | ⟨ e , ⟨ e∈ , ke ⟩ ⟩ =
  lift ⟨ βᵛ⁻ {A'} {λ X → checkedᵠ kind₄ (kindᶠ (flat t)) X (keep kind₄ t X)} vA' ω
           (inj₁ ⟨ refl , ⟨ e , ⟨ ⟨ e∈ , (λ { refl → proj₂ d∈ (kind-ω (sym ke)) }) ⟩ , (λ k → dk (trans (cong kind₄ (sym ke)) k)) ⟩ ⟩ ⟩)
       , inj₁ refl ⟩
project-r t {A} {A'} vA cA vA' r w (inj₂ ⟨ c , w∈ ⟩) with test-ok t vA (proj₁ vA') r c
... | ⟨ d , ⟨ d∈ , ⟨ dk , h ⟩ ⟩ ⟩ =
  ⊑-mono w (λ e e∈ → ⟨ βᵛ⁻ {A'} {λ X → checkedᵠ kind₄ (kindᶠ (flat t)) X (keep kind₄ t X)} vA' e (inj₂ e∈)
                     , inj₂ (proj₂ (proj₂ e∈)) ⟩)
    (⊑-⇂ w (λ e e∈ ke → ⟨ h , trans (cong kind₄ (trans ke kw)) dk ⟩)
      (⊑-⌊⌋ w w≢ (r w w∈)))
  where
  w≢ = proj₁ vA w w∈
  kw : kind w ≡ kind d
  kw = ~-kind w d (cA w d w∈ (proj₁ d∈))

{- a call: the closure's code, applied to its environment and the argument -}
callc-r : ∀ {F A F' A'} → Val F → Con F → Val A → Val F' → Con F' → Val A' → Con A'
  → Lifted _⊑_ F (F' ⇂ Kd fun) → Lifted _⊑_ A A'
  → Lifted _⊑_ (strictᵐ (carᵐ ⟨ F , ptt ⟩) (strictᵐ (cdrᵐ ⟨ F , ptt ⟩) (strictᵐ A
                  (callᵐ ⟨ carᵐ ⟨ F , ptt ⟩ , ⟨ cdrᵐ ⟨ F , ptt ⟩ , ⟨ A , ptt ⟩ ⟩ ⟩))))
               (binds 2 ⟨ F' , ⟨ A' , ptt ⟩ ⟩ callcᵈ)
callc-r {F} {A} {F'} {A'} vF cF vA vF' cF' vA' cA' rF rA w w∈ = go w∈
  where
  C = carᵐ ⟨ F , ptt ⟩
  D = cdrᵐ ⟨ F , ptt ⟩
  Q = F' ⇂ Kd fun
  prods : ∀ d → d ∈ ⌊ F ⌋ → kind d ≡ prod
  prods d d∈ = kind₄-prod (⊑-kok d (rF d (proj₁ d∈)) (proj₂ d∈))
  car-in : ∀ {u} → u ∈ C → Σ[ v ∈ Value ] ⦅ u , v ⦆ ∈ ⌊ F ⌋
  car-in u∈ = no-bad {prod} {⌊ F ⌋} {car ⟨ ⌊ F ⌋ , ptt ⟩} prods _ (βᵛ {F} {λ X → checked prod X (car ⟨ X , ptt ⟩)} vF _ u∈)
  cdr-in : ∀ {v} → v ∈ D → Σ[ u ∈ Value ] ⦅ u , v ⦆ ∈ ⌊ F ⌋
  cdr-in v∈ = no-bad {prod} {⌊ F ⌋} {cdr ⟨ ⌊ F ⌋ , ptt ⟩} prods _ (βᵛ {F} {λ X → checked prod X (cdr ⟨ X , ptt ⟩)} vF _ v∈)
  C-ω : ω ∈ C → ⊥
  C-ω ω∈ = let ⟨ v , p∈ ⟩ = car-in ω∈ in car-≢ {ω} {v} {Q} (rF ⦅ ω , v ⦆ (proj₁ p∈)) refl
  D-ω : ω ∈ D → ⊥
  D-ω ω∈ = let ⟨ u , p∈ ⟩ = cdr-in ω∈ in lower (proj₁ (proj₂ (rF ⦅ u , ω ⦆ (proj₁ p∈)))) refl
  funs : ∀ d → d ∈ ⌊ C ⌋ → kind d ≡ fun
  funs d d∈ = let ⟨ v , p∈ ⟩ = car-in (proj₁ d∈) in code-fun (kind v) d (proj₁ (rF _ (proj₁ p∈)))
  E = ⌊ Cdrs Q ⌋
  X = ⌊ A' ⌋
  cE : Con E
  cE = Con-⊆ (cdrs-con {Q} (Con-⊆ cF' (λ _ → proj₁))) ⌊⌋-⊆

  call : ∀ {V U} → (V ↦ (U ↦ w)) ∈ ⌊ C ⌋ → mem V ⊆ ⌊ D ⌋ → mem U ⊆ ⌊ A ⌋ → w ⊑ binds 2 ⟨ F' , ⟨ A' , ptt ⟩ ⟩ callcᵈ
  call {V} {U} u∈ V⊆ U⊆ with car-in (proj₁ u∈)
  ... | ⟨ e₀ , p∈ ⟩ =
    ⊑-mono w into (proj₁ (rF _ (proj₁ p∈)) E X cE (Con-⊆ cA' ⌊⌋-⊆) (λ _ → proj₂) (λ _ → proj₂) rV rU)
    where
    rV : V ⊑* (E ⇂ₖ kind e₀)
    rV = ⊑*-from V λ v v∈ → let ⟨ u' , q∈ ⟩ = cdr-in (proj₁ (V⊆ v v∈)) ; r = rF _ (proj₁ q∈) in
      subst (λ k → v ⊑ (E ⇂ₖ k)) (~-kind v e₀ (proj₂ (cF _ _ (proj₁ q∈) (proj₁ p∈))))
        (⊑-kind v (⊑-⌊⌋ v (lower (proj₁ (proj₂ r))) (proj₂ (proj₂ r))))
    rU : U ⊑* X
    rU = ⊑*-from U λ x x∈ → ⊑-⌊⌋ x (proj₂ (U⊆ x x∈)) (rA x (proj₁ (U⊆ x x∈)))
    into : ⋆ ⟨ ⋆ ⟨ Cars Q , ⟨ E ⇂ₖ kind e₀ , ptt ⟩ ⟩ , ⟨ X , ptt ⟩ ⟩ ⊆ binds 2 ⟨ F' , ⟨ A' , ptt ⟩ ⟩ callcᵈ
    into y y∈ = βᵛ⁻ {F'} {λ P → A' ≫= λ Y → ⋆ ⟨ ⋆ ⟨ car ⟨ P , ptt ⟩ , ⟨ cdr ⟨ P , ptt ⟩ , ptt ⟩ ⟩ , ⟨ Y , ptt ⟩ ⟩} vF' y
      (βᵛ⁻ {A'} {λ Y → ⋆ ⟨ ⋆ ⟨ car ⟨ ⌊ F' ⌋ , ptt ⟩ , ⟨ cdr ⟨ ⌊ F' ⌋ , ptt ⟩ , ptt ⟩ ⟩ , ⟨ Y , ptt ⟩ ⟩} vA' y
        (lower (⋆-mono ⟨ ⋆ ⟨ Cars Q , ⟨ E ⇂ₖ kind e₀ , ptt ⟩ ⟩ , ⟨ X , ptt ⟩ ⟩
                       ⟨ ⋆ ⟨ car ⟨ ⌊ F' ⌋ , ptt ⟩ , ⟨ cdr ⟨ ⌊ F' ⌋ , ptt ⟩ , ptt ⟩ ⟩ , ⟨ X , ptt ⟩ ⟩
          ⟨ lift (lower (⋆-mono ⟨ Cars Q , ⟨ E ⇂ₖ kind e₀ , ptt ⟩ ⟩ ⟨ car ⟨ ⌊ F' ⌋ , ptt ⟩ , ⟨ cdr ⟨ ⌊ F' ⌋ , ptt ⟩ , ptt ⟩ ⟩
                    ⟨ lift (λ { u ⟨ v , q ⟩ → ⟨ v , ⟨ proj₁ q , (λ ()) ⟩ ⟩ })
                    , ⟨ lift (λ { v ⟨ ⟨ ⟨ u , q ⟩ , _ ⟩ , _ ⟩ → ⟨ u , ⟨ proj₁ q , (λ ()) ⟩ ⟩ }) , ptt ⟩ ⟩))
          , ⟨ lift (λ _ z → z) , ptt ⟩ ⟩) y y∈))
  go : w ∈ strictᵐ C (strictᵐ D (strictᵐ A (callᵐ ⟨ C , ⟨ D , ⟨ A , ptt ⟩ ⟩ ⟩))) → w ⊑ binds 2 ⟨ F' , ⟨ A' , ptt ⟩ ⟩ callcᵈ
  go (inj₁ ⟨ _ , ω∈ ⟩) = ⊥-elim (C-ω ω∈)
  go (inj₂ ⟨ _ , inj₁ ⟨ _ , ω∈ ⟩ ⟩) = ⊥-elim (D-ω ω∈)
  go (inj₂ ⟨ _ , inj₂ ⟨ _ , inj₁ ⟨ _ , ω∈ ⟩ ⟩ ⟩) = ⊥-elim (proj₁ vA ω ω∈ refl)
  go (inj₂ ⟨ _ , inj₂ ⟨ _ , inj₂ ⟨ _ , inj₁ ⟨ _ , ω∈ ⟩ ⟩ ⟩ ⟩) = ⊥-elim (C-ω ω∈)
  go (inj₂ ⟨ _ , inj₂ ⟨ _ , inj₂ ⟨ _ , inj₂ ⟨ _ , inj₁ ⟨ _ , ω∈ ⟩ ⟩ ⟩ ⟩ ⟩) = ⊥-elim (D-ω ω∈)
  go (inj₂ ⟨ _ , inj₂ ⟨ _ , inj₂ ⟨ _ , inj₂ ⟨ _ , inj₂ ⟨ _ , inj₁ ⟨ _ , ω∈ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩) = ⊥-elim (proj₁ vA ω ω∈ refl)
  go (inj₂ ⟨ _ , inj₂ ⟨ _ , inj₂ ⟨ _ , inj₂ ⟨ _ , inj₂ ⟨ _ , inj₂ ⟨ _ , k∈ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩)
    with no-bad {fun} {⌊ C ⌋} {⋆ ⟨ ⋆ ⟨ ⌊ C ⌋ , ⟨ ⌊ D ⌋ , ptt ⟩ ⟩ , ⟨ ⌊ A ⌋ , ptt ⟩ ⟩} funs w k∈
  ... | ⟨ U , ⟨ ⟨ V , ⟨ u∈ , ⟨ V⊆ , _ ⟩ ⟩ ⟩ , ⟨ U⊆ , _ ⟩ ⟩ ⟩ = call u∈ V⊆ U⊆

{- a slot binding contains its body on the whole set, which is continuous -}
let-⊇ : ∀ {D F} → Con D → Conv D → Mono₁ F → Finitary F ⌊ D ⌋ → F ⌊ D ⌋ ⊆ letᵗ D F
let-⊇ {D} {F} cD c m fin w w∈ = proj₂ (letᵗ-≫= {D} {F} m cD (λ _ → fin)) w (inj₂ ⟨ c , w∈ ⟩)

{- The relation preserved ----------------------------------------------------------}




module Sim {Σ : List ℕ} {Tᶜ T : Table}
  (TR : ∀ {n} (f : Σ ∋ n) → SR (code n) (Tᶜ (lvl f)) (T (lvl f)))
  (TVᶜ : ∀ k → Val (Tᶜ k)) (TV : ∀ k → Val (T k)) (TC : ∀ k → Con (T k)) where

  module _ {Δ : Ctx} {ρᶜ ρ : Env Value} (h : ER {Δ} ρᶜ ρ) (cρ : Con-env ρ) (NE : nonempty-env ρ) where

    vᶜ : ∀ {A} (a : Atm Σ Δ A) → Val (𝒜 a Tᶜ ρᶜ)
    vᶜ (var x) = valᶜ h x
    vᶜ (lit B c) = ℬ-val
    vᶜ (ref f) = TVᶜ _

    v' : ∀ {A} (a : Atm Σ Δ A) → Val (𝒜 a T ρ)
    v' (var x) = ⟨ clean h x , NE (idx x) ⟩
    v' (lit B c) = ℬ-val
    v' (ref f) = TV _

    c' : ∀ {A} (a : Atm Σ Δ A) → Con (𝒜 a T ρ)
    c' a = con TC M.⌜ a ⌝ᵃ cρ

    ar : ∀ {A} (a : Atm Σ Δ A) → SR A (𝒜 a Tᶜ ρᶜ) (𝒜 a T ρ)
    ar (var x) = rel h x
    ar (lit B c) = ℬ-r
    ar (ref f) = TR f

    aconᶠ : (a : Atm Σ Δ ⟪ fun ⟫) → Con (𝒜 a Tᶜ ρᶜ)
    aconᶠ (var x) = conᶜ h x

    aconᴬ : (a : Atm Σ Δ Any) → Con (𝒜 a Tᶜ ρᶜ)
    aconᴬ (var x) = conᶜ h x

    {- an atom of a flat type: its values have its kind -}

    ar-kind : ∀ {G} (a : Atm Σ Δ ⟪ G ⟫) d → d ∈ ⌊ 𝒜 a Tᶜ ρᶜ ⌋ → kind₄ (kind d) ≡ kindᶠ G
    ar-kind a d ⟨ d∈ , d≢ ⟩ = ⊑-kok d (ar a d d∈) d≢

    simS : ∀ {A} (s : Simple Σ Δ A) → SR A (𝒮ᶜ s Tᶜ ρᶜ) (𝒮 s T ρ)
    simS (atm a) = ar a
    simS (pack {n} c e) d d∈ with pair-elim (βᵛ {F = λ Y → pair ⟨ ⌊ 𝒜 c Tᶜ ρᶜ ⌋ , ⟨ Y , ptt ⟩ ⟩} (vᶜ e) d (βᵛ {F = λ X → 𝒜 e Tᶜ ρᶜ ≫= λ Y → pair ⟨ X , ⟨ Y , ptt ⟩ ⟩} (vᶜ c) d d∈))
    ... | ⟨ u , ⟨ v , ⟨ refl , ⟨ ⟨ u∈ , _ ⟩ , ⟨ v∈ , v≢ ⟩ ⟩ ⟩ ⟩ ⟩ =
      ⟨ subst (λ k → Code k u (Cars Q)) (sym kv) (code-mono (tup n) u C⊆ (ar c u u∈))
      , ⟨ lift v≢ , ⊑-mono v E⊆ rv ⟩ ⟩
      where
      C' = 𝒜 c T ρ
      E' = 𝒜 e T ρ
      Q = pairᵐ ⟨ C' , ⟨ E' , ptt ⟩ ⟩ ⇂ Kd fun
      rv = ar e v v∈
      kv : kind v ≡ tup n
      kv = kind₄-tup (⊑-kok v rv v≢)
      in-Q : ∀ {x y} → x ∈ C' → y ∈ E' → ⦅ x , y ⦆ ∈ Q
      in-Q x∈ y∈ = ⟨ βᵛ⁻ {F = λ X → E' ≫= λ Y → pair ⟨ X , ⟨ Y , ptt ⟩ ⟩} (v' c) _
                       (βᵛ⁻ {F = λ Y → pair ⟨ ⌊ C' ⌋ , ⟨ Y , ptt ⟩ ⟩} (v' e) _
                          ⟨ ⟨ x∈ , proj₁ (v' c) _ x∈ ⟩ , ⟨ y∈ , proj₁ (v' e) _ y∈ ⟩ ⟩) , inj₂ refl ⟩
      C⊆ : C' ⊆ Cars Q
      C⊆ x x∈ = let ⟨ y , y∈ ⟩ = proj₂ (v' e) in ⟨ y , in-Q x∈ y∈ ⟩
      E⊆ : (E' ⇂ Kd (tup n)) ⊆ Cdrs Q
      E⊆ y ⟨ y∈ , _ ⟩ = let ⟨ x , x∈ ⟩ = proj₂ (v' c) in ⟨ x , in-Q x∈ y∈ ⟩
    simS (callc f a) = callc-r (vᶜ f) (aconᶠ f) (vᶜ a) (v' f) (c' f) (v' a) (c' a) (ar f) (ar a)
    simS (tuple {n = n} as) d d∈ =
      ⊑-⇂ d (λ e e∈ _ → 𝒯ᵐ-kok n e e∈) (binds-lift n ⊑-lift cons rels (λ cl hs → 𝒯-r n cl hs) d d∈)
      where
      cons : ∀ i → Con (nthD (⟦ M.⌜ as ⌝ᵛ ⟧s[ T ] ρ) i)
      cons i = subst Con (sym (nth-atm as T ρ i)) (c' (Data.Vec.lookup as i))
      rels : ∀ i → Lifted _⊑_ (nthD (⟦ M.⌜ as ⌝ᵛ ⟧s[ Tᶜ ] ρᶜ) i) (nthD (⟦ M.⌜ as ⌝ᵛ ⟧s[ T ] ρ) i)
      rels i x x∈ = subst (x ⊑_) (sym (nth-atm as T ρ i))
                      (ar (Data.Vec.lookup as i) x (subst (λ D → D x) (nth-atm as Tᶜ ρᶜ i) x∈))
    simS (get {n} i a) w w∈ = ⊑-mono w N⊆ (proj₂ (ar a (tup[ i ] w) (proj₁ t∈)))
      where
      A' = 𝒜 a T ρ
      t∈ : tup[ i ] w ∈ ⌊ 𝒜 a Tᶜ ρᶜ ⌋
      t∈ = no-bad {tup n} {⌊ 𝒜 a Tᶜ ρᶜ ⌋} {proj i ⟨ ⌊ 𝒜 a Tᶜ ρᶜ ⌋ , ptt ⟩} (λ d d∈ → kind₄-tup (ar-kind a d d∈)) w
             (βᵛ {F = λ X → checked (tup n) X (proj i ⟨ X , ptt ⟩)} (vᶜ a) w w∈)

      N⊆ : Nth i (A' ⇂ Kd (tup n)) ⊆ 𝒮 (get i a) T ρ
      N⊆ e ⟨ e∈ , _ ⟩ = βᵛ⁻ {F = λ X → proj i ⟨ X , ptt ⟩} (v' a) e ⟨ e∈ , proj₁ (v' a) _ e∈ ⟩
    simS (inl a) d d∈ with inl-elim {d = d} (βᵛ {F = λ X → inlᴰ ⟨ X , ptt ⟩} (vᶜ a) d d∈)
    ... | ⟨ x , ⟨ refl , ⟨ x∈ , x≢ ⟩ ⟩ ⟩ = ⟨ lift x≢ , ⊑-mono x L⊆ (ar a x x∈) ⟩
      where
      L⊆ : 𝒜 a T ρ ⊆ Lefts (𝒮 (inl a) T ρ ⇂ Kd sum)
      L⊆ e e∈ = ⟨ βᵛ⁻ {F = λ X → inlᴰ ⟨ X , ptt ⟩} (v' a) _ ⟨ e∈ , proj₁ (v' a) _ e∈ ⟩ , inj₂ refl ⟩
    simS (inr a) d d∈ with inr-elim {d = d} (βᵛ {F = λ X → inrᴰ ⟨ X , ptt ⟩} (vᶜ a) d d∈)
    ... | ⟨ x , ⟨ refl , ⟨ x∈ , x≢ ⟩ ⟩ ⟩ = ⟨ lift x≢ , ⊑-mono x R⊆ (ar a x x∈) ⟩
      where
      R⊆ : 𝒜 a T ρ ⊆ Rights (𝒮 (inr a) T ρ ⇂ Kd sum)
      R⊆ e e∈ = ⟨ βᵛ⁻ {F = λ X → inrᴰ ⟨ X , ptt ⟩} (v' a) _ ⟨ e∈ , proj₁ (v' a) _ e∈ ⟩ , inj₂ refl ⟩
    simS (prim p a b) = prim-r p (vᶜ a) (vᶜ b) (v' a) (v' b)
      (λ d d∈ → kind₄-base (ar-kind a d d∈)) (λ d d∈ → kind₄-base (ar-kind b d d∈))
      (λ k k∈ → proj₁ (lower (ar a _ k∈))) (λ k k∈ → proj₁ (lower (ar b _ k∈)))
    simS (inject G a) d d∈ = ⊑-mono d (λ _ → proj₁) (ar a d d∈)
    simS (project t a) = project-r t (vᶜ a) (aconᴬ a) (v' a) (ar a)


    {- an error of the simple expression is one of CFGᵀ -}
    sr-ω : ∀ {A} (s : Simple Σ Δ A) → ω ∈ 𝒮ᶜ s Tᶜ ρᶜ → ω ∈ 𝒮 s T ρ
    sr-ω (atm a) ω∈ = ⊥-elim (proj₁ (vᶜ a) ω ω∈ refl)
    sr-ω {Any} s ω∈ = lower (simS s ω ω∈)
    sr-ω {⟪ G ⟫} s ω∈ = proj₁ (lower (simS s ω ω∈))

    {- a value of the simple expression gives one of CFGᵀ -}
    sr-conv : ∀ {A} (s : Simple Σ Δ A) → Conv (𝒮ᶜ s Tᶜ ρᶜ) → Conv (𝒮 s T ρ)
    sr-conv (atm a) _ = Val⇒Conv (v' a)
    sr-conv {Any} s ⟨ d , ⟨ d∈ , d≢ ⟩ ⟩ = ⊑-val d d≢ (simS s d d∈)
    sr-conv {⟪ G ⟫} s ⟨ d , ⟨ d∈ , d≢ ⟩ ⟩ = let ⟨ e , ⟨ e∈ , e≢ ⟩ ⟩ = ⊑-val d d≢ (simS s d d∈) in ⟨ e , ⟨ proj₁ e∈ , e≢ ⟩ ⟩

    {- the values the slot binds -}
    sr-mem : ∀ {A} (s : Simple Σ Δ A) V → mem V ⊆ ⌊ 𝒮ᶜ s Tᶜ ρᶜ ⌋ → SR A (mem V) ⌊ 𝒮 s T ρ ⌋
    sr-mem {code n} (atm a) V V⊆ u u∈ = code-mono (tup n) u (⌊⌋-clean (proj₁ (v' a))) (ar a u (proj₁ (V⊆ u u∈)))
    sr-mem {Any} s V V⊆ x x∈ = ⊑-⌊⌋ x (proj₂ (V⊆ x x∈)) (simS s x (proj₁ (V⊆ x x∈)))
    sr-mem {⟪ G ⟫} s V V⊆ x x∈ =
      ⊑-mono x (λ e e∈ → ⟨ ⟨ proj₁ (proj₁ e∈) , proj₂ e∈ ⟩ , proj₂ (proj₁ e∈) ⟩) (⊑-⌊⌋ x (proj₂ (V⊆ x x∈)) (simS s x (proj₁ (V⊆ x x∈))))

  {- the blocks are related -}
  BR : ∀ {Bs} → BEnv Bs → BEnv Bs → Set₁
  BR {Bs} Bᶜ B = ∀ {Δ} (l : Bs ∋ Δ) {ρᶜ ρ} → ER {Δ} ρᶜ ρ → Con-env ρ → nonempty-env ρ → Lifted _⊑_ (Bᶜ l ρᶜ) (B l ρ)

  {- the environment of the rest of a tail, with a new slot -}
  er-ext : ∀ {Δ' Δ A} (p : Δ' ≤ₗ Δ) {ρᶜ ρ Xᶜ X} → ER {Δ} ρᶜ ρ → SR A Xᶜ X → Val Xᶜ → Con Xᶜ → Clean X
    → ER {A ∷ Δ'} (Xᶜ • drop p ρᶜ) (X • drop p ρ)
  er-ext p {ρᶜ} {ρ} h r v c cl = record
    { rel = λ { Z → r ; (S y) → subst₂ (SR _) (sym (drop-idx p ρᶜ y)) (sym (drop-idx p ρ y)) (rel h (⊑-∋ p y)) }
    ; valᶜ = λ { Z → v ; (S y) → subst Val (sym (drop-idx p ρᶜ y)) (valᶜ h (⊑-∋ p y)) }
    ; conᶜ = λ { Z → c ; (S y) → subst Con (sym (drop-idx p ρᶜ y)) (conᶜ h (⊑-∋ p y)) }
    ; clean = λ { Z → cl ; (S y) → subst Clean (sym (drop-idx p ρ y)) (clean h (⊑-∋ p y)) } }

  tail-r : ∀ {Bs Δ} (t : Tail Σ Bs Δ) {Bᶜ B : BEnv Bs} → BR Bᶜ B → (∀ {Δ'} (l : Bs ∋ Δ') → Ok (B l))
    → ∀ {ρᶜ ρ} → ER {Δ} ρᶜ ρ → Con-env ρ → nonempty-env ρ → Lifted _⊑_ (⟦ t ⟧ᶜᵗ Tᶜ Bᶜ ρᶜ) (⟦ t ⟧ᵗ T B ρ)
  tail-r (return s) br oB h cρ NE = simS h cρ NE s
  tail-r (goto l) br oB h cρ NE = br l h cρ NE
  tail-r (seq {Δ'} {A} p s t) {Bᶜ} {B} br oB {ρᶜ} {ρ} h cρ NE w w∈
    with proj₁ (letᵐ-unfold {𝒮ᶜ s Tᶜ ρᶜ} {λ X → ⟦ t ⟧ᶜᵗ Tᶜ Bᶜ (X • drop p ρᶜ)}) w w∈
  ... | inj₁ ⟨ refl , ω∈ ⟩ = lift (inj₁ ⟨ refl , sr-ω h cρ NE s ω∈ ⟩)
  ... | inj₂ ⟨ _ , ⟨ V , ⟨ ⟨ ⟨ w∈′ , ⟨ neV , cV ⟩ ⟩ , nV ⟩ , ⟨ V⊆ , _ ⟩ ⟩ ⟩ ⟩ =
    ⊑-mono w (let-⊇ cD cv mF fin) (tail-r t br oB h′ cρ′ NE′ w w∈′)
    where
    D = 𝒮 s T ρ
    F = λ X → ⟦ t ⟧ᵗ T B (X • drop p ρ)
    cD : Con D
    cD = con TC M.⌜ ⌞ s ⌟ ⌝ cρ
    cv : Conv D
    cv = sr-conv h cρ NE s (let ⟨ v , v∈ ⟩ = E≢[]⇒nonempty-mem neV in ⟨ v , V⊆ v v∈ ⟩)
    okF = drop-ok p (tail-ok TC t oB)
    mF : Mono₁ F
    mF {X} {Y} X⊆ = proj₁ okF {X • ρ} {Y • ρ} (λ { zero → X⊆ ; (suc i) → λ _ z → z })
    fin : Finitary F ⌊ D ⌋
    fin = fin₁ okF NE cv
    h′ = er-ext p h (sr-mem h cρ NE s V V⊆) (noerr-val V neV nV) (≈⇒Con cV) (λ _ → proj₂)
    cρ′ = Con-• (Con-⊆ cD ⌊⌋-⊆) (drop-con p cρ)
    NE′ = extend-nonempty-env (drop-ne p NE) cv
  tail-r (case {Δ'} a p l₁ l₂) {Bᶜ} {B} br oB {ρᶜ} {ρ} h cρ NE w w∈
    with no-bad {inj} {⌊ 𝒜 a Tᶜ ρᶜ ⌋}
           {𝒞 ⟨ ⌊ 𝒜 a Tᶜ ρᶜ ⌋ ⇂ ValPayload , ⟨ (λ X → Bᶜ l₁ (X • drop p ρᶜ)) , ⟨ (λ X → Bᶜ l₂ (X • drop p ρᶜ)) , ptt ⟩ ⟩ ⟩}
           (λ d d∈ → kind₄-inj (ar-kind h cρ NE a d d∈)) w
           (βᵛ {𝒜 a Tᶜ ρᶜ} {λ X → checked inj X (𝒞 ⟨ X ⇂ ValPayload , ⟨ (λ X → Bᶜ l₁ (X • drop p ρᶜ)) , ⟨ (λ X → Bᶜ l₂ (X • drop p ρᶜ)) , ptt ⟩ ⟩ ⟩)}
               (vᶜ h cρ NE a) w w∈)
  ... | inj₁ ⟨ v , ⟨ V , ⟨ all , ⟨ w∈′ , c ⟩ ⟩ ⟩ ⟩ = ⊑-mono w (λ y y∈ → βᵛ⁻ {A'} {λ X → 𝒞 ⟨ X ⇂ ValPayload , ⟨ F₁ , ⟨ F₂ , ptt ⟩ ⟩ ⟩} (v' h cρ NE a) y
       (𝒞ˡ-⊇ {⌊ A' ⌋ ⇂ ValPayload} {F₁} {F₂} cY (fin₁ (drop-ok p (oB l₁)) NE neY) (λ d y → y) y y∈))
      (br l₁ (er-ext p h rY (noerr-val (v ∷ V) (λ ()) (λ ω∈ → proj₂ (all ω ω∈) refl)) (≈⇒Con c) (λ _ → proj₂))
             (Con-• cY (drop-con p cρ)) (extend-nonempty-env (drop-ne p NE) neY) w w∈′)
    where
    A' = 𝒜 a T ρ
    F₁ = λ X → B l₁ (X • drop p ρ)
    F₂ = λ X → B l₂ (X • drop p ρ)
    Y : 𝒫 Value
    Y d = (⌊ A' ⌋ ⇂ ValPayload) (left d)
    cY : Con Y
    cY = Con-⊆ (lefts-con (Con-⊆ (c' h cρ NE a) ⌊⌋-⊆)) (λ d y → proj₁ y)
    rY : SR Any (mem (v ∷ V)) Y
    rY x x∈ = ⊑-mono x (λ e e∈ → ⟨ ⟨ proj₁ (proj₁ e∈) , (λ ()) ⟩ , proj₂ e∈ ⟩)
                (⊑-⇂ x (λ e e∈ ke ω≡ → proj₂ (all x x∈) (kind-ω (trans (sym ke) (cong kind ω≡))))
                  (proj₂ (ar h cρ NE a (left x) (proj₁ (proj₁ (all x x∈))))))
    neY : nonempty Y
    neY = ⊑-ne v (rY v (here refl))
  ... | inj₂ ⟨ v , ⟨ V , ⟨ all , ⟨ w∈′ , c ⟩ ⟩ ⟩ ⟩ = ⊑-mono w (λ y y∈ → βᵛ⁻ {A'} {λ X → 𝒞 ⟨ X ⇂ ValPayload , ⟨ F₁ , ⟨ F₂ , ptt ⟩ ⟩ ⟩} (v' h cρ NE a) y
       (𝒞ʳ-⊇ {⌊ A' ⌋ ⇂ ValPayload} {F₁} {F₂} cY (fin₁ (drop-ok p (oB l₂)) NE neY) (λ d y → y) y y∈))
      (br l₂ (er-ext p h rY (noerr-val (v ∷ V) (λ ()) (λ ω∈ → proj₂ (all ω ω∈) refl)) (≈⇒Con c) (λ _ → proj₂))
             (Con-• cY (drop-con p cρ)) (extend-nonempty-env (drop-ne p NE) neY) w w∈′)
    where
    A' = 𝒜 a T ρ
    F₁ = λ X → B l₁ (X • drop p ρ)
    F₂ = λ X → B l₂ (X • drop p ρ)
    Y : 𝒫 Value
    Y d = (⌊ A' ⌋ ⇂ ValPayload) (right d)
    cY : Con Y
    cY = Con-⊆ (rights-con (Con-⊆ (c' h cρ NE a) ⌊⌋-⊆)) (λ d y → proj₁ y)
    rY : SR Any (mem (v ∷ V)) Y
    rY x x∈ = ⊑-mono x (λ e e∈ → ⟨ ⟨ proj₁ (proj₁ e∈) , (λ ()) ⟩ , proj₂ e∈ ⟩)
                (⊑-⇂ x (λ e e∈ ke ω≡ → proj₂ (all x x∈) (kind-ω (trans (sym ke) (cong kind ω≡))))
                  (proj₂ (ar h cρ NE a (right x) (proj₁ (proj₁ (all x x∈))))))
    neY : nonempty Y
    neY = ⊑-ne v (rY v (here refl))


  blocks-r : ∀ {Bs} (bs : Blocks Σ Bs) → BR (blocksᶜ bs Tᶜ) (blocks bs T)
  blocks-r (bs ▷ t) Z = tail-r t (blocks-r bs) (blocks-ok TC bs)
  blocks-r (bs ▷ t) (S l) = blocks-r bs l

  run-r : ∀ {Δ} (b : Body Σ Δ) {ρᶜ ρ} → ER {Δ} ρᶜ ρ → Con-env ρ → nonempty-env ρ → Lifted _⊑_ (runᶜ b Tᶜ ρᶜ) (run b T ρ)
  run-r (body bs t) = tail-r t (blocks-r bs) (blocks-ok TC bs)

  {- the code of a definition, on related environments of its kind and arguments -}
  code-r : ∀ {n} (b : Body Σ (Any ∷ ⟪ tup n ⟫ ∷ [])) → SR (code n) (codeᶜʰ Tᶜ b) (codeᶜ T b)
  code-r {n} b = code-ΛΛ λ V U w neV neU cV cU nV nU w∈ E X cE cX clE clX rV rU → bodyᵣ V U w neV neU nV nU w∈ E X cE cX clE clX rV rU
    where
    bodyᵣ : ∀ V U w → V ≢ [] → U ≢ [] → NoErr V → NoErr U
      → w ∈ letᵐ ⟨ mem V , ⟨ (λ X' → letᵐ ⟨ mem U , ⟨ (λ Y' → runᶜ b Tᶜ (Y' • X' • λ _ → init)) , ptt ⟩ ⟩) , ptt ⟩ ⟩
      → ∀ E X → Con E → Con X → Clean E → Clean X → V ⊑* (E ⇂ₖ tup n) → U ⊑* X
      → w ⊑ ⋆ ⟨ ⋆ ⟨ codeᶜ T b , ⟨ E ⇂ₖ tup n , ptt ⟩ ⟩ , ⟨ X , ptt ⟩ ⟩
    bodyᵣ V U w neV neU nV nU w∈ E X cE cX clE clX rV rU
      with proj₁ (letᵐ-entries (noerr-val V neV nV)) w w∈
    ... | ⟨ V' , ⟨ neV' , ⟨ cV' , ⟨ nV' , ⟨ V'⊆ , w∈′ ⟩ ⟩ ⟩ ⟩ ⟩
      with proj₁ (letᵐ-entries (noerr-val U neU nU)) w w∈′
    ... | ⟨ U' , ⟨ neU' , ⟨ cU' , ⟨ nU' , ⟨ U'⊆ , w∈″ ⟩ ⟩ ⟩ ⟩ ⟩ =
      ⊑-mono w (ΛΛᵐ-call {λ X′ Y′ → run b T (Y′ • X′ • λ _ → init)} cE′ cX clE′ clX
                  (fin₂ (run-ok TC b) neE neX))
        (run-r b h′ (Con-• cX (Con-• cE′ (λ _ → Con-⌈⌉ ω))) NE′ w w∈″)
      where
      E′ = E ⇂ₖ tup n
      cE′ = Con-⊆ cE (λ _ → proj₁)
      clE′ : Clean E′
      clE′ d d∈ = clE d (proj₁ d∈)
      neE : nonempty E′
      neE = let ⟨ v , v∈ ⟩ = E≢[]⇒nonempty-mem neV in ⊑-ne v (⊑*-∈ rV v∈)
      neX : nonempty X
      neX = let ⟨ u , u∈ ⟩ = E≢[]⇒nonempty-mem neU in ⊑-ne u (⊑*-∈ rU u∈)
      NE′ : nonempty-env (X • E′ • λ _ → init)
      NE′ = extend-nonempty-env (extend-nonempty-env (λ _ → ⟨ ω , refl ⟩) neE) neX
      h′ : ER {Any ∷ ⟪ tup n ⟫ ∷ []} (mem U' • mem V' • λ _ → init) (X • E′ • λ _ → init)
      h′ = record
        { rel = λ { Z → λ x x∈ → ⊑*-∈ rU (U'⊆ x x∈)
                  ; (S Z) → λ x x∈ → ⊑-⇂ x (λ e e∈ ke → inj₂ (cong kind₄ (proj₂ e∈))) (⊑*-∈ rV (V'⊆ x x∈)) }
        ; valᶜ = λ { Z → noerr-val U' neU' nU' ; (S Z) → noerr-val V' neV' nV' }
        ; conᶜ = λ { Z → ≈⇒Con cU' ; (S Z) → ≈⇒Con cV' }
        ; clean = λ { Z → clX ; (S Z) → clE′ } }

{- Tables ------------------------------------------------------------------------------}

{- a reference at the position of a definition has the type of the definition -}
lvl-type : ∀ {Σ ns : List ℕ} {m n : ℕ} (s : (m ∷ ns) ≤ₗ Σ) (f : Σ ∋ n) → lvl f ≡ length ns → n ≡ m
lvl-type here⊑ Z e = refl
lvl-type here⊑ (S f) e = ⊥-elim (<⇒≢ (lvl-< f) e)
lvl-type {ns = ns} (there⊑ s) Z e = ⊥-elim (<⇒≢ (⊑-len s) (sym e))
  where open import proof.Framework.Lookup using (⊑-len)
lvl-type (there⊑ s) (S f) e = lvl-type s f e

tbl-r : ∀ {Σ ns} (s : ns ≤ₗ Σ) (ds : All (λ n → Body Σ (Any ∷ ⟪ tup n ⟫ ∷ [])) ns)
  → ∀ {n} (f : Σ ∋ n) → SR (code n) (tbl (codeᶜʰ {Σ}) ds (lvl f)) (tbl (codeᶜ {Σ}) ds (lvl f))
tbl-r s [] {n} f = errcode-rel (tup n)
tbl-r {Σ} {_ ∷ ns} s (d ∷ ds) {n} f with lvl f ≟ length ns
... | yes e = subst (λ k → SR (code k) (codeᶜʰ (tbl codeᶜʰ ds) d) (codeᶜ (tbl codeᶜ ds) d)) (sym (lvl-type s f e))
  (Sim.code-r (tbl-r s' ds) (tbl-val (λ _ → ΛΛᵐ-val) ds) (tbl-val (λ _ → ΛΛᵐ-val) ds) (tbl-con {c = codeᶜ {Σ}} (λ TC b → codeᶜ-con TC b) ds) d)
  where s' = Framework.Membership.⊑-trans (there⊑ here⊑) s
        open import proof.Semantics.GraphErr.Typed.Clos5 using (tbl-val; tbl-con)
        open import proof.Semantics.GraphErr.Typed.CFG using (codeᶜ-con)
        import Framework.Membership
... | no _ = tbl-r (Framework.Membership.⊑-trans (there⊑ here⊑) s) ds f
  where import Framework.Membership

{- CFGᵀ with checks reflects into CFGᵀ -}
reflect : ∀ (P : Program) → Lifted _⊑_ ⟦ P ⟧ᶜʰ ⟦ P ⟧ᶜ
reflect (program {Σ} ds b) =
  Sim.run-r (tbl-r here⊑ ds) (tbl-val (λ _ → ΛΛᵐ-val) ds) (tbl-val (λ _ → ΛΛᵐ-val) ds) (tbl-con {c = codeᶜ {Σ}} (λ TC b → codeᶜ-con TC b) ds) b

    (record { rel = λ () ; valᶜ = λ () ; conᶜ = λ () ; clean = λ () }) (λ _ → Con-⌈⌉ ω) (λ _ → ⟨ ω , refl ⟩)
  where open import proof.Semantics.GraphErr.Typed.Clos5 using (tbl-val; tbl-con)
        open import proof.Semantics.GraphErr.Typed.CFG using (codeᶜ-con)

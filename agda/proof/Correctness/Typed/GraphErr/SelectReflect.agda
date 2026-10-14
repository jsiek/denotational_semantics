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
open import proof.Framework.GraphModel.TypedBinders using (ΛΛᵐ-call)
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
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)
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
    simS (callc f a) w w∈ = {!!}
    simS (tuple {n = n} as) = {!!}
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
    simS (project t a) = {!!}

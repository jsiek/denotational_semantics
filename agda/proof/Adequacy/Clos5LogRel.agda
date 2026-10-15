{-

  Adequacy of the graph model for the Clos5ᵀ machine: every element of
  the denotation of a program is witnessed by a run of the machine, for
  the table ds of its definitions. As for untyped Clos5
  (Untyped/proof/Adequacy/Clos5LogRel.agda): a logical relation 𝕍 d v, by
  recursion on the denotational value d (and on the injections dyn of v;
  Clos5Values.agda, shared with X86ᵀ, which runs definitions otherwise),
  and the fundamental lemma (adequate) by induction on the term, with the
  table related to the code pointers (𝕋, tab). Typed values have the
  shape of their type, so no case for a value of the wrong kind is
  needed, but for project, where the tag of an Any value is read off
  the element it is related to (tag). A definition sees only the older
  ones in the semantics, and the machine finds it in the whole table
  (tab, through the levels of the references).

-}

open import Data.List using (List; []; _∷_; length)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _≟_)
open import Language.Typed.Type renaming (_≟_ to _≟F_)
open import Language.Typed.Clos5

module proof.Adequacy.Clos5LogRel {Σ : List ℕ} (ds : All (Code Σ) Σ) where

open import Framework.Primitives using (Base; base-rep; Int)
open import Language.Prim using (Prim; sub; eq; δ; int; bool)
open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.Domain
  using (Value; _↦_; ν; ω; ⦅_,_⦆; tup[_]_; left; right; ⟨⟩; _•_) renaming (const to dconst)
open import proof.Framework.GraphModel.Ops using (nthD)
open import proof.Semantics.Graph.Prim using () renaming (out to dout)
open import Semantics.Graph.Typed.Ops using (Table; tables; accepts; fun₄; init)
open import Semantics.Graph.Typed.Clos5 using (⟦_⟧[_]; ⟦_⟧s[_]; code′)
open import Semantics.CEK.Typed.Clos5
open import Semantics.Observation using (Obs; o-const; Answer)
open import Framework.Lookup using (_!_)
open import proof.Adequacy.Clos5Common ds
open import proof.Adequacy.Clos5Values using (module Rel; proj?-ok)
import proof.Framework.GraphModel.Env as E

open import Data.Bool using (true; false)
open import Data.Maybe using (just)
open import Framework.Smallstep Obs using (next?)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin; zero; suc)
open import Data.Integer using (_-_) renaming (_≟_ to _≟ℤ_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (_×_; Σ-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Vec using (Vec; []; _∷_; toList; lookup)
open import Data.Vec.Properties using (length-toList)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (yes; no; does)

{- The logical relation (Clos5Values.agda) --------------------------------------------}

{- definition f runs on the environment e and the argument a to a value with P -}
Run : ∀ {n} → Σ ∋ n → Val Σ ⟪ tup n ⟫ → Val Σ Any → (Val Σ Any → Set) → Set
Run f e a P = Σ[ v ∈ Val Σ Any ] (a ∷ e ∷ []) ⊢ ds ! f ⇓ v × P v

open Rel Run public

{- Lemmas about runs -------------------------------------------------------------------}

collect : ∀ {Γ A} {γ : Env Σ Γ} {M : Tm Σ Γ A} {v} (P : Value → Val Σ A → Set) V
  → (∀ d → d ∈ mem V → Σ[ v' ∈ Val Σ A ] γ ⊢ M ⇓ v' × P d v') → γ ⊢ M ⇓ v
  → ∀ d → d ∈ mem V → P d v
collect P V all e d d∈ with all d d∈
... | ⟨ v' , ⟨ e' , r ⟩ ⟩ with ⇓-det e e'
... | refl = r

{- the environment of a closure related to the second component of a pair -}
snd𝕍 : Value → Val Σ ⟪ fun ⟫ → Set
snd𝕍 u (pack c e) = 𝕍 u e

{- The fundamental lemma -----------------------------------------------------------------}

adequate : ∀ {Γ A} (M : Tm Σ Γ A) {T : Table Σ} {ρ} {γ : Env Σ Γ} {d} → 𝕋 T → 𝔾 ρ γ → d ∈ ⟦ M ⟧[ T ] ρ
  → Σ[ v ∈ Val Σ A ] γ ⊢ M ⇓ v × 𝕍 d v
adequate-args : ∀ {Γ n} (Ms : Vec (Tm Σ Γ Any) n) {T : Table Σ} {ρ} {γ : Env Σ Γ} → 𝕋 T → 𝔾 ρ γ
  → (∀ j → nonempty (nthD (⟦ Ms ⟧s[ T ] ρ) j))
  → Σ[ vs ∈ List (Val Σ Any) ] Evals γ Ms vs × (∀ j d → d ∈ nthD (⟦ Ms ⟧s[ T ] ρ) j → 𝕍At j d vs)

adequate (` x) 𝕋T G d∈ = ⟨ _ , ⟨ (λ κ → refl ∷↠ done) , G x _ d∈ ⟩ ⟩
adequate (fun-ref f) 𝕋T G d∈ = ⟨ code f , ⟨ (λ κ → refl ∷↠ done) , 𝕋T f _ d∈ ⟩ ⟩
adequate (pack L M) {γ = γ} {d} 𝕋T G d∈ with pair-inv d d∈
... | ⟨ u , ⟨ u' , ⟨ refl , ⟨ u∈ , u'∈ ⟩ ⟩ ⟩ ⟩ with adequate L 𝕋T G u∈ | adequate M 𝕋T G u'∈
... | ⟨ c , ⟨ eL , rL ⟩ ⟩ | ⟨ e , ⟨ eM , rM ⟩ ⟩ =
  ⟨ pack c e , ⟨ (λ κ → refl ∷↠ eL (packL M γ κ) ++↠ refl ∷↠ eM (packR c κ) ++↠ refl ∷↠ done) , ⟨ rL , rM ⟩ ⟩ ⟩
adequate (callc L M) 𝕋T G ⟨ [] , ⟨ _ , ⟨ _ , ne ⟩ ⟩ ⟩ = ⊥-elim (ne refl)
adequate (callc L M) 𝕋T G ⟨ _ ∷ _ , ⟨ ⟨ [] , ⟨ _ , ⟨ _ , ne ⟩ ⟩ ⟩ , _ ⟩ ⟩ = ⊥-elim (ne refl)
adequate (callc L M) {γ = γ} {d} 𝕋T G ⟨ v₀ ∷ V , ⟨ ⟨ u₀ ∷ U , ⟨ ⟨ e₀ , f∈ ⟩ , ⟨ U⊆ , _ ⟩ ⟩ ⟩ , ⟨ V⊆ , _ ⟩ ⟩ ⟩
    with adequate L 𝕋T G f∈ | adequate M 𝕋T G (V⊆ v₀ (here refl))
... | ⟨ pack (code g) e , ⟨ eL , ⟨ rc , _ ⟩ ⟩ ⟩ | ⟨ a , ⟨ eM , _ ⟩ ⟩
    with rc e (all→𝕍s (u₀ ∷ U) (collect snd𝕍 (u₀ ∷ U) (λ u u∈ → snd (adequate L 𝕋T G (proj₂ (U⊆ u u∈)))) eL))
            a (all→𝕍s (v₀ ∷ V) (collect 𝕍 (v₀ ∷ V) (λ u u∈ → adequate M 𝕋T G (V⊆ u u∈)) eM))
  where
  snd : ∀ {u u'} → Σ[ v ∈ Val Σ ⟪ fun ⟫ ] γ ⊢ L ⇓ v × 𝕍 ⦅ u' , u ⦆ v → Σ[ v ∈ Val Σ ⟪ fun ⟫ ] γ ⊢ L ⇓ v × snd𝕍 u v
  snd ⟨ pack c e , ⟨ ev , r ⟩ ⟩ = ⟨ pack c e , ⟨ ev , proj₂ r ⟩ ⟩
... | ⟨ v , ⟨ eB , r ⟩ ⟩ =
  ⟨ v , ⟨ (λ κ → refl ∷↠ eL (callL M γ κ) ++↠ refl ∷↠ eM (callR (pack (code g) e) κ) ++↠ refl ∷↠ eB κ) , r ⟩ ⟩
adequate (lit B c) {d = d} 𝕋T G d∈ with ℬ-inv d d∈
... | refl = ⟨ const c , ⟨ (λ κ → refl ∷↠ done) , refl ⟩ ⟩
adequate (tuple {n = n} Ms) {γ = γ} {d} 𝕋T G d∈ with 𝒯-inv n d d∈
... | inj₁ ⟨ refl , refl ⟩ with tuple-run {γ = γ} [] Ms [] refl (none Ms)
  where
  none : (Ms : Vec (Tm Σ _ Any) 0) → Evals γ Ms []
  none [] = []
...   | ⟨ [] , ⟨ τ , _ ⟩ ⟩ = ⟨ tup [] , ⟨ (λ κ → refl ∷↠ τ κ) , tt ⟩ ⟩
adequate (tuple {n = n} Ms) {γ = γ} {d} 𝕋T G d∈
    | inj₂ ⟨ m , ⟨ i , ⟨ u , ⟨ refl , ⟨ refl , ⟨ u∈ , ne ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ with adequate-args Ms 𝕋T G ne
... | ⟨ vs , ⟨ evs , rs ⟩ ⟩ with tuple-run {γ = γ} [] Ms vs refl evs
... | ⟨ ws , ⟨ τ , teq ⟩ ⟩ =
  ⟨ tup ws , ⟨ (λ κ → refl ∷↠ τ κ) , subst (𝕍At i u) (sym teq) (rs i u u∈) ⟩ ⟩
adequate (get i M) 𝕋T G d∈ with adequate M 𝕋T G d∈
... | ⟨ tup ws , ⟨ e , r ⟩ ⟩ =
  ⟨ lookup ws i , ⟨ (λ κ → refl ∷↠ e (getK i κ) ++↠ refl ∷↠ done) , 𝕍At-lookup i _ ws r ⟩ ⟩
adequate (inl M) {d = d} 𝕋T G d∈ with inl-inv d d∈
... | ⟨ u , ⟨ refl , u∈ ⟩ ⟩ with adequate M 𝕋T G u∈
... | ⟨ v , ⟨ e , r ⟩ ⟩ = ⟨ inl v , ⟨ (λ κ → refl ∷↠ e (inlK κ) ++↠ refl ∷↠ done) , r ⟩ ⟩
adequate (inr M) {d = d} 𝕋T G d∈ with inr-inv d d∈
... | ⟨ u , ⟨ refl , u∈ ⟩ ⟩ with adequate M 𝕋T G u∈
... | ⟨ v , ⟨ e , r ⟩ ⟩ = ⟨ inr v , ⟨ (λ κ → refl ∷↠ e (inrK κ) ++↠ refl ∷↠ done) , r ⟩ ⟩
adequate (case L M N) {γ = γ} 𝕋T G (inj₁ ⟨ u , ⟨ U , ⟨ allL , ⟨ w∈ , _ ⟩ ⟩ ⟩ ⟩)
    with adequate L 𝕋T G (allL u (here refl))
... | ⟨ inl a , ⟨ eL , _ ⟩ ⟩
    with adequate M 𝕋T (𝔾-ext (u ∷ U) a G (all→𝕍s (u ∷ U)
           (collect (λ d v → 𝕍 (left d) v) (u ∷ U) (λ d d∈ → adequate L 𝕋T G (allL d d∈)) eL))) w∈
... | ⟨ v , ⟨ eM , r ⟩ ⟩ = ⟨ v , ⟨ (λ κ → refl ∷↠ eL (caseK M N γ κ) ++↠ refl ∷↠ eM κ) , r ⟩ ⟩
adequate (case L M N) 𝕋T G (inj₁ ⟨ u , ⟨ U , ⟨ allL , _ ⟩ ⟩ ⟩) | ⟨ inr a , ⟨ _ , () ⟩ ⟩
adequate (case L M N) {γ = γ} 𝕋T G (inj₂ ⟨ u , ⟨ U , ⟨ allR , ⟨ w∈ , _ ⟩ ⟩ ⟩ ⟩)
    with adequate L 𝕋T G (allR u (here refl))
... | ⟨ inr a , ⟨ eL , _ ⟩ ⟩
    with adequate N 𝕋T (𝔾-ext (u ∷ U) a G (all→𝕍s (u ∷ U)
           (collect (λ d v → 𝕍 (right d) v) (u ∷ U) (λ d d∈ → adequate L 𝕋T G (allR d d∈)) eL))) w∈
... | ⟨ v , ⟨ eN , r ⟩ ⟩ = ⟨ v , ⟨ (λ κ → refl ∷↠ eL (caseK M N γ κ) ++↠ refl ∷↠ eN κ) , r ⟩ ⟩
adequate (case L M N) 𝕋T G (inj₂ ⟨ u , ⟨ U , ⟨ allR , _ ⟩ ⟩ ⟩) | ⟨ inl a , ⟨ _ , () ⟩ ⟩
adequate (prim p L M) {γ = γ} 𝕋T G ⟨ n , ⟨ m , ⟨ n∈ , ⟨ m∈ , refl ⟩ ⟩ ⟩ ⟩
    with adequate L 𝕋T G n∈ | adequate M 𝕋T G m∈
... | ⟨ const _ , ⟨ eL , refl ⟩ ⟩ | ⟨ const _ , ⟨ eM , refl ⟩ ⟩ =
  ⟨ δᵀ p n m
  , ⟨ (λ κ → refl ∷↠ eL (primL p M γ κ) ++↠ refl ∷↠ eM (primR p n κ) ++↠ refl ∷↠ done) , 𝕍-δ p n m ⟩ ⟩
adequate (let′ M N) 𝕋T G ⟨ [] , ⟨ _ , ⟨ _ , ne ⟩ ⟩ ⟩ = ⊥-elim (ne refl)
adequate (let′ M N) {γ = γ} 𝕋T G ⟨ u ∷ U , ⟨ ⟨ d∈ , _ ⟩ , ⟨ U⊆ , _ ⟩ ⟩ ⟩
    with adequate M 𝕋T G (U⊆ u (here refl))
... | ⟨ a , ⟨ eM , _ ⟩ ⟩
    with adequate N 𝕋T (𝔾-ext (u ∷ U) a G (all→𝕍s (u ∷ U)
           (collect 𝕍 (u ∷ U) (λ d' d'∈ → adequate M 𝕋T G (U⊆ d' d'∈)) eM))) d∈
... | ⟨ v , ⟨ eN , r ⟩ ⟩ = ⟨ v , ⟨ (λ κ → refl ∷↠ eM (letK N γ κ) ++↠ refl ∷↠ eN κ) , r ⟩ ⟩
adequate (inject G' M) 𝕋T G d∈ with adequate M 𝕋T G d∈
... | ⟨ v , ⟨ e , r ⟩ ⟩ = ⟨ dyn G' v , ⟨ (λ κ → refl ∷↠ e (injK G' κ) ++↠ refl ∷↠ done) , r ⟩ ⟩
adequate (project t M) 𝕋T G ⟨ ⟨ d₀ , ⟨ d₀∈ , acc ⟩ ⟩ , d∈ ⟩
    with adequate M 𝕋T G d∈ | adequate M 𝕋T G d₀∈
... | ⟨ dyn H u , ⟨ e , r ⟩ ⟩ | ⟨ v₀ , ⟨ e₀ , r₀ ⟩ ⟩ with ⇓-det e₀ e
... | refl with tag t d₀ u acc r₀
... | refl = ⟨ u , ⟨ (λ κ → refl ∷↠ e (projK t κ) ++↠ cong (next? _ (λ w → ret w κ)) (proj?-ok t u) ∷↠ done) , r ⟩ ⟩

adequate-args [] 𝕋T G ne = ⟨ [] , ⟨ [] , (λ ()) ⟩ ⟩
adequate-args (M ∷ Ms) 𝕋T G ne with adequate M 𝕋T G (proj₂ (ne zero)) | adequate-args Ms 𝕋T G (λ j → ne (suc j))
... | ⟨ v , ⟨ e , _ ⟩ ⟩ | ⟨ vs , ⟨ evs , rs ⟩ ⟩ = ⟨ v ∷ vs , ⟨ e ∷ evs , R ⟩ ⟩
  where
  R : ∀ j d → d ∈ nthD (⟦ M ∷ Ms ⟧s[ _ ] _) j → 𝕍At j d (v ∷ vs)
  R zero d d∈ = ⟨ len evs , collect 𝕍 (d ∷ []) (λ { d' (here refl) → adequate M 𝕋T G d∈ }) e d (here refl) ⟩
    where
    len : ∀ {j Ns ws} → Evals _ {j} Ns ws → length ws ≡ j
    len [] = refl
    len (_ ∷ es) = cong suc (len es)
  R (suc j) d d∈ = rs j d d∈

{- The table of the program ---------------------------------------------------------------}

{- the code of definition f, which the machine finds -}
tab-ds : 𝕋 (tables code′ ds)
tab-ds = tab code′ ds λ {T} 𝕋T {n} f → code-𝕍 (λ X Y → ⟦ ds ! f ⟧[ T ] (Y • X • λ _ → init)) λ X Y w w∈ e Xe a Ya →
  adequate (ds ! f) 𝕋T (λ { Z d d∈ → 𝕍s-∈ Y Ya d∈ ; (S Z) d d∈ → 𝕍s-∈ X Xe d∈ }) w∈

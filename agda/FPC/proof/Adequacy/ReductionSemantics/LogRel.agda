{-

  Adequacy of the graph model for the reduction semantics of FPC
  (FPC/Semantics/ReductionSemantics/FPC.agda), as Plotkin's for PCF:
  every element of the denotation of a closed program is witnessed by
  the value the program reduces to.

  As for the clocked interpreter (FPC/proof/Adequacy/LogRel.agda): a
  logical relation 𝕍 d V, by recursion on the denotational value d (and
  on the folds of V), relates a constant to itself, a function entry
  U ↦ w to the λs whose body, with any value related to every element
  of U substituted for its variable, reduces to a value related to w,
  and so on. Reduction is by substitution, so there are no environments
  or closures: V is a closed value, and the fundamental lemma (adequate)
  is by induction on the term, under a closing substitution σ of values
  related to the environment (𝔾). A run of a subterm is a run of the
  term, in a frame (proof/Framework/Reduction.agda); reduction is
  deterministic (⇓-det), so an application needs one argument value
  related to all of the (finitely many) elements of U (collect).

-}

module FPC.proof.Adequacy.ReductionSemantics.LogRel where

open import Framework.Primitives using (Base; base-rep; Int)
open import Language.Prim using (sub; eq) renaming (δ to δᴾ)
open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.Domain renaming (const to dconst)
open import proof.Framework.GraphModel.Ops using (nthD)
open import proof.Semantics.Graph.Prim using () renaming (out to dout)
import proof.Framework.GraphModel.Env as E
open import FPC.Language.Type hiding (_[_])
open import FPC.Language.FPC
open import FPC.Language.FPCSubst using (exts; tmK; travs)
open import FPC.Semantics.GraphModel.FPC using (⟦_⟧; ⟦_⟧s)
open import FPC.Framework.AllUtil using (All; []; _∷_; lookup; pos)
open import FPC.proof.Semantics.ReductionSemantics.FPC
  using (red; reds; obs; out; _[_]; β; get?; case?; prim?; unfold?; value-red; exts-[]; lam; lit; tuple; inl; inr; fold)
  renaming (Value to Val; _•_ to _•ₛ_; sub to subst-tm)
open import Semantics.Observation using (Obs; o-error; o-const)
open import FPC.proof.Framework.ReductionAll Obs o-error using (Each; []; _∷_; each-lookup)
open import Semantics.Reduction.Smallstep using (Red; val; error; to; step-in)
open import proof.Framework.Reduction Obs o-error using (Star*; ε; _◅_; _◅◅_; Frame; frame; star-in; val-in)

open import Data.Bool using (true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin; zero; suc)
open import Data.Integer using () renaming (_≟_ to _≟ℤ_)
open import Data.List using (List; []; _∷_; length)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; Σ-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (does)

{- Evaluation -----------------------------------------------------------------------}

{- M reduces to the value V -}
infix 4 _⇓_
_⇓_ : ∀ {A} → Tm [] A → Tm [] A → Set
M ⇓ V = Star* red M V × Val V

{- reduction is deterministic -}
⇓-det : ∀ {A} {M V₁ V₂ : Tm [] A} → M ⇓ V₁ → M ⇓ V₂ → V₁ ≡ V₂
⇓-det ⟨ σ₁ , v₁ ⟩ ⟨ σ₂ , v₂ ⟩ = det σ₁ v₁ σ₂ v₂
  where
  det : ∀ {A} {M V₁ V₂ : Tm [] A} → Star* red M V₁ → Val V₁ → Star* red M V₂ → Val V₂ → V₁ ≡ V₂
  det ε _ ε _ = refl
  det ε v (s ◅ _) _ with trans (sym (value-red v)) s
  ... | ()
  det (s ◅ _) _ ε v with trans (sym (value-red v)) s
  ... | ()
  det (s ◅ σ) v (s' ◅ σ') v' with trans (sym s) s'
  ... | refl = det σ v σ' v'

{- the contexts that reduce a subterm first: an operand, once those
   before it are values -}
fr : ∀ {A B : Set} (g : A → B) {κ : A → Red B} {redA : A → Red A} {redB : B → Red B}
  → (∀ X → redB (g X) ≡ step-in g (redA X) (κ X)) → Frame redA redB g
fr g = frame _

app-l : ∀ {A B} (M : Tm [] A) → Frame red red (λ L → app {B = B} L M)
app-l M = fr (λ L → app L M) (λ _ → refl)

app-r : ∀ {A B} {V : Tm [] (A ⇒ B)} → Val V → Frame red red (app V)
app-r {V = V} v = fr (app V) (λ _ → val-in (value-red v))

{- The logical relation ---------------------------------------------------------------}

𝕍 : ∀ {A} → Value → Tm [] A → Set
𝕍s : ∀ {A} → List Value → Tm [] A → Set
𝕍At : ∀ {n Δ} → Fin n → Value → All (Tm []) Δ → Set

𝕍 d (fold V) = 𝕍 d V
𝕍 (dconst k) (lit B c) = dconst k ≡ dconst c
𝕍 (U ↦ w) (lam {B = B} N) = ∀ W → Val W → 𝕍s U W → Σ[ V ∈ Tm [] B ] (N [ W ]) ⇓ V × 𝕍 w V
𝕍 ν (lam N) = ⊤
𝕍 ⟨⟩ (tuple []) = ⊤
𝕍 (tup[ i ] d) (tuple Vs) = 𝕍At i d Vs
𝕍 (left d) (inl V) = 𝕍 d V
𝕍 (right d) (inr V) = 𝕍 d V
𝕍 _ _ = ⊥

𝕍s [] V = ⊤
𝕍s (d ∷ U) V = 𝕍 d V × 𝕍s U V

𝕍At {ℕ.suc n} {_ ∷ Δ} zero d (V ∷ Vs) = length Δ ≡ n × 𝕍 d V
𝕍At (suc i) d (V ∷ Vs) = 𝕍At i d Vs
𝕍At _ d _ = ⊥

𝕍s-∈ : ∀ {A} U {V : Tm [] A} {d} → 𝕍s U V → d ∈ mem U → 𝕍 d V
𝕍s-∈ (d ∷ U) ⟨ r , _ ⟩ (here refl) = r
𝕍s-∈ (d ∷ U) ⟨ _ , rs ⟩ (there d∈) = 𝕍s-∈ U rs d∈

all→𝕍s : ∀ {A} U {V : Tm [] A} → (∀ d → d ∈ mem U → 𝕍 d V) → 𝕍s U V
all→𝕍s [] all = tt
all→𝕍s (d ∷ U) all = ⟨ all d (here refl) , all→𝕍s U (λ d' d'∈ → all d' (there d'∈)) ⟩

𝕍At-lookup : ∀ {Δ A} (i : Δ ∋ A) d (Vs : All (Tm []) Δ) → 𝕍At (pos i) d Vs → 𝕍 d (lookup Vs i)
𝕍At-lookup Z d (V ∷ Vs) ⟨ _ , r ⟩ = r
𝕍At-lookup (S i) d (V ∷ Vs) r = 𝕍At-lookup i d Vs r

{- the output of a primitive -}
out-val : ∀ p n m → Val (out {[]} p n m)
out-val sub n m = lit
out-val eq n m with does (n ≟ℤ m)
... | true = inl (tuple [])
... | false = inr (tuple [])

𝕍-out : ∀ p n m → 𝕍 (dout (δᴾ p n m)) (out {[]} p n m)
𝕍-out sub n m = refl
𝕍-out eq n m with does (n ≟ℤ m)
... | true = tt
... | false = tt

{- the observation of a value related to a constant is that constant -}
𝕍-const : ∀ {A B} {k : base-rep B} (V : Tm [] A) → 𝕍 (dconst k) V → obs V ≡ o-const B k
𝕍-const (fold V) r = 𝕍-const V r
𝕍-const (lit B c) refl = refl

{- Related substitutions ---------------------------------------------------------------}

{- σ substitutes, for each variable, a value related to every element of
   its denotation in ρ -}
𝔾 : ∀ {Γ} → E.Env Value → (∀ {B} → Γ ∋ B → Tm [] B) → Set
𝔾 {Γ} ρ σ = ∀ {A} (x : Γ ∋ A) → Val (σ x) × (∀ d → d ∈ ρ (idx x) → 𝕍 d (σ x))

𝔾-ext : ∀ {Γ A ρ} {σ : ∀ {B} → Γ ∋ B → Tm [] B} U {W : Tm [] A} → 𝔾 ρ σ → Val W → 𝕍s U W
  → 𝔾 (mem U • ρ) (W •ₛ σ)
𝔾-ext U G w r Z = ⟨ w , (λ d d∈ → 𝕍s-∈ U r d∈) ⟩
𝔾-ext U G w r (S x) = G x

{- one value related to all elements of U, all of which M produces -}
collect : ∀ {A} (M : Tm [] A) {V} (P : Value → Tm [] A → Set) U
  → (∀ d → d ∈ mem U → Σ[ V' ∈ Tm [] A ] M ⇓ V' × P d V') → M ⇓ V
  → ∀ d → d ∈ mem U → P d V
collect M P U all e d d∈ with all d d∈
... | ⟨ V' , ⟨ e' , r ⟩ ⟩ with ⇓-det e e'
... | refl = r

{- a body, under a substitution and then for its variable -}
body : ∀ {Γ A B} (σ : ∀ {C} → Γ ∋ C → Tm [] C) (W : Tm [] A) (N : Tm (A ∷ Γ) B) {V}
  → Star* red (subst-tm (W •ₛ σ) N) V → Star* red (subst-tm (exts tmK σ) N [ W ]) V
body σ W N = subst (λ T → Star* red T _) (sym (exts-[] σ W N))

{- The fundamental lemma ----------------------------------------------------------------}

adequate : ∀ {Γ A} (M : Tm Γ A) {ρ} {σ : ∀ {B} → Γ ∋ B → Tm [] B} {d} → 𝔾 ρ σ → d ∈ ⟦ M ⟧ ρ
  → Σ[ V ∈ Tm [] A ] subst-tm σ M ⇓ V × 𝕍 d V
adequate-args : ∀ {Γ Δ} (Ms : All (Tm Γ) Δ) {ρ} {σ : ∀ {B} → Γ ∋ B → Tm [] B} → 𝔾 ρ σ
  → (∀ j → nonempty (nthD (⟦ Ms ⟧s ρ) j))
  → Σ[ Vs ∈ All (Tm []) Δ ] (Star* reds (travs tmK σ Ms) Vs × Each Val Vs)
      × (∀ j d → d ∈ nthD (⟦ Ms ⟧s ρ) j → 𝕍At j d Vs)

adequate (` x) {σ = σ} G d∈ = ⟨ σ x , ⟨ ⟨ ε , proj₁ (G x) ⟩ , proj₂ (G x) _ d∈ ⟩ ⟩
adequate (lam N) {d = ν} G d∈ = ⟨ _ , ⟨ ⟨ ε , lam ⟩ , tt ⟩ ⟩
adequate (lam N) {σ = σ} {d = U ↦ w} G ⟨ w∈ , _ ⟩ = ⟨ _ , ⟨ ⟨ ε , lam ⟩ , R ⟩ ⟩
  where
  R : ∀ W → Val W → 𝕍s U W → Σ[ V ∈ Tm [] _ ] (subst-tm (exts tmK σ) N [ W ]) ⇓ V × 𝕍 w V
  R W w r with adequate N (𝔾-ext U G w r) w∈
  ... | ⟨ V , ⟨ ⟨ s , v ⟩ , r' ⟩ ⟩ = ⟨ V , ⟨ ⟨ body σ W N s , v ⟩ , r' ⟩ ⟩
adequate (app L M) G ⟨ [] , ⟨ _ , ⟨ _ , ne ⟩ ⟩ ⟩ = ⊥-elim (ne refl)
adequate (app L M) {σ = σ} G ⟨ u ∷ U , ⟨ f∈ , ⟨ V⊆ , _ ⟩ ⟩ ⟩
    with adequate L G f∈ | adequate M G (V⊆ u (here refl))
... | ⟨ _ , ⟨ ⟨ sL , lam {N = N} ⟩ , rL ⟩ ⟩ | ⟨ W , ⟨ ⟨ sM , w ⟩ , _ ⟩ ⟩
    with rL W w (all→𝕍s (u ∷ U) (collect (subst-tm σ M) 𝕍 (u ∷ U) (λ d' d'∈ → adequate M G (V⊆ d' d'∈)) ⟨ sM , w ⟩))
... | ⟨ V , ⟨ ⟨ sN , v ⟩ , r ⟩ ⟩ =
  ⟨ V , ⟨ ⟨ star-in (app-l _) sL ◅◅ star-in (app-r lam) sM ◅◅ (val-in (value-red w) ◅ sN) , v ⟩ , r ⟩ ⟩
adequate (lit B c) {d = dconst k} G ⟨ refl , refl ⟩ = ⟨ lit B c , ⟨ ⟨ ε , lit ⟩ , refl ⟩ ⟩
adequate (tuple []) {d = ⟨⟩} G tt = ⟨ tuple [] , ⟨ ⟨ ε , tuple [] ⟩ , tt ⟩ ⟩
adequate (tuple (M ∷ Ms)) {d = tup[ i ] u} G ⟨ refl , ⟨ u∈ , ne ⟩ ⟩ with adequate-args (M ∷ Ms) G ne
... | ⟨ Vs , ⟨ ⟨ ss , vs ⟩ , rs ⟩ ⟩ = ⟨ tuple Vs , ⟨ ⟨ star-in (fr tuple (λ _ → refl)) ss , tuple vs ⟩ , rs i u u∈ ⟩ ⟩
adequate (get i M) G d∈ with adequate M G d∈
... | ⟨ tuple Vs , ⟨ ⟨ s , tuple vs ⟩ , r ⟩ ⟩ =
  ⟨ lookup Vs i , ⟨ ⟨ star-in (fr (get i) (λ _ → refl)) s ◅◅ (val-in (value-red (tuple vs)) ◅ ε) , each-lookup vs i ⟩
                  , 𝕍At-lookup i _ Vs r ⟩ ⟩
adequate (inl M) {d = left u} G u∈ with adequate M G u∈
... | ⟨ V , ⟨ ⟨ s , v ⟩ , r ⟩ ⟩ = ⟨ inl V , ⟨ ⟨ star-in (fr inl (λ _ → refl)) s , inl v ⟩ , r ⟩ ⟩
adequate (inr M) {d = right u} G u∈ with adequate M G u∈
... | ⟨ V , ⟨ ⟨ s , v ⟩ , r ⟩ ⟩ = ⟨ inr V , ⟨ ⟨ star-in (fr inr (λ _ → refl)) s , inr v ⟩ , r ⟩ ⟩
adequate (case L M N) {σ = σ} G (inj₁ ⟨ u , ⟨ U , ⟨ allL , ⟨ w∈ , _ ⟩ ⟩ ⟩ ⟩) with adequate L G (allL u (here refl))
... | ⟨ _ , ⟨ ⟨ _ , inr _ ⟩ , () ⟩ ⟩
... | ⟨ inl W , ⟨ ⟨ sL , inl w ⟩ , _ ⟩ ⟩
    with adequate M (𝔾-ext (u ∷ U) G w (all→𝕍s (u ∷ U)
           (collect (subst-tm σ L) (λ d V → 𝕍 (left d) V) (u ∷ U) (λ d d∈ → adequate L G (allL d d∈)) ⟨ sL , inl w ⟩))) w∈
... | ⟨ V , ⟨ ⟨ sM , v ⟩ , r ⟩ ⟩ =
  ⟨ V , ⟨ ⟨ star-in (fr (λ L' → case L' _ _) (λ _ → refl)) sL ◅◅ (val-in (value-red (inl w)) ◅ body σ W M sM) , v ⟩ , r ⟩ ⟩
adequate (case L M N) {σ = σ} G (inj₂ ⟨ u , ⟨ U , ⟨ allR , ⟨ w∈ , _ ⟩ ⟩ ⟩ ⟩) with adequate L G (allR u (here refl))
... | ⟨ _ , ⟨ ⟨ _ , inl _ ⟩ , () ⟩ ⟩
... | ⟨ inr W , ⟨ ⟨ sL , inr w ⟩ , _ ⟩ ⟩
    with adequate N (𝔾-ext (u ∷ U) G w (all→𝕍s (u ∷ U)
           (collect (subst-tm σ L) (λ d V → 𝕍 (right d) V) (u ∷ U) (λ d d∈ → adequate L G (allR d d∈)) ⟨ sL , inr w ⟩))) w∈
... | ⟨ V , ⟨ ⟨ sN , v ⟩ , r ⟩ ⟩ =
  ⟨ V , ⟨ ⟨ star-in (fr (λ L' → case L' _ _) (λ _ → refl)) sL ◅◅ (val-in (value-red (inr w)) ◅ body σ W N sN) , v ⟩ , r ⟩ ⟩
adequate (prim p L M) G ⟨ n , ⟨ m , ⟨ n∈ , ⟨ m∈ , refl ⟩ ⟩ ⟩ ⟩
    with adequate L G n∈ | adequate M G m∈
... | ⟨ _ , ⟨ ⟨ sL , lit ⟩ , refl ⟩ ⟩ | ⟨ _ , ⟨ ⟨ sM , lit ⟩ , refl ⟩ ⟩ =
  ⟨ out p n m , ⟨ ⟨ star-in (fr (λ L' → prim p L' _) (λ _ → refl)) sL ◅◅ star-in (fr (prim p (lit Int n)) (λ _ → refl)) sM ◅◅ (refl ◅ ε) , out-val p n m ⟩
              , 𝕍-out p n m ⟩ ⟩
adequate (let′ M N) G ⟨ [] , ⟨ _ , ⟨ _ , ne ⟩ ⟩ ⟩ = ⊥-elim (ne refl)
adequate (let′ M N) {σ = σ} G ⟨ u ∷ U , ⟨ ⟨ w∈ , _ ⟩ , ⟨ V⊆ , _ ⟩ ⟩ ⟩
    with adequate M G (V⊆ u (here refl))
... | ⟨ W , ⟨ ⟨ sM , w ⟩ , _ ⟩ ⟩
    with adequate N (𝔾-ext (u ∷ U) G w (all→𝕍s (u ∷ U)
           (collect (subst-tm σ M) 𝕍 (u ∷ U) (λ d d∈ → adequate M G (V⊆ d d∈)) ⟨ sM , w ⟩))) w∈
... | ⟨ V , ⟨ ⟨ sN , v ⟩ , r ⟩ ⟩ =
  ⟨ V , ⟨ ⟨ star-in (fr (λ M' → let′ M' _) (λ _ → refl)) sM ◅◅ (val-in (value-red w) ◅ body σ W N sN) , v ⟩ , r ⟩ ⟩
adequate (fold M) G d∈ with adequate M G d∈
... | ⟨ V , ⟨ ⟨ s , v ⟩ , r ⟩ ⟩ = ⟨ fold V , ⟨ ⟨ star-in (fr fold (λ _ → refl)) s , fold v ⟩ , r ⟩ ⟩
adequate (unfold M) G d∈ with adequate M G d∈
... | ⟨ fold V , ⟨ ⟨ s , fold v ⟩ , r ⟩ ⟩ =
  ⟨ V , ⟨ ⟨ star-in (fr unfold (λ _ → refl)) s ◅◅ (val-in (value-red (fold v)) ◅ ε) , v ⟩ , r ⟩ ⟩

adequate-args [] G ne = ⟨ [] , ⟨ ⟨ ε , [] ⟩ , (λ ()) ⟩ ⟩
adequate-args (M ∷ Ms) {σ = σ} G ne with adequate M G (proj₂ (ne zero)) | adequate-args Ms G (λ j → ne (suc j))
... | ⟨ V , ⟨ ⟨ s , v ⟩ , _ ⟩ ⟩ | ⟨ Vs , ⟨ ⟨ ss , vs ⟩ , rs ⟩ ⟩ =
  ⟨ V ∷ Vs , ⟨ ⟨ star-in (fr (_∷ _) (λ _ → refl)) s ◅◅ star-in (fr (V ∷_) (λ _ → val-in (value-red v))) ss , v ∷ vs ⟩ , R ⟩ ⟩
  where
  R : ∀ j d → d ∈ nthD (⟦ M ∷ Ms ⟧s _) j → 𝕍At j d (V ∷ Vs)
  R zero d d∈ = ⟨ refl , collect (subst-tm σ M) 𝕍 (d ∷ []) (λ { d' (here refl) → adequate M G d∈ }) ⟨ s , v ⟩ d (here refl) ⟩
  R (suc j) d d∈ = rs j d d∈

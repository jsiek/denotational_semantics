{-

  The values of the Clos5μ machine (Mu/Semantics/CEK/Clos5.agda) in the
  graph model, for the adequacy proof of the X86μ machine, which shares
  them (Mu/proof/Adequacy/X86.agda), as Clos5Values.agda is for the
  typed pipeline:

  * Rel Run: the logical relation 𝕍 d v, by recursion on the
    denotational value d (and on the folds of v), given what it means
    to run definition f on an environment and an argument (Run), and a
    table related to the code pointers (𝕋, tab);
  * Den T: the denotation 𝒱 v of a value, a code pointer denoting its
    entry of the table T;
  * levels and inversions of the operators whose elements have one shape.

  A fold is the identity on denotations: 𝕍 d (fold v) is 𝕍 d v and
  𝒱 (fold v) is 𝒱 v. There is no project, so no tags.

-}

module Mu.proof.Adequacy.Clos5Values where

open import Framework.Primitives using (Base; base-rep; Int)
open import Language.Prim using (Prim; sub; eq; δ; int; bool)
open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.Domain
  using (Value; _↦_; ν; ω; ⦅_,_⦆; tup[_]_; left; right; ⟨⟩; _•_; Con) renaming (const to dconst)
open import proof.Framework.GraphModel.Ops
  using (ℬ; 𝒯; nthD; Λ; ℬ-consis; pair-consis; inl-consis; inr-consis) renaming (pair to dpair; inl to inlD; inr to inrD)
open import proof.Semantics.Graph.Prim using (primD) renaming (out to dout)
open import Mu.Language.Type
open import Mu.Language.Clos5 using (DSig; sig)
open import Mu.proof.Semantics.Graph.Ops using (Table; tables; ConT; init)
open import Mu.Semantics.CEK.Clos5
open import Mu.Framework.AllUtil using (All; []; _∷_; lookup; pos)
open import Semantics.Observation using (Obs; o-const; Answer)
open import Mu.proof.Adequacy.Tuples using (At; AllNE; 𝒯L; AllCon; 𝒯L-con)
import proof.Framework.GraphModel.Env as E

open import Data.Bool using (true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin; zero; suc)
open import Data.Integer using () renaming (_≟_ to _≟ℤ_)
open import Data.List using (List; []; _∷_; length)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (ℕ; zero; suc; _≟_; _<_)
open import Data.Nat.Properties using (<-irrefl; ≤-refl; m<n⇒m<1+n)
open import Data.Product using (_×_; Σ-syntax; ∃-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Level using (lift; lower)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (yes; no; does)

{- Levels ----------------------------------------------------------------------}

lvl< : ∀ {A : Set} {Γ : List A} {a} (x : Γ ∋ a) → lvl x < length Γ
lvl< Z = ≤-refl
lvl< (S x) = m<n⇒m<1+n (lvl< x)

{- an index is determined by its level -}
lvl-inj : ∀ {Γ : List DSig} {m n} (f : Γ ∋ m) (g : Γ ∋ n) → lvl f ≡ lvl g → _≡_ {A = ∃[ k ] Γ ∋ k} ⟨ m , f ⟩ ⟨ n , g ⟩
lvl-inj Z Z e = refl
lvl-inj Z (S g) e = ⊥-elim (<-irrefl (sym e) (lvl< g))
lvl-inj (S f) Z e = ⊥-elim (<-irrefl e (lvl< f))
lvl-inj (S f) (S g) e with lvl-inj f g e
... | refl = refl

{- Inversions ------------------------------------------------------------------------}

ℬ-inv : ∀ {B} {k : base-rep B} d → d ∈ ℬ B k ptt → d ≡ dconst k
ℬ-inv (dconst k) ⟨ refl , refl ⟩ = refl
ℬ-inv (V ↦ w) ()
ℬ-inv ν ()
ℬ-inv ω ()
ℬ-inv ⦅ u , v ⦆ ()
ℬ-inv (tup[ i ] d) ()
ℬ-inv (left d) ()
ℬ-inv (right d) ()
ℬ-inv ⟨⟩ ()

pair-inv : ∀ {D E} d → d ∈ dpair ⟨ D , ⟨ E , ptt ⟩ ⟩ → Σ[ u ∈ Value ] Σ[ u' ∈ Value ] d ≡ ⦅ u , u' ⦆ × u ∈ D × u' ∈ E
pair-inv ⦅ u , u' ⦆ ⟨ u∈ , u'∈ ⟩ = ⟨ u , ⟨ u' , ⟨ refl , ⟨ u∈ , u'∈ ⟩ ⟩ ⟩ ⟩
pair-inv (dconst k) ()
pair-inv (V ↦ w) ()
pair-inv ν ()
pair-inv ω ()
pair-inv (tup[ i ] d) ()
pair-inv (left d) ()
pair-inv (right d) ()
pair-inv ⟨⟩ ()

inl-inv : ∀ {D} d → d ∈ inlD ⟨ D , ptt ⟩ → Σ[ u ∈ Value ] d ≡ left u × u ∈ D
inl-inv (left u) u∈ = ⟨ u , ⟨ refl , u∈ ⟩ ⟩
inl-inv (dconst k) ()
inl-inv (V ↦ w) ()
inl-inv ν ()
inl-inv ω ()
inl-inv ⦅ u , v ⦆ ()
inl-inv (tup[ i ] d) ()
inl-inv (right d) ()
inl-inv ⟨⟩ ()

inr-inv : ∀ {D} d → d ∈ inrD ⟨ D , ptt ⟩ → Σ[ u ∈ Value ] d ≡ right u × u ∈ D
inr-inv (right u) u∈ = ⟨ u , ⟨ refl , u∈ ⟩ ⟩
inr-inv (dconst k) ()
inr-inv (V ↦ w) ()
inr-inv ν ()
inr-inv ω ()
inr-inv ⦅ u , v ⦆ ()
inr-inv (tup[ i ] d) ()
inr-inv (left d) ()
inr-inv ⟨⟩ ()

{- an element of a tuple of n components -}
𝒯-inv : ∀ n {Ds} d → d ∈ 𝒯 n Ds
  → (n ≡ 0 × d ≡ ⟨⟩) ⊎ Σ[ m ∈ ℕ ] Σ[ i ∈ Fin (suc m) ] Σ[ u ∈ Value ] Σ[ e ∈ n ≡ suc m ]
       d ≡ tup[ i ] u × u ∈ nthD Ds (subst Fin (sym e) i) × (∀ j → nonempty (nthD Ds j))
𝒯-inv zero ⟨⟩ _ = inj₁ ⟨ refl , refl ⟩
𝒯-inv (suc n) (tup[ i ] u) ⟨ refl , ⟨ u∈ , ne ⟩ ⟩ = inj₂ ⟨ n , ⟨ i , ⟨ u , ⟨ refl , ⟨ refl , ⟨ u∈ , ne ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
𝒯-inv zero (tup[ i ] u) ()
𝒯-inv (suc n) ⟨⟩ ()
𝒯-inv zero (dconst k) ()
𝒯-inv (suc n) (dconst k) ()
𝒯-inv zero (V ↦ w) ()
𝒯-inv (suc n) (V ↦ w) ()
𝒯-inv zero ν ()
𝒯-inv (suc n) ν ()
𝒯-inv zero ω ()
𝒯-inv (suc n) ω ()
𝒯-inv zero ⦅ u , v ⦆ ()
𝒯-inv (suc n) ⦅ u , v ⦆ ()
𝒯-inv zero (left d) ()
𝒯-inv (suc n) (left d) ()
𝒯-inv zero (right d) ()
𝒯-inv (suc n) (right d) ()

𝒯L[]-inv : ∀ d → d ∈ 𝒯L [] → d ≡ ⟨⟩
𝒯L[]-inv ⟨⟩ _ = refl
𝒯L[]-inv (tup[ zero ] d) ⟨ () , _ ⟩
𝒯L[]-inv (tup[ suc i ] d) ⟨ () , _ ⟩
𝒯L[]-inv (dconst k) ()
𝒯L[]-inv (V ↦ w) ()
𝒯L[]-inv ν ()
𝒯L[]-inv ω ()
𝒯L[]-inv ⦅ u , v ⦆ ()
𝒯L[]-inv (left d) ()
𝒯L[]-inv (right d) ()

{- The logical relation, given what running definition f on e and a to a
   value with P means ---------------------------------------------------------------}

module Rel {Σ : List DSig}
  (Run : ∀ {Δ A B} → Σ ∋ sig Δ A B → Val Σ (tup Δ) → Val Σ A → (Val Σ B → Set) → Set) where

  𝕍 : ∀ {A} → Value → Val Σ A → Set
  𝕍s : ∀ {A} → List Value → Val Σ A → Set
  𝕍At : ∀ {n Δ} → Fin n → Value → All (Val Σ) Δ → Set

  𝕍 d (fold v) = 𝕍 d v
  𝕍 (dconst k) (const k') = dconst k ≡ dconst k'
  𝕍 ν (code f) = ⊤
  𝕍 (X ↦ ν) (code f) = ⊤
  𝕍 (X ↦ (Y ↦ w)) (code f) = ∀ e → 𝕍s X e → ∀ a → 𝕍s Y a → Run f e a (𝕍 w)
  𝕍 ⦅ u , u' ⦆ (pack c e) = 𝕍 u c × 𝕍 u' e
  𝕍 ⟨⟩ (tup []) = ⊤
  𝕍 (tup[ i ] d) (tup ws) = 𝕍At i d ws
  𝕍 (left d) (inl v) = 𝕍 d v
  𝕍 (right d) (inr v) = 𝕍 d v
  𝕍 _ _ = ⊥

  𝕍s [] v = ⊤
  𝕍s (d ∷ V) v = 𝕍 d v × 𝕍s V v

  𝕍At {suc n} zero d (_∷_ {xs = Δ} v vs) = length Δ ≡ n × 𝕍 d v
  𝕍At (suc i) d (v ∷ vs) = 𝕍At i d vs
  𝕍At _ d [] = ⊥

  𝕍s-∈ : ∀ {A} V {v : Val Σ A} {d} → 𝕍s V v → d ∈ mem V → 𝕍 d v
  𝕍s-∈ (d ∷ V) ⟨ r , _ ⟩ (here refl) = r
  𝕍s-∈ (d ∷ V) ⟨ _ , rs ⟩ (there d∈) = 𝕍s-∈ V rs d∈

  all→𝕍s : ∀ {A} V {v : Val Σ A} → (∀ d → d ∈ mem V → 𝕍 d v) → 𝕍s V v
  all→𝕍s [] all = tt
  all→𝕍s (d ∷ V) all = ⟨ all d (here refl) , all→𝕍s V (λ d' d'∈ → all d' (there d'∈)) ⟩

  𝕍At-lookup : ∀ {Δ A} (i : Δ ∋ A) d (ws : All (Val Σ) Δ) → 𝕍At (pos i) d ws → 𝕍 d (lookup ws i)
  𝕍At-lookup Z d (w ∷ ws) ⟨ _ , r ⟩ = r
  𝕍At-lookup (S i) d (w ∷ ws) r = 𝕍At-lookup i d ws r

  {- primitives -}
  𝕍-δ : ∀ p n m → 𝕍 (dout (δ p n m)) (δᵀ {Σ} p n m)
  𝕍-δ sub n m = refl
  𝕍-δ eq n m with does (n ≟ℤ m)
  ... | true = tt
  ... | false = tt

  {- the observation of a value related to a constant is that constant -}
  𝕍-const : ∀ {A B} {k : base-rep B} (v : Val Σ A) → 𝕍 (dconst k) v → obs v ≡ o-const B k
  𝕍-const (fold v) r = 𝕍-const v r
  𝕍-const (const k) refl = refl
  𝕍-const (code f) ()
  𝕍-const (pack c e) ()
  𝕍-const (tup ws) ()
  𝕍-const (inl v) ()
  𝕍-const (inr v) ()

  obs-answer : ∀ {A} (v : Val Σ A) → Answer (obs v)
  obs-answer (fold v) = obs-answer v
  obs-answer (code f) ()
  obs-answer (pack c e) ()
  obs-answer (const k) ()
  obs-answer (tup ws) ()
  obs-answer (inl v) ()
  obs-answer (inr v) ()

  {- related environments -}
  𝔾 : ∀ {Γ} → E.Env Value → Env Σ Γ → Set
  𝔾 {Γ} ρ γ = ∀ {A} (x : Γ ∋ A) d → d ∈ ρ (idx x) → 𝕍 d (lookup γ x)

  {- The table ------------------------------------------------------------------------}

  𝕋 : Table Σ → Set
  𝕋 T = ∀ {Δ A B} (f : Σ ∋ sig Δ A B) d → d ∈ T f → 𝕍 d (code f)

  {- code is related to a function of two parameters that runs as definition f does -}
  code-𝕍 : ∀ {Δ A B} {f : Σ ∋ sig Δ A B} (F : 𝒫 Value → 𝒫 Value → 𝒫 Value)
    → (∀ X Y w → w ∈ F (mem X) (mem Y) → ∀ e → 𝕍s X e → ∀ a → 𝕍s Y a → Run f e a (𝕍 w))
    → ∀ d → d ∈ Λ ⟨ (λ X → Λ ⟨ F X , ptt ⟩) , ptt ⟩ → 𝕍 d (code f)
  code-𝕍 F h ν _ = tt
  code-𝕍 F h (X ↦ ν) _ = tt
  code-𝕍 F h (X ↦ (Y ↦ w)) ⟨ ⟨ w∈ , _ ⟩ , _ ⟩ = h X Y w w∈
  code-𝕍 F h (X ↦ dconst k) ()
  code-𝕍 F h (X ↦ ω) ()
  code-𝕍 F h (X ↦ ⦅ u , v ⦆) ()
  code-𝕍 F h (X ↦ (tup[ i ] d)) ()
  code-𝕍 F h (X ↦ left d) ()
  code-𝕍 F h (X ↦ right d) ()
  code-𝕍 F h (X ↦ ⟨⟩) ()
  code-𝕍 F h (dconst k) ()
  code-𝕍 F h ω ()
  code-𝕍 F h ⦅ u , v ⦆ ()
  code-𝕍 F h (tup[ i ] d) ()
  code-𝕍 F h (left d) ()
  code-𝕍 F h (right d) ()
  code-𝕍 F h ⟨⟩ ()

  {- the table of definitions ds whose code is related to its code pointer,
     given a related table -}
  module _ {D : DSig → Set} (cd : Table Σ → ∀ {s} → D s → 𝒫 Value) (ds : All D Σ)
    (rel : ∀ {T : Table Σ} → 𝕋 T → ∀ {Δ A B} (f : Σ ∋ sig Δ A B) d → d ∈ cd T (lookup ds f) → 𝕍 d (code f)) where

    {- a part ps of the table, reached through r -}
    tab′ : ∀ {ss} (ps : All D ss) (r : ∀ {s} → ss ∋ s → Σ ∋ s) → (∀ {s} (g : ss ∋ s) → lvl (r g) ≡ lvl g)
      → (∀ {s} (g : ss ∋ s) → lookup ds (r g) ≡ lookup ps g) → 𝕋 (tables cd ps)
    tab′ [] r rl L f d ()
    tab′ {_ ∷ ss} (N ∷ ps) r rl L f d d∈ with lvl f ≟ length ss
    ... | no _ = tab′ ps (λ x → r (S x)) (λ x → rl (S x)) (λ x → L (S x)) f d d∈
    ... | yes l with lvl-inj f (r Z) (trans l (sym (rl Z)))
    ...   | refl = rel (tab′ ps (λ x → r (S x)) (λ x → rl (S x)) (λ x → L (S x))) (r Z) d
                     (subst (λ N → d ∈ cd _ N) (sym (L Z)) d∈)

    tab : 𝕋 (tables cd ds)
    tab = tab′ ds (λ x → x) (λ _ → refl) (λ _ → refl)

{- The denotations of values, in a table T whose entries are consistent
   functions -----------------------------------------------------------------------}

module Den {Σ : List DSig} (T : Table Σ) (cT : ConT T) (T-ν : ∀ {s} (f : Σ ∋ s) → ν ∈ T f) where

  𝒱 : ∀ {A} → Val Σ A → 𝒫 Value
  𝒱v : ∀ {Δ} → All (Val Σ) Δ → List (𝒫 Value)
  𝒱 (code f) = T f
  𝒱 (pack c e) = dpair ⟨ 𝒱 c , ⟨ 𝒱 e , ptt ⟩ ⟩
  𝒱 (const {B} k) = ℬ B k ptt
  𝒱 (tup ws) = 𝒯L (𝒱v ws)
  𝒱 (inl v) = inlD ⟨ 𝒱 v , ptt ⟩
  𝒱 (inr v) = inrD ⟨ 𝒱 v , ptt ⟩
  𝒱 (fold v) = 𝒱 v
  𝒱v [] = []
  𝒱v (w ∷ ws) = 𝒱 w ∷ 𝒱v ws

  len𝒱v : ∀ {Δ} (ws : All (Val Σ) Δ) → length (𝒱v ws) ≡ length Δ
  len𝒱v [] = refl
  len𝒱v (w ∷ ws) = cong suc (len𝒱v ws)

  𝒱-ne : ∀ {A} (v : Val Σ A) → nonempty (𝒱 v)
  𝒱v-ne : ∀ {Δ} (ws : All (Val Σ) Δ) → AllNE (𝒱v ws)
  𝒱-ne (code f) = ⟨ ν , T-ν f ⟩
  𝒱-ne (pack c e) with 𝒱-ne c | 𝒱-ne e
  ... | ⟨ a , a∈ ⟩ | ⟨ b , b∈ ⟩ = ⟨ ⦅ a , b ⦆ , ⟨ a∈ , b∈ ⟩ ⟩
  𝒱-ne (const k) = ⟨ dconst k , ⟨ refl , refl ⟩ ⟩
  𝒱-ne (tup []) = ⟨ ⟨⟩ , tt ⟩
  𝒱-ne (tup (w ∷ ws)) with 𝒱-ne w
  ... | ⟨ d , d∈ ⟩ = ⟨ tup[ zero ] d , ⟨ ⟨ len𝒱v ws , d∈ ⟩ , ⟨ ⟨ d , d∈ ⟩ , 𝒱v-ne ws ⟩ ⟩ ⟩
  𝒱-ne (inl v) = let ⟨ d , d∈ ⟩ = 𝒱-ne v in ⟨ left d , d∈ ⟩
  𝒱-ne (inr v) = let ⟨ d , d∈ ⟩ = 𝒱-ne v in ⟨ right d , d∈ ⟩
  𝒱-ne (fold v) = 𝒱-ne v
  𝒱v-ne [] = tt
  𝒱v-ne (w ∷ ws) = ⟨ 𝒱-ne w , 𝒱v-ne ws ⟩

  𝒱-con : ∀ {A} (v : Val Σ A) → Con (𝒱 v)
  𝒱v-con : ∀ {Δ} (ws : All (Val Σ) Δ) → AllCon (𝒱v ws)
  𝒱-con (code f) = cT f
  𝒱-con (pack c e) = lower (pair-consis _ _ ⟨ lift (𝒱-con c) , ⟨ lift (𝒱-con e) , ptt ⟩ ⟩)
  𝒱-con (const {B} k) = lower (ℬ-consis B k ptt ptt ptt)
  𝒱-con (tup ws) = 𝒯L-con (𝒱v ws) (𝒱v-con ws)
  𝒱-con (inl v) = lower (inl-consis _ _ ⟨ lift (𝒱-con v) , ptt ⟩)
  𝒱-con (inr v) = lower (inr-consis _ _ ⟨ lift (𝒱-con v) , ptt ⟩)
  𝒱-con (fold v) = 𝒱-con v
  𝒱v-con [] = tt
  𝒱v-con (w ∷ ws) = ⟨ 𝒱-con w , 𝒱v-con ws ⟩

  At-lookup : ∀ {Δ A} (i : Δ ∋ A) (ws : All (Val Σ) Δ) {d} → d ∈ 𝒱 (lookup ws i) → At (pos i) (𝒱v ws) d
  At-lookup Z (w ∷ ws) d∈ = ⟨ len𝒱v ws , d∈ ⟩
  At-lookup (S i) (w ∷ ws) d∈ = At-lookup i ws d∈

  {- environments -}
  𝓔 : ∀ {Γ} → Env Σ Γ → E.Env Value
  𝓔 [] = λ _ → init
  𝓔 (v ∷ γ) = 𝒱 v • 𝓔 γ

  𝓔-ne : ∀ {Γ} (γ : Env Σ Γ) → E.nonempty-env (𝓔 γ)
  𝓔-ne [] x = ⟨ ω , refl ⟩
  𝓔-ne (v ∷ γ) zero = 𝒱-ne v
  𝓔-ne (v ∷ γ) (suc x) = 𝓔-ne γ x

  𝓔-lookup : ∀ {Γ A} (γ : Env Σ Γ) (x : Γ ∋ A) → 𝒱 (lookup γ x) ⊆ 𝓔 γ (idx x)
  𝓔-lookup (v ∷ γ) Z = λ d z → z
  𝓔-lookup (v ∷ γ) (S x) = 𝓔-lookup γ x

  {- primitives -}
  prim-⊆ : ∀ p n m → 𝒱 (δᵀ {Σ} p n m) ⊆ primD p ⟨ ℬ Int n ptt , ⟨ ℬ Int m ptt , ptt ⟩ ⟩
  prim-⊆ p n m d d∈ = ⟨ n , ⟨ m , ⟨ ⟨ refl , refl ⟩ , ⟨ ⟨ refl , refl ⟩ , out-≡ p d d∈ ⟩ ⟩ ⟩ ⟩
    where
    out-≡ : ∀ p d → d ∈ 𝒱 (δᵀ {Σ} p n m) → d ≡ dout (δ p n m)
    out-≡ sub d d∈ = ℬ-inv d d∈
    out-≡ eq d d∈ with does (n ≟ℤ m)
    ... | true with inl-inv d d∈
    ...   | ⟨ u , ⟨ refl , u∈ ⟩ ⟩ = cong left (𝒯L[]-inv u u∈)
    out-≡ eq d d∈ | false with inr-inv d d∈
    ...   | ⟨ u , ⟨ refl , u∈ ⟩ ⟩ = cong right (𝒯L[]-inv u u∈)

  {- the denotation of a value observed as a constant holds it -}
  𝒱-const : ∀ {A B} {k : base-rep B} (v : Val Σ A) → obs v ≡ o-const B k → dconst k ∈ 𝒱 v
  𝒱-const (fold v) e = 𝒱-const v e
  𝒱-const (const k) refl = ⟨ refl , refl ⟩
  𝒱-const (code f) ()
  𝒱-const (pack c e) ()
  𝒱-const (tup ws) ()
  𝒱-const (inl v) ()
  𝒱-const (inr v) ()

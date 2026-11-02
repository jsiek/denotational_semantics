{-

  Soundness of the clocked interpreter of FPC
  (Mu/Semantics/ClockedInterpreters/FPC.agda) with respect to the graph model
  (Mu/Semantics/GraphModel/FPC.agda): what the interpreter returns, at any
  clock, denotes a part of the denotation of the program; and it never
  errs.

  As the soundness of the FPC machine (Mu/proof/Adequacy/AbstractMachines/Soundness.agda),
  through denotations of values (𝒱; a closure denotes its λ in the
  denotation of its environment, 𝓔), but by induction on the clock and
  the term instead of over the steps of a machine: no continuations.
  Sound r D holds of a result r when r is a value whose denotation is
  part of D, or a timeout (and never of an error), and it is carried
  through the binds of the interpreter (bind-holds). A call (and let,
  and case) uses the continuity of the semantics (fin₁) and that every
  value denotes a nonempty, consistent set, as the machine's β steps do.

-}

module Mu.proof.Adequacy.Soundness where

open import Framework.Primitives using (Int)
open import Language.Prim using (Prim; sub; eq) renaming (δ to δᴾ)
open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.Domain hiding (ρ₀) renaming (const to dconst)
open import Mu.Semantics.GraphModel.Closed using (ρ₀)
open import proof.Framework.GraphModel.Ops
  using (⋆; ℬ; 𝒯; nthD; 𝒞; Λ; proj; Λ-consis; ℬ-consis; inl-consis; inr-consis)
  renaming (inl to inlD; inr to inrD)
open import proof.Framework.GraphModel.Continuity using (⋆-good; inl-good; inr-good)
open import proof.Framework.GraphModel.ContinuityBase using (Good; mono)
open import proof.Framework.GraphModel.DenotProperties using (Every)
open import proof.Framework.GraphModel.TypedOkBase using (fin₁)
import proof.Framework.GraphModel.Env as E
open import proof.Semantics.Graph.Prim using (primD; primD-good) renaming (out to dout)
open import proof.Semantics.Interp.Clock using (Result; timeout; error; ret; _>>=_)
open import Mu.proof.Adequacy.Tuples using (At; AllNE; 𝒯L; AllCon; 𝒯L-con; _⊆L_; 𝒯L-mono; At-length)
open import Mu.Language.Type
open import Mu.Language.FPC
open import Mu.proof.Semantics.GraphModel.FPC using (⟦_⟧; ⟦_⟧s; ok)
open import Mu.Framework.AllUtil using (All; []; _∷_; lookup; pos)
open import Mu.Semantics.ClockedInterpreters.FPC
open import Semantics.Observation using (o-const)

open import Data.Bool using (true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (zero; suc)
import Data.Nat as N
open import Data.Integer using () renaming (_≟_ to _≟ℤ_)
open import Data.List using (List; []; _∷_; length)
open import Data.Product using (_×_; Σ-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Level using (lift; lower)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (does)

{- monotonicity of an operator in its operands -}
private
  m1 : ∀ {g} → Good ⊤ (■ ∷ []) g → ∀ {D E} → D ⊆ E → g ⟨ D , ptt ⟩ ⊆ g ⟨ E , ptt ⟩
  m1 G D⊆ = lower (mono G _ _ ⟨ lift D⊆ , ptt ⟩)
  m2 : ∀ {g} → Good ⊤ (■ ∷ ■ ∷ []) g → ∀ {D D' E E'} → D ⊆ D' → E ⊆ E'
    → g ⟨ D , ⟨ E , ptt ⟩ ⟩ ⊆ g ⟨ D' , ⟨ E' , ptt ⟩ ⟩
  m2 G D⊆ E⊆ = lower (mono G _ _ ⟨ lift D⊆ , ⟨ lift E⊆ , ptt ⟩ ⟩)
  ⊆r : ∀ {D : 𝒫 Value} → D ⊆ D
  ⊆r _ z = z
  _⨾_ : ∀ {D E F : 𝒫 Value} → D ⊆ E → E ⊆ F → D ⊆ F
  (D⊆ ⨾ E⊆) d d∈ = E⊆ d (D⊆ d d∈)

{- Denotations of values and environments ---------------------------------------}

𝒱 : ∀ {A} → Val A → 𝒫 Value
𝒱s : ∀ {Δ} → All Val Δ → List (𝒫 Value)
𝓔 : ∀ {Γ} → Env Γ → E.Env Value

{- no FPC program has a value of a code type -}
𝒱 (code N) = ⌈ ⟨⟩ ⌉
𝒱 (pack (code N) (tup γ)) = Λ ⟨ (λ X → ⟦ N ⟧ (X • 𝓔 γ)) , ptt ⟩
𝒱 (const {B} k) = ℬ B k ptt
𝒱 (tup vs) = 𝒯L (𝒱s vs)
𝒱 (inl v) = inlD ⟨ 𝒱 v , ptt ⟩
𝒱 (inr v) = inrD ⟨ 𝒱 v , ptt ⟩
𝒱 (fold v) = 𝒱 v

𝒱s [] = []
𝒱s (v ∷ vs) = 𝒱 v ∷ 𝒱s vs

𝓔 [] = ρ₀
𝓔 (v ∷ γ) = 𝒱 v • 𝓔 γ

⟦_⟧* : ∀ {Γ Δ} → All (Tm Γ) Δ → E.Env Value → List (𝒫 Value)
⟦ [] ⟧* ρ = []
⟦ M ∷ Ms ⟧* ρ = ⟦ M ⟧ ρ ∷ ⟦ Ms ⟧* ρ

{- Values denote nonempty, consistent sets ------------------------------------}

len𝒱s : ∀ {Δ} (vs : All Val Δ) → length (𝒱s vs) ≡ length Δ
len𝒱s [] = refl
len𝒱s (v ∷ vs) = cong N.suc (len𝒱s vs)

𝒱-ne : ∀ {A} (v : Val A) → nonempty (𝒱 v)
𝒱s-ne : ∀ {Δ} (vs : All Val Δ) → AllNE (𝒱s vs)
𝒱-ne (code N) = ⟨ ⟨⟩ , refl ⟩
𝒱-ne (pack (code N) (tup γ)) = ⟨ ν , tt ⟩
𝒱-ne (const k) = ⟨ dconst k , ⟨ refl , refl ⟩ ⟩
𝒱-ne (tup []) = ⟨ ⟨⟩ , tt ⟩
𝒱-ne (tup (v ∷ vs)) with 𝒱-ne v
... | ⟨ d , d∈ ⟩ = ⟨ tup[ zero ] d , ⟨ ⟨ len𝒱s vs , d∈ ⟩ , ⟨ ⟨ d , d∈ ⟩ , 𝒱s-ne vs ⟩ ⟩ ⟩
𝒱-ne (inl v) = let ⟨ d , d∈ ⟩ = 𝒱-ne v in ⟨ left d , d∈ ⟩
𝒱-ne (inr v) = let ⟨ d , d∈ ⟩ = 𝒱-ne v in ⟨ right d , d∈ ⟩
𝒱-ne (fold v) = 𝒱-ne v
𝒱s-ne [] = tt
𝒱s-ne (v ∷ vs) = ⟨ 𝒱-ne v , 𝒱s-ne vs ⟩

𝓔-ne : ∀ {Γ} (γ : Env Γ) → E.nonempty-env (𝓔 γ)
𝓔-ne [] x = ⟨ ⟨⟩ , refl ⟩
𝓔-ne (v ∷ γ) zero = 𝒱-ne v
𝓔-ne (v ∷ γ) (suc x) = 𝓔-ne γ x

𝒱-con : ∀ {A} (v : Val A) → Con (𝒱 v)
𝒱s-con : ∀ {Δ} (vs : All Val Δ) → AllCon (𝒱s vs)
𝓔-con : ∀ {Γ} (γ : Env Γ) → Con-env (𝓔 γ)
𝒱-con (code N) = Con-⌈⌉ ⟨⟩
𝒱-con (pack (code N) (tup γ)) =
  lower (Λ-consis _ _ ⟨ (λ X X' X~ → lift (proj₂ (proj₂ (ok N)) (E.•-~ (Every _~_) (𝓔-con γ) X~))) , ptt ⟩)
𝒱-con (const {B} k) = lower (ℬ-consis B k ptt ptt ptt)
𝒱-con (tup vs) = 𝒯L-con (𝒱s vs) (𝒱s-con vs)
𝒱-con (inl v) = lower (inl-consis _ _ ⟨ lift (𝒱-con v) , ptt ⟩)
𝒱-con (inr v) = lower (inr-consis _ _ ⟨ lift (𝒱-con v) , ptt ⟩)
𝒱-con (fold v) = 𝒱-con v
𝒱s-con [] = tt
𝒱s-con (v ∷ vs) = ⟨ 𝒱-con v , 𝒱s-con vs ⟩
𝓔-con [] x = Con-⌈⌉ ⟨⟩
𝓔-con (v ∷ γ) zero = 𝒱-con v
𝓔-con (v ∷ γ) (suc x) = 𝓔-con γ x

𝓔-lookup : ∀ {Γ A} (γ : Env Γ) (x : Γ ∋ A) → 𝒱 (lookup γ x) ⊆ 𝓔 γ (idx x)
𝓔-lookup (v ∷ γ) Z = ⊆r
𝓔-lookup (v ∷ γ) (S x) = 𝓔-lookup γ x

{- the denotation of a value observed as a constant holds it -}
𝒱-const : ∀ {A B} {k} (v : Val A) → obs v ≡ o-const B k → dconst k ∈ 𝒱 v
𝒱-const (const k) refl = ⟨ refl , refl ⟩
𝒱-const (fold v) e = 𝒱-const v e
𝒱-const (code N) ()
𝒱-const (pack c e) ()
𝒱-const (tup vs) ()
𝒱-const (inl v) ()
𝒱-const (inr v) ()

{- Tuples and primitives --------------------------------------------------------}

𝒯L-args : ∀ {Γ Δ} (Ms : All (Tm Γ) Δ) ρ → 𝒯L (⟦ Ms ⟧* ρ) ⊆ 𝒯 (length Δ) (⟦ Ms ⟧s ρ)
𝒯L-args [] ρ ⟨⟩ tt = tt
𝒯L-args [] ρ (tup[ zero ] d) ⟨ () , _ ⟩
𝒯L-args [] ρ (tup[ suc i ] d) ⟨ () , _ ⟩
𝒯L-args (M ∷ Ms) ρ ⟨⟩ ()
𝒯L-args {Γ} (M ∷ Ms) ρ (tup[_]_ {m} i d) ⟨ a , ne ⟩ with trans (sym (At-length i _ d a)) (len (M ∷ Ms))
  where
  len : ∀ {Δ} (Ns : All (Tm Γ) Δ) → length (⟦ Ns ⟧* ρ) ≡ length Δ
  len [] = refl
  len (N ∷ Ns) = cong N.suc (len Ns)
... | refl = ⟨ refl , ⟨ at (M ∷ Ms) i a , all (M ∷ Ms) ne ⟩ ⟩
  where
  at : ∀ {Δ} (Ns : All (Tm Γ) Δ) (i : Fin (length Δ)) → At i (⟦ Ns ⟧* ρ) d → d ∈ nthD (⟦ Ns ⟧s ρ) i
  at (N ∷ Ns) zero ⟨ _ , d∈ ⟩ = d∈
  at (N ∷ Ns) (suc i) a = at Ns i a
  all : ∀ {Δ} (Ns : All (Tm Γ) Δ) → AllNE (⟦ Ns ⟧* ρ) → ∀ i → nonempty (nthD (⟦ Ns ⟧s ρ) i)
  all (N ∷ Ns) ⟨ ne , _ ⟩ zero = ne
  all (N ∷ Ns) ⟨ _ , nes ⟩ (suc i) = all Ns nes i
𝒯L-args Ms ρ (dconst k) ()
𝒯L-args Ms ρ (V ↦ w) ()
𝒯L-args Ms ρ ν ()
𝒯L-args Ms ρ ω ()
𝒯L-args Ms ρ ⦅ u , v ⦆ ()
𝒯L-args Ms ρ (left d) ()
𝒯L-args Ms ρ (right d) ()

At-lookup : ∀ {Δ A} (vs : All Val Δ) (i : Δ ∋ A) {d} → d ∈ 𝒱 (lookup vs i) → At (pos i) (𝒱s vs) d
At-lookup (v ∷ vs) Z d∈ = ⟨ len𝒱s vs , d∈ ⟩
At-lookup (v ∷ vs) (S i) d∈ = At-lookup vs i d∈

prim-⊆ : ∀ p n m → 𝒱 (δ p (const n) (const m)) ⊆ primD p ⟨ ℬ Int n ptt , ⟨ ℬ Int m ptt , ptt ⟩ ⟩
prim-⊆ p n m d d∈ = ⟨ n , ⟨ m , ⟨ ⟨ refl , refl ⟩ , ⟨ ⟨ refl , refl ⟩ , out-≡ p d d∈ ⟩ ⟩ ⟩ ⟩
  where
  out-≡ : ∀ p d → d ∈ 𝒱 (δ p (const n) (const m)) → d ≡ dout (δᴾ p n m)
  out-≡ sub (dconst k) ⟨ refl , refl ⟩ = refl
  out-≡ eq d d∈ with does (n ≟ℤ m)
  out-≡ eq (left ⟨⟩) d∈ | true = refl
  out-≡ eq (left (tup[ zero ] u)) ⟨ () , _ ⟩ | true
  out-≡ eq (left (tup[ suc i ] u)) ⟨ () , _ ⟩ | true
  out-≡ eq (right ⟨⟩) d∈ | false = refl
  out-≡ eq (right (tup[ zero ] u)) ⟨ () , _ ⟩ | false
  out-≡ eq (right (tup[ suc i ] u)) ⟨ () , _ ⟩ | false

{- β: a body, run on a value, uses a finite part of its denotation -}
app-β : ∀ {Γ A B} (N : Tm (A ∷ Γ) B) (γ : Env Γ) (w : Val A)
  → ⟦ N ⟧ (𝓔 (w ∷ γ)) ⊆ ⋆ ⟨ Λ ⟨ (λ X → ⟦ N ⟧ (X • 𝓔 γ)) , ptt ⟩ , ⟨ 𝒱 w , ptt ⟩ ⟩
app-β N γ w d d∈ with fin₁ (ok N) (𝓔-ne γ) (𝒱-ne w) d d∈
... | ⟨ V , ⟨ ne , ⟨ V⊆ , d∈′ ⟩ ⟩ ⟩ = ⟨ V , ⟨ ⟨ d∈′ , ⟨ ne , Con⇒≈ V (𝒱-con w) V⊆ ⟩ ⟩ , ⟨ V⊆ , ne ⟩ ⟩ ⟩

case-inl : ∀ {Γ A B C} (L : Tm Γ (A ⊹ B)) (M : Tm (A ∷ Γ) C) N (γ : Env Γ) (v : Val A)
  → 𝒱 (inl {B = B} v) ⊆ ⟦ L ⟧ (𝓔 γ) → ⟦ M ⟧ (𝓔 (v ∷ γ)) ⊆ ⟦ case L M N ⟧ (𝓔 γ)
case-inl L M N γ v L⊆ d d∈ with fin₁ (ok M) (𝓔-ne γ) (𝒱-ne v) d d∈
... | ⟨ [] , ⟨ ne , _ ⟩ ⟩ = ⊥-elim (ne refl)
... | ⟨ u ∷ U , ⟨ _ , ⟨ V⊆ , d∈′ ⟩ ⟩ ⟩ =
  inj₁ ⟨ u , ⟨ U , ⟨ (λ d' d'∈ → L⊆ _ (V⊆ d' d'∈)) , ⟨ d∈′ , Con⇒≈ (u ∷ U) (𝒱-con v) V⊆ ⟩ ⟩ ⟩ ⟩

case-inr : ∀ {Γ A B C} (L : Tm Γ (A ⊹ B)) M (N : Tm (B ∷ Γ) C) (γ : Env Γ) (v : Val B)
  → 𝒱 (inr {A = A} v) ⊆ ⟦ L ⟧ (𝓔 γ) → ⟦ N ⟧ (𝓔 (v ∷ γ)) ⊆ ⟦ case L M N ⟧ (𝓔 γ)
case-inr L M N γ v L⊆ d d∈ with fin₁ (ok N) (𝓔-ne γ) (𝒱-ne v) d d∈
... | ⟨ [] , ⟨ ne , _ ⟩ ⟩ = ⊥-elim (ne refl)
... | ⟨ u ∷ U , ⟨ _ , ⟨ V⊆ , d∈′ ⟩ ⟩ ⟩ =
  inj₂ ⟨ u , ⟨ U , ⟨ (λ d' d'∈ → L⊆ _ (V⊆ d' d'∈)) , ⟨ d∈′ , Con⇒≈ (u ∷ U) (𝒱-con v) V⊆ ⟩ ⟩ ⟩ ⟩

{- Results that hold ------------------------------------------------------------}

{- a value with P, or a timeout; never an error -}
data Holds {X : Set} (P : X → Set) : Result X → Set where
  timeout : Holds P timeout
  ret : ∀ {v} → P v → Holds P (ret v)

bind-holds : ∀ {X Y : Set} {P : X → Set} {Q : Y → Set} {r : Result X} {f : X → Result Y}
  → Holds P r → (∀ v → P v → Holds Q (f v)) → Holds Q (r >>= f)
bind-holds timeout k = timeout
bind-holds (ret {v} h) k = k v h

holds-map : ∀ {X : Set} {P Q : X → Set} {r : Result X} → (∀ v → P v → Q v) → Holds P r → Holds Q r
holds-map f timeout = timeout
holds-map f (ret {v} h) = ret (f v h)

Sound : ∀ {A} → Result (Val A) → 𝒫 Value → Set
Sound r D = Holds (λ v → 𝒱 v ⊆ D) r

sound-⊆ : ∀ {A} {r : Result (Val A)} {D E} → D ⊆ E → Sound r D → Sound r E
sound-⊆ D⊆ = holds-map (λ v v⊆ → v⊆ ⨾ D⊆)

{- Soundness ------------------------------------------------------------------}

sound : ∀ {Γ A} ck (γ : Env Γ) (M : Tm Γ A) → Sound (eval ck γ M) (⟦ M ⟧ (𝓔 γ))
sounds : ∀ {Γ Δ} ck (γ : Env Γ) (Ms : All (Tm Γ) Δ) → Holds (λ vs → 𝒱s vs ⊆L ⟦ Ms ⟧* (𝓔 γ)) (evals ck γ Ms)
sound-call : ∀ {A B} ck (f : Val (A ⇒ B)) (w : Val A) → Sound (call ck f w) (⋆ ⟨ 𝒱 f , ⟨ 𝒱 w , ptt ⟩ ⟩)

sound ck γ (` x) = ret (𝓔-lookup γ x)
sound ck γ (lam N) = ret ⊆r
sound ck γ (app L M) =
  bind-holds (sound ck γ L) λ f L⊆ → bind-holds (sound ck γ M) λ w M⊆ → sound-⊆ (m2 ⋆-good L⊆ M⊆) (sound-call ck f w)
sound ck γ (lit B c) = ret ⊆r
sound ck γ (tuple Ms) =
  bind-holds (sounds ck γ Ms) λ vs s → ret (𝒯L-mono _ _ s ⨾ 𝒯L-args Ms (𝓔 γ))
sound ck γ (get i M) =
  bind-holds (sound ck γ M) λ { (tup vs) M⊆ → ret λ d d∈ → M⊆ _ ⟨ At-lookup vs i d∈ , 𝒱s-ne vs ⟩ }
sound ck γ (inl M) = bind-holds (sound ck γ M) λ v M⊆ → ret (m1 inl-good M⊆)
sound ck γ (inr M) = bind-holds (sound ck γ M) λ v M⊆ → ret (m1 inr-good M⊆)
sound ck γ (case L M N) = bind-holds (sound ck γ L) λ
  { (inl v) L⊆ → sound-⊆ (case-inl L M N γ v L⊆) (sound ck (v ∷ γ) M)
  ; (inr v) L⊆ → sound-⊆ (case-inr L M N γ v L⊆) (sound ck (v ∷ γ) N) }
sound ck γ (prim p L M) = bind-holds (sound ck γ L) λ
  { (const n) L⊆ → bind-holds (sound ck γ M) λ
    { (const m) M⊆ → ret (prim-⊆ p n m ⨾ m2 (primD-good p) L⊆ M⊆) } }
sound ck γ (let′ M N) = bind-holds (sound ck γ M) λ v M⊆ →
  sound-⊆ (app-β N γ v ⨾ m2 ⋆-good (⊆r {D = Λ ⟨ (λ X → ⟦ N ⟧ (X • 𝓔 γ)) , ptt ⟩}) M⊆) (sound ck (v ∷ γ) N)
sound ck γ (fold M) = bind-holds (sound ck γ M) λ v M⊆ → ret M⊆
sound ck γ (unfold M) = bind-holds (sound ck γ M) λ { (fold v) M⊆ → ret M⊆ }

sounds ck γ [] = ret tt
sounds ck γ (M ∷ Ms) =
  bind-holds (sound ck γ M) λ v M⊆ → bind-holds (sounds ck γ Ms) λ vs s → ret ⟨ M⊆ , s ⟩

sound-call zero f w = timeout
sound-call (suc ck) (pack (code N) (tup γ)) w = sound-⊆ (app-β N γ w) (sound ck (w ∷ γ) N)

{-

  Soundness of the ISWIMμ machine (Mu/Semantics/CEK/ISWIM.agda) with
  respect to the graph model (Mu/Semantics/Graph/ISWIM.agda): what the
  machine computes is in the denotation of the program.

  As for ISWIM (proof/Adequacy/Soundness.agda): each machine state
  denotes a set of values (𝒮), through denotations of machine values
  (𝒱; a closure denotes its λ in the denotation of its environment, 𝓔),
  and of continuations, the contexts their frames stand for (𝒦); every
  step can only shrink it (step-⊆). The β steps (application, case,
  let) use the continuity of the semantics (fin₁, from
  Mu/proof/Semantics/Graph/ISWIM.agda) and that every value denotes a
  nonempty, consistent set. fold v denotes 𝒱 v, and foldK and unfoldK
  are the identity, as fold and unfold are in the semantics. The
  machine is typed, so no step is stuck, and the only final state
  returns a value to halt.

-}

module Mu.proof.Adequacy.CEK.Soundness where

open import Framework.Primitives using (Int)
open import Language.Prim using (Prim; sub; eq; δ)
open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.Domain hiding (ρ₀) renaming (const to dconst)
open import Mu.Semantics.Graph.Closed using (ρ₀)
open import proof.Framework.GraphModel.Ops
  using (⋆; ℬ; 𝒯; nthD; 𝒞; Λ; proj; Λ-consis; ℬ-consis; inl-consis; inr-consis)
  renaming (inl to inlD; inr to inrD)
open import proof.Framework.GraphModel.Continuity using (⋆-good; proj-good; inl-good; inr-good)
open import proof.Framework.GraphModel.ContinuityBase using (Good; mono)
open import proof.Framework.GraphModel.DenotProperties using (Every)
open import proof.Framework.GraphModel.TypedOkBase using (fin₁)
import proof.Framework.GraphModel.Env as E
open import proof.Semantics.Graph.Prim using (primD; primD-good) renaming (out to dout)
open import proof.Framework.Runs using (module Runs)
open import Mu.proof.Adequacy.Tuples using (At; AllNE; 𝒯L; AllCon; 𝒯L-con; _⊆L_; ⊆L-refl; 𝒯L-mono; At-length)
open import Mu.Language.Type
open import Mu.Language.ISWIM
open import Mu.proof.Semantics.Graph.ISWIM using (⟦_⟧; ⟦_⟧s; ok; con)
open import Mu.Framework.AllUtil using (All; []; _∷_; lookup; pos; _<><_; _<><ᵃ_)
open import Mu.Semantics.CEK.ISWIM
open import Semantics.Observation using (Obs; o-const)
open import Semantics.CEK.Smallstep using (Star; Terminates; next; stop)

open import Data.Bool using (true; false)
open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (zero; suc)
import Data.Nat as N
open import Data.Integer using (ℤ) renaming (_≟_ to _≟ℤ_)
open import Data.List using (List; []; _∷_; length; replicate)
open import Data.Product using (_×_; Σ-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Level using (lift; lower)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (does)

open Runs step public

{- monotonicity of an operator in its operands -}
private
  m1 : ∀ {g} → Good ⊤ (■ ∷ []) g → ∀ {D E} → D ⊆ E → g ⟨ D , ptt ⟩ ⊆ g ⟨ E , ptt ⟩
  m1 G D⊆ = lower (mono G _ _ ⟨ lift D⊆ , ptt ⟩)
  m2l : ∀ {g} → Good ⊤ (■ ∷ ■ ∷ []) g → ∀ X {D E} → D ⊆ E → g ⟨ D , ⟨ X , ptt ⟩ ⟩ ⊆ g ⟨ E , ⟨ X , ptt ⟩ ⟩
  m2l G X D⊆ = lower (mono G _ _ ⟨ lift D⊆ , ⟨ lift (λ _ z → z) , ptt ⟩ ⟩)
  m2r : ∀ {g} → Good ⊤ (■ ∷ ■ ∷ []) g → ∀ X {D E} → D ⊆ E → g ⟨ X , ⟨ D , ptt ⟩ ⟩ ⊆ g ⟨ X , ⟨ E , ptt ⟩ ⟩
  m2r G X D⊆ = lower (mono G _ _ ⟨ lift (λ _ z → z) , ⟨ lift D⊆ , ptt ⟩ ⟩)
  ⊆r : ∀ {D : 𝒫 Value} → D ⊆ D
  ⊆r _ z = z

{- Denotations of values, environments, continuations and states ------------}

𝒱 : ∀ {A} → Val A → 𝒫 Value
𝒱s : ∀ {Δ} → All Val Δ → List (𝒫 Value)
𝓔 : ∀ {Γ} → Env Γ → E.Env Value

{- no ISWIMμ program has a value of a code type -}
𝒱 (code N) = ⌈ ⟨⟩ ⌉
𝒱 (clo N γ) = Λ ⟨ (λ X → ⟦ N ⟧ (X • 𝓔 γ)) , ptt ⟩
𝒱 (const {B} k) = ℬ B k ptt
𝒱 (tup vs) = 𝒯L (𝒱s vs)
𝒱 (inl v) = inlD ⟨ 𝒱 v , ptt ⟩
𝒱 (inr v) = inrD ⟨ 𝒱 v , ptt ⟩
𝒱 (fold v) = 𝒱 v

𝒱s [] = []
𝒱s (v ∷ vs) = 𝒱 v ∷ 𝒱s vs

𝓔 [] = ρ₀
𝓔 (v ∷ γ) = 𝒱 v • 𝓔 γ

{- the values so far of a tuple (newest first), in front of the rest -}
rev𝒱 : ∀ {Δ'} → All Val Δ' → List (𝒫 Value) → List (𝒫 Value)
rev𝒱 [] Ds = Ds
rev𝒱 (v ∷ vs) Ds = rev𝒱 vs (𝒱 v ∷ Ds)

⟦_⟧* : ∀ {Γ Δ} → All (Tm Γ) Δ → E.Env Value → List (𝒫 Value)
⟦ [] ⟧* ρ = []
⟦ M ∷ Ms ⟧* ρ = ⟦ M ⟧ ρ ∷ ⟦ Ms ⟧* ρ

𝒦 : ∀ {A} → Cont A → 𝒫 Value → 𝒫 Value
𝒦 halt D = D
𝒦 (appL M γ κ) D = 𝒦 κ (⋆ ⟨ D , ⟨ ⟦ M ⟧ (𝓔 γ) , ptt ⟩ ⟩)
𝒦 (appR f κ) D = 𝒦 κ (⋆ ⟨ 𝒱 f , ⟨ D , ptt ⟩ ⟩)
𝒦 (tupK vs Ms γ κ) D = 𝒦 κ (𝒯L (rev𝒱 vs (D ∷ ⟦ Ms ⟧* (𝓔 γ))))
𝒦 (getK i κ) D = 𝒦 κ (proj (pos i) ⟨ D , ptt ⟩)
𝒦 (inlK κ) D = 𝒦 κ (inlD ⟨ D , ptt ⟩)
𝒦 (inrK κ) D = 𝒦 κ (inrD ⟨ D , ptt ⟩)
𝒦 (caseK M N γ κ) D = 𝒦 κ (𝒞 ⟨ D , ⟨ (λ X → ⟦ M ⟧ (X • 𝓔 γ)) , ⟨ (λ X → ⟦ N ⟧ (X • 𝓔 γ)) , ptt ⟩ ⟩ ⟩)
𝒦 (primL p M γ κ) D = 𝒦 κ (primD p ⟨ D , ⟨ ⟦ M ⟧ (𝓔 γ) , ptt ⟩ ⟩)
𝒦 (primR p n κ) D = 𝒦 κ (primD p ⟨ ℬ Int n ptt , ⟨ D , ptt ⟩ ⟩)
𝒦 (letK N γ κ) D = 𝒦 κ (⋆ ⟨ Λ ⟨ (λ X → ⟦ N ⟧ (X • 𝓔 γ)) , ptt ⟩ , ⟨ D , ptt ⟩ ⟩)
𝒦 (foldK κ) D = 𝒦 κ D
𝒦 (unfoldK κ) D = 𝒦 κ D

𝒮 : State → 𝒫 Value
𝒮 (eval M γ κ) = 𝒦 κ (⟦ M ⟧ (𝓔 γ))
𝒮 (ret v κ) = 𝒦 κ (𝒱 v)

𝒦-mono : ∀ {A} (κ : Cont A) {D E} → D ⊆ E → 𝒦 κ D ⊆ 𝒦 κ E
𝒦-mono halt D⊆ = D⊆
𝒦-mono (appL M γ κ) D⊆ = 𝒦-mono κ (m2l ⋆-good (⟦ M ⟧ (𝓔 γ)) D⊆)
𝒦-mono (appR f κ) D⊆ = 𝒦-mono κ (m2r ⋆-good (𝒱 f) D⊆)
𝒦-mono (tupK vs Ms γ κ) D⊆ = 𝒦-mono κ (𝒯L-mono _ _ (rev-mono vs ⟨ D⊆ , ⊆L-refl _ ⟩))
  where
  rev-mono : ∀ {Δ'} (vs : All Val Δ') {Ds Es} → Ds ⊆L Es → rev𝒱 vs Ds ⊆L rev𝒱 vs Es
  rev-mono [] s = s
  rev-mono (v ∷ vs) s = rev-mono vs ⟨ ⊆r , s ⟩
𝒦-mono (getK i κ) D⊆ = 𝒦-mono κ (m1 (proj-good (pos i)) D⊆)
𝒦-mono (inlK κ) D⊆ = 𝒦-mono κ (m1 inl-good D⊆)
𝒦-mono (inrK κ) D⊆ = 𝒦-mono κ (m1 inr-good D⊆)
𝒦-mono (caseK M N γ κ) D⊆ = 𝒦-mono κ G
  where
  G : _ ⊆ _
  G w (inj₁ ⟨ u , ⟨ U , ⟨ allL , w∈ ⟩ ⟩ ⟩) = inj₁ ⟨ u , ⟨ U , ⟨ (λ d d∈ → D⊆ _ (allL d d∈)) , w∈ ⟩ ⟩ ⟩
  G w (inj₂ ⟨ u , ⟨ U , ⟨ allR , w∈ ⟩ ⟩ ⟩) = inj₂ ⟨ u , ⟨ U , ⟨ (λ d d∈ → D⊆ _ (allR d d∈)) , w∈ ⟩ ⟩ ⟩
𝒦-mono (primL p M γ κ) D⊆ = 𝒦-mono κ (m2l (primD-good p) (⟦ M ⟧ (𝓔 γ)) D⊆)
𝒦-mono (primR p n κ) D⊆ = 𝒦-mono κ (m2r (primD-good p) (ℬ Int n ptt) D⊆)
𝒦-mono (letK N γ κ) D⊆ = 𝒦-mono κ (m2r ⋆-good (Λ ⟨ (λ X → ⟦ N ⟧ (X • 𝓔 γ)) , ptt ⟩) D⊆)
𝒦-mono (foldK κ) D⊆ = 𝒦-mono κ D⊆
𝒦-mono (unfoldK κ) D⊆ = 𝒦-mono κ D⊆

{- Values denote nonempty, consistent sets ------------------------------------}

len𝒱s : ∀ {Δ} (vs : All Val Δ) → length (𝒱s vs) ≡ length Δ
len𝒱s [] = refl
len𝒱s (v ∷ vs) = cong N.suc (len𝒱s vs)

𝒱-ne : ∀ {A} (v : Val A) → nonempty (𝒱 v)
𝒱s-ne : ∀ {Δ} (vs : All Val Δ) → AllNE (𝒱s vs)
𝒱-ne (code N) = ⟨ ⟨⟩ , refl ⟩
𝒱-ne (clo N γ) = ⟨ ν , tt ⟩
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
𝒱-con (clo N γ) = lower (Λ-consis _ _ ⟨ (λ X X' X~ → lift (proj₂ (proj₂ (ok N)) (E.•-~ (Every _~_) (𝓔-con γ) X~))) , ptt ⟩)
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
𝒱-const (clo N γ) ()
𝒱-const (tup vs) ()
𝒱-const (inl v) ()
𝒱-const (inr v) ()

{- Tuples and primitives --------------------------------------------------------}

𝒱s-<>< : ∀ {Δ' Δ} (vs : All Val Δ') (ws : All Val Δ) → 𝒱s (vs <><ᵃ ws) ≡ rev𝒱 vs (𝒱s ws)
𝒱s-<>< [] ws = refl
𝒱s-<>< (v ∷ vs) ws = 𝒱s-<>< vs (v ∷ ws)

tuple-next-𝒮 : ∀ {Γ Δ' Δ} (vs : All Val Δ') (Ms : All (Tm Γ) Δ) (γ : Env Γ) κ
  → 𝒮 (tuple-next vs Ms γ κ) ⊆ 𝒦 κ (𝒯L (rev𝒱 vs (⟦ Ms ⟧* (𝓔 γ))))
tuple-next-𝒮 vs [] γ κ d d∈ = subst (λ Ds → 𝒦 κ (𝒯L Ds) d) (𝒱s-<>< vs []) d∈
tuple-next-𝒮 vs (M ∷ Ms) γ κ d d∈ = d∈

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

prim-⊆ : ∀ p n m → 𝒱 (δᵀ p n m) ⊆ primD p ⟨ ℬ Int n ptt , ⟨ ℬ Int m ptt , ptt ⟩ ⟩
prim-⊆ p n m d d∈ = ⟨ n , ⟨ m , ⟨ ⟨ refl , refl ⟩ , ⟨ ⟨ refl , refl ⟩ , out-≡ p d d∈ ⟩ ⟩ ⟩ ⟩
  where
  out-≡ : ∀ p d → d ∈ 𝒱 (δᵀ p n m) → d ≡ dout (δ p n m)
  out-≡ sub (dconst k) ⟨ refl , refl ⟩ = refl
  out-≡ eq d d∈ with does (n ≟ℤ m)
  out-≡ eq (left ⟨⟩) d∈ | true = refl
  out-≡ eq (left (tup[ zero ] u)) ⟨ () , _ ⟩ | true
  out-≡ eq (left (tup[ suc i ] u)) ⟨ () , _ ⟩ | true
  out-≡ eq (right ⟨⟩) d∈ | false = refl
  out-≡ eq (right (tup[ zero ] u)) ⟨ () , _ ⟩ | false
  out-≡ eq (right (tup[ suc i ] u)) ⟨ () , _ ⟩ | false

{- Steps shrink the denotation of the state --------------------------------}

{- a body, run on a value, uses a finite part of its denotation -}
body-in : ∀ {Γ A B} (N : Tm (A ∷ Γ) B) (γ : Env Γ) (v : Val A) d → d ∈ ⟦ N ⟧ (𝓔 (v ∷ γ))
  → Σ[ V ∈ List Value ] V ≢ [] × mem V ⊆ 𝒱 v × d ∈ ⟦ N ⟧ (mem V • 𝓔 γ)
body-in N γ v d d∈ = fin₁ (ok N) (𝓔-ne γ) (𝒱-ne v) d d∈

app-β : ∀ {Γ A B} (N : Tm (A ∷ Γ) B) (γ : Env Γ) (w : Val A)
  → ⟦ N ⟧ (𝓔 (w ∷ γ)) ⊆ ⋆ ⟨ Λ ⟨ (λ X → ⟦ N ⟧ (X • 𝓔 γ)) , ptt ⟩ , ⟨ 𝒱 w , ptt ⟩ ⟩
app-β N γ w d d∈ with body-in N γ w d d∈
... | ⟨ V , ⟨ ne , ⟨ V⊆ , d∈′ ⟩ ⟩ ⟩ = ⟨ V , ⟨ ⟨ d∈′ , ⟨ ne , Con⇒≈ V (𝒱-con w) V⊆ ⟩ ⟩ , ⟨ V⊆ , ne ⟩ ⟩ ⟩

step-⊆ : ∀ s {s'} → step s ≡ next s' → 𝒮 s' ⊆ 𝒮 s
step-⊆ (eval (` x) γ κ) refl = 𝒦-mono κ (𝓔-lookup γ x)
step-⊆ (eval (lam N) γ κ) refl = ⊆r
step-⊆ (eval (app L M) γ κ) refl = ⊆r
step-⊆ (eval (lit B c) γ κ) refl = ⊆r
step-⊆ (eval (tuple Ms) γ κ) refl d d∈ = 𝒦-mono κ (𝒯L-args Ms (𝓔 γ)) d (tuple-next-𝒮 [] Ms γ κ d d∈)
step-⊆ (eval (get i M) γ κ) refl = ⊆r
step-⊆ (eval (inl M) γ κ) refl = ⊆r
step-⊆ (eval (inr M) γ κ) refl = ⊆r
step-⊆ (eval (case L M N) γ κ) refl = ⊆r
step-⊆ (eval (prim p L M) γ κ) refl = ⊆r
step-⊆ (eval (let′ M N) γ κ) refl = ⊆r
step-⊆ (eval (fold M) γ κ) refl = ⊆r
step-⊆ (eval (unfold M) γ κ) refl = ⊆r
step-⊆ (ret v halt) ()
step-⊆ (ret f (appL M γ κ)) refl = ⊆r
step-⊆ (ret w (appR (clo N γ) κ)) refl = 𝒦-mono κ (app-β N γ w)
step-⊆ (ret v (tupK vs Ms γ κ)) refl = tuple-next-𝒮 (v ∷ vs) Ms γ κ
step-⊆ (ret (tup vs) (getK i κ)) refl = 𝒦-mono κ λ d d∈ → ⟨ At-lookup vs i d∈ , 𝒱s-ne vs ⟩
step-⊆ (ret v (inlK κ)) refl = ⊆r
step-⊆ (ret v (inrK κ)) refl = ⊆r
step-⊆ (ret (inl v) (caseK M N γ κ)) refl = 𝒦-mono κ β
  where
  β : ⟦ M ⟧ (𝓔 (v ∷ γ)) ⊆ _
  β d d∈ with body-in M γ v d d∈
  ... | ⟨ [] , ⟨ ne , _ ⟩ ⟩ = ⊥-elim (ne refl)
  ... | ⟨ u ∷ U , ⟨ _ , ⟨ V⊆ , d∈′ ⟩ ⟩ ⟩ = inj₁ ⟨ u , ⟨ U , ⟨ V⊆ , ⟨ d∈′ , Con⇒≈ (u ∷ U) (𝒱-con v) V⊆ ⟩ ⟩ ⟩ ⟩
step-⊆ (ret (inr v) (caseK M N γ κ)) refl = 𝒦-mono κ β
  where
  β : ⟦ N ⟧ (𝓔 (v ∷ γ)) ⊆ _
  β d d∈ with body-in N γ v d d∈
  ... | ⟨ [] , ⟨ ne , _ ⟩ ⟩ = ⊥-elim (ne refl)
  ... | ⟨ u ∷ U , ⟨ _ , ⟨ V⊆ , d∈′ ⟩ ⟩ ⟩ = inj₂ ⟨ u , ⟨ U , ⟨ V⊆ , ⟨ d∈′ , Con⇒≈ (u ∷ U) (𝒱-con v) V⊆ ⟩ ⟩ ⟩ ⟩
step-⊆ (ret (const n) (primL p M γ κ)) refl = ⊆r
step-⊆ (ret (const m) (primR p n κ)) refl = 𝒦-mono κ (prim-⊆ p n m)
step-⊆ (ret v (letK N γ κ)) refl = 𝒦-mono κ (app-β N γ v)
step-⊆ (ret v (foldK κ)) refl = ⊆r
step-⊆ (ret (fold v) (unfoldK κ)) refl = ⊆r

↠-⊆ : ∀ {s t} → s ↠ t → 𝒮 t ⊆ 𝒮 s
↠-⊆ done = ⊆r
↠-⊆ {s} (st ∷↠ σ) d d∈ = step-⊆ s st d (↠-⊆ σ d d∈)

{- Soundness ------------------------------------------------------------------}

{- the only final state returns a value to halt -}
halts : ∀ s {o} → step s ≡ stop o → Σ[ A ∈ Type ] Σ[ v ∈ Val A ] s ≡ ret v halt × o ≡ obs v
halts (eval (` x) γ κ) ()
halts (eval (lam N) γ κ) ()
halts (eval (app L M) γ κ) ()
halts (eval (lit B c) γ κ) ()
halts (eval (tuple Ms) γ κ) ()
halts (eval (get i M) γ κ) ()
halts (eval (inl M) γ κ) ()
halts (eval (inr M) γ κ) ()
halts (eval (case L M N) γ κ) ()
halts (eval (prim p L M) γ κ) ()
halts (eval (let′ M N) γ κ) ()
halts (eval (fold M) γ κ) ()
halts (eval (unfold M) γ κ) ()
halts (ret v halt) refl = ⟨ _ , ⟨ v , ⟨ refl , refl ⟩ ⟩ ⟩
halts (ret f (appL M γ κ)) ()
halts (ret w (appR (clo N γ) κ)) ()
halts (ret v (tupK vs Ms γ κ)) ()
halts (ret (tup vs) (getK i κ)) ()
halts (ret v (inlK κ)) ()
halts (ret v (inrK κ)) ()
halts (ret (inl v) (caseK M N γ κ)) ()
halts (ret (inr v) (caseK M N γ κ)) ()
halts (ret (const n) (primL p M γ κ)) ()
halts (ret (const m) (primR p n κ)) ()
halts (ret v (letK N γ κ)) ()
halts (ret v (foldK κ)) ()
halts (ret (fold v) (unfoldK κ)) ()

{- a program that terminates with o returns a value observed as o, which
   denotes a part of the program's denotation -}
soundness : ∀ {A} (M : Tm [] A) {o} → Terminates (sem M) o
  → Σ[ B ∈ Type ] Σ[ v ∈ Val B ] o ≡ obs v × 𝒱 v ⊆ ⟦ M ⟧ ρ₀
soundness M ⟨ s , ⟨ σ , fin ⟩ ⟩ with halts s fin
... | ⟨ B , ⟨ v , ⟨ refl , refl ⟩ ⟩ ⟩ = ⟨ B , ⟨ v , ⟨ refl , ↠-⊆ (star→↠ σ) ⟩ ⟩ ⟩

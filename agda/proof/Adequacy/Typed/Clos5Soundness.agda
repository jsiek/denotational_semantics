{-

  Soundness of the Clos5ᵀ machine with respect to the graph model: what
  the machine computes is in the denotation of the program, for a
  program whose definitions refer only to older ones (OlderDefs,
  proof/Compiler/Typed/GlobalizeOlder.agda).

  As for untyped Clos5 (proof/Adequacy/Clos5Soundness.agda), each state
  denotes a set of values (𝒮) that a step can only shrink (step-⊆).
  Every reference exists, so the states are interpreted with the table
  itself. A call runs definition f with the whole table, while the
  semantics gives it the table of the older ones; since it refers only
  to older ones, the first is part of the second (tbl-mono, agree), and
  its code applied to the environment and argument contains its body
  (ΛΛ-β, by the continuity of the body, fin₂).

-}

open import Data.List using (List; []; _∷_; length)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _<_)
open import Language.Typed.Type renaming (_≟_ to _≟F_)
open import Language.Typed.Clos5
open import proof.Compiler.Typed.GlobalizeOlder using (Older; Olders; OlderDefs)

module proof.Adequacy.Typed.Clos5Soundness {Σ : List ℕ} (ds : All (Code Σ) Σ) (od : OlderDefs ds) where

open import Framework.Primitives using (Base; base-rep; Int)
open import Language.Prim using (Prim; sub; eq; δ; int; bool)
open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.Domain
  using (Value; _↦_; ν; ω; ⦅_,_⦆; tup[_]_; left; right; ⟨⟩; _•_; ■; Con; Con⇒≈)
  renaming (const to dconst)
open import proof.Framework.GraphModel.Ops
  using (⋆; ℬ; 𝒯; nthD; car; cdr; 𝒞; Λ; proj; ⋆₂-mono; ΛΛ-β; ℬ-consis; pair-consis; inl-consis; inr-consis)
  renaming (pair to dpair; inl to inlD; inr to inrD)
open import proof.Framework.GraphModel.Continuity
  using (⋆-good; pair-good; 𝒯-good; proj-good; inl-good; inr-good; 𝒞-good; letD-good)
open import proof.Framework.GraphModel.ContinuityBase using (Good; mono)
open import proof.Framework.GraphModel.Env using (•-~)
import proof.Framework.GraphModel.Env as E
open import proof.Semantics.Graph.Prim using (primD; primD-good) renaming (out to dout)
open import proof.Semantics.Graph.Typed.Ops
  using (Table; tables; ConT; tables-con; accepts; fun₄; projectᵍ; project-good; init; Ok; fin₁; fin₂; callc-good)
open import proof.Semantics.Graph.Typed.Clos5 using (⟦_⟧[_]; ⟦_⟧s[_]; code′; table; ok; code-con; table-con)
open import Semantics.CEK.Typed.Clos5
open import Framework.Lookup using (_!_)
open import proof.Adequacy.Typed.Clos5Common ds
open import proof.Adequacy.Soundness using (At; AllNE; 𝒯L; AllCon; 𝒯L-con; _⊆L_; ⊆L-refl; 𝒯L-mono; At-length)

open import Data.Bool using (true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin; zero; suc)
open import Data.Integer using (ℤ) renaming (_≟_ to _≟ℤ_)
open import Data.List using (reverse)
open import Data.List.Base using (reverseAcc)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_×_; Σ-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Data.Vec using (Vec; []; _∷_; toList; lookup)
open import Level using (Lift; lift; lower)
open import proof.Framework.GraphModel.DOpSig using (results-rel-pres)
open import Data.List using (replicate)
open import Relation.Binary.PropositionalEquality using (_≢_)
open import Semantics.CEK.Smallstep using (Star; machine; next; stop)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (yes; no; does)

{- monotonicity of an operator in its operands -}
private
  m1 : ∀ {g} → Good ⊤ (■ ∷ []) g → ∀ {D E} → D ⊆ E → g ⟨ D , ptt ⟩ ⊆ g ⟨ E , ptt ⟩
  m1 G D⊆ = lower (mono G _ _ ⟨ lift D⊆ , ptt ⟩)
  m2 : ∀ {g} → Good ⊤ (■ ∷ ■ ∷ []) g → ∀ {D D' E E'} → D ⊆ D' → E ⊆ E' → g ⟨ D , ⟨ E , ptt ⟩ ⟩ ⊆ g ⟨ D' , ⟨ E' , ptt ⟩ ⟩
  m2 G D⊆ E⊆ = lower (mono G _ _ ⟨ lift D⊆ , ⟨ lift E⊆ , ptt ⟩ ⟩)
  m2l : ∀ {g} → Good ⊤ (■ ∷ ■ ∷ []) g → ∀ X {D E} → D ⊆ E → g ⟨ D , ⟨ X , ptt ⟩ ⟩ ⊆ g ⟨ E , ⟨ X , ptt ⟩ ⟩
  m2l G X D⊆ = lower (mono G _ _ ⟨ lift D⊆ , ⟨ lift (λ _ z → z) , ptt ⟩ ⟩)
  m2r : ∀ {g} → Good ⊤ (■ ∷ ■ ∷ []) g → ∀ X {D E} → D ⊆ E → g ⟨ X , ⟨ D , ptt ⟩ ⟩ ⊆ g ⟨ X , ⟨ E , ptt ⟩ ⟩
  m2r G X D⊆ = lower (mono G _ _ ⟨ lift (λ _ z → z) , ⟨ lift D⊆ , ptt ⟩ ⟩)
  ⊆r : ∀ {D : 𝒫 Value} → D ⊆ D
  ⊆r _ z = z

{- The semantics in the table depends only on the references a term makes ---------}

tbl-mono : ∀ {Γ A} {T T' : Table Σ} {k} (M : Tm Σ Γ A) → ConT T → Older k M
  → (∀ {m} (g : Σ ∋ m) → lvl g < k → T g ⊆ T' g) → ∀ ρ → ⟦ M ⟧[ T ] ρ ⊆ ⟦ M ⟧[ T' ] ρ
tbl-monos : ∀ {Γ n} {T T' : Table Σ} {k} (Ms : Vec (Tm Σ Γ Any) n) → ConT T → Olders k Ms
  → (∀ {m} (g : Σ ∋ m) → lvl g < k → T g ⊆ T' g) → ∀ ρ
  → results-rel-pres _⊆_ (replicate n ■) (⟦ Ms ⟧s[ T ] ρ) (⟦ Ms ⟧s[ T' ] ρ)
tbl-mono (` x) cT o h ρ = ⊆r
tbl-mono (fun-ref f) cT o h ρ = h f o
tbl-mono (pack L M) cT ⟨ o₁ , o₂ ⟩ h ρ = m2 pair-good (tbl-mono L cT o₁ h ρ) (tbl-mono M cT o₂ h ρ)
tbl-mono (callc L M) cT ⟨ o₁ , o₂ ⟩ h ρ = m2 callc-good (tbl-mono L cT o₁ h ρ) (tbl-mono M cT o₂ h ρ)
tbl-mono (lit B c) cT o h ρ = ⊆r
tbl-mono (tuple {n = n} Ms) cT o h ρ = lower (mono (𝒯-good {⊤} n) _ _ (tbl-monos Ms cT o h ρ))
tbl-mono (get i M) cT o h ρ = m1 (proj-good i) (tbl-mono M cT o h ρ)
tbl-mono (inl M) cT o h ρ = m1 inl-good (tbl-mono M cT o h ρ)
tbl-mono (inr M) cT o h ρ = m1 inr-good (tbl-mono M cT o h ρ)
tbl-mono {T = T} (case L M N) cT ⟨ o₁ , ⟨ o₂ , o₃ ⟩ ⟩ h ρ =
  lower (mono (𝒞-good {⊤}) _ _ ⟨ lift (tbl-mono L cT o₁ h ρ) , ⟨ body M o₂ , ⟨ body N o₃ , ptt ⟩ ⟩ ⟩)
  where
  body : ∀ B → Older _ B → ∀ X X' → X ⊆ X' → Lift _ (⟦ B ⟧[ T ] (X • ρ) ⊆ ⟦ B ⟧[ _ ] (X' • ρ))
  body B oB X X' X⊆ = lift λ d d∈ → tbl-mono B cT oB h (X' • ρ) d (proj₁ (ok cT B) (•-~ _⊆_ (λ _ → ⊆r) X⊆) d d∈)
tbl-mono (prim p L M) cT ⟨ o₁ , o₂ ⟩ h ρ = m2 (primD-good p) (tbl-mono L cT o₁ h ρ) (tbl-mono M cT o₂ h ρ)
tbl-mono {T = T} (let′ M N) cT ⟨ o₁ , o₂ ⟩ h ρ =
  lower (mono (letD-good {⊤}) _ _ ⟨ lift (tbl-mono M cT o₁ h ρ)
    , ⟨ (λ X X' X⊆ → lift λ d d∈ → tbl-mono N cT o₂ h (X' • ρ) d (proj₁ (ok cT N) (•-~ _⊆_ (λ _ → ⊆r) X⊆) d d∈)) , ptt ⟩ ⟩)
tbl-mono (inject G M) cT o h ρ = tbl-mono M cT o h ρ
tbl-mono (project t M) cT o h ρ = m1 (project-good fun₄ t) (tbl-mono M cT o h ρ)
tbl-monos [] cT o h ρ = ptt
tbl-monos (M ∷ Ms) cT ⟨ o , os ⟩ h ρ = ⟨ lift (tbl-mono M cT o h ρ) , tbl-monos Ms cT os h ρ ⟩

olderAt : ∀ {ns n} {ps : All (Code Σ) ns} → OlderDefs ps → (f : ns ∋ n) → Older (length (older f)) (ps ! f)
olderAt {ps = p ∷ ps} ⟨ o , _ ⟩ Z = o
olderAt {ps = p ∷ ps} ⟨ _ , os ⟩ (S f) = olderAt os f

{- Denotations of values, environments, continuations and states ---------------------}

T : Table Σ
T = table ds

cT : ConT T
cT = table-con ds

T-ν : ∀ {n} (f : Σ ∋ n) → ν ∈ T f
T-ν f = subst (ν ∈_) (sym (table-at code′ ds f)) tt

𝒱 : ∀ {A} → Val Σ A → 𝒫 Value
𝒱v : ∀ {n} → Vec (Val Σ Any) n → List (𝒫 Value)
𝒱 (code f) = T f
𝒱 (pack c e) = dpair ⟨ 𝒱 c , ⟨ 𝒱 e , ptt ⟩ ⟩
𝒱 (const {B} k) = ℬ B k ptt
𝒱 (tup ws) = 𝒯L (𝒱v ws)
𝒱 (inl v) = inlD ⟨ 𝒱 v , ptt ⟩
𝒱 (inr v) = inrD ⟨ 𝒱 v , ptt ⟩
𝒱 (dyn G v) = 𝒱 v
𝒱v [] = []
𝒱v (w ∷ ws) = 𝒱 w ∷ 𝒱v ws

𝒱-ne : ∀ {A} (v : Val Σ A) → nonempty (𝒱 v)
𝒱v-ne : ∀ {n} (ws : Vec (Val Σ Any) n) → AllNE (𝒱v ws)
len𝒱v : ∀ {n} (ws : Vec (Val Σ Any) n) → length (𝒱v ws) ≡ n
len𝒱v [] = refl
len𝒱v (w ∷ ws) = cong suc (len𝒱v ws)
𝒱-ne (code f) = ⟨ ν , T-ν f ⟩
𝒱-ne (pack c e) with 𝒱-ne c | 𝒱-ne e
... | ⟨ a , a∈ ⟩ | ⟨ b , b∈ ⟩ = ⟨ ⦅ a , b ⦆ , ⟨ a∈ , b∈ ⟩ ⟩
𝒱-ne (const k) = ⟨ dconst k , ⟨ refl , refl ⟩ ⟩
𝒱-ne (tup []) = ⟨ ⟨⟩ , tt ⟩
𝒱-ne (tup (w ∷ ws)) with 𝒱-ne w
... | ⟨ d , d∈ ⟩ = ⟨ tup[ zero ] d , ⟨ ⟨ len𝒱v ws , d∈ ⟩ , ⟨ ⟨ d , d∈ ⟩ , 𝒱v-ne ws ⟩ ⟩ ⟩
𝒱-ne (inl v) = let ⟨ d , d∈ ⟩ = 𝒱-ne v in ⟨ left d , d∈ ⟩
𝒱-ne (inr v) = let ⟨ d , d∈ ⟩ = 𝒱-ne v in ⟨ right d , d∈ ⟩
𝒱-ne (dyn G v) = 𝒱-ne v
𝒱v-ne [] = tt
𝒱v-ne (w ∷ ws) = ⟨ 𝒱-ne w , 𝒱v-ne ws ⟩

𝒱-con : ∀ {A} (v : Val Σ A) → Con (𝒱 v)
𝒱v-con : ∀ {n} (ws : Vec (Val Σ Any) n) → AllCon (𝒱v ws)
𝒱-con (code f) = cT f
𝒱-con (pack c e) = lower (pair-consis _ _ ⟨ lift (𝒱-con c) , ⟨ lift (𝒱-con e) , ptt ⟩ ⟩)
𝒱-con (const {B} k) = lower (ℬ-consis B k ptt ptt ptt)
𝒱-con (tup ws) = 𝒯L-con (𝒱v ws) (𝒱v-con ws)
𝒱-con (inl v) = lower (inl-consis _ _ ⟨ lift (𝒱-con v) , ptt ⟩)
𝒱-con (inr v) = lower (inr-consis _ _ ⟨ lift (𝒱-con v) , ptt ⟩)
𝒱-con (dyn G v) = 𝒱-con v
𝒱v-con [] = tt
𝒱v-con (w ∷ ws) = ⟨ 𝒱-con w , 𝒱v-con ws ⟩

At-lookup : ∀ {n} (i : Fin n) (ws : Vec (Val Σ Any) n) {d} → d ∈ 𝒱 (lookup ws i) → At i (𝒱v ws) d
At-lookup zero (w ∷ ws) d∈ = ⟨ len𝒱v ws , d∈ ⟩
At-lookup (suc i) (w ∷ ws) d∈ = At-lookup i ws d∈

𝓔 : ∀ {Γ} → Env Σ Γ → E.Env Value
𝓔 [] = λ _ → init
𝓔 (v ∷ γ) = 𝒱 v • 𝓔 γ

𝓔-ne : ∀ {Γ} (γ : Env Σ Γ) → E.nonempty-env (𝓔 γ)
𝓔-ne [] x = ⟨ ω , refl ⟩
𝓔-ne (v ∷ γ) zero = 𝒱-ne v
𝓔-ne (v ∷ γ) (suc x) = 𝓔-ne γ x

𝓔-lookup : ∀ {Γ A} (γ : Env Σ Γ) (x : Γ ∋ A) → 𝒱 (γ ! x) ⊆ 𝓔 γ (idx x)
𝓔-lookup (v ∷ γ) Z = ⊆r
𝓔-lookup (v ∷ γ) (S x) = 𝓔-lookup γ x

⟦_⟧⁺ : ∀ {Γ A} → Tm Σ Γ A → E.Env Value → 𝒫 Value
⟦ M ⟧⁺ = ⟦ M ⟧[ T ]

⟦_⟧* : ∀ {Γ j} → Vec (Tm Σ Γ Any) j → E.Env Value → List (𝒫 Value)
⟦ [] ⟧* ρ = []
⟦ M ∷ Ms ⟧* ρ = ⟦ M ⟧⁺ ρ ∷ ⟦ Ms ⟧* ρ

rev𝒱 : List (Val Σ Any) → List (𝒫 Value) → List (𝒫 Value)
rev𝒱 [] Ds = Ds
rev𝒱 (v ∷ vs) Ds = rev𝒱 vs (𝒱 v ∷ Ds)

𝒦 : ∀ {A} → Cont Σ A → 𝒫 Value → 𝒫 Value
𝒦 halt D = D
𝒦 (callL M γ κ) D = 𝒦 κ (⋆ ⟨ ⋆ ⟨ car ⟨ D , ptt ⟩ , ⟨ cdr ⟨ D , ptt ⟩ , ptt ⟩ ⟩ , ⟨ ⟦ M ⟧⁺ (𝓔 γ) , ptt ⟩ ⟩)
𝒦 (callR f κ) D = 𝒦 κ (⋆ ⟨ ⋆ ⟨ car ⟨ 𝒱 f , ptt ⟩ , ⟨ cdr ⟨ 𝒱 f , ptt ⟩ , ptt ⟩ ⟩ , ⟨ D , ptt ⟩ ⟩)
𝒦 (packL M γ κ) D = 𝒦 κ (dpair ⟨ D , ⟨ ⟦ M ⟧⁺ (𝓔 γ) , ptt ⟩ ⟩)
𝒦 (packR c κ) D = 𝒦 κ (dpair ⟨ 𝒱 c , ⟨ D , ptt ⟩ ⟩)
𝒦 (tupK vs Ms γ e κ) D = 𝒦 κ (𝒯L (rev𝒱 vs (D ∷ ⟦ Ms ⟧* (𝓔 γ))))
𝒦 (getK i κ) D = 𝒦 κ (proj i ⟨ D , ptt ⟩)
𝒦 (inlK κ) D = 𝒦 κ (inlD ⟨ D , ptt ⟩)
𝒦 (inrK κ) D = 𝒦 κ (inrD ⟨ D , ptt ⟩)
𝒦 (caseK M N γ κ) D = 𝒦 κ (𝒞 ⟨ D , ⟨ (λ X → ⟦ M ⟧⁺ (X • 𝓔 γ)) , ⟨ (λ X → ⟦ N ⟧⁺ (X • 𝓔 γ)) , ptt ⟩ ⟩ ⟩)
𝒦 (primL p M γ κ) D = 𝒦 κ (primD p ⟨ D , ⟨ ⟦ M ⟧⁺ (𝓔 γ) , ptt ⟩ ⟩)
𝒦 (primR p n κ) D = 𝒦 κ (primD p ⟨ ℬ Int n ptt , ⟨ D , ptt ⟩ ⟩)
𝒦 (letK N γ κ) D = 𝒦 κ (⋆ ⟨ Λ ⟨ (λ X → ⟦ N ⟧⁺ (X • 𝓔 γ)) , ptt ⟩ , ⟨ D , ptt ⟩ ⟩)
𝒦 (injK G κ) D = 𝒦 κ D
𝒦 (projK t κ) D = 𝒦 κ (projectᵍ fun₄ t D)

𝒮 : State Σ → 𝒫 Value
𝒮 (eval M γ κ) = 𝒦 κ (⟦ M ⟧⁺ (𝓔 γ))
𝒮 (ret v κ) = 𝒦 κ (𝒱 v)

𝒦-mono : ∀ {A} (κ : Cont Σ A) {D E} → D ⊆ E → 𝒦 κ D ⊆ 𝒦 κ E
𝒦-mono halt D⊆ = D⊆
𝒦-mono (callL M γ κ) D⊆ = 𝒦-mono κ (m2l callc-good (⟦ M ⟧⁺ (𝓔 γ)) D⊆)
𝒦-mono (callR f κ) D⊆ = 𝒦-mono κ (m2r callc-good (𝒱 f) D⊆)
𝒦-mono (packL M γ κ) D⊆ = 𝒦-mono κ (m2l pair-good (⟦ M ⟧⁺ (𝓔 γ)) D⊆)
𝒦-mono (packR c κ) D⊆ = 𝒦-mono κ (m2r pair-good (𝒱 c) D⊆)
𝒦-mono (tupK vs Ms γ e κ) {D} {E} D⊆ = 𝒦-mono κ (𝒯L-mono _ _ (rev-mono vs ⟨ D⊆ , ⊆L-refl _ ⟩))
  where
  rev-mono : ∀ vs {Ds Es} → Ds ⊆L Es → rev𝒱 vs Ds ⊆L rev𝒱 vs Es
  rev-mono [] s = s
  rev-mono (v ∷ vs) s = rev-mono vs ⟨ ⊆r , s ⟩
𝒦-mono (getK i κ) D⊆ = 𝒦-mono κ (m1 (proj-good i) D⊆)
𝒦-mono (inlK κ) D⊆ = 𝒦-mono κ (m1 inl-good D⊆)
𝒦-mono (inrK κ) D⊆ = 𝒦-mono κ (m1 inr-good D⊆)
𝒦-mono (caseK M N γ κ) D⊆ = 𝒦-mono κ G
  where
  G : _ ⊆ _
  G w (inj₁ ⟨ u , ⟨ U , ⟨ allL , w∈ ⟩ ⟩ ⟩) = inj₁ ⟨ u , ⟨ U , ⟨ (λ d d∈ → D⊆ _ (allL d d∈)) , w∈ ⟩ ⟩ ⟩
  G w (inj₂ ⟨ u , ⟨ U , ⟨ allR , w∈ ⟩ ⟩ ⟩) = inj₂ ⟨ u , ⟨ U , ⟨ (λ d d∈ → D⊆ _ (allR d d∈)) , w∈ ⟩ ⟩ ⟩
𝒦-mono (primL p M γ κ) D⊆ = 𝒦-mono κ (m2l (primD-good p) (⟦ M ⟧⁺ (𝓔 γ)) D⊆)
𝒦-mono (primR p n κ) D⊆ = 𝒦-mono κ (m2r (primD-good p) (ℬ Int n ptt) D⊆)
𝒦-mono (letK N γ κ) D⊆ = 𝒦-mono κ (m2r ⋆-good (Λ ⟨ (λ X → ⟦ N ⟧⁺ (X • 𝓔 γ)) , ptt ⟩) D⊆)
𝒦-mono (injK G κ) D⊆ = 𝒦-mono κ D⊆
𝒦-mono (projK t κ) D⊆ = 𝒦-mono κ (m1 (project-good fun₄ t) D⊆)

{- Calls ------------------------------------------------------------------------------------}

{- calling definition f on the environment e and the argument a -}
call-⊆ : ∀ {n} (f : Σ ∋ n) (e : Val Σ ⟪ tup n ⟫) (a : Val Σ Any)
  → ⟦ ds ! f ⟧⁺ (𝓔 (a ∷ e ∷ []))
    ⊆ ⋆ ⟨ ⋆ ⟨ car ⟨ 𝒱 (pack (code f) e) , ptt ⟩ , ⟨ cdr ⟨ 𝒱 (pack (code f) e) , ptt ⟩ , ptt ⟩ ⟩ , ⟨ 𝒱 a , ptt ⟩ ⟩
call-⊆ f e a d d∈ =
  lower (⋆₂-mono _ _ ⟨ lift car⊆ , ⟨ lift cdr⊆ , ⟨ lift ⊆r , ptt ⟩ ⟩ ⟩) d
    (subst (λ C → d ∈ ⋆ ⟨ ⋆ ⟨ C , ⟨ 𝒱 e , ptt ⟩ ⟩ , ⟨ 𝒱 a , ptt ⟩ ⟩) (sym (table-at code′ ds f))
      (ΛΛ-β {F = λ X Y → ⟦ ds ! f ⟧[ T' ] (Y • X • λ _ → init)} (𝒱-con e) (𝒱-con a)
         (λ w w∈ → fin₂ (ok cT' (ds ! f)) (𝒱-ne e) (𝒱-ne a) w w∈) d
         (tbl-mono (ds ! f) cT (olderAt od f)
            (λ g g< x x∈ → subst (x ∈_) (agree code′ ds f g g<) x∈) _ d d∈)))
  where
  T' = tables code′ (drop f ds)
  cT' = tables-con code-con (drop f ds)
  car⊆ : T f ⊆ car ⟨ 𝒱 (pack (code f) e) , ptt ⟩
  car⊆ x x∈ = let ⟨ b , b∈ ⟩ = 𝒱-ne e in ⟨ b , ⟨ x∈ , b∈ ⟩ ⟩
  cdr⊆ : 𝒱 e ⊆ cdr ⟨ 𝒱 (pack (code f) e) , ptt ⟩
  cdr⊆ x x∈ = ⟨ ν , ⟨ T-ν f , x∈ ⟩ ⟩

{- one parameter (case, let): the body uses a finite part of the value -}
body-in : ∀ {Γ A B} (N : Tm Σ (A ∷ Γ) B) (γ : Env Σ Γ) (v : Val Σ A) d → d ∈ ⟦ N ⟧⁺ (𝓔 (v ∷ γ))
  → Σ[ V ∈ List Value ] V ≢ [] × mem V ⊆ 𝒱 v × d ∈ ⟦ N ⟧⁺ (mem V • 𝓔 γ)
body-in N γ v d d∈ = fin₁ (ok cT N) (𝓔-ne γ) (𝒱-ne v) d d∈

{- Tuples -------------------------------------------------------------------------------------}

𝒱s : List (Val Σ Any) → List (𝒫 Value)
𝒱s [] = []
𝒱s (v ∷ vs) = 𝒱 v ∷ 𝒱s vs

𝒱v-toList : ∀ {n} (ws : Vec (Val Σ Any) n) → 𝒱v ws ≡ 𝒱s (toList ws)
𝒱v-toList [] = refl
𝒱v-toList (w ∷ ws) = cong (𝒱 w ∷_) (𝒱v-toList ws)

𝒱s-reverseAcc : ∀ acc vs → 𝒱s (reverseAcc acc vs) ≡ rev𝒱 vs (𝒱s acc)
𝒱s-reverseAcc acc [] = refl
𝒱s-reverseAcc acc (v ∷ vs) = 𝒱s-reverseAcc (v ∷ acc) vs

tuple-next-𝒮 : ∀ {Γ n j} vs (Ms : Vec (Tm Σ Γ Any) j) (γ : Env Σ Γ) (e : length vs Data.Nat.+ j ≡ n) κ
  → 𝒮 (tuple-next vs Ms γ e κ) ⊆ 𝒦 κ (𝒯L (rev𝒱 vs (⟦ Ms ⟧* (𝓔 γ))))
tuple-next-𝒮 vs [] γ e κ d d∈ =
  subst (λ Ds → 𝒦 κ (𝒯L Ds) d)
    (trans (𝒱v-toList (collected′ vs e)) (trans (cong 𝒱s (toList-collected vs e)) (𝒱s-reverseAcc [] vs))) d∈
  where open import Framework.VecUtil using () renaming (collected to collected′)
tuple-next-𝒮 vs (M ∷ Ms) γ e κ d d∈ = d∈

𝒯L-args : ∀ {Γ n} (Ms : Vec (Tm Σ Γ Any) n) ρ → 𝒯L (⟦ Ms ⟧* ρ) ⊆ 𝒯 n (⟦ Ms ⟧s[ T ] ρ)
𝒯L-args [] ρ ⟨⟩ tt = tt
𝒯L-args [] ρ (tup[ zero ] d) ⟨ () , _ ⟩
𝒯L-args [] ρ (tup[ suc i ] d) ⟨ () , _ ⟩
𝒯L-args (M ∷ Ms) ρ ⟨⟩ ()
𝒯L-args {Γ} (M ∷ Ms) ρ (tup[_]_ {m} i d) ⟨ a , ne ⟩ with trans (sym (At-length i _ d a)) (len (M ∷ Ms))
  where
  len : ∀ {j} (Ns : Vec (Tm Σ Γ Any) j) → length (⟦ Ns ⟧* ρ) ≡ j
  len [] = refl
  len (N ∷ Ns) = cong suc (len Ns)
... | refl = go (M ∷ Ms) i a ne
  where
  go : ∀ {j} (Ns : Vec (Tm Σ Γ Any) (suc j)) (i : Fin (suc j)) → At i (⟦ Ns ⟧* ρ) d → AllNE (⟦ Ns ⟧* ρ)
    → tup[ i ] d ∈ 𝒯 (suc j) (⟦ Ns ⟧s[ T ] ρ)
  go Ns i a ne = ⟨ refl , ⟨ at Ns i a , all Ns ne ⟩ ⟩
    where
    at : ∀ {j} (Ns : Vec (Tm Σ Γ Any) j) (i : Fin j) → At i (⟦ Ns ⟧* ρ) d → d ∈ nthD (⟦ Ns ⟧s[ T ] ρ) i
    at (N ∷ Ns) zero ⟨ _ , d∈ ⟩ = d∈
    at (N ∷ Ns) (suc i) a = at Ns i a
    all : ∀ {j} (Ns : Vec (Tm Σ Γ Any) j) → AllNE (⟦ Ns ⟧* ρ) → ∀ i → nonempty (nthD (⟦ Ns ⟧s[ T ] ρ) i)
    all (N ∷ Ns) ⟨ ne , _ ⟩ zero = ne
    all (N ∷ Ns) ⟨ _ , nes ⟩ (suc i) = all Ns nes i
𝒯L-args Ms ρ (dconst k) ()
𝒯L-args Ms ρ (V ↦ w) ()
𝒯L-args Ms ρ ν ()
𝒯L-args Ms ρ ω ()
𝒯L-args Ms ρ ⦅ u , v ⦆ ()
𝒯L-args Ms ρ (left d) ()
𝒯L-args Ms ρ (right d) ()

{- Primitives and project ------------------------------------------------------------------}

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

{- a value of a tag's type has an element that the tag accepts -}
acc-𝒱 : ∀ t (u : Val Σ ⟪ flat t ⟫) → Σ[ d ∈ Value ] d ∈ 𝒱 u × accepts fun₄ t d
acc-𝒱 tfun (pack c e) with 𝒱-ne c | 𝒱-ne e
... | ⟨ a , a∈ ⟩ | ⟨ b , b∈ ⟩ = ⟨ ⦅ a , b ⦆ , ⟨ ⟨ a∈ , b∈ ⟩ , tt ⟩ ⟩
acc-𝒱 tsum (inl v) = let ⟨ d , d∈ ⟩ = 𝒱-ne v in ⟨ left d , ⟨ d∈ , inj₁ ⟨ d , refl ⟩ ⟩ ⟩
acc-𝒱 tsum (inr v) = let ⟨ d , d∈ ⟩ = 𝒱-ne v in ⟨ right d , ⟨ d∈ , inj₂ ⟨ d , refl ⟩ ⟩ ⟩
acc-𝒱 tint (const k) = ⟨ dconst k , ⟨ ⟨ refl , refl ⟩ , ⟨ k , refl ⟩ ⟩ ⟩
acc-𝒱 (ttup n i) (tup ws) =
  let ⟨ d , d∈ ⟩ = 𝒱-ne (lookup ws i) in ⟨ tup[ i ] d , ⟨ ⟨ At-lookup i ws d∈ , 𝒱v-ne ws ⟩ , ⟨ d , refl ⟩ ⟩ ⟩

{- Steps shrink the denotation of the state ---------------------------------------------------}

begin-⊆ : ∀ {Γ A} (M : Tm Σ Γ A) (γ : Env Σ Γ) κ → 𝒮 (begin M γ κ) ⊆ 𝒮 (eval M γ κ)
begin-⊆ (` x) γ κ = 𝒦-mono κ (𝓔-lookup γ x)
begin-⊆ (fun-ref f) γ κ = λ d d∈ → d∈
begin-⊆ (pack L M) γ κ = λ d d∈ → d∈
begin-⊆ (callc L M) γ κ = λ d d∈ → d∈
begin-⊆ (lit B c) γ κ = λ d d∈ → d∈
begin-⊆ (tuple Ms) γ κ d d∈ = 𝒦-mono κ (𝒯L-args Ms (𝓔 γ)) d (tuple-next-𝒮 [] Ms γ refl κ d d∈)
begin-⊆ (get i M) γ κ = λ d d∈ → d∈
begin-⊆ (inl M) γ κ = λ d d∈ → d∈
begin-⊆ (inr M) γ κ = λ d d∈ → d∈
begin-⊆ (case L M N) γ κ = λ d d∈ → d∈
begin-⊆ (prim p L M) γ κ = λ d d∈ → d∈
begin-⊆ (let′ M N) γ κ = λ d d∈ → d∈
begin-⊆ (inject G M) γ κ = λ d d∈ → d∈
begin-⊆ (project t M) γ κ = λ d d∈ → d∈

step-⊆ : ∀ s {s'} → step ds s ≡ next s' → 𝒮 s' ⊆ 𝒮 s
step-⊆ (eval M γ κ) refl = begin-⊆ M γ κ
step-⊆ (ret v halt) ()
step-⊆ (ret v (callL M γ κ)) refl = λ d d∈ → d∈
step-⊆ (ret a (callR (pack (code f) e) κ)) refl = 𝒦-mono κ (call-⊆ f e a)
step-⊆ (ret c (packL M γ κ)) refl = λ d d∈ → d∈
step-⊆ (ret e (packR c κ)) refl = λ d d∈ → d∈
step-⊆ (ret v (tupK vs Ms γ e κ)) refl = tuple-next-𝒮 (v ∷ vs) Ms γ _ κ
step-⊆ (ret (tup ws) (getK i κ)) refl = 𝒦-mono κ λ d d∈ → ⟨ At-lookup i ws d∈ , 𝒱v-ne ws ⟩
step-⊆ (ret v (inlK κ)) refl = λ d d∈ → d∈
step-⊆ (ret v (inrK κ)) refl = λ d d∈ → d∈
step-⊆ (ret (inl u) (caseK M N γ κ)) refl = 𝒦-mono κ β
  where
  β : ⟦ M ⟧⁺ (𝓔 (u ∷ γ)) ⊆ 𝒞 ⟨ inlD ⟨ 𝒱 u , ptt ⟩ , ⟨ (λ X → ⟦ M ⟧⁺ (X • 𝓔 γ)) , ⟨ (λ X → ⟦ N ⟧⁺ (X • 𝓔 γ)) , ptt ⟩ ⟩ ⟩
  β d d∈ with body-in M γ u d d∈
  ... | ⟨ [] , ⟨ ne , _ ⟩ ⟩ = ⊥-elim (ne refl)
  ... | ⟨ w ∷ W , ⟨ _ , ⟨ V⊆ , d∈′ ⟩ ⟩ ⟩ = inj₁ ⟨ w , ⟨ W , ⟨ V⊆ , ⟨ d∈′ , Con⇒≈ (w ∷ W) (𝒱-con u) V⊆ ⟩ ⟩ ⟩ ⟩
step-⊆ (ret (inr u) (caseK M N γ κ)) refl = 𝒦-mono κ β
  where
  β : ⟦ N ⟧⁺ (𝓔 (u ∷ γ)) ⊆ 𝒞 ⟨ inrD ⟨ 𝒱 u , ptt ⟩ , ⟨ (λ X → ⟦ M ⟧⁺ (X • 𝓔 γ)) , ⟨ (λ X → ⟦ N ⟧⁺ (X • 𝓔 γ)) , ptt ⟩ ⟩ ⟩
  β d d∈ with body-in N γ u d d∈
  ... | ⟨ [] , ⟨ ne , _ ⟩ ⟩ = ⊥-elim (ne refl)
  ... | ⟨ w ∷ W , ⟨ _ , ⟨ V⊆ , d∈′ ⟩ ⟩ ⟩ = inj₂ ⟨ w , ⟨ W , ⟨ V⊆ , ⟨ d∈′ , Con⇒≈ (w ∷ W) (𝒱-con u) V⊆ ⟩ ⟩ ⟩ ⟩
step-⊆ (ret (const n) (primL p M γ κ)) refl = λ d d∈ → d∈
step-⊆ (ret (const m) (primR p n κ)) refl = 𝒦-mono κ (prim-⊆ p n m)
step-⊆ (ret v (letK N γ κ)) refl = 𝒦-mono κ β
  where
  β : ⟦ N ⟧⁺ (𝓔 (v ∷ γ)) ⊆ ⋆ ⟨ Λ ⟨ (λ X → ⟦ N ⟧⁺ (X • 𝓔 γ)) , ptt ⟩ , ⟨ 𝒱 v , ptt ⟩ ⟩
  β d d∈ with body-in N γ v d d∈
  ... | ⟨ V , ⟨ ne , ⟨ V⊆ , d∈′ ⟩ ⟩ ⟩ = ⟨ V , ⟨ ⟨ d∈′ , ⟨ ne , Con⇒≈ V (𝒱-con v) V⊆ ⟩ ⟩ , ⟨ V⊆ , ne ⟩ ⟩ ⟩
step-⊆ (ret v (injK G κ)) refl = λ d d∈ → d∈
step-⊆ (ret (dyn H u) (projK t κ)) e with H ≟F flat t
step-⊆ (ret (dyn H u) (projK t κ)) refl | yes refl = 𝒦-mono κ λ d d∈ → ⟨ acc-𝒱 t u , d∈ ⟩
step-⊆ (ret (dyn H u) (projK t κ)) () | no _

↠-⊆ : ∀ {s t} → s ↠ t → 𝒮 t ⊆ 𝒮 s
↠-⊆ done = ⊆r
↠-⊆ {s} (st ∷↠ σ) d d∈ = step-⊆ s st d (↠-⊆ σ d d∈)

{- Final states ------------------------------------------------------------------------------}

open import Semantics.Observation using (Obs; o-error; o-const; Answer)

{- a state that stops with an answer returns a value to halt -}
halts : ∀ s {o} → step ds s ≡ stop o → Answer o → Σ[ v ∈ Val Σ Any ] s ≡ ret v halt × o ≡ obs v
halts (eval M γ κ) () ans
halts (ret v halt) refl ans = ⟨ v , ⟨ refl , refl ⟩ ⟩
halts (ret v (projK t κ)) e ans with proj? t v
halts (ret v (projK t κ)) () ans | just w
halts (ret v (projK t κ)) refl ans | nothing = ⊥-elim (ans refl)
halts (ret v (callL M γ κ)) () ans
halts (ret v (callR f κ)) () ans
halts (ret v (packL M γ κ)) () ans
halts (ret v (packR c κ)) () ans
halts (ret v (tupK vs Ms γ e κ)) () ans
halts (ret v (getK i κ)) () ans
halts (ret v (inlK κ)) () ans
halts (ret v (inrK κ)) () ans
halts (ret v (caseK M N γ κ)) () ans
halts (ret v (primL p M γ κ)) () ans
halts (ret v (primR p n κ)) () ans
halts (ret v (letK N γ κ)) () ans
halts (ret v (injK G κ)) () ans

{- the denotation of a value observed as a constant holds it -}
𝒱-const : ∀ {A B} {k : base-rep B} (v : Val Σ A) → obs v ≡ o-const B k → dconst k ∈ 𝒱 v
𝒱-const (dyn G v) e = 𝒱-const v e
𝒱-const (const k) refl = ⟨ refl , refl ⟩
𝒱-const (code f) ()
𝒱-const (pack c e) ()
𝒱-const (tup ws) ()
𝒱-const (inl v) ()
𝒱-const (inr v) ()

{- what the machine stops with, from main -}
final : ∀ {M : Tm Σ [] Any} {s o} → Star (machine (State Σ) (step ds) (eval M [] halt)) (eval M [] halt) s
  → step ds s ≡ stop o → Answer o → Σ[ v ∈ Val Σ Any ] o ≡ obs v × 𝒱 v ⊆ ⟦ M ⟧⁺ (λ _ → init)
final {s = s} σ fin ans with halts s fin ans
... | ⟨ v , ⟨ refl , refl ⟩ ⟩ = ⟨ v , ⟨ refl , ↠-⊆ (star→↠ σ) ⟩ ⟩

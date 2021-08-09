module ISWIMPValue where

open import Primitives
open import Syntax using (Rename)
open import ISWIM hiding (Ctx)
open ISWIM.ASTMod using (WF-rel; len-mk-list)
open import AbstractBindingTree Op sig using (Ctx; CHole)
open import WellScoped Op sig using (WF-plug) 
open import Fold2 Op sig
open import ScopedTuple hiding (𝒫)
open import Sig
open import Utilities using (extensionality)
open import SetsAsPredicates
open import PValueCBV
open import SemanticProperties Op sig

open import Data.Empty using (⊥-elim) renaming (⊥ to False)
open import Data.List using (List ; _∷_ ; []; _++_; length)
open import Data.List.Properties using (++-conicalˡ)
open import Data.List.Membership.Propositional renaming (_∈_ to _⋵_)
open import Data.List.Membership.Propositional.Properties
  using (∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any using (here; there) 
open import Data.Nat using (ℕ; zero; suc; _≟_; _<_; s≤s)
open import Data.Product using (_×_; Σ; Σ-syntax; proj₁; proj₂)
    renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt) renaming (⊤ to True)
open import Level renaming (zero to lzero; suc to lsuc)
open import Relation.Binary.PropositionalEquality
    using (_≡_; _≢_; refl; sym; subst)
open import Relation.Nullary using (¬_; Dec; yes; no)


{- Denotational Semantics of the ISWIM Language via fold ----------------------}

interp-op  : (op : Op) → Tuple (sig op) (ArgTy (𝒫 Value)) → 𝒫 Value
interp-op lam ⟨ F , _ ⟩ = Λ F
interp-op app ⟨ D₁ , ⟨ D₂ , _ ⟩ ⟩ = D₁ ▪ D₂
interp-op (lit P k) _ = ℘ P k

{- interp-op is monotonic -}
mono-op : {op : Op} {xs ys : Tuple (sig op) (ArgTy (𝒫 Value))}
   → ⊆-args (sig op) xs ys → interp-op op xs ⊆ interp-op op ys
mono-op {lam} {⟨ f , _ ⟩ } {⟨ g , _ ⟩} ⟨ f⊆g , _ ⟩ =
    Λ-ext-⊆ (λ {X} → lower (f⊆g X))
mono-op {app} {⟨ a , ⟨ b , _ ⟩ ⟩} {⟨ c , ⟨ d , _ ⟩ ⟩} ⟨ a<c , ⟨ b<d , _ ⟩ ⟩ =
    ▪-cong-⊆ (lower a<c) (lower b<d)
mono-op {lit P k} {xs} {ys} xs⊆ys d d∈k = d∈k

instance
  ISWIM-Semantics : Semantics
  ISWIM-Semantics = record { interp-op = interp-op ; mono-op = mono-op }
open Semantics {{...}}

⟦⟧-app : ∀{L M : Term}{ρ : Env}
  → ⟦ L · M ⟧ ρ ≡ ⟦ L ⟧ ρ ▪ ⟦ M ⟧ ρ
⟦⟧-app = refl

⟦⟧-lam : ∀{N : Term}{ρ : Env}
  → ⟦ ƛ N ⟧ ρ ≡ Λ (λ D → ⟦ N ⟧ (D • ρ))
⟦⟧-lam = refl

⟦⟧-prim : ∀{P : Prim}{k : rep P}{ρ : Env}
  → ⟦ $ P k ⟧ ρ ≡ ℘ P k
⟦⟧-prim = refl

{- interp-op is continuous -}
continuous-op : ∀{op}{ρ}{NE-ρ}{v}{args}
   → v ∈ ⟦ op ⦅ args ⦆ ⟧ ρ
   → pred-args (Cont-Env-Arg ρ NE-ρ) (sig op) args
   → Σ[ ρ′ ∈ Env ] finite-env ρ′ × ρ′ ⊆ₑ ρ × v ∈ (⟦ op ⦅ args ⦆ ⟧ ρ′)
continuous-op {lam} {ρ} {NE-ρ} {v} {cons (bind (ast N)) nil}
    v∈Λ ⟨ IH-N , _ ⟩ =
    Λ-continuous {NE-ρ = NE-ρ} v∈Λ IH-N (⟦⟧-monotone N)
continuous-op {app} {ρ} {NE-ρ} {w} {cons (ast L) (cons (ast M) nil)}
    w∈⟦L·M⟧ρ ⟨ IH-L , ⟨ IH-M , _ ⟩ ⟩ =
    ▪-continuous{NE-ρ = NE-ρ} w∈⟦L·M⟧ρ IH-L IH-M (⟦⟧-monotone L) (⟦⟧-monotone M)
continuous-op {lit p x} {ρ} {NE-ρ} {v} {nil} v∈⟦M⟧ρ _ =
  ⟨ initial-finite-env ρ NE-ρ , ⟨ initial-fin ρ NE-ρ , ⟨ initial-fin-⊆ ρ NE-ρ ,
    v∈⟦M⟧ρ ⟩ ⟩ ⟩

instance
  ISWIM-Continuous : ContinuousSemantics
  ISWIM-Continuous = record { continuous-op =
      λ{op}{ρ}{NE-ρ} → continuous-op{op}{ρ}{NE-ρ} }
open ContinuousSemantics {{...}}

{- Syntactic values terminate (i.e., have nonempty denotations) ---------------}

value-nonempty : ∀{V : Term}{ρ}
  → nonempty-env ρ → TermValue V → nonempty (⟦ V ⟧ ρ)
value-nonempty NE-ρ (V-var {x}) = NE-ρ x
value-nonempty NE-ρ (V-ƛ) = ⟨ ν , tt ⟩
value-nonempty NE-ρ (V-lit {base B} {k}) = ⟨ const k , k∈℘k ⟩
value-nonempty NE-ρ (V-lit {B ⇒ P} {k}) = ⟨ ν , tt ⟩

{- Substitution Lemma (via fold-subst-fusion) ---------------------------------}

⟦⟧-par-subst : ∀ {M : Term}{σ : Subst}{ρ : Var → 𝒫 Value}
  → ⟦ ⟪ σ ⟫ M ⟧ ρ ≡ ⟦ M ⟧ (λ x → ⟦ σ x ⟧ ρ)
⟦⟧-par-subst {M}{ρ} = fold-subst-fusion M

⟦⟧-subst : ∀ {M N : Term}{ρ : Var → 𝒫 Value}
  → ⟦ M [ N ] ⟧ ρ ≡ ⟦ M ⟧ ((⟦ N ⟧ ρ) • ρ)
⟦⟧-subst {M}{N}{ρ} =
  subst (λ X → ⟦ M [ N ] ⟧ ρ ≡ ⟦ M ⟧ X) (extensionality EQ)
        (⟦⟧-par-subst {M}{N • id})
  where 
  EQ : (x : Var) → ⟦ (N • id) x ⟧ ρ ≡ (⟦ N ⟧ ρ • ρ) x
  EQ zero = refl
  EQ (suc x) = refl

{- Soundness of Reduction with respect to Denotations -------------------------}

⟦⟧—→ : ∀{M N : Term}{ρ : Var → 𝒫 Value} {NE-ρ : nonempty-env ρ}
   → M —→ N
   → ⟦ M ⟧ ρ ≃ ⟦ N ⟧ ρ
⟦⟧—→ {L · M} {L′ · M} {ρ}{NE-ρ} (ξ₁-rule L—→L′) =
    let IH = ⟦⟧—→{ρ = ρ}{NE-ρ} L—→L′ in
    ⟦ L · M ⟧ ρ              ≃⟨⟩
    (⟦ L ⟧ ρ) ▪ (⟦ M ⟧ ρ)    ≃⟨ ▪-cong IH ≃-refl ⟩
    (⟦ L′ ⟧ ρ) ▪ (⟦ M ⟧ ρ)   ≃⟨⟩
    ⟦ L′ · M ⟧ ρ             ∎ where open ≃-Reasoning  
⟦⟧—→ {V · M} {.(_ · _)} {ρ}{NE-ρ} (ξ₂-rule {M′ = M′} v M—→M′) =
    let IH = ⟦⟧—→{ρ = ρ}{NE-ρ} M—→M′ in
    ⟦ V · M ⟧ ρ              ≃⟨⟩
    (⟦ V ⟧ ρ) ▪ (⟦ M ⟧ ρ)    ≃⟨ ▪-cong (≃-refl{D = ⟦ V ⟧ ρ}) IH ⟩
    (⟦ V ⟧ ρ) ▪ (⟦ M′ ⟧ ρ)   ≃⟨⟩
    ⟦ V · M′ ⟧ ρ             ∎ where open ≃-Reasoning  
⟦⟧—→ {ƛ N · V} {_} {ρ} {NE-ρ} (β-rule v) =
    ⟦ ƛ N · V ⟧ ρ                           ≃⟨⟩
    (Λ (λ D → ⟦ N ⟧ (D • ρ))) ▪ (⟦ V ⟧ ρ)   ≃⟨ Λ⟦⟧-▪-id {N}{ρ}{NE-ρ}
                                                   (value-nonempty NE-ρ v) ⟩
    ⟦ N ⟧ (⟦ V ⟧ ρ • ρ)               ≃⟨ ≃-reflexive (sym (⟦⟧-subst{N}{V}{ρ})) ⟩
    ⟦ N [ V ] ⟧ ρ                     ∎ where open ≃-Reasoning
⟦⟧—→ {($ (B ⇒ P) f · $ (base B) k)} {_} {ρ} δ-rule =
    ⟦ $ (B ⇒ P) f · $ (base B) k ⟧ ρ        ≃⟨⟩
    (℘ (B ⇒ P) f) ▪ (℘ (base B) k)         ≃⟨ ℘-▪-≃ {B}{P} ⟩
    ⟦ $ P (f k) ⟧ ρ                         ∎ where open ≃-Reasoning

soundness : ∀ {M N : Term} {ρ : Env}{NE-ρ : nonempty-env ρ}
  → M —↠ N
    -------------------
  → ⟦ M ⟧ ρ ≃ ⟦ N ⟧ ρ
soundness {M}{_}{ρ} (M □) =
    ⟦ M ⟧ ρ ≃⟨⟩ ⟦ M ⟧ ρ ∎ where open ≃-Reasoning
soundness {M}{N}{ρ}{NE-ρ} (_—→⟨_⟩_ M {M = M′} M—→M′ M′—↠N) =
    ⟦ M ⟧ ρ      ≃⟨ ⟦⟧—→{ρ = ρ}{NE-ρ} M—→M′ ⟩ 
    ⟦ M′ ⟧ ρ     ≃⟨ soundness{ρ = ρ}{NE-ρ} M′—↠N ⟩ 
    ⟦ N ⟧ ρ      ∎ where open ≃-Reasoning

{- Adequacy of Denotations ----------------------------------------------------}

open import EvalISWIM {- the big-step semantics of ISWIM -}

{- Relate denotational values to big-step values -}
𝕍 : Value → Val → Set
𝕍s : List Value → Val → Set

𝕍 (const {B} k) (val-const {P} p) = ℘ P p (const {B} k)
𝕍 (const {B} k) (val-clos N γ) = False
𝕍 (const {B} k) bogus = False
𝕍 (V ↦ w) (val-const {P} f) = ℘ P f (V ↦ w)
𝕍 (V ↦ w) (val-clos N γ) =
    (∀{c : Val} → 𝕍s V c → Σ[ c' ∈ Val ] (γ ,' c) ⊢ N ⇓ c'  ×  𝕍 w c')
𝕍 (V ↦ w) bogus = False
𝕍 ν (val-const {base B} k) = False
𝕍 ν (val-const {B ⇒ P} f) = True
𝕍 ν (val-clos N γ) = True
𝕍 ν bogus = False

𝕍s [] c = True
𝕍s (v ∷ V) c = 𝕍 v c × 𝕍s V c

𝕍kc⇒c≡k : ∀{B}{k}{c} → 𝕍 (const {B} k) c  →  c ≡ val-const {base B} k
𝕍kc⇒c≡k {B} {k} {val-const {P} k′} 𝕍kc
    with k′∈℘k⇒P≡B {P}{B} 𝕍kc
... | refl
    with k′∈℘k⇒k′≡k 𝕍kc
... | refl = refl

℘⇒𝕍 : ∀{P}{k}{w}  → ℘ P k w  →  𝕍 w (val-const {P} k)
℘⇒𝕍 {P} {k} {const x} w∈k = w∈k
℘⇒𝕍 {P} {k} {x ↦ w} w∈k = w∈k
℘⇒𝕍 {B ⇒ P} {k} {ν} w∈k = tt

V⊆𝕍c⇒𝕍sV : ∀{V}{c} → (∀ u → mem V u → 𝕍 u c) → 𝕍s V c
V⊆𝕍c⇒𝕍sV {[]} V⊆𝕍c = tt
V⊆𝕍c⇒𝕍sV {v ∷ V} V⊆𝕍c =
    ⟨ V⊆𝕍c v (here refl) , V⊆𝕍c⇒𝕍sV (λ u z → V⊆𝕍c u (there z)) ⟩

𝕍sV⇒V⊆𝕍c : ∀{V}{c} → 𝕍s V c → (∀ u → mem V u → 𝕍 u c)
𝕍sV⇒V⊆𝕍c {[]} {c} vs u ()
𝕍sV⇒V⊆𝕍c {x ∷ V} {c} ⟨ 𝕍c , 𝕍sc ⟩ .x (here refl) = 𝕍c
𝕍sV⇒V⊆𝕍c {x ∷ V} {c} ⟨ 𝕍c , 𝕍sc ⟩ u (there u∈V) = 𝕍sV⇒V⊆𝕍c 𝕍sc u u∈V

{- Relate denotational environments to big-step environments -}
data 𝔾 : Env → ValEnv → Set₁ where
  𝔾-∅ : ∀ {ρ} → 𝔾 ρ ∅'
  𝔾-ext : ∀{γ : Env}{γ' : ValEnv}{D c} → 𝔾 γ γ' → (∀ v → v ∈ D → 𝕍 v c)
     → 𝔾 (D • γ) (γ' ,' c)

𝔾⇒𝕍 : ∀ {ρ : Env}{γ : ValEnv}{x}{lt : x < length γ}{v}
   → 𝔾 ρ γ  →  v ∈ ρ x  →  𝕍 v (nth γ x)
𝔾⇒𝕍 {.(_ • _)} {.(_ ∷ _)} {zero} {s≤s lt} {v} (𝔾-ext 𝔾ργ D⊆V) v∈D = D⊆V v v∈D
𝔾⇒𝕍 {.(_ • _)} {.(_ ∷ _)} {suc x} {s≤s lt} {v} (𝔾-ext 𝔾ργ D⊆V) v∈ρx =
  𝔾⇒𝕍{lt = lt} 𝔾ργ v∈ρx

¬𝕍[bogus] : ∀ v → ¬ 𝕍 v bogus
¬𝕍[bogus] (const k) x = x
¬𝕍[bogus] (V ↦ w) x = x

℘pv⇒𝕍vp : ∀ {P}{p}{v} →  ℘ P p v  →  𝕍 v (val-const {P} p)
℘pv⇒𝕍vp {v = const k} ℘pv = ℘pv
℘pv⇒𝕍vp {v = V ↦ w} ℘pv = ℘pv
℘pv⇒𝕍vp {B ⇒ P} {p} {ν} ℘pv = tt

{- the main lemma -}
⟦⟧⇒⇓ : ∀{M : Term}{γ}{wfM : WF (length γ) M}{ρ}{v}
   → 𝔾 ρ γ  →  v ∈ ⟦ M ⟧ ρ
   → Σ[ c ∈ Val ] γ ⊢ M ⇓ c  ×  (∀ u → u ∈ ⟦ M ⟧ ρ → 𝕍 u c)
⟦⟧⇒⇓ {` x}{γ}{WF-var ∋x lt}{ρ}{v} 𝔾ργ v∈⟦M⟧ρ =
    let lt' = subst (λ □ → x < □) (len-mk-list (length γ)) lt in
   ⟨ nth γ x , ⟨ ⇓-var , (λ v v∈ρx → 𝔾⇒𝕍{lt = lt'} 𝔾ργ v∈ρx) ⟩ ⟩
⟦⟧⇒⇓ {L · M}{γ}
    {WF-op (WF-cons (WF-ast wfL) (WF-cons (WF-ast wfM) WF-nil)) _}
    {ρ}{w} 𝔾ργ w∈LMρ = G
    where
    Part1 : ∀{L}{M}{ρ}{w}{wfL : WF (length γ) L}{wfM : WF (length γ) M}
      → 𝔾 ρ γ  →  w ∈ ⟦ L · M ⟧ ρ
      → Σ[ c ∈ Val ] γ ⊢ L · M ⇓ c × 𝕍 w c
    Part2 : ∀{c₁ c₂}{L M}{γ}{V w}
       → γ ⊢ L ⇓ c₁  →  𝕍 (V ↦ w) c₁
       → γ ⊢ M ⇓ c₂  →  𝕍s V c₂
       → Σ[ c ∈ Val ] γ ⊢ L · M ⇓ c × 𝕍 w c
       
    Part1 {L}{M}{ρ}{w}{wfL}{wfM} 𝔾ργ ⟨ V , ⟨ V↦w∈⟦L⟧ρ , ⟨ V⊆⟦M⟧ρ , V≢[] ⟩ ⟩ ⟩ 
        with V
    ... | [] = ⊥-elim (V≢[] refl)    
    ... | v ∷ V′
        with ⟦⟧⇒⇓ {L}{γ}{wfL}{ρ}{(v ∷ V′) ↦ w} 𝔾ργ V↦w∈⟦L⟧ρ
    ... | ⟨ c₁ , ⟨ L⇓c₁ , ⟦L⟧⊆𝕍c₁ ⟩ ⟩ 
        with ⟦⟧⇒⇓ {M}{γ}{wfM}{ρ}{v} 𝔾ργ (V⊆⟦M⟧ρ v (here refl))
    ... | ⟨ c₂ , ⟨ M⇓c₂ , ⟦M⟧⊆𝕍c₂ ⟩ ⟩ =
        Part2 L⇓c₁ 𝕍Vwc₁ M⇓c₂ 𝕍sc₂
        where
        𝕍Vwc₁ : 𝕍 ((v ∷ V′) ↦ w) c₁
        𝕍Vwc₁ = ⟦L⟧⊆𝕍c₁ ((v ∷ V′) ↦ w) V↦w∈⟦L⟧ρ
        𝕍sc₂ : 𝕍s (v ∷ V′) c₂
        𝕍sc₂ = ⟨ (⟦M⟧⊆𝕍c₂ v (V⊆⟦M⟧ρ v (here refl))) ,
                 (V⊆𝕍c⇒𝕍sV (λ u u∈V′ → ⟦M⟧⊆𝕍c₂ u (V⊆⟦M⟧ρ u (there u∈V′)) )) ⟩
    Part2 {val-const {B ⇒ P} f}{c₂}{L}{M}{γ}{V}{w}
        L⇓c₁ ⟨ k , ⟨ refl , w∈fk ⟩ ⟩ M⇓ ⟨ 𝕍kc₂ , _ ⟩ 
           rewrite 𝕍kc⇒c≡k {B}{k}{c₂} 𝕍kc₂ =
       ⟨ (val-const {P} (f k)) , ⟨ (⇓-prim L⇓c₁ M⇓) , ℘⇒𝕍 {P} w∈fk ⟩ ⟩
    Part2 {val-clos N γ′{wfN}}{c₂}{L}{M}{γ}{V}{w} L⇓c₁ 𝕍Vwc₁ M⇓ 𝕍sVc₂
       with 𝕍Vwc₁ {c₂} 𝕍sVc₂
    ... | ⟨ c₃ , ⟨ N⇓c₃ , 𝕍wc₃ ⟩ ⟩ =
        ⟨ c₃ , ⟨ (⇓-app{wf = WF-rel N wfN} L⇓c₁ M⇓ N⇓c₃) , 𝕍wc₃ ⟩ ⟩
          
    G : Σ[ c ∈ Val ] γ ⊢ L · M ⇓ c  ×  (∀ u → u ∈ ⟦ L · M ⟧ ρ → 𝕍 u c)
    G   with Part1{L}{M}{wfL = wfL}{wfM} 𝔾ργ w∈LMρ
    ... | ⟨ c , ⟨ LM⇓c , 𝕍wc ⟩ ⟩ = ⟨ c , ⟨ LM⇓c , H ⟩ ⟩
        where
        H : ∀ u → u ∈ ⟦ L · M ⟧ ρ → 𝕍 u c
        H u u∈LM
            with Part1{L}{M}{wfL = wfL}{wfM} 𝔾ργ u∈LM
        ... | ⟨ c′ , ⟨ LM⇓c′ , 𝕍wc′ ⟩ ⟩ rewrite ⇓-determ LM⇓c′ LM⇓c = 𝕍wc′
⟦⟧⇒⇓ {ƛ N}{γ}{WF-op (WF-cons (WF-bind (WF-ast wfN)) WF-nil) _}{ρ}{v}
    𝔾ργ v∈⟦M⟧ρ =
    ⟨ (val-clos N γ {wfN}) , ⟨ ⇓-lam {wf = wfN} , G ⟩ ⟩
    where
    G : (u : Value) → u ∈ ⟦ ƛ N ⟧ ρ → 𝕍 u (val-clos N γ {wfN})
    G ν u∈ƛN = tt
    G (V ↦ w) ⟨ w∈⟦N⟧[V•ρ] , V≠[] ⟩ {c} 𝕍sVc
        with ⟦⟧⇒⇓ {N}{c ∷ γ}{wfN}{mem V • ρ}{w}
                   (𝔾-ext{c = c} 𝔾ργ (𝕍sV⇒V⊆𝕍c 𝕍sVc)) w∈⟦N⟧[V•ρ]
    ... | ⟨ c′ , ⟨ N⇓c′ , ⟦N⟧⊆𝕍c′ ⟩ ⟩ =
          ⟨ c′ , ⟨ N⇓c′ , ⟦N⟧⊆𝕍c′ w w∈⟦N⟧[V•ρ] ⟩ ⟩
⟦⟧⇒⇓ {$ P k}{γ}{wfPk}{ρ}{v} 𝔾ργ v∈⟦M⟧ρ =
    ⟨ val-const {P} k , ⟨ ⇓-lit , (λ u ℘pu → ℘pv⇒𝕍vp {P} ℘pu) ⟩ ⟩

adequacy : ∀{M V : Term}{wfM : WF 0 M}{ρ}{NE-ρ : nonempty-env ρ}
   → TermValue V  →  ⟦ M ⟧ ρ ≃ ⟦ V ⟧ ρ
    ----------------------------------
   → Σ[ c ∈ Val ] ∅' ⊢ M ⇓ c
adequacy{M}{V}{wfM}{ρ}{NE-ρ} Vval ⟦M⟧≃⟦V⟧
    with value-nonempty{V}{ρ} NE-ρ Vval
... | ⟨ v , v∈⟦V⟧ ⟩
    with ⟦⟧⇒⇓ {wfM = wfM} 𝔾-∅ (proj₂ ⟦M⟧≃⟦V⟧ v v∈⟦V⟧)
... | ⟨ c , ⟨ M⇓c , _ ⟩ ⟩ =
    ⟨ c , M⇓c ⟩

{- corollary of adequacy and soundness:
   reduction to a value implies big-step termination -}
reduce→⇓ : ∀ {M V : Term}{wfM : WF 0 M}
   → TermValue V  →  M —↠ V
    -------------------------
   → Σ[ c ∈ Val ] ∅' ⊢ M ⇓ c
reduce→⇓ {M}{V}{wfM} v M—↠N =
   let ρ = λ x → ⌈ ν ⌉ in
   let NE-ρ = λ x → ⟨ ν , refl ⟩ in
   adequacy {M}{V}{wfM}{ρ = ρ}{NE-ρ} v (soundness{NE-ρ = NE-ρ} M—↠N)

{- Compositionality -----------------------------------------------------------}

compositionality : ∀{C : Ctx} {M N : Term}{ρ}
   → (∀ {ρ} → ⟦ M ⟧ ρ ≃ ⟦ N ⟧ ρ)
    --------------------------------
   → ⟦ plug C M ⟧ ρ ≃ ⟦ plug C N ⟧ ρ
compositionality{CHole}{M}{N}{ρ} ⟦M⟧=⟦N⟧ = ⟦M⟧=⟦N⟧
compositionality{COp lam (ccons (CBind (CAst C′)) nil refl)}{M}{N}{ρ} ⟦M⟧=⟦N⟧ =
   Λ-ext λ {X} → compositionality {C′}{M}{N}{X • ρ} ⟦M⟧=⟦N⟧
compositionality{COp app (tcons (ast L) (tcons x Cs refl) refl)} ⟦M⟧=⟦N⟧ =
   ≃-refl
compositionality {COp app (tcons (ast L) (ccons (CAst C′) nil refl) refl)}
   {M}{N}{ρ} ⟦M⟧=⟦N⟧ =
   ▪-cong{⟦ L ⟧ ρ} ≃-refl (compositionality {C′} ⟦M⟧=⟦N⟧)
compositionality{COp app (ccons (CAst C′) (cons (ast M′) nil) refl)}{M}{N}{ρ}
  ⟦M⟧=⟦N⟧ =
  ▪-cong{D₂ = ⟦ M′ ⟧ ρ} (compositionality {C′}{M}{N}{ρ} ⟦M⟧=⟦N⟧) ≃-refl

{- Denotational Equality implies Contextual Equivalence -----------------------}

denot-equal⇒context-equal : ∀{M N : Term}
  → (∀ {ρ} → ⟦ M ⟧ ρ ≃ ⟦ N ⟧ ρ)
    ---------------------------
  → M ≅ N
denot-equal⇒context-equal {M}{N} eq {C}{wfC}{wfM}{wfN} =
  record { to = λ tm → equal⇒terminates{wfM = wfM}{wfN}{wfC} eq tm ;
           from = λ tn → equal⇒terminates{wfM = wfN}{wfM}{wfC} (≃-sym eq) tn }
  where
  equal⇒terminates : ∀{M N : Term} {C : Ctx}{wfM : WF (ctx-depth C 0) M}
      {wfN : WF (ctx-depth C 0) N}{wfC : WF-Ctx 0 C}
    → (∀ {ρ} → ⟦ M ⟧ ρ ≃ ⟦ N ⟧ ρ)  →  terminates (plug C M)
    → terminates (plug C N)
  equal⇒terminates {M}{N}{C}{wfM}{wfN}{wfC} M≃N ⟨ N′ , ⟨ Nv , CM—↠N′ ⟩ ⟩ =
     let ρ = λ x → ⌈ ν ⌉ in
     let NE-ρ = λ x → ⟨ ν , refl ⟩ in
     let CM≃λN′ = soundness{ρ = ρ}{NE-ρ} CM—↠N′ in
     let CM≃CN = compositionality{C}{M}{N}{ρ} M≃N in
     let CN≃λN′ = ≃-trans (≃-sym CM≃CN) CM≃λN′ in
     let adq = adequacy{plug C N}{wfM = WF-plug wfC wfN}{ρ}{NE-ρ} Nv CN≃λN′ in
     ⇓→—↠ {wfM = WF-plug wfC wfN} (proj₂ adq)

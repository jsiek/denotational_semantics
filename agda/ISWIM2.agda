module ISWIM2 where

{-

   ISWIM: the call-by-value lambda calculus with constants.

   This version uses a simpler definition of substitution that doesn't
   require the Shiftable requirement.

-}

open import Primitives
open import Syntax using (Rename)
open import ISWIM hiding (_[_]; id; ext; subst-zero;
    _—→_; _—↠_; Ctx; terminates;
    _—→⟨_⟩_; _—↠⟨_⟩_; —↠-trans; _□;
    —→-app-cong; appR-cong; appL-cong; _≅_;
    β-rule; ξ₁-rule; ξ₂-rule; δ-rule) public
open import AbstractBindingTree Op sig using (Ctx; CHole)
open import WellScoped Op sig using (WF-plug) 
open import Fold2 Op sig
open import ScopedTuple hiding (𝒫)
open import Sig
open import Utilities using (_iff_)

open import Data.List using (List; []; _∷_; length)
open import Data.Nat using (ℕ; zero; suc; _<_)
open import Data.Nat.Properties using (≤-pred)
open import Data.Product using (_×_; Σ; Σ-syntax) renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality
    using (_≡_; refl; sym; trans; subst)

{- Substitution ----------------------------------------------------------------}

id : Subst
id = (λ x → ` x)

_[_] : Term → Term → Term
N [ M ] =  ⟪ M • id ⟫ N

⇑ : Subst → Subst
⇑ σ x = rename suc (σ x)

ext : Subst → Subst
ext σ = ` 0 • ⇑ σ

subst-zero : Term → Subst
subst-zero M = M • id

subst-zero-exts-cons : ∀{σ : Subst}{M : Term} → ext σ ⨟ subst-zero M ≡ M • σ
subst-zero-exts-cons {σ}{M} = {!!}
{-
   begin
   ext σ ⨟ subst-zero M  ≡⟨ cong(λ □ → □  ⨟ subst-zero M)(exts-cons-shift σ) ⟩
   (` 0 • (σ ⨟ ↑ 1)) ⨟ (M • id) ≡⟨ sub-cons-seq _ _ _ ⟩
   M • ((σ ⨟ ↑ 1) ⨟ (M • id))   ≡⟨ cong (_•_ M) (sub-assoc{σ}{↑ 1}{M • id}) ⟩
   M • (σ ⨟ (↑ 1 ⨟ (M • id)))   ≡⟨ cong (λ □ → M • (σ ⨟ □)) (sub-tail M _) ⟩
   M • (σ ⨟ id)                 ≡⟨ cong (_•_ M) (sub-idR _) ⟩
   M • σ                        ∎
-}

{- Reduction semantics ---------------------------------------------------------}

infix 2 _—→_
data _—→_ : Term → Term → Set where
  ξ₁-rule : ∀  {L L′ M : Term}
    → L —→ L′
      ----------------
    → L · M —→ L′ · M
  ξ₂-rule : ∀  {L M M′ : Term}
    → TermValue L  →  M —→ M′
      -----------------------
    → L · M —→ L · M′
  β-rule : ∀  {N M : Term}
    → TermValue M
      --------------------
    → (ƛ N) · M —→ N [ M ]
  δ-rule : ∀ {B}{P} {f : base-rep B → rep P} {k}
      ---------------------------------------------
    → ($ (B ⇒ P) f) · ($ (base B) k)  —→  $ P (f k)

open import MultiStep Op sig _—→_ public

—→-app-cong : ∀ {L L' M : Term}
            → L —→ L'
            → L · M —→ L' · M
—→-app-cong (ξ₁-rule ll') = ξ₁-rule (—→-app-cong ll')
—→-app-cong (ξ₂-rule v ll') = ξ₁-rule (ξ₂-rule v ll')
—→-app-cong (β-rule v) = ξ₁-rule (β-rule v)
—→-app-cong δ-rule = ξ₁-rule δ-rule

appL-cong : ∀ {L L' M : Term}
         → L —↠ L'
           ---------------
         → L · M —↠ L' · M
appL-cong {L}{L'}{M} (L □) = L · M □
appL-cong {L}{L'}{M} (L —→⟨ r ⟩ rs) = L · M —→⟨ ξ₁-rule r ⟩ appL-cong rs

appR-cong : ∀ {L M M' : Term}
         → TermValue L
         → M —↠ M'
           ---------------
         → L · M —↠ L · M'
appR-cong {L}{M}{M'} v (M □) = L · M □
appR-cong {L}{M}{M'} v (M —→⟨ r ⟩ rs) =
    L · M —→⟨ ξ₂-rule v r ⟩ appR-cong v rs

terminates : ∀(M : Term) → Set
terminates  M = Σ[ N ∈ Term ] TermValue N × (M —↠ N)

_≅_ : ∀(M N : Term) → Set₁
(_≅_ M N) = ∀ {C : Ctx}{wfC : WF-Ctx 0 C}
              {wfM : WF (ctx-depth C 0) M}{wfN : WF (ctx-depth C 0) N}
              → (terminates (plug C M)) iff (terminates (plug C N))

open import EvalISWIM
  hiding (_≈_; _≈ₑ_; ≈→TermValue; γ≈ₑσ→γ[x]≈σ[x]; ⇓→—↠×≈; ⇓→—↠) public

data _≈_ : Val → Term → Set
data _≈ₑ_ : ValEnv → Subst → Set

data _≈_ where
  ≈-const : ∀{N}{p}{k}
     → N ≡ $ p k
     → (val-const {p} k) ≈ N
  ≈-clos : ∀ {σ}{γ}{M N : Term}{wf : WF (suc (length γ)) M}
     → γ ≈ₑ σ
     → (N ≡ ⟪ σ ⟫ (ƛ M))
     → (val-clos M γ {wf}) ≈ N

data _≈ₑ_ where
  ≈ₑ-id : ∅' ≈ₑ id
  ≈ₑ-ext : ∀ {γ : ValEnv} {σ : Subst} {c} {N : Term}
      → γ ≈ₑ σ  →  c ≈ N
        -------------------
      → (γ ,' c) ≈ₑ (N • σ)

≈→TermValue : ∀{V : Val}{M : Term}
            → V ≈ M
            → TermValue M
≈→TermValue {val-const x} {M} (≈-const refl) = V-lit
≈→TermValue {val-clos N x} {M} (≈-clos _ refl) = V-ƛ

γ≈ₑσ→γ[x]≈σ[x] : ∀{x}{γ}{σ}
   → γ ≈ₑ σ
   → x < length γ
   → nth γ x ≈ σ x
γ≈ₑσ→γ[x]≈σ[x] {zero} {.(_ ∷ _)} {.(_ • _)} (≈ₑ-ext γ≈ₑσ c≈N) x<γ = c≈N
γ≈ₑσ→γ[x]≈σ[x] {suc x} {.(_ ∷ _)} {.(_ • _)} (≈ₑ-ext γ≈ₑσ c≈N) x<γ =
    γ≈ₑσ→γ[x]≈σ[x] γ≈ₑσ (≤-pred x<γ )

⇓→—↠×≈ : ∀{γ : ValEnv}{σ : Subst}{M : Term}{c : Val}
       → WF (length γ) M
       → γ ⊢ M ⇓ c  →  γ ≈ₑ σ
         ---------------------------------------
       → Σ[ N ∈ Term ] (⟪ σ ⟫ M —↠ N) × c ≈ N
⇓→—↠×≈ wf (⇓-lit {p = p}{k}) γ≈ₑσ =
    ⟨ $ p k , ⟨ $ p k □ , ≈-const refl ⟩ ⟩
⇓→—↠×≈ {γ = γ}{σ} (WF-var ∋x lt) (⇓-var {x = x}) γ≈ₑσ
    with subst (λ □ → x < □) (ISWIM.ASTMod.len-mk-list (length γ)) lt
... | lt' =
    ⟨ σ x , ⟨ σ x □ , γ≈ₑσ→γ[x]≈σ[x] γ≈ₑσ lt' ⟩ ⟩
⇓→—↠×≈ {σ = σ} {c = val-clos N γ} wf (⇓-lam{wf = wf'}) γ≈ₑσ =
    ⟨ ⟪ σ ⟫ (ƛ N) , ⟨ ⟪ σ ⟫ (ƛ N) □ , ≈-clos {wf = wf'} γ≈ₑσ refl ⟩ ⟩
⇓→—↠×≈ {γ} {σ = σ} {app ⦅ cons (ast L) (cons (ast M) nil) ⦆} {c}
    (WF-op (WF-cons (WF-ast wfL) (WF-cons (WF-ast wfM) WF-nil)) _)
    (⇓-prim {P = P}{B}{f}{k} L⇓f M⇓k) γ≈ₑσ 
    with ⇓→—↠×≈{σ = σ} wfL L⇓f γ≈ₑσ
... | ⟨ L′ , ⟨ σL—↠f , ≈-const L′≡ ⟩ ⟩
    rewrite L′≡ 
    with ⇓→—↠×≈{σ = σ} wfM M⇓k γ≈ₑσ
... | ⟨ M′ , ⟨ σM—↠M′ , ≈-const M′≡ ⟩ ⟩
    rewrite M′≡ =
    ⟨ $ P (f k) , ⟨ r , ≈-const refl ⟩ ⟩
    where
    r = (⟪ σ ⟫ L) · (⟪ σ ⟫ M)
        —↠⟨ appL-cong σL—↠f  ⟩
        ($ (B ⇒ P) f) · (⟪ σ ⟫ M)
        —↠⟨ appR-cong V-lit σM—↠M′ ⟩
        ($ (B ⇒ P) f) · ($ (base B) k)
        —→⟨ δ-rule ⟩
        ($ P (f k))  □
⇓→—↠×≈ {γ} {σ = σ} {app ⦅ cons (ast L) (cons (ast M) nil) ⦆} {c}
    (WF-op (WF-cons (WF-ast wfL) (WF-cons (WF-ast wfM) WF-nil)) _)
    (⇓-app {Γ}{δ = δ}{N}{V}{V′} L⇓ƛNδ M⇓V N⇓V′) γ≈ₑσ
    with ⇓→—↠×≈{σ = σ} wfL L⇓ƛNδ γ≈ₑσ
... | ⟨ L′ , ⟨ σL—↠ƛτN , ≈-clos {σ = τ}{wf = wfN} δ≈ₑτ L′≡ ⟩ ⟩
    rewrite L′≡
    with ⇓→—↠×≈{σ = σ} wfM M⇓V γ≈ₑσ
... | ⟨ M′ , ⟨ σM—↠M′ , V≈M′ ⟩ ⟩ 
    with ⇓→—↠×≈ {σ = M′ • τ} wfN N⇓V′ (≈ₑ-ext δ≈ₑτ V≈M′)
       | β-rule {⟪ ext τ ⟫ N}{M′} (≈→TermValue V≈M′)
... | ⟨ N′ , ⟨ —↠N′ , c≈N′ ⟩ ⟩ | ƛτN·σM—→ 
    rewrite ISWIM.ASTMod.sub-sub{M = N}{σ₁ = ext τ}{σ₂ = subst-zero M′} 
    | sym (subst-zero-exts-cons {τ}{M′}) =
    ⟨ N′ , ⟨ r , c≈N′ ⟩ ⟩
    where
    r = (⟪ σ ⟫ L) · (⟪ σ ⟫ M)                —↠⟨ appL-cong σL—↠ƛτN ⟩
        (ƛ (⟪ ext τ ⟫ N)) · (⟪ σ ⟫ M)       —↠⟨ appR-cong V-ƛ σM—↠M′ ⟩
        (ƛ (⟪ ext τ ⟫ N)) · M′              —→⟨ ƛτN·σM—→ ⟩
        ⟪ ext τ ⨟ M′ • id ⟫ N               —↠⟨ —↠N′ ⟩
        N′ □

⇓→—↠ :  ∀{M : Term}{c : Val} {wfM : WF 0 M}
     → ∅' ⊢ M ⇓ c
       -----------------------------------------
     → Σ[ N ∈ Term ] TermValue N × (M —↠ N)
⇓→—↠ {M} {c} {wfM} M⇓c
    with ⇓→—↠×≈{σ = id} wfM M⇓c ≈ₑ-id
... | ⟨ N , ⟨ rs , c≈N ⟩ ⟩
    rewrite ISWIM.ASTMod.sub-id{M = M} =
    ⟨ N , ⟨ (≈→TermValue c≈N) , rs ⟩ ⟩

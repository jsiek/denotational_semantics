{-# OPTIONS --allow-unsolved-metas #-}

module GraphModel.ISWIM where
{-

 The source language of the compiler

-}

open import Utilities using (_iff_)
open import Primitives
open import ScopedTuple hiding (𝒫)
open import NewSigUtil
open import NewDOpSig
open import Utilities using (extensionality)
open import SetsAsPredicates
open import GraphModel.Domain
open import GraphModel.DOp
open import NewDenotProperties
open import Syntax using (Sig; ext; ∁; ν; ■; Var; _•_; ↑; id; _⨟_) public

open import Data.Empty renaming (⊥ to Bot)
open import Data.Nat using (ℕ; zero; suc; _+_; _<_)
open import Data.Nat.Properties using (+-suc)
open import Data.List using (List; []; _∷_; replicate)
open import Data.Product
   using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Unit using (⊤; tt)
open import Level renaming (zero to lzero; suc to lsuc)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; sym; cong; cong₂; cong-app)
open Eq.≡-Reasoning

{- Syntax ---------------------------------------------------------------------}

data Op : Set where
  lam : Op
  app : Op
  lit : (B : Base) → (k : base-rep B) → Op
  tuple : (n : ℕ) → Op
  get : (n : ℕ) → Op
  inl-op : Op
  inr-op : Op
  case-op : Op

sig : Op → List Sig
sig lam = (ν ■) ∷ []
sig app = ■ ∷ ■ ∷ []
sig (lit B k) = []
sig (tuple n) = replicate n ■
sig (get i) = ■ ∷ []
sig inl-op = ■ ∷ []
sig inr-op = ■ ∷ []
sig case-op = ■ ∷ ν ■ ∷ ν ■ ∷ []



module ASTMod = Syntax.OpSig Op sig
open ASTMod using (`_; _⦅_⦆; Subst; Ctx; plug; rename; 
                   ⟪_⟫; _[_]; subst-zero; clear; bind; ast; cons; nil;
                   Arg; Args;
                   rename-id; exts-cons-shift; WF; WF-Ctx; ctx-depth;
                   WF-op; WF-cons; WF-nil; WF-ast; WF-bind; WF-var;
                   COp; CAst; CBind; ccons; tcons; append₊)
            renaming (ABT to AST) public


open import Fold2 Op sig

𝕆-ISWIM : DOpSig (𝒫 Value) sig
𝕆-ISWIM lam = Λ
𝕆-ISWIM app = ⋆
𝕆-ISWIM (lit B k) = ℬ B k
𝕆-ISWIM (tuple n) = 𝒯 n
𝕆-ISWIM (get n) = proj n
𝕆-ISWIM inl-op = ℒ
𝕆-ISWIM inr-op = ℛ
𝕆-ISWIM case-op = 𝒞-new

𝕆-ISWIM-mono : 𝕆-monotone sig 𝕆-ISWIM
𝕆-ISWIM-mono lam = Λ-mono
𝕆-ISWIM-mono app = ⋆-mono
𝕆-ISWIM-mono (lit B k) _ _ _ = lift (λ x x₁ → x₁)
𝕆-ISWIM-mono (tuple n) = 𝒯-mono n
𝕆-ISWIM-mono (get n) = proj-mono n
𝕆-ISWIM-mono inl-op = ℒ-mono
𝕆-ISWIM-mono inr-op = ℛ-mono
𝕆-ISWIM-mono case-op = 𝒞-new-mono

𝕆-ISWIM-consis : 𝕆-consistent _~_ sig 𝕆-ISWIM
𝕆-ISWIM-consis lam = Λ-consis
𝕆-ISWIM-consis app = ⋆-consis
𝕆-ISWIM-consis (lit B k) = ℬ-consis B k
𝕆-ISWIM-consis (tuple n) = 𝒯-consis n
𝕆-ISWIM-consis (get n) = proj-consis n
𝕆-ISWIM-consis inl-op = ℒ-consis
𝕆-ISWIM-consis inr-op = ℛ-consis
𝕆-ISWIM-consis case-op = 𝒞-new-consis

{-

interp-op1  : (op : Op) → Tuple (sig op) (Result (𝒫 Value)) → 𝒫 Value
interp-op1 (clos-op n) ⟨ F , Ds ⟩ =
    (Λ λ X → Λ′ (𝒯 n Ds) λ Y → F X Y) ▪ (𝒯 n Ds)
interp-op1 app ⟨ D₁ , ⟨ D₂ , _ ⟩ ⟩ = D₁ ▪ D₂
interp-op1 (lit B k) _ = ℬ B k
interp-op1 pair-op ⟨ D₁ , ⟨ D₂ , _ ⟩ ⟩ = 〘 D₁ , D₂ 〙
interp-op1 fst-op ⟨ D , _ ⟩  = car D
interp-op1 snd-op ⟨ D , _ ⟩ = cdr D
interp-op1 (tuple n) results = 𝒯 n results
interp-op1 (get i) ⟨ D , _ ⟩ = proj D i
interp-op1 inl-op ⟨ D , _ ⟩ = ℒ D
interp-op1 inr-op ⟨ D , _ ⟩ = ℛ D
interp-op1 case-op ⟨ D , ⟨ E , ⟨ F , _ ⟩ ⟩ ⟩ = 𝒞 D (Λ E) (Λ F)


Term : Set
Term = AST

pattern clos n N fvs = (clos-op n) ⦅ cons (clear (bind (bind (ast N)))) fvs ⦆

infixl 7  _·_
pattern _·_ L M = app ⦅ cons (ast L) (cons (ast M) nil) ⦆

pattern $ B k = lit B k ⦅ nil ⦆

pattern pair L M = pair-op ⦅ cons (ast L) (cons (ast M) nil) ⦆
pattern fst M = fst-op ⦅ cons (ast M) nil ⦆
pattern snd M = snd-op ⦅ cons (ast M) nil ⦆

pattern _❲_❳ M i = (get i) ⦅ cons (ast M) nil ⦆

pattern inl M = inl-op ⦅ cons (ast M) nil ⦆
pattern inr M = inr-op ⦅ cons (ast M) nil ⦆
pattern case L M N = case-op ⦅ cons (ast L) (cons (bind (ast M)) (cons (bind (ast N)) nil)) ⦆





mono-op1 : {op : Op} {xs ys : Tuple (sig op) (Result (𝒫 Value))}
   → ⊆-results (sig op) xs ys → interp-op1 op xs ⊆ interp-op1 op ys
mono-op1 {clos-op n} {⟨ f , fvs₁ ⟩ } {⟨ g , fvs₂ ⟩} ⟨ f⊆g , fvs⊆ ⟩ = {!!}
{-
    ▪-mono-⊆ (Λ-ext-⊆ λ {X} → Λ-ext-⊆ λ {Y} → lower (f⊆g X Y))
             (𝒯-mono-⊆ (rel-results⇒rel-∏ ⊆-result⇒⊆ fvs⊆)) 
-}
mono-op1 {app} {⟨ a , ⟨ b , _ ⟩ ⟩} {⟨ c , ⟨ d , _ ⟩ ⟩} ⟨ a<c , ⟨ b<d , _ ⟩ ⟩ =
    ▪-mono-⊆ (lower a<c) (lower b<d)
mono-op1 {lit P k} {xs} {ys} xs⊆ys d d∈k = d∈k
mono-op1 {pair-op} {⟨ D₁ , ⟨ D₂ , _ ⟩ ⟩} {⟨ E₁ , ⟨ E₂ , _ ⟩ ⟩}
    ⟨ lift D₁⊆E₁ , ⟨ lift D₂⊆E₂ , _ ⟩ ⟩ = cons-mono-⊆ D₁⊆E₁ D₂⊆E₂
mono-op1 {fst-op} {⟨ D , _ ⟩} {⟨ E , _ ⟩} ⟨ lift D⊆E , _ ⟩ = car-mono-⊆ D⊆E 
mono-op1 {snd-op} {⟨ D , _ ⟩} {⟨ E , _ ⟩} ⟨ lift D⊆E , _ ⟩ = cdr-mono-⊆ D⊆E 
mono-op1 {tuple n} {args₁}{args₂} IHs =
    𝒯-mono-⊆ (rel-results⇒rel-∏ ⊆-result⇒⊆ IHs)
mono-op1 {get i} {⟨ D , _ ⟩} {⟨ E , _ ⟩} ⟨ lift D⊆E , _ ⟩ = proj-mono-⊆ D⊆E
mono-op1 {inl-op} {⟨ D , _ ⟩} {⟨ E , _ ⟩} ⟨ lift D⊆E , _ ⟩ = ℒ-mono-⊆ D⊆E
mono-op1 {inr-op} {⟨ D , _ ⟩} {⟨ E , _ ⟩} ⟨ lift D⊆E , _ ⟩ = ℛ-mono-⊆ D⊆E
mono-op1 {case-op} {⟨ D₁ , ⟨ f₁ , ⟨ g₁ , _ ⟩ ⟩ ⟩}
                  {⟨ D₂ , ⟨ f₂ , ⟨ g₂ , _ ⟩ ⟩ ⟩}
                  ⟨ lift D₁⊆D₂ , ⟨ f₁⊆f₂ , ⟨ g₁⊆g₂ , _ ⟩ ⟩ ⟩ =
    𝒞-mono-⊆ D₁⊆D₂ (λ X → lower (f₁⊆f₂ X)) (λ X → lower (g₁⊆g₂ X))

instance
  ISWIMClos-Semantics : Semantics
  ISWIMClos-Semantics = record { interp-op = interp-op1 ;
                                 mono-op = λ {op} → mono-op1 {op} }
open Semantics {{...}} public

⟦⟧-clos : ∀{n}{N : Term}{fvs : Args (replicate n ■)}{ρ : Env}
  → ⟦ clos n N fvs ⟧ ρ ≡
         (Λ λ D → Λ′ (𝒯 n (⟦ fvs ⟧₊ ρ)) λ E → ⟦ N ⟧ (E • D • (λ x → init)))
             ▪ (𝒯 n (⟦ fvs ⟧₊ ρ))
⟦⟧-clos = refl

cont-op2 : ∀{op}{ρ}{NE-ρ}{v}{args}
   → v ∈ ⟦ op ⦅ args ⦆ ⟧ ρ
   → all-args (Cont-Env-Arg ρ NE-ρ) (sig op) args
   → Σ[ ρ′ ∈ Env ] finite-env ρ′ × ρ′ ⊆ₑ ρ × v ∈ (⟦ op ⦅ args ⦆ ⟧ ρ′)
cont-op2 {clos-op n} {ρ} {NE-ρ} {v}
    {cons (clear (bind (bind (ast N)))) fvs}
    ⟨ V , ⟨ FVS , ⟨ ⟨ v∈ΛN , V≢[] ⟩ , ⟨ V⊆𝒯fvs , _ ⟩ ⟩ ⟩ ⟩
    ⟨ IH-N , IH-fvs ⟩
    with continuous-∈⇒⊆ (λ ρ → 𝒯 n (⟦ fvs ⟧₊ ρ)) ρ NE-ρ
            (⟦⟧-monotone (tuple n ⦅ fvs ⦆)) V V⊆𝒯fvs
            (λ u _ u∈ → (all-Cont-Env-Arg⇒cont-envs{NE-ρ = NE-ρ} IH-fvs) u u∈)
... | ⟨ ρ′ , ⟨ fρ′ , ⟨ ρ′⊆ρ , V⊆𝒯fvsρ′ ⟩ ⟩ ⟩ =
    {!!}
    {-
    ⟨ ρ′ , ⟨ fρ′ , ⟨ ρ′⊆ρ ,
    ⟨ V , ⟨ FVS , ⟨ ⟨ v∈ΛN , V≢[] ⟩ , ⟨ V⊆𝒯fvsρ′ , V≢[] ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
    -}
cont-op2 {app} {ρ} {NE-ρ} {w} {cons (ast L) (cons (ast M) nil)}
    w∈⟦L·M⟧ρ ⟨ IH-L , ⟨ IH-M , _ ⟩ ⟩ =
    ▪-continuous{NE-ρ = NE-ρ} w∈⟦L·M⟧ρ IH-L IH-M (⟦⟧-monotone L) (⟦⟧-monotone M)
cont-op2 {lit p x} {ρ} {NE-ρ} {v} {nil} v∈⟦M⟧ρ _ =
    ⟨ initial-finite-env ρ NE-ρ , ⟨ initial-fin ρ NE-ρ ,
    ⟨ initial-fin-⊆ ρ NE-ρ ,
      v∈⟦M⟧ρ ⟩ ⟩ ⟩
cont-op2 {pair-op}{ρ}{NE-ρ}{v}{cons (ast M) (cons (ast N) nil)} v∈⟦M⟧ρ
    ⟨ IH-M , ⟨ IH-N , _ ⟩ ⟩ =
    cons-continuous{NE-ρ = NE-ρ} v∈⟦M⟧ρ IH-M IH-N
        (⟦⟧-monotone M) (⟦⟧-monotone N)
cont-op2 {fst-op} {ρ} {NE-ρ} {v} {cons (ast M) nil} v∈⟦M⟧ρ
    ⟨ IH-M , _ ⟩ =
    car-continuous{NE-ρ = NE-ρ} v∈⟦M⟧ρ IH-M (⟦⟧-monotone M)
cont-op2 {snd-op} {ρ} {NE-ρ} {v} {cons (ast M) nil} v∈⟦M⟧ρ
    ⟨ IH-M , _ ⟩ =
    cdr-continuous{NE-ρ = NE-ρ} v∈⟦M⟧ρ IH-M (⟦⟧-monotone M)
cont-op2 {tuple n} {ρ} {NE-ρ} {v} {args} v∈⟦M⟧ρ cont-args =
   𝒯-continuous{NE-ρ = NE-ρ} v∈⟦M⟧ρ
       (all-Cont-Env-Arg⇒cont-envs{NE-ρ = NE-ρ} cont-args)
       (⟦⟧-monotone-args args)
cont-op2 {get i} {ρ} {NE-ρ} {v} {cons (ast M) nil} v∈⟦M⟧ρ ⟨ cM , _ ⟩ =
    proj-continuous{NE-ρ = NE-ρ} v∈⟦M⟧ρ cM (⟦⟧-monotone M)
cont-op2 {inl-op}{ρ}{NE-ρ}{v}{cons (ast M) nil} v∈ ⟨ cM , _ ⟩ =
    ℒ-continuous{NE-ρ = NE-ρ} v∈ cM (⟦⟧-monotone M)
cont-op2 {inr-op}{ρ}{NE-ρ}{v}{cons (ast M) nil} v∈ ⟨ cM , _ ⟩ =
    ℛ-continuous{NE-ρ = NE-ρ} v∈ cM (⟦⟧-monotone M)
cont-op2 {case-op}{ρ}{NE-ρ}{v}
    {cons (ast L) (cons (bind (ast M)) (cons (bind (ast N)) nil))}
    v∈ ⟨ IH-L , ⟨ IH-M , ⟨ IH-N , _ ⟩ ⟩ ⟩ =
   𝒞-continuous{NE-ρ = NE-ρ} v∈ IH-L (⟦⟧-monotone L) IH-M (⟦⟧-monotone M)
       IH-N (⟦⟧-monotone N)

instance
  ISWIM-Continuous : ContinuousSemantics
  ISWIM-Continuous = record { continuous-op =
      λ{op}{ρ}{NE-ρ} → cont-op2{op}{ρ}{NE-ρ} }
open ContinuousSemantics {{...}} public
-}
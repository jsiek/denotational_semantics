{-# OPTIONS --allow-unsolved-metas #-}

module NewClos3 where
{-
 This intermediate semantics uses a single binding 
   that accepts a tuple which is unpacked later.
 This semantics is after the 'concretize/uncurry' pass,
   and before the 'delay' pass.
-}

open import Utilities using (_iff_)
open import Primitives
open import ScopedTuple hiding (𝒫)
open import NewSigUtil
open import NewResultsCurried
open import Utilities using (extensionality)
open import SetsAsPredicates
open import NewPValueCBVAnnot
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
  clos-op : ℕ → Op
  app : Op
  prim : (P : Prim) → rep P → Op
  pair-op : Op
  fst-op : Op
  snd-op : Op
  tuple : ℕ → Op
  get : ℕ → Op
  inl-op : Op
  inr-op : Op
  case-op : Op

sig : Op → List Sig
sig (clos-op n) = ∁ (ν (ν ■)) ∷ (replicate n ■)
sig app = ■ ∷ ■ ∷ []
sig (prim P f) = []
sig pair-op = ■ ∷ ■ ∷ []
sig fst-op = ■ ∷ []
sig snd-op = ■ ∷ []
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


𝕆-Clos3 : DenotOps (𝒫 Value) sig
𝕆-Clos3 (clos-op n) 𝒻 = 
  DComp-rest (replicate n ■) ■ ■ (𝒯 n) (λ T → 𝒜 n (Λ (𝒻 T)))
𝕆-Clos3 app = _⋆_
𝕆-Clos3 (prim P f) = 𝓅 P f
𝕆-Clos3 pair-op = ⟪_,_⟫
𝕆-Clos3 fst-op = car
𝕆-Clos3 snd-op = cdr
𝕆-Clos3 (tuple n) = 𝒯 n
𝕆-Clos3 (get i) = proj i
𝕆-Clos3 inl-op = ℒ
𝕆-Clos3 inr-op = ℛ
𝕆-Clos3 case-op = 𝒞-new

𝕆-Clos3-mono : 𝕆-monotone sig 𝕆-Clos3
𝕆-Clos3-mono (clos-op x) F1 F2 F~ = 
  DComp-rest-pres _⊆_ (replicate x ■) ■ ■ (𝒯 x) (𝒯 x) 
                  (λ T → 𝒜 x (Λ (F1 T))) (λ T → 𝒜 x (Λ (F2 T))) 
                  (𝒯-mono x) 
                  (λ T T' T⊆ → 𝒜-mono x (Λ (F1 T)) (Λ (F2 T')) 
                               (Λ-mono (F1 T) (F2 T') (F~ T T' (lower T⊆))))
𝕆-Clos3-mono app = ⋆-mono
𝕆-Clos3-mono (prim P x) = lift λ d x → x
𝕆-Clos3-mono pair-op = cons-mono
𝕆-Clos3-mono fst-op = car-mono
𝕆-Clos3-mono snd-op = cdr-mono
𝕆-Clos3-mono (tuple x) = 𝒯-mono x
𝕆-Clos3-mono (get x) = proj-mono x
𝕆-Clos3-mono inl-op = ℒ-mono
𝕆-Clos3-mono inr-op = ℛ-mono
𝕆-Clos3-mono case-op = 𝒞-new-mono

𝕆-Clos3-consis : 𝕆-consistent _~_ sig 𝕆-Clos3
𝕆-Clos3-consis (clos-op x) F1 F2 F~ = 
  DComp-rest-pres (Every _~_) (replicate x ■) ■ ■ (𝒯 x) (𝒯 x) 
                  (λ T → 𝒜 x (Λ (F1 T))) ((λ T → 𝒜 x (Λ (F2 T)))) 
  (𝒯-consis x) (λ T T' T~ → 𝒜-consis x (Λ (F1 T)) (Λ (F2 T')) 
                            (Λ-consis (F1 T) (F2 T') (F~ T T' (lower T~))))
𝕆-Clos3-consis app = ⋆-consis
𝕆-Clos3-consis (prim P x) = 𝓅-consis P x
𝕆-Clos3-consis pair-op = cons-consis
𝕆-Clos3-consis fst-op = car-consis
𝕆-Clos3-consis snd-op = cdr-consis
𝕆-Clos3-consis (tuple x) = 𝒯-consis x
𝕆-Clos3-consis (get x) = proj-consis x
𝕆-Clos3-consis inl-op = ℒ-consis
𝕆-Clos3-consis inr-op = ℛ-consis
𝕆-Clos3-consis case-op = 𝒞-new-consis


open import Fold2 Op sig
open import NewSemanticProperties Op sig


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
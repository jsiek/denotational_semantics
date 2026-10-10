module NewClos4Single where
{-

 In this intermediate semantics all functions take two parameters,
   so application have two operands and
 This semantics is after the 'delay' pass,
   and before the 'globalize' pass.

-}

open import Utilities using (_iff_)
open import Primitives
open import ScopedTuple hiding (𝒫)
open import NewSigUtil
open import NewDOpSig
open import Utilities using (extensionality)
open import SetsAsPredicates
open import NewDenotProperties
open import NewDomainSingleAnnPair
open import NewDOpSingleAnnPair
open import Syntax using (Sig; ext; ∁; ν; ■; Var; _•_; ↑; id; _⨟_) public

open import Data.Empty renaming (⊥ to Bot)
open import Data.Nat using (ℕ; zero; suc; _+_; _<_)
open import Data.Nat.Properties using (+-suc)
open import Data.List using (List; []; _∷_; replicate)
open import Data.Product
   using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Unit using (⊤; tt)
open import Data.Unit.Polymorphic using () renaming (tt to ptt; ⊤ to pTrue)
open import Level renaming (zero to lzero; suc to lsuc)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; sym; cong; cong₂; cong-app)
open Eq.≡-Reasoning

{- Syntax ---------------------------------------------------------------------}

data Op : Set where
  fun-op : Op
  app : Op
  lit : (B : Base) → (k : base-rep B) → Op
  pair-op : Op
  fst-op : Op
  snd-op : Op
  tuple : ℕ → Op
  get : ℕ → Op
  inl-op : Op
  inr-op : Op
  case-op : Op

sig : Op → List Sig
sig fun-op = ∁ (ν (ν ■)) ∷ []
sig app = ■ ∷ ■ ∷ ■ ∷ []
sig (lit B k) = []
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

𝕆-Clos4 : DOpSig (𝒫 Value) sig
𝕆-Clos4 fun-op ⟨ F , _ ⟩ = Λ ⟨ (λ X → Λ ⟨ (λ Y → F X Y) , ptt ⟩) , ptt ⟩
𝕆-Clos4 app ⟨ L , ⟨ M , ⟨ N , _ ⟩ ⟩ ⟩ = ⋆ ⟨ ⋆ ⟨ L , ⟨ M , ptt ⟩ ⟩ , ⟨ N , ptt ⟩ ⟩
𝕆-Clos4 (lit B k) = ℬ B k
𝕆-Clos4 pair-op = pair
𝕆-Clos4 fst-op = car
𝕆-Clos4 snd-op = cdr
𝕆-Clos4 (tuple x) = 𝒯 x
𝕆-Clos4 (get x) = proj x
𝕆-Clos4 inl-op = ℒ
𝕆-Clos4 inr-op = ℛ
𝕆-Clos4 case-op = 𝒞

𝕆-Clos4-mono : 𝕆-monotone sig 𝕆-Clos4
𝕆-Clos4-mono fun-op ⟨ F1 , _ ⟩ ⟨ F2 , _ ⟩  ⟨ F~ , _ ⟩ = 
  Λ-mono ⟨ (λ X → Λ ⟨ (F1 X) , ptt ⟩) , ptt ⟩ ⟨ (λ X → Λ ⟨ (F2 X) , ptt ⟩) , ptt ⟩
         ⟨ (λ X1 X2 X~ → Λ-mono ⟨ (F1 X1) , ptt ⟩ ⟨ (F2 X2) , ptt ⟩ 
                                ⟨ (F~ X1 X2 X~) , ptt ⟩) , ptt ⟩
𝕆-Clos4-mono app ⟨ L1 , ⟨ M1 , ⟨ N1 , _ ⟩ ⟩ ⟩ 
                 ⟨ L2 , ⟨ M2 , ⟨ N2 , _ ⟩ ⟩ ⟩ ⟨ L~ , ⟨ M~ , ⟨ N~ , _ ⟩ ⟩ ⟩ = 
  ⋆-mono ⟨ ⋆ ⟨ L1 , ⟨ M1 , ptt ⟩ ⟩ , ⟨ N1 , ptt ⟩ ⟩
         ⟨ ⋆ ⟨ L2 , ⟨ M2 , ptt ⟩ ⟩ , ⟨ N2 , ptt ⟩ ⟩
         ⟨ ⋆-mono ⟨ L1 , ⟨ M1 , ptt ⟩ ⟩ ⟨ L2 , ⟨ M2 , ptt ⟩ ⟩  ⟨ L~ , ⟨ M~ , ptt ⟩ ⟩ 
         , ⟨ N~ , ptt ⟩ ⟩
𝕆-Clos4-mono (lit B k) _ _ _ = lift (λ d d∈ → d∈)
𝕆-Clos4-mono pair-op = pair-mono
𝕆-Clos4-mono fst-op = car-mono
𝕆-Clos4-mono snd-op = cdr-mono
𝕆-Clos4-mono (tuple x) = 𝒯-mono x
𝕆-Clos4-mono (get x) = proj-mono x
𝕆-Clos4-mono inl-op = ℒ-mono
𝕆-Clos4-mono inr-op = ℛ-mono
𝕆-Clos4-mono case-op = 𝒞-mono

𝕆-Clos4-consis : 𝕆-consistent _~_ sig 𝕆-Clos4
𝕆-Clos4-consis fun-op ⟨ F1 , _ ⟩ ⟨ F2 , _ ⟩  ⟨ F~ , _ ⟩ = 
  Λ-consis ⟨ (λ X → Λ ⟨ (F1 X) , ptt ⟩) , ptt ⟩ ⟨ (λ X → Λ ⟨ (F2 X) , ptt ⟩) , ptt ⟩
         ⟨ (λ X1 X2 X~ → Λ-consis ⟨ (F1 X1) , ptt ⟩ ⟨ (F2 X2) , ptt ⟩ 
                                ⟨ (F~ X1 X2 X~) , ptt ⟩) , ptt ⟩
𝕆-Clos4-consis app ⟨ L1 , ⟨ M1 , ⟨ N1 , _ ⟩ ⟩ ⟩ 
                 ⟨ L2 , ⟨ M2 , ⟨ N2 , _ ⟩ ⟩ ⟩ ⟨ L~ , ⟨ M~ , ⟨ N~ , _ ⟩ ⟩ ⟩ = 
  ⋆-consis ⟨ ⋆ ⟨ L1 , ⟨ M1 , ptt ⟩ ⟩ , ⟨ N1 , ptt ⟩ ⟩
         ⟨ ⋆ ⟨ L2 , ⟨ M2 , ptt ⟩ ⟩ , ⟨ N2 , ptt ⟩ ⟩
         ⟨ ⋆-consis ⟨ L1 , ⟨ M1 , ptt ⟩ ⟩ ⟨ L2 , ⟨ M2 , ptt ⟩ ⟩  ⟨ L~ , ⟨ M~ , ptt ⟩ ⟩ 
         , ⟨ N~ , ptt ⟩ ⟩
 {- DComp-pres (Every _~_) (■ ∷ ■ ∷ []) ■ (■ ∷ []) ■ _⋆_ _⋆_ _⋆_ _⋆_ ⋆-consis ⋆-consis -}
𝕆-Clos4-consis (lit B k) = ℬ-consis B k
𝕆-Clos4-consis pair-op = pair-consis
𝕆-Clos4-consis fst-op = car-consis
𝕆-Clos4-consis snd-op = cdr-consis
𝕆-Clos4-consis (tuple x) = 𝒯-consis x
𝕆-Clos4-consis (get x) = proj-consis x
𝕆-Clos4-consis inl-op = ℒ-consis
𝕆-Clos4-consis inr-op = ℛ-consis
𝕆-Clos4-consis case-op = 𝒞-consis


open import Fold2 Op sig
open import NewSemantics Op sig public

instance
  Clos4-Semantics : Semantics
  Clos4-Semantics = record { interp-op = 𝕆-Clos4 ;
                                  mono-op = 𝕆-Clos4-mono ;
                                  error = ω }
open Semantics {{...}} public



{-

interp-op2  : (op : Op) → Tuple (sig op) (Result (𝒫 Value)) → 𝒫 Value
interp-op2 fun-op ⟨ F , _ ⟩ = Λ λ X → Λ λ Y → F X Y
interp-op2 app ⟨ D₁ , ⟨ D₂ , ⟨ D₃ , _ ⟩ ⟩ ⟩ = (D₁ ▪ D₂) ▪ D₃
interp-op2 (lit B k) _ = ℬ B k
interp-op2 pair-op ⟨ D₁ , ⟨ D₂ , _ ⟩ ⟩ = 〘 D₁ , D₂ 〙
interp-op2 fst-op ⟨ D , _ ⟩  = car D
interp-op2 snd-op ⟨ D , _ ⟩ = cdr D
interp-op2 (tuple n) results = 𝒯 n results
interp-op2 (get i) ⟨ D , _ ⟩ = proj D i
interp-op2 inl-op ⟨ D , _ ⟩ = ℒ D
interp-op2 inr-op ⟨ D , _ ⟩ = ℛ D
interp-op2 case-op ⟨ D , ⟨ E , ⟨ F , _ ⟩ ⟩ ⟩ = 𝒞 D (Λ E) (Λ F)

Term : Set
Term = AST

pattern fun N = fun-op ⦅ cons (clear (bind (bind (ast N)))) nil ⦆

infixl 7  _⦉_,_⦊
pattern _⦉_,_⦊ L M N = app ⦅ cons (ast L) (cons (ast M) (cons (ast N) nil)) ⦆

pattern $ B k = lit B k ⦅ nil ⦆

pattern pair L M = pair-op ⦅ cons (ast L) (cons (ast M) nil) ⦆
pattern fst M = fst-op ⦅ cons (ast M) nil ⦆
pattern snd M = snd-op ⦅ cons (ast M) nil ⦆

pattern _❲_❳ M i = (get i) ⦅ cons (ast M) nil ⦆

pattern inl M = inl-op ⦅ cons (ast M) nil ⦆
pattern inr M = inr-op ⦅ cons (ast M) nil ⦆
pattern case L M N = case-op ⦅ cons (ast L) (cons (bind (ast M)) (cons (bind (ast N)) nil)) ⦆



interp-op2  : (op : Op) → Tuple (sig op) (Result (𝒫 Value)) → 𝒫 Value
interp-op2 fun-op ⟨ F , _ ⟩ = Λ λ X → Λ λ Y → F X Y
interp-op2 app ⟨ D₁ , ⟨ D₂ , ⟨ D₃ , _ ⟩ ⟩ ⟩ = (D₁ ▪ D₂) ▪ D₃
interp-op2 (lit B k) _ = ℬ B k
interp-op2 pair-op ⟨ D₁ , ⟨ D₂ , _ ⟩ ⟩ = 〘 D₁ , D₂ 〙
interp-op2 fst-op ⟨ D , _ ⟩  = car D
interp-op2 snd-op ⟨ D , _ ⟩ = cdr D
interp-op2 (tuple n) results = 𝒯 n results
interp-op2 (get i) ⟨ D , _ ⟩ = proj D i
interp-op2 inl-op ⟨ D , _ ⟩ = ℒ D
interp-op2 inr-op ⟨ D , _ ⟩ = ℛ D
interp-op2 case-op ⟨ D , ⟨ E , ⟨ F , _ ⟩ ⟩ ⟩ = 𝒞 D (Λ E) (Λ F)

mono-op2 : {op : Op} {xs ys : Tuple (sig op) (Result (𝒫 Value))}
   → ⊆-results (sig op) xs ys → interp-op2 op xs ⊆ interp-op2 op ys
mono-op2 {fun-op} {⟨ f , _ ⟩ } {⟨ g , _ ⟩} ⟨ f⊆g , _ ⟩ =
    Λ-ext-⊆ λ {X} → Λ-ext-⊆ λ {Y} → lower (f⊆g X Y)
mono-op2 {app} {⟨ a , ⟨ b , ⟨ c , _ ⟩ ⟩ ⟩} {⟨ x , ⟨ y , ⟨ z , _ ⟩ ⟩ ⟩}
    ⟨ a<x , ⟨ b<y , ⟨ c<z , _ ⟩ ⟩ ⟩ =
    ▪-mono-⊆ (▪-mono-⊆ (lower a<x) (lower b<y)) (lower c<z)
mono-op2 {lit B k} {xs} {ys} xs⊆ys d d∈k = d∈k
mono-op2 {pair-op} {⟨ D₁ , ⟨ D₂ , _ ⟩ ⟩} {⟨ E₁ , ⟨ E₂ , _ ⟩ ⟩}
    ⟨ lift D₁⊆E₁ , ⟨ lift D₂⊆E₂ , _ ⟩ ⟩ = cons-mono-⊆ D₁⊆E₁ D₂⊆E₂
mono-op2 {fst-op} {⟨ D , _ ⟩} {⟨ E , _ ⟩} ⟨ lift D⊆E , _ ⟩ = car-mono-⊆ D⊆E 
mono-op2 {snd-op} {⟨ D , _ ⟩} {⟨ E , _ ⟩} ⟨ lift D⊆E , _ ⟩ = cdr-mono-⊆ D⊆E 
mono-op2 {tuple n} {args₁}{args₂} IHs =
    𝒯-mono-⊆ (rel-results⇒rel-∏ ⊆-result⇒⊆ IHs)
mono-op2 {get i} {⟨ D , _ ⟩} {⟨ E , _ ⟩} ⟨ lift D⊆E , _ ⟩ = proj-mono-⊆ D⊆E
mono-op2 {inl-op} {⟨ D , _ ⟩} {⟨ E , _ ⟩} ⟨ lift D⊆E , _ ⟩ = ℒ-mono-⊆ D⊆E
mono-op2 {inr-op} {⟨ D , _ ⟩} {⟨ E , _ ⟩} ⟨ lift D⊆E , _ ⟩ = ℛ-mono-⊆ D⊆E
mono-op2 {case-op} {⟨ D₁ , ⟨ f₁ , ⟨ g₁ , _ ⟩ ⟩ ⟩}
                  {⟨ D₂ , ⟨ f₂ , ⟨ g₂ , _ ⟩ ⟩ ⟩}
                  ⟨ lift D₁⊆D₂ , ⟨ f₁⊆f₂ , ⟨ g₁⊆g₂ , _ ⟩ ⟩ ⟩ =
    𝒞-mono-⊆ D₁⊆D₂ (λ X → lower (f₁⊆f₂ X)) (λ X → lower (g₁⊆g₂ X))

instance
  ISWIMClos2-Semantics : Semantics
  ISWIMClos2-Semantics = record { interp-op = interp-op2 ;
                                  mono-op = λ {op} → mono-op2 {op} }
open Semantics {{...}} public

⟦⟧-fun : ∀{N : Term}{ρ : Env}
  → ⟦ fun N ⟧ ρ ≡ Λ λ D → Λ λ E → ⟦ N ⟧ (E • D • (λ x → init))
⟦⟧-fun = refl

⟦⟧-app : ∀{L M N : Term}{ρ : Env}{w : Value}
   → w ∈ ⟦ L ⦉ M , N ⦊ ⟧ ρ ≡ w ∈ ((⟦ L ⟧ ρ) ▪ (⟦ M ⟧ ρ)) ▪ (⟦ N ⟧ ρ)
⟦⟧-app = refl

cont-op2 : ∀{op}{ρ}{NE-ρ}{v}{args}
   → v ∈ ⟦ op ⦅ args ⦆ ⟧ ρ
   → all-args (Cont-Env-Arg ρ NE-ρ) (sig op) args
   → Σ[ ρ′ ∈ Env ] finite-env ρ′ × ρ′ ⊆ₑ ρ × v ∈ (⟦ op ⦅ args ⦆ ⟧ ρ′)
cont-op2 {fun-op} {ρ} {NE-ρ} {v} {cons (clear (bind (bind (ast N)))) nil}
    v∈⟦funN⟧ ⟨ IH-N , _ ⟩ =
    {- Wow, the lack of lexical scoping makes this case easy! -}
    ⟨ initial-finite-env ρ NE-ρ , ⟨ initial-fin ρ NE-ρ ,
    ⟨ initial-fin-⊆ ρ NE-ρ , v∈⟦funN⟧ ⟩ ⟩ ⟩
cont-op2 {app} {ρ} {NE-ρ} {w}
   {cons (ast L) (cons (ast M) (cons (ast N) nil))}
   ⟨ V , ⟨ FVS , ⟨ ⟨ V′ , ⟨ V′↦V↦w∈⟦L⟧ , ⟨ V′⊆⟦M⟧ , V′≢[] ⟩ ⟩ ⟩ ,
         ⟨ V⊆⟦N⟧ , V≢[] ⟩ ⟩ ⟩ ⟩
   ⟨ IH-L , ⟨ IH-M , ⟨ IH-N , _ ⟩ ⟩ ⟩ =
   ▪-continuous{λ ρ → ((⟦ L ⟧ ρ) ▪ (⟦ M ⟧ ρ))}{⟦ N ⟧}{ρ}{NE-ρ}
     ⟨ V , ⟨ FVS , ⟨ ⟨ V′ , ⟨ V′↦V↦w∈⟦L⟧ , ⟨ V′⊆⟦M⟧ , V′≢[] ⟩ ⟩ ⟩ ,
           ⟨ V⊆⟦N⟧ , V≢[] ⟩ ⟩ ⟩ ⟩
     (λ v v∈ → ▪-continuous {NE-ρ = NE-ρ} v∈ IH-L IH-M (⟦⟧-monotone L)
                            (⟦⟧-monotone M))
     IH-N
     (λ {ρ}{ρ′} ρ⊆ρ′ → ▪-mono-⊆ (⟦⟧-monotone{ρ = ρ}{ρ′} L ρ⊆ρ′)
                                (⟦⟧-monotone{ρ = ρ}{ρ′} M ρ⊆ρ′))
     (⟦⟧-monotone N)
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
  ISWIMClos2-Continuous : ContinuousSemantics
  ISWIMClos2-Continuous = record { continuous-op =
                λ{op}{ρ}{NE-ρ} → cont-op2{op}{ρ}{NE-ρ} }
open ContinuousSemantics {{...}} public


-}
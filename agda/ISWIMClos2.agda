module ISWIMClos2 where
{-

 The intermediate language after the delay pass of the compiler.
 It differs from ISWIM in that functions take two parameters and 
 functions are not lexically scoped.

-}

open import Utilities using (_iff_)
open import Primitives
open import ScopedTuple hiding (𝒫)
open import Sig
open import Utilities using (extensionality)
open import SetsAsPredicates
open import PValueCBV
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
  fun-op : Op
  app : Op
  lit : (p : Prim) → rep p → Op
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
sig (lit p k) = []
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
                   ⟪_⟫; _[_]; subst-zero; clear; bind; ast; cons; nil; Args;
                   rename-id; exts-cons-shift; WF; WF-Ctx; ctx-depth;
                   WF-op; WF-cons; WF-nil; WF-ast; WF-bind; WF-var;
                   COp; CAst; CBind; ccons; tcons; append₊)
            renaming (ABT to AST) public

Term : Set
Term = AST

pattern fun N = fun-op ⦅ cons (clear (bind (bind (ast N)))) nil ⦆

infixl 7  _⦉_,_⦊
pattern _⦉_,_⦊ L M N = app ⦅ cons (ast L) (cons (ast M) (cons (ast N) nil)) ⦆

pattern $ p k = lit p k ⦅ nil ⦆

pattern pair L M = pair-op ⦅ cons (ast L) (cons (ast M) nil) ⦆
pattern fst M = fst-op ⦅ cons (ast M) nil ⦆
pattern snd M = snd-op ⦅ cons (ast M) nil ⦆

pattern _❲_❳ M i = (get i) ⦅ cons (ast M) nil ⦆

pattern inl M = inl-op ⦅ cons (ast M) nil ⦆
pattern inr M = inr-op ⦅ cons (ast M) nil ⦆
pattern case L M N = case-op ⦅ cons (ast L) (cons (bind (ast M)) (cons (bind (ast N)) nil)) ⦆

open import Fold2 Op sig
open import SemanticProperties Op sig

interp-op  : (op : Op) → Tuple (sig op) (Result (𝒫 Value)) → 𝒫 Value
interp-op fun-op ⟨ F , _ ⟩ = Λ λ X → Λ λ Y → F X Y
interp-op app ⟨ D₁ , ⟨ D₂ , ⟨ D₃ , _ ⟩ ⟩ ⟩ = (D₁ ▪ D₂) ▪ D₃
interp-op (lit P k) _ = ℘ P k
interp-op pair-op ⟨ D₁ , ⟨ D₂ , _ ⟩ ⟩ = 〘 D₁ , D₂ 〙
interp-op fst-op ⟨ D , _ ⟩  = car D
interp-op snd-op ⟨ D , _ ⟩ = cdr D
interp-op (tuple n) results = 𝒯 n results
interp-op (get i) ⟨ D , _ ⟩ = proj D i
interp-op inl-op ⟨ D , _ ⟩ = ℒ D
interp-op inr-op ⟨ D , _ ⟩ = ℛ D
interp-op case-op ⟨ D , ⟨ E , ⟨ F , _ ⟩ ⟩ ⟩ = 𝒞 D (Λ E) (Λ F)

mono-op : {op : Op} {xs ys : Tuple (sig op) (Result (𝒫 Value))}
   → ⊆-results (sig op) xs ys → interp-op op xs ⊆ interp-op op ys
mono-op {fun-op} {⟨ f , _ ⟩ } {⟨ g , _ ⟩} ⟨ f⊆g , _ ⟩ =
    Λ-ext-⊆ λ {X} → Λ-ext-⊆ λ {Y} → lower (f⊆g X Y)
mono-op {app} {⟨ a , ⟨ b , ⟨ c , _ ⟩ ⟩ ⟩} {⟨ x , ⟨ y , ⟨ z , _ ⟩ ⟩ ⟩}
    ⟨ a<x , ⟨ b<y , ⟨ c<z , _ ⟩ ⟩ ⟩ =
    ▪-mono-⊆ (▪-mono-⊆ (lower a<x) (lower b<y)) (lower c<z)
mono-op {lit P k} {xs} {ys} xs⊆ys d d∈k = d∈k
mono-op {pair-op} {⟨ D₁ , ⟨ D₂ , _ ⟩ ⟩} {⟨ E₁ , ⟨ E₂ , _ ⟩ ⟩}
    ⟨ lift D₁⊆E₁ , ⟨ lift D₂⊆E₂ , _ ⟩ ⟩ = cons-mono-⊆ D₁⊆E₁ D₂⊆E₂
mono-op {fst-op} {⟨ D , _ ⟩} {⟨ E , _ ⟩} ⟨ lift D⊆E , _ ⟩ = car-mono-⊆ D⊆E 
mono-op {snd-op} {⟨ D , _ ⟩} {⟨ E , _ ⟩} ⟨ lift D⊆E , _ ⟩ = cdr-mono-⊆ D⊆E 
mono-op {tuple n} {args₁}{args₂} IHs =
    𝒯-mono-⊆ (rel-results⇒rel-∏ ⊆-result⇒⊆ IHs)
mono-op {get i} {⟨ D , _ ⟩} {⟨ E , _ ⟩} ⟨ lift D⊆E , _ ⟩ = proj-mono-⊆ D⊆E
mono-op {inl-op} {⟨ D , _ ⟩} {⟨ E , _ ⟩} ⟨ lift D⊆E , _ ⟩ = ℒ-mono-⊆ D⊆E
mono-op {inr-op} {⟨ D , _ ⟩} {⟨ E , _ ⟩} ⟨ lift D⊆E , _ ⟩ = ℛ-mono-⊆ D⊆E
mono-op {case-op} {⟨ D₁ , ⟨ f₁ , ⟨ g₁ , _ ⟩ ⟩ ⟩}
                  {⟨ D₂ , ⟨ f₂ , ⟨ g₂ , _ ⟩ ⟩ ⟩}
                  ⟨ lift D₁⊆D₂ , ⟨ f₁⊆f₂ , ⟨ g₁⊆g₂ , _ ⟩ ⟩ ⟩ =
    𝒞-mono-⊆ D₁⊆D₂ (λ X → lower (f₁⊆f₂ X)) (λ X → lower (g₁⊆g₂ X))

instance
  ISWIMClos-Semantics : Semantics
  ISWIMClos-Semantics = record { interp-op = interp-op ;
                                 mono-op = λ {op} → mono-op {op} }
open Semantics {{...}}

⟦⟧-fun : ∀{N : Term}{ρ : Env}
  → ⟦ fun N ⟧ ρ ≡ Λ λ D → Λ λ E → ⟦ N ⟧ (E • D • (λ x → init))
⟦⟧-fun = refl

⟦⟧-app : ∀{L M N : Term}{ρ : Env}{w : Value}
   → w ∈ ⟦ L ⦉ M , N ⦊ ⟧ ρ ≡ w ∈ ((⟦ L ⟧ ρ) ▪ (⟦ M ⟧ ρ)) ▪ (⟦ N ⟧ ρ)
⟦⟧-app = refl

continuous-op : ∀{op}{ρ}{NE-ρ}{v}{args}
   → v ∈ ⟦ op ⦅ args ⦆ ⟧ ρ
   → all-args (Cont-Env-Arg ρ NE-ρ) (sig op) args
   → Σ[ ρ′ ∈ Env ] finite-env ρ′ × ρ′ ⊆ₑ ρ × v ∈ (⟦ op ⦅ args ⦆ ⟧ ρ′)
continuous-op {fun-op} {ρ} {NE-ρ} {v} {cons (clear (bind (bind (ast N)))) nil}
    v∈⟦funN⟧ ⟨ IH-N , _ ⟩ =
    {- Wow, the lack of lexical scoping makes this case easy! -}
    ⟨ initial-finite-env ρ NE-ρ , ⟨ initial-fin ρ NE-ρ ,
    ⟨ initial-fin-⊆ ρ NE-ρ , v∈⟦funN⟧ ⟩ ⟩ ⟩
continuous-op {app} {ρ} {NE-ρ} {w}
   {cons (ast L) (cons (ast M) (cons (ast N) nil))}
   ⟨ V , ⟨ ⟨ V′ , ⟨ V′↦V↦w∈⟦L⟧ , ⟨ V′⊆⟦M⟧ , V′≢[] ⟩ ⟩ ⟩ , ⟨ V⊆⟦N⟧ , V≢[] ⟩ ⟩ ⟩
   ⟨ IH-L , ⟨ IH-M , ⟨ IH-N , _ ⟩ ⟩ ⟩ =

   ▪-continuous{λ ρ → ((⟦ L ⟧ ρ) ▪ (⟦ M ⟧ ρ))}{⟦ N ⟧}{ρ}{NE-ρ}
     ⟨ V , ⟨ ⟨ V′ , ⟨ V′↦V↦w∈⟦L⟧ , ⟨ V′⊆⟦M⟧ , V′≢[] ⟩ ⟩ ⟩ , ⟨ V⊆⟦N⟧ , V≢[] ⟩ ⟩ ⟩
     (λ v v∈ → ▪-continuous {!!} {!!} {!!} {!!} {!!})
     IH-N
     (λ {ρ}{ρ′} ρ⊆ρ′ →
         ▪-mono-⊆ (⟦⟧-monotone{ρ = ρ}{ρ′} L ρ⊆ρ′)
                  (⟦⟧-monotone{ρ = ρ}{ρ′} M ρ⊆ρ′))
     (⟦⟧-monotone N)
continuous-op {lit p x} {ρ} {NE-ρ} {v} {nil} v∈⟦M⟧ρ _ =
    ⟨ initial-finite-env ρ NE-ρ , ⟨ initial-fin ρ NE-ρ ,
    ⟨ initial-fin-⊆ ρ NE-ρ ,
      v∈⟦M⟧ρ ⟩ ⟩ ⟩
continuous-op {pair-op}{ρ}{NE-ρ}{v}{cons (ast M) (cons (ast N) nil)} v∈⟦M⟧ρ
    ⟨ IH-M , ⟨ IH-N , _ ⟩ ⟩ =
    cons-continuous{NE-ρ = NE-ρ} v∈⟦M⟧ρ IH-M IH-N
        (⟦⟧-monotone M) (⟦⟧-monotone N)
continuous-op {fst-op} {ρ} {NE-ρ} {v} {cons (ast M) nil} v∈⟦M⟧ρ
    ⟨ IH-M , _ ⟩ =
    car-continuous{NE-ρ = NE-ρ} v∈⟦M⟧ρ IH-M (⟦⟧-monotone M)
continuous-op {snd-op} {ρ} {NE-ρ} {v} {cons (ast M) nil} v∈⟦M⟧ρ
    ⟨ IH-M , _ ⟩ =
    cdr-continuous{NE-ρ = NE-ρ} v∈⟦M⟧ρ IH-M (⟦⟧-monotone M)
continuous-op {tuple n} {ρ} {NE-ρ} {v} {args} v∈⟦M⟧ρ cont-args =
   𝒯-continuous{NE-ρ = NE-ρ} v∈⟦M⟧ρ
       (all-Cont-Env-Arg⇒cont-envs{NE-ρ = NE-ρ} cont-args)
       (⟦⟧-monotone-args args)
continuous-op {get i} {ρ} {NE-ρ} {v} {cons (ast M) nil} v∈⟦M⟧ρ ⟨ cM , _ ⟩ =
    proj-continuous{NE-ρ = NE-ρ} v∈⟦M⟧ρ cM (⟦⟧-monotone M)
continuous-op {inl-op}{ρ}{NE-ρ}{v}{cons (ast M) nil} v∈ ⟨ cM , _ ⟩ =
    ℒ-continuous{NE-ρ = NE-ρ} v∈ cM (⟦⟧-monotone M)
continuous-op {inr-op}{ρ}{NE-ρ}{v}{cons (ast M) nil} v∈ ⟨ cM , _ ⟩ =
    ℛ-continuous{NE-ρ = NE-ρ} v∈ cM (⟦⟧-monotone M)
continuous-op {case-op}{ρ}{NE-ρ}{v}
    {cons (ast L) (cons (bind (ast M)) (cons (bind (ast N)) nil))}
    v∈ ⟨ IH-L , ⟨ IH-M , ⟨ IH-N , _ ⟩ ⟩ ⟩ =
   𝒞-continuous{NE-ρ = NE-ρ} v∈ IH-L (⟦⟧-monotone L) IH-M (⟦⟧-monotone M)
       IH-N (⟦⟧-monotone N)

instance
  ISWIM-Continuous : ContinuousSemantics
  ISWIM-Continuous = record { continuous-op =
      λ{op}{ρ}{NE-ρ} → continuous-op{op}{ρ}{NE-ρ} }
open ContinuousSemantics {{...}}

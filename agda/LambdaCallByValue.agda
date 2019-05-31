{-

  Call-by-value Lambda Calculus

-}

module LambdaCallByValue where

open import Variables
open import Lambda
open Lambda.ASTMod
   using (`_; _⦅_⦆; Subst;
          exts; cons; bind; nil; rename; ⟪_⟫; subst-zero; _[_]; rename-id)
open import ValueBCD
open import Structures
open DomainAux domain
open OrderingAux domain ordering

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool  
open import Data.List using (List; []; _∷_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong; cong₂; cong-app)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)

data TermValue : ∀ {Γ} → Term Γ → Set where

  V-var : ∀ {Γ}{x : Var Γ}
      --------------------
    → TermValue {Γ} (` x)

  V-ƛ : ∀ {Γ} {N : Term (suc Γ)}
      -----------
    → TermValue (ƛ N)

infix 2 _—→_

data _—→_ : ∀ {Γ} → (Term Γ) → (Term Γ) → Set where

  ξ₁-rule : ∀ {Γ} {L L′ M : Term Γ}
    → L —→ L′
      ----------------
    → L · M —→ L′ · M

  ξ₂-rule : ∀ {Γ} {L M M′ : Term Γ}
    → TermValue L
    → M —→ M′
      ----------------
    → L · M —→ L · M′

  β-rule : ∀ {Γ} {N : Term (suc Γ)} {M : Term Γ}
    → TermValue M
      ---------------------------------
    → (ƛ N) · M —→ N [ M ]

infix  2 _—↠_
infixr 2 _—→⟨_⟩_
infix  3 _▩

data _—↠_ : ∀ {Γ} → (Term Γ) → (Term Γ) → Set where

  _▩ : ∀ {Γ} (M : Term Γ)
      --------
    → M —↠ M

  _—→⟨_⟩_ : ∀ {Γ} (L : Term Γ) {M N : Term Γ}
    → L —→ M
    → M —↠ N
      ---------
    → L —↠ N


infixl 7 _●_
_●_ : ∀{Γ} → Denotation Γ → Denotation Γ → Denotation Γ
_●_ {Γ} D₁ D₂ γ w = Σ[ v ∈ Value ] D₁ γ (v ↦ w) × D₂ γ v 

model : LambdaModel
model = record { _●_ = _●_ ; ℱ = ℱ }

●-≲ : ∀{Γ Δ}{γ : Env Γ}{δ : Env  Δ}{D₁ D₂ : Denotation Γ}
          {D₁′ D₂′ : Denotation Δ}
       → D₁ γ ≲ D₁′ δ  →  D₂ γ ≲ D₂′ δ
       → (D₁ ● D₂) γ ≲ (D₁′ ● D₂′) δ
●-≲ {γ = γ} {δ} {D₁} {D₂} {D₁′} {D₂′} D₁γ≲D₁′δ D₂γ≲D₂′δ {w}
    ⟨ v , ⟨ fst₁ , snd ⟩ ⟩
    with D₁γ≲D₁′δ {w} | D₂γ≲D₂′δ {w}
... | a | b = ⟨ v , ⟨ (D₁γ≲D₁′δ fst₁) , (D₂γ≲D₂′δ snd) ⟩ ⟩



●-⊔ : ∀{Γ}{D₁ D₂ : Denotation Γ}{γ : Env Γ} {u v : Value}
    → WFDenot Γ D₁ → WFDenot Γ D₂
    → (D₁ ● D₂) γ u → (D₁ ● D₂) γ v → (D₁ ● D₂) γ (u ⊔ v)
●-⊔ {Γ}{D₁}{D₂}{γ}{u}{v} wf1 wf2 ⟨ u' , ⟨ fst₁ , snd ⟩ ⟩
                    ⟨ v' , ⟨ fst₃ , snd₁ ⟩ ⟩ =
  let a = WFDenot.⊔-closed wf1 fst₁ fst₃ in                      
  ⟨ (u' ⊔ v') ,
  ⟨ WFDenot.⊑-closed wf1 a Dist⊔↦⊔ ,
    WFDenot.⊔-closed wf2 snd snd₁ ⟩ ⟩

●-⊑ : ∀{Γ}{D₁ D₂ : Denotation Γ} {γ : Env Γ} {v w : Value}
    → WFDenot Γ D₁ → (D₁ ● D₂) γ v → w ⊑ v
    → (D₁ ● D₂) γ w
●-⊑ {v = v}{w} d ⟨ v' , ⟨ fst₁ , snd ⟩ ⟩ w⊑v =
  ⟨ v' , ⟨ WFDenot.⊑-closed d fst₁ lt  , snd ⟩ ⟩
  where lt : v' ↦ w ⊑ v' ↦ v
        lt = ⊑-fun ⊑-refl w⊑v

model_basics : LambdaModelBasics model
model_basics = (record { ℱ-≲ = ℱ-≲ ;
               ●-≲ = λ {Γ}{Δ}{γ}{δ}{D₁}{D₂}{D₁′}{D₂′} x y →
                       ●-≲ {D₁ = D₁}{D₂ = D₂}{D₁′ = D₁′}{D₂′ = D₂′} x y;
               ℱ-⊑ = ℱ-⊑;
               ●-⊑ = λ {Γ}{D₁}{D₂} a b c → ●-⊑ {D₂ = D₂} a b c;
               ℱ-⊔ = λ {Γ}{D}{γ}{u}{v} → ℱ-⊔{D = D}{γ}{u}{v} ;
               ●-⊔ = ●-⊔
               })

open import RenamePreserveReflect domain ordering model model_basics
  using (⊑-env)  
open import Filter domain ordering model model_basics
open import SubstitutionPreserve domain ordering model model_basics

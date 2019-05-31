{- 

   ISWIM: the call-by-value lambda calculus with constants.

-}

module ISWIM where

open import Variables
open import Structures
open import Primitives

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool  
open import Data.List using (List; []; _∷_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong; cong₂; cong-app)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Data.Product
   using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Empty renaming (⊥ to Bot)
open import Data.Unit using (⊤; tt)


data Op : Set where
  lam : Op
  app : Op
  const : ∀{p : Prim} → rep p → Op

sig : Op → List Bool
sig lam = true ∷ []
sig app = false ∷ false ∷ []
sig (const {p} k) = []

import Syntax2
module ASTMod = Syntax2 Op sig
open ASTMod using (AST; `_; _⦅_⦆; Subst;
    rename; ⟪_⟫; _[_]; _•_; _⨟_; ↑;
    exts; exts-cons-shift; bind; cons; nil)

infixl 7  _·_

Term : ℕ → Set
Term Γ = AST Γ

ƛ : ∀{Γ} → Term (suc Γ) → Term Γ
ƛ N = lam ⦅ bind N nil ⦆

_·_ : ∀{Γ} → Term Γ → Term Γ → Term Γ
L · M = app ⦅ cons L (cons M nil) ⦆

$_ : ∀{Γ}{p : Prim} → rep p → Term Γ
$_ {Γ}{p} k = const {p} k ⦅ nil ⦆



data TermValue : ∀ {Γ} → Term Γ → Set where

  V-var : ∀ {Γ}{x : Var Γ}
      --------------------
    → TermValue {Γ} (` x)

  V-ƛ : ∀ {Γ} {N : Term (suc Γ)}
      -----------
    → TermValue (ƛ N)

  V-const : ∀ {Γ} {p : Prim} {k : rep p}
      ---------------------------
    → TermValue {Γ} ($_ {Γ}{p} k)

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

  δ-rule : ∀ {Γ}{B}{P} {f : base-rep B → rep P} {k : base-rep B}
      ------------------------------------------------------------
    → ($_ {Γ} {B ⇒ P} f) · ($_ {Γ}{base B} k) —→ ($_ {Γ}{P} (f k))

infix  2 _—↠_
infixr 2 _—→⟨_⟩_
infix  3 _□

data _—↠_ : ∀ {Γ} → (Term Γ) → (Term Γ) → Set where

  _□ : ∀ {Γ} (M : Term Γ)
      --------
    → M —↠ M

  _—→⟨_⟩_ : ∀ {Γ} (L : Term Γ) {M N : Term Γ}
    → L —→ M
    → M —↠ N
      ---------
    → L —↠ N


infixr 7 _↦_
infixl 5 _⊔_

data Value : Set where
  ⊥ : Value
  lit : {B : Base} → base-rep B → Value
  _↦_ : Value → Value → Value
  _⊔_ : Value → Value → Value

domain : Domain
domain = record { Value = Value ; ⊥ = ⊥ ; _↦_ = _↦_ ; _⊔_ = _⊔_ }

open DomainAux domain

ℱ : ∀{Γ} → Denotation (suc Γ) → Denotation Γ
ℱ D γ (v ↦ w) = D (γ `, v) w
ℱ D γ ⊥ = ⊤
ℱ D γ (lit k) = Bot
ℱ D γ (u ⊔ v) = (ℱ D γ u) × (ℱ D γ v)

ℱ-⊔ : ∀{Γ}{D : Denotation (suc Γ)}{γ : Env Γ} {u v : Value}
    → ℱ D γ u → ℱ D γ v → ℱ D γ (u ⊔ v)
ℱ-⊔ d1 d2 = ⟨ d1 , d2 ⟩

ℱ-⊥ : ∀{Γ}{D : Denotation (suc Γ)}{γ : Env Γ}
    → ℱ D γ ⊥
ℱ-⊥ = tt

ℱ-≲ : ∀{Γ Δ}{γ : Env Γ}{δ : Env Δ}{D : Denotation (suc Γ)}
          {D′ : Denotation (suc Δ)}
       → (∀{v : Value} → D (γ `, v) ≲ D′ (δ `, v))
       → ℱ D γ ≲ ℱ D′ δ
ℱ-≲ D≲D′ {⊥} = λ _ → tt
ℱ-≲ D≲D′ {lit k} = λ x → x
ℱ-≲ D≲D′ {v ↦ w} = D≲D′
ℱ-≲ {D = D}{D′} D≲D′ {u ⊔ v} ℱDγ
    with ℱ-≲{D = D}{D′} D≲D′ {u} | ℱ-≲{D = D}{D′} D≲D′ {v}
... | a | b =
    ⟨ (a (proj₁ ℱDγ)) , (b (proj₂ ℱDγ)) ⟩

cong-ℱ : ∀{Γ Δ}{γ : Env Γ}{δ : Env Δ}{D : Denotation (suc Γ)}
          {D′ : Denotation (suc Δ)}
       → (∀{v : Value} → D (γ `, v) ≃ D′ (δ `, v))
       → ℱ D γ ≃ ℱ D′ δ
cong-ℱ {D = D}{D′} D≃D′ {v} =
  ⟨ (ℱ-≲ (proj₁ D≃D′)) {v = v} , (ℱ-≲ (proj₂ D≃D′)) {v = v} ⟩

infix 4 _⊑_

data _⊑_ : Value → Value → Set where

  ⊑-⊥ : ∀ {v} → ⊥ ⊑ v

  ⊑-lit : ∀ {B}{k} → lit {B} k ⊑ lit {B} k

  ⊑-conj-L : ∀ {u v w}
      → v ⊑ u
      → w ⊑ u
        -----------
      → (v ⊔ w) ⊑ u

  ⊑-conj-R1 : ∀ {u v w}
     → u ⊑ v
       -----------
     → u ⊑ (v ⊔ w)

  ⊑-conj-R2 : ∀ {u v w}
     → u ⊑ w
       -----------
     → u ⊑ (v ⊔ w)

  ⊑-trans : ∀ {u v w}
     → u ⊑ v
     → v ⊑ w
       -----
     → u ⊑ w

  ⊑-fun : ∀ {v w v′ w′}
       → v′ ⊑ v
       → w ⊑ w′
         -------------------
       → (v ↦ w) ⊑ (v′ ↦ w′)

  ⊑-dist : ∀{v w w′}
         ---------------------------------
       → v ↦ (w ⊔ w′) ⊑ (v ↦ w) ⊔ (v ↦ w′)

⊑-refl : ∀ {v} → v ⊑ v
⊑-refl {⊥} = ⊑-⊥
⊑-refl {lit k} = ⊑-lit
⊑-refl {v ↦ v′} = ⊑-fun ⊑-refl ⊑-refl
⊑-refl {v₁ ⊔ v₂} = ⊑-conj-L (⊑-conj-R1 ⊑-refl) (⊑-conj-R2 ⊑-refl)

ordering : ValueOrdering domain
ordering = record
             { _⊑_ = _⊑_
             ; ⊑-⊥ = ⊑-⊥
             ; ⊑-conj-L = ⊑-conj-L
             ; ⊑-conj-R1 = ⊑-conj-R1
             ; ⊑-conj-R2 = ⊑-conj-R2
             ; ⊑-trans = ⊑-trans
             ; ⊑-fun = ⊑-fun
             ; ⊑-dist = ⊑-dist
             ; ⊑-refl = ⊑-refl
             }

open OrderingAux domain ordering

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

●-⊑ : ∀{Γ}{D₁ D₂ : Denotation Γ} {γ : Env Γ} {v w : Value}
    → WFDenot Γ D₁ → (D₁ ● D₂) γ v → w ⊑ v
    → (D₁ ● D₂) γ w
●-⊑ {v = v}{w} d ⟨ v' , ⟨ fst₁ , snd ⟩ ⟩ w⊑v =
  ⟨ v' , ⟨ WFDenot.⊑-closed d fst₁ lt  , snd ⟩ ⟩
  where lt : v' ↦ w ⊑ v' ↦ v
        lt = ⊑-fun ⊑-refl w⊑v

ℱ-⊑ : ∀{Γ}{D : Denotation (suc Γ)}{γ : Env Γ} {v w : Value}
       → WFDenot (suc Γ) D
       → ℱ D γ v → w ⊑ v → ℱ D γ w
ℱ-⊑ d ℱDγv ⊑-⊥ = tt
ℱ-⊑ d ℱDγv ⊑-lit = ℱDγv
ℱ-⊑ d ℱDγv (⊑-conj-L w⊑v w⊑v₁) = ⟨ (ℱ-⊑ d ℱDγv w⊑v) , (ℱ-⊑ d ℱDγv w⊑v₁) ⟩
ℱ-⊑ d ℱDγv (⊑-conj-R1 w⊑v) = ℱ-⊑ d (proj₁ ℱDγv) w⊑v
ℱ-⊑ d ℱDγv (⊑-conj-R2 w⊑v) = ℱ-⊑ d (proj₂ ℱDγv) w⊑v
ℱ-⊑ d ℱDγv (⊑-trans w⊑v w⊑v₁) = ℱ-⊑ d (ℱ-⊑ d ℱDγv w⊑v₁) w⊑v
ℱ-⊑ {Γ}{D}{γ}{v ↦ w}{v' ↦ w'} d ℱDγv (⊑-fun v⊑v' w'⊑w) =
  WFDenot.⊑-closed d (WFDenot.⊑-env d ℱDγv b) w'⊑w
  where b : (γ `, v) `⊑ (γ `, v')
        b Z = v⊑v'
        b (S x) = ⊑-refl 
ℱ-⊑ d ℱDγv ⊑-dist = WFDenot.⊔-closed d (proj₁ ℱDγv) (proj₂ ℱDγv)

●-⊔ : ∀{Γ}{D₁ D₂ : Denotation Γ}{γ : Env Γ} {u v : Value}
    → WFDenot Γ D₁ → WFDenot Γ D₂
    → (D₁ ● D₂) γ u → (D₁ ● D₂) γ v → (D₁ ● D₂) γ (u ⊔ v)
●-⊔ {Γ}{D₁}{D₂}{γ}{u}{v} wf1 wf2 ⟨ u' , ⟨ fst₁ , snd ⟩ ⟩
                                 ⟨ v' , ⟨ fst₃ , snd₁ ⟩ ⟩ =
  let a = WFDenot.⊔-closed wf1 fst₁ fst₃ in                      
  ⟨ (u' ⊔ v') ,
  ⟨ WFDenot.⊑-closed wf1 a Dist⊔↦⊔ ,
    WFDenot.⊔-closed wf2 snd snd₁ ⟩ ⟩

model_basics : LambdaModelBasics model
model_basics = record
                 { ℱ-≲ = ℱ-≲ ;
                   ●-≲ = λ {Γ}{Δ}{γ}{δ}{D₁}{D₂}{D₁′}{D₂′} x y →
                       ●-≲ {D₁ = D₁}{D₂ = D₂}{D₁′ = D₁′}{D₂′ = D₂′} x y ;
                   ℱ-⊑ = ℱ-⊑ ;
                   ●-⊑ = λ {Γ}{D₁}{D₂} a b c → ●-⊑ {D₂ = D₂} a b c;
                   ℱ-⊔ = λ {Γ}{D}{γ}{u}{v} → ℱ-⊔{D = D}{γ}{u}{v} ;
                   ●-⊔ = ●-⊔ }

open import RenamePreserveReflect domain ordering model model_basics
open import Filter domain ordering model model_basics
open import SubstitutionPreserve domain ordering model model_basics

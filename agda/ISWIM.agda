{- 

   ISWIM: the call-by-value lambda calculus with constants.

-}

module ISWIM where

open import Utilities using (_iff_)
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
  lit : (p : Prim) → rep p → Op

sig : Op → List ℕ
sig lam = 1 ∷ []
sig app = 0 ∷ 0 ∷ []
sig (lit p k) = []

open import Syntax using (Var; _•_; ↑; id) public
module ASTMod = Syntax.OpSig Op sig
open ASTMod using (`_; _⦅_⦆; Subst; Ctx; plug;
                   rename; ⟦_⟧;
                   ⟪_⟫; _[_]; subst-zero; bind; ast; cons; nil; exts;
                   rename-id; _⨟_; exts-cons-shift; WF; WF-Ctx; ctx-depth)
            renaming (ABT to AST) public

Term : Set
Term = AST

pattern ƛ N = lam ⦅ cons (bind (ast N)) nil ⦆

infixl 7  _·_
pattern _·_ L M = app ⦅ cons (ast L) (cons (ast M) nil) ⦆

pattern $ p k = lit p k ⦅ nil ⦆


data TermValue : Term → Set where

  V-var : ∀ {x : Var}
      --------------------
    → TermValue  (` x)

  V-ƛ : ∀  {N : Term}
      -----------
    → TermValue (ƛ N)

  V-lit : ∀  {p : Prim} {k : rep p}
      ---------------------------
    → TermValue  ($ p k)

infix 2 _—→_

data _—→_ : Term → Term → Set where

  ξ₁-rule : ∀  {L L′ M : Term}
    → L —→ L′
      ----------------
    → L · M —→ L′ · M

  ξ₂-rule : ∀  {L M M′ : Term}
    → TermValue L
    → M —→ M′
      ----------------
    → L · M —→ L · M′

  β-rule : ∀  {N : Term} {M : Term}
    → TermValue M
      ---------------------------------
    → (ƛ N) · M —→ N [ M ]

  δ-rule : ∀ {B}{P} {f : base-rep B → rep P} {k : base-rep B}
      ------------------------------------------------------------
    → _—→_  (($ (B ⇒ P) f) · ($ (base B) k)) ($ P (f k))


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

_≅_ : ∀(M N : Term) → Set
(_≅_ M N) = ∀ {C : Ctx}{wfC : WF-Ctx 0 C}
              {wfM : WF (ctx-depth C) M}{wfN : WF (ctx-depth C) N}
              → (terminates (plug C M)) iff (terminates (plug C N))

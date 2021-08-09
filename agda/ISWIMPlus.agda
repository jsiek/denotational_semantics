{- 

   ISWIMPlus: the call-by-value lambda calculus with constants,
     products, etc.

-}

module ISWIMPlus where

open import Utilities using (_iff_)
open import Primitives
open import Data.Empty renaming (⊥ to Bot)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool  
open import Data.List using (List; []; _∷_)
open import Data.Product
   using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Unit using (⊤; tt)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong; cong₂; cong-app)
open Eq.≡-Reasoning
open import Syntax using (Sig; ext; ν; ■; Var; _•_; ↑; id; _⨟_) public

data Op : Set where
  lam : Op
  app : Op
  lit : (p : Prim) → rep p → Op
  pair-op : Op
  fst-op : Op
  snd-op : Op

sig : Op → List Sig
sig lam = ν ■ ∷ []
sig app = ■ ∷ ■ ∷ []
sig (lit p k) = []
sig pair-op = ■ ∷ ■ ∷ []
sig fst-op = ■ ∷ []
sig snd-op = ■ ∷ []

module ASTMod = Syntax.OpSig Op sig
open ASTMod using (`_; _⦅_⦆; Subst; Ctx; plug; rename; 
                   ⟪_⟫; _[_]; subst-zero; bind; ast; cons; nil; 
                   rename-id; exts-cons-shift; WF; WF-Ctx; ctx-depth;
                   WF-op; WF-cons; WF-nil; WF-ast; WF-bind; WF-var;
                   COp; CAst; CBind; ccons; tcons)
            renaming (ABT to AST) public

Term : Set
Term = AST

pattern ƛ N = lam ⦅ cons (bind (ast N)) nil ⦆

infixl 7  _·_
pattern _·_ L M = app ⦅ cons (ast L) (cons (ast M) nil) ⦆

pattern $ p k = lit p k ⦅ nil ⦆

pattern pair L M = pair-op ⦅ cons (ast L) (cons (ast M) nil) ⦆
pattern fst M = fst-op ⦅ cons (ast M) nil ⦆
pattern snd M = snd-op ⦅ cons (ast M) nil ⦆

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

  V-pair : ∀  {M N : Term}
    → TermValue M  → TermValue N
      --------------------------
    → TermValue (pair M N)

data Frame : Set where
  F-·₁ : Term → Frame 
  F-·₂ : (M : Term) → {Mv : TermValue M} → Frame
  F-×₁ : Term → Frame
  F-×₂ : (L : Term) → {Lv : TermValue L} → Frame
  F-fst : Frame
  F-snd : Frame

fill : Term → Frame → Term
fill L (F-·₁ M)  = L · M
fill M (F-·₂ L)  = L · M
fill M (F-×₁ N)  = pair M N
fill N (F-×₂ M)  = pair M N
fill M F-fst     = fst M
fill M F-snd     = snd M

infix 2 _—→_

data _—→_ : Term → Term → Set where

  ξ-rule : ∀  {L L′ : Term} (F : Frame)
    → L —→ L′
      ----------------
    → fill L F —→ fill L′ F

  β-rule : ∀  {N : Term} {M : Term}
    → TermValue M
      ---------------------------------
    → (ƛ N) · M —→ N [ M ]

  δ-rule : ∀ {B}{P} {f : base-rep B → rep P} {k : base-rep B}
      ------------------------------------------------------------
    → _—→_  (($ (B ⇒ P) f) · ($ (base B) k)) ($ P (f k))

  fst-rule : ∀  {N : Term} {M : Term}
    → TermValue M  →  TermValue N
      ---------------------------------
    → fst (pair M N) —→ M

  snd-rule : ∀  {N : Term} {M : Term}
    → TermValue M  →  TermValue N
      ---------------------------------
    → snd (pair M N) —→ N


open import MultiStep Op sig _—→_ public

—→-app-cong : ∀ {L L' M : Term}
            → L —→ L'
            → L · M —→ L' · M
—→-app-cong {M = M} (ξ-rule F ll') = ξ-rule (F-·₁ M) (ξ-rule F ll')
—→-app-cong {M = M} (β-rule v) = ξ-rule (F-·₁ M) (β-rule v)
—→-app-cong {M = M} δ-rule = ξ-rule (F-·₁ M) δ-rule
—→-app-cong {M = M} (fst-rule Mv Nv) = ξ-rule (F-·₁ M) (fst-rule Mv Nv)
—→-app-cong {M = M} (snd-rule Mv Nv) = ξ-rule (F-·₁ M) (snd-rule Mv Nv)

appL-cong : ∀ {L L' M : Term}
         → L —↠ L'
           ---------------
         → L · M —↠ L' · M
appL-cong {L}{L'}{M} (L □) = L · M □
appL-cong {L}{L'}{M} (L —→⟨ r ⟩ rs) =
    L · M —→⟨ ξ-rule (F-·₁ M) r ⟩ appL-cong rs

appR-cong : ∀ {L M M' : Term}
         → TermValue L
         → M —↠ M'
           ---------------
         → L · M —↠ L · M'
appR-cong {L}{M}{M'} v (M □) = L · M □
appR-cong {L}{M}{M'} v (M —→⟨ r ⟩ rs) =
    L · M —→⟨ ξ-rule (F-·₂ L {v}) r ⟩ appR-cong v rs

pairL-cong : ∀ {L L' M : Term}
         → L —↠ L'
           ---------------
         → pair L M —↠ pair L' M
pairL-cong {L}{L'}{M} (L □) = pair L M □
pairL-cong {L}{L'}{M} (L —→⟨ r ⟩ rs) =
    pair L M —→⟨ ξ-rule (F-×₁ M) r ⟩ pairL-cong rs

pairR-cong : ∀ {L M M' : Term}
         → TermValue L
         → M —↠ M'
           ---------------
         → pair L M —↠ pair L M'
pairR-cong {L}{M}{M'} v (M □) = pair L M □
pairR-cong {L}{M}{M'} v (M —→⟨ r ⟩ rs) =
    pair L M —→⟨ ξ-rule (F-×₂ L {v}) r ⟩ pairR-cong v rs

fstL-cong : ∀ {L L' M : Term}
         → L —↠ L'
           -------------------
         → (fst L) —↠ (fst L')
fstL-cong {L}{L'}{M} (L □) = (fst L) □
fstL-cong {L}{L'}{M} (L —→⟨ r ⟩ rs) =
    (fst L) —→⟨ ξ-rule F-fst r ⟩ fstL-cong {M = M} rs

sndL-cong : ∀ {L L' M : Term}
         → L —↠ L'
           -------------------
         → (snd L) —↠ (snd L')
sndL-cong {L}{L'}{M} (L □) = (snd L) □
sndL-cong {L}{L'}{M} (L —→⟨ r ⟩ rs) =
    (snd L) —→⟨ ξ-rule F-snd r ⟩ sndL-cong {M = M} rs


terminates : ∀(M : Term) → Set
terminates  M = Σ[ N ∈ Term ] TermValue N × (M —↠ N)

_≅_ : ∀(M N : Term) → Set₁
(_≅_ M N) = ∀ {C : Ctx}{wfC : WF-Ctx 0 C}
              {wfM : WF (ctx-depth C 0) M}{wfN : WF (ctx-depth C 0) N}
              → (terminates (plug C M)) iff (terminates (plug C N))

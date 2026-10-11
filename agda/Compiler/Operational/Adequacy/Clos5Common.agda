{-

  Definitions shared by the soundness and adequacy proofs for Clos5
  (see Adequacy/Clos5.agda for the overview):

  * s ↠ t, runs of the Clos5 machine of a table ds from any state, and
    their determinism;
  * where a definition found by the machine (global ds k) sits in the
    table, and what the semantics makes of it (table-at, table-agree).

-}

open import Data.List using (List; []; _∷_; _++_; [_]; length; reverse)
open import Compiler.Lang.Clos5 using (AST; global)

module Compiler.Operational.Adequacy.Clos5Common (ds : List AST) where

open import SetsAsPredicates
open import Compiler.Model.Graph.Domain.ISWIM.Domain using (ν)
open import Compiler.Model.Graph.Sem.Clos5Iswim using (table) renaming (code to codeD)
open import Compiler.Model.Graph.Correctness.GlobalizeCorrect using (table-ext; table-top)
open import Compiler.Operational.Smallstep using (Star; ε; _◅_; next; stop; machine)
open import Compiler.Lang.ListUtil using (_‼_)
open import Compiler.Operational.Machine.Clos5
open import Compiler.Compile.GlobalizeTable using (_⊑_)
open import Compiler.Operational.Adequacy.Clos5WF using (DefsWF)

open import Data.List.Properties
  using (++-assoc; reverse-++; unfold-reverse; reverse-involutive; length-reverse)
open import Data.Maybe using (just)
open import Data.Nat using (zero; suc; _<_; _≟_)
open import Data.Nat.Properties using (n<1+n; ≤-pred; m≤n⇒m<n∨m≡n)
open import Data.Product using (_×_; Σ-syntax; _,_; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Relation.Nullary using (yes; no)
open import Data.Empty using (⊥-elim)

{- Runs of the machine -----------------------------------------------------------}

infixr 5 _∷↠_
infix 4 _↠_
data _↠_ : State → State → Set where
  done : ∀ {s} → s ↠ s
  _∷↠_ : ∀ {s s' s''} → step ds s ≡ next s' → s' ↠ s'' → s ↠ s''

infixr 5 _++↠_
_++↠_ : ∀ {s s' s''} → s ↠ s' → s' ↠ s'' → s ↠ s''
done ++↠ τ = τ
(st ∷↠ σ) ++↠ τ = st ∷↠ (σ ++↠ τ)

↠→star : ∀ {s₀ s t} → s ↠ t → Star (machine State (step ds) s₀) s t
↠→star done = ε
↠→star (st ∷↠ σ) = st ◅ ↠→star σ

star→↠ : ∀ {s₀ s t} → Star (machine State (step ds) s₀) s t → s ↠ t
star→↠ ε = done
star→↠ (st ◅ σ) = st ∷↠ star→↠ σ

private
  next-inj : ∀ {a b : State} → next a ≡ next b → a ≡ b
  next-inj refl = refl

{- two runs to final states end in the same state -}
↠-final-det : ∀ {s t₁ t₂ o₁ o₂} → s ↠ t₁ → s ↠ t₂
  → step ds t₁ ≡ stop o₁ → step ds t₂ ≡ stop o₂ → t₁ ≡ t₂
↠-final-det done done f₁ f₂ = refl
↠-final-det done (st ∷↠ σ) f₁ f₂ with trans (sym f₁) st
... | ()
↠-final-det (st ∷↠ σ) done f₁ f₂ with trans (sym f₂) st
... | ()
↠-final-det (st₁ ∷↠ σ₁) (st₂ ∷↠ σ₂) f₁ f₂ with next-inj (trans (sym st₁) st₂)
... | refl = ↠-final-det σ₁ σ₂ f₁ f₂

length-obs-list : ∀ vs → length (obs-list vs) ≡ length vs
length-obs-list [] = refl
length-obs-list (v ∷ vs) = cong suc (length-obs-list vs)

{- The table of global definitions ------------------------------------------------}

private
  ‼-split : ∀ {A : Set} (L : List A) k {B} → L ‼ k ≡ just B
    → Σ[ a ∈ List A ] Σ[ b ∈ List A ] L ≡ a ++ B ∷ b × length a ≡ k
  ‼-split (x ∷ L) zero refl = [] , L , refl , refl
  ‼-split (x ∷ L) (suc k) eq with ‼-split L k eq
  ... | a , b , refl , refl = x ∷ a , b , refl , refl

{- the definition that the machine finds at k sits on top of the k
   definitions older than it -}
global-split : ∀ k {B} → global ds k ≡ just B → Σ[ Ns ∈ List AST ] (B ∷ Ns ⊑ ds) × length Ns ≡ k
global-split k {B} eq with ‼-split (reverse ds) k eq
... | a , b , e , refl =
  reverse a , (reverse b
  , trans (sym (reverse-involutive ds))
      (trans (cong reverse e)
        (trans (reverse-++ a (B ∷ b))
          (trans (cong (_++ reverse a) (unfold-reverse B b))
                 (++-assoc (reverse b) [ B ] (reverse a))))))
  , length-reverse a

DefsWF-⊑ : ∀ {Ns} → Ns ⊑ ds → DefsWF ds → DefsWF Ns
DefsWF-⊑ (xs , refl) = go xs
  where
  go : ∀ xs {Ns} → DefsWF (xs ++ Ns) → DefsWF Ns
  go [] w = w
  go (x ∷ xs) w = go xs (proj₂ w)

{- the meaning of a definition, with the table of the older ones -}
table-at : ∀ {B Ns} → B ∷ Ns ⊑ ds → table ds (length Ns) ≡ codeD (table Ns) B
table-at {B} {Ns} (xs , refl) =
  trans (table-ext xs (B ∷ Ns) (length Ns) (n<1+n (length Ns))) (table-top B Ns)

{- the older definitions mean the same in the whole table -}
table-agree : ∀ {Ns} → Ns ⊑ ds → ∀ j → j < length Ns → table ds j ≡ table Ns j
table-agree {Ns} (xs , refl) j j< = table-ext xs Ns j j<

{- every existing definition is a function -}
ν-table : ∀ (Ns : List AST) k → k < length Ns → ν ∈ table Ns k
ν-table (N ∷ Ns) k k< with k ≟ length Ns
... | yes _ = tt
... | no k≢ with m≤n⇒m<n∨m≡n (≤-pred k<)
...   | inj₁ lt = ν-table Ns k lt
...   | inj₂ eq = ⊥-elim (k≢ eq)

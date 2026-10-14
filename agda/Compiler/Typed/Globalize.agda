{-

  Typed globalize (Clos4ᵀ → Clos5ᵀ): the code of every function becomes a
  global definition, and the code itself a reference to it, as the
  untyped pass (Compiler/Globalize.agda) does.

  The pass threads the definitions made so far, newest first, each typed
  over the table of the older ones (Made), from left to right; for code
  it first globalizes the body, so the functions nested in it become
  definitions first. A term made earlier is over a smaller table than
  the one at the end, so it is weakened (wk) to the table its context
  has; at the end every definition is weakened to the whole table.

-}

module Compiler.Typed.Globalize where

open import Language.Typed.Type
open import Framework.Membership using (_⊑_; here⊑; there⊑; ⊑-∋; ⊑-trans)
import Language.Typed.Clos4 as S
open import Language.Typed.Clos5

open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Nat using (ℕ)
open import Data.Vec using (Vec; []; _∷_)

{- the definitions made so far, newest first, each over the older ones -}
data Made : List ℕ → Set where
  [] : Made []
  _▷_ : ∀ {Σ n} → Made Σ → Code Σ n → Made (n ∷ Σ)

{- a result over the table after some more definitions -}
record Out (Σ : List ℕ) (P : List ℕ → Set) : Set where
  constructor out
  field
    {Σ'} : List ℕ
    grows : Σ ⊑ Σ'
    made : Made Σ'
    res : P Σ'

glob : ∀ {Σ Γ A} → S.Tm Γ A → Made Σ → Out Σ (λ Σ' → Tm Σ' Γ A)
globs : ∀ {Σ Γ n} → Vec (S.Tm Γ Any) n → Made Σ → Out Σ (λ Σ' → Vec (Tm Σ' Γ Any) n)
glob₁ : ∀ {Σ Γ Γ₁ A B} → (∀ {Σ'} → Tm Σ' Γ₁ A → Tm Σ' Γ B) → S.Tm Γ₁ A → Made Σ
  → Out Σ (λ Σ' → Tm Σ' Γ B)
glob₂ : ∀ {Σ Γ Γ₁ Γ₂ A B C} → (∀ {Σ'} → Tm Σ' Γ₁ A → Tm Σ' Γ₂ B → Tm Σ' Γ C)
  → S.Tm Γ₁ A → S.Tm Γ₂ B → Made Σ → Out Σ (λ Σ' → Tm Σ' Γ C)

glob (S.` x) D = out here⊑ D (` x)
glob (S.code N) D with glob N D
... | out s D' N' = out (there⊑ s) (D' ▷ N') (fun-ref Z)
glob (S.pack L M) D = glob₂ pack L M D
glob (S.callc L M) D = glob₂ callc L M D
glob (S.lit B c) D = out here⊑ D (lit B c)
glob (S.tuple Ms) D with globs Ms D
... | out s D' Ms' = out s D' (tuple Ms')
glob (S.get i M) D = glob₁ (get i) M D
glob (S.inl M) D = glob₁ inl M D
glob (S.inr M) D = glob₁ inr M D
glob (S.case L M N) D with glob L D
... | out s₁ D₁ L' with glob M D₁
...   | out s₂ D₂ M' with glob N D₂
...     | out s₃ D₃ N' =
  out (⊑-trans s₁ (⊑-trans s₂ s₃)) D₃ (case (wk (⊑-∋ (⊑-trans s₂ s₃)) L') (wk (⊑-∋ s₃) M') N')
glob (S.prim p L M) D = glob₂ (prim p) L M D
glob (S.let′ M N) D = glob₂ let′ M N D
glob (S.inject G M) D = glob₁ (inject G) M D
glob (S.project t M) D = glob₁ (project t) M D

globs [] D = out here⊑ D []
globs (M ∷ Ms) D with glob M D
... | out s₁ D₁ M' with globs Ms D₁
...   | out s₂ D₂ Ms' = out (⊑-trans s₁ s₂) D₂ (wk (⊑-∋ s₂) M' ∷ Ms')

glob₁ f M D with glob M D
... | out s D' M' = out s D' (f M')

glob₂ f L M D with glob L D
... | out s₁ D₁ L' with glob M D₁
...   | out s₂ D₂ M' = out (⊑-trans s₁ s₂) D₂ (f (wk (⊑-∋ s₂) L') M')

{- the definitions made, each over the whole table -}
close : ∀ {Σ Σ'} → Made Σ' → Σ' ⊑ Σ → All (Code Σ) Σ'
close [] s = []
close (D ▷ N) s = wk (⊑-∋ s') N ∷ close D s'
  where s' = ⊑-trans (there⊑ here⊑) s

{- the pass, for a whole program -}
globalize : S.Tm [] Any → Program
globalize M with glob M []
... | out _ D M' = program (close D here⊑) M'

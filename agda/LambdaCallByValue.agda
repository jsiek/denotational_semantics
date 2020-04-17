{-

  Call-by-value Lambda Calculus

-}

module LambdaCallByValue where

open import Utilities using (_iff_)
open import Lambda
open Lambda.ASTMod using (Var; `_; Subst; Ctx; plug; _[_])
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)

data TermValue : Term → Set where

  V-var : ∀{x : Var}
      --------------------
    → TermValue (` x)

  V-ƛ : ∀ {N : Term}
      ---------------
    → TermValue (ƛ N)

infix 2 _—→_

data _—→_ : Term → Term → Set where

  ξ₁-rule : ∀ {L L′ M : Term}
    → L —→ L′
      ----------------
    → L · M —→ L′ · M

  ξ₂-rule : ∀ {L M M′ : Term}
    → TermValue L
    → M —→ M′
      ----------------
    → L · M —→ L · M′

  β-rule : ∀ {N : Term} {M : Term}
    → TermValue M
      ---------------------------------
    → (ƛ N) · M —→ N [ M ]

open import MultiStep Op sig _—→_ public

—→-app-cong : ∀{L L' M : Term}
            → L —→ L'
            → L · M —→ L' · M
—→-app-cong (ξ₁-rule ll') = ξ₁-rule (—→-app-cong ll')
—→-app-cong (ξ₂-rule v ll') = ξ₁-rule (ξ₂-rule v ll')
—→-app-cong (β-rule v) = ξ₁-rule (β-rule v)

appL-cong : ∀ {L L' M : Term}
         → L —↠ L'
           ---------------
         → L · M —↠ L' · M
appL-cong{L}{L'}{M} (L □) = L · M □
appL-cong{L}{L'}{M} (L —→⟨ r ⟩ rs) = L · M —→⟨ ξ₁-rule r ⟩ appL-cong rs

appR-cong : ∀ {L M M' : Term}
         → TermValue L
         → M —↠ M'
           ---------------
         → L · M —↠ L · M'
appR-cong{L}{M}{M'} v (M □) = L · M □
appR-cong{L}{M}{M'} v (M —→⟨ r ⟩ rs) =
    L · M —→⟨ ξ₂-rule v r ⟩ appR-cong v rs

terminates : (M : Term ) → Set
terminates M = Σ[ N ∈ Term ] (M —↠ ƛ N)

_≅_ : (M N : Term) → Set
(_≅_ M N) = ∀ {C : Ctx}
              → (terminates (plug C M)) iff (terminates (plug C N))

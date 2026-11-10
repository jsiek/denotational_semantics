{-

  Lemmas about logical equivalence (Framework/Iff.agda): equivalences
  chain.

-}

module proof.Framework.Iff where

open import Framework.Iff public

open import Data.Product using () renaming (_,_ to ⟨_,_⟩)

⇔∘ : ∀ {A B C : Set} → A ⇔ B → B ⇔ C → A ⇔ C
⇔∘ ⟨ f , g ⟩ ⟨ h , k ⟩ = ⟨ (λ a → h (f a)) , (λ c → g (k c)) ⟩

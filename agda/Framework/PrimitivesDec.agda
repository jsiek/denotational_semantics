{-

  Decidable equality of base types (Framework/Primitives.agda).

-}

module Framework.PrimitivesDec where

open import Framework.Primitives using (Base; Nat; Int; 𝔹; Unit; Void; Blame)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (Dec; yes; no)

_≟B_ : (B C : Base) → Dec (B ≡ C)
Nat ≟B Nat = yes refl
Int ≟B Int = yes refl
𝔹 ≟B 𝔹 = yes refl
Unit ≟B Unit = yes refl
Void ≟B Void = yes refl
Blame ≟B Blame = yes refl
Nat ≟B Int = no λ ()
Nat ≟B 𝔹 = no λ ()
Nat ≟B Unit = no λ ()
Nat ≟B Void = no λ ()
Nat ≟B Blame = no λ ()
Int ≟B Nat = no λ ()
Int ≟B 𝔹 = no λ ()
Int ≟B Unit = no λ ()
Int ≟B Void = no λ ()
Int ≟B Blame = no λ ()
𝔹 ≟B Nat = no λ ()
𝔹 ≟B Int = no λ ()
𝔹 ≟B Unit = no λ ()
𝔹 ≟B Void = no λ ()
𝔹 ≟B Blame = no λ ()
Unit ≟B Nat = no λ ()
Unit ≟B Int = no λ ()
Unit ≟B 𝔹 = no λ ()
Unit ≟B Void = no λ ()
Unit ≟B Blame = no λ ()
Void ≟B Nat = no λ ()
Void ≟B Int = no λ ()
Void ≟B 𝔹 = no λ ()
Void ≟B Unit = no λ ()
Void ≟B Blame = no λ ()
Blame ≟B Nat = no λ ()
Blame ≟B Int = no λ ()
Blame ≟B 𝔹 = no λ ()
Blame ≟B Unit = no λ ()
Blame ≟B Void = no λ ()


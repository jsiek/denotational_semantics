{-

  Keeping some of n things, chosen by flags (true: keep): how many are
  kept (count), the kept ones (select), and the renaming (squeeze) of
  n + 1 variables, of which 0 is fixed and suc i is the i-th thing, to
  0 and the kept things; it sends the others (not Kept) to 0.

-}

module Framework.Select where

open import Data.Bool using (Bool; true; false; T)
open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ; suc)
open import Data.Unit using (⊤)
open import Data.Vec using (Vec; []; _∷_; lookup)

count : ∀ {n} → Vec Bool n → ℕ
count [] = 0
count (true ∷ fl) = suc (count fl)
count (false ∷ fl) = count fl

select : ∀ {a n} {A : Set a} (fl : Vec Bool n) → Vec A n → Vec A (count fl)
select [] [] = []
select (true ∷ fl) (x ∷ xs) = x ∷ select fl xs
select (false ∷ fl) (x ∷ xs) = select fl xs

{- a renaming under a binder -}
ext : ∀ {k k'} → (Fin k → Fin k') → Fin (suc k) → Fin (suc k')
ext r zero = zero
ext r (suc x) = suc (r x)

Kept : ∀ {n} → Vec Bool n → Fin (suc n) → Set
Kept fl zero = ⊤
Kept fl (suc i) = T (lookup fl i)

squeeze : ∀ {n} (fl : Vec Bool n) → Fin (suc n) → Fin (suc (count fl))
squeeze fl zero = zero
squeeze [] (suc ())
squeeze (true ∷ fl) (suc zero) = suc zero
squeeze (true ∷ fl) (suc (suc i)) = ext suc (squeeze fl (suc i))
squeeze (false ∷ fl) (suc i) = squeeze fl i

{-

  Collecting the values of n subterms, left to right, into a vector, for
  machines whose values are typed by the length of a tuple: the values
  so far are kept newest first in a vector vs of length m, and with the
  j subterms still to evaluate the tuple has length m +ʳ j, which needs
  no rewriting as vs grows; at the end, vs <>< [] is the tuple in order.

-}

module Framework.VecUtil where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Vec using (Vec; []; _∷_)

{- m added to n, one at a time -}
_+ʳ_ : ℕ → ℕ → ℕ
zero +ʳ n = n
suc m +ʳ n = m +ʳ suc n

{- xs reversed, in front of ys -}
_<><_ : ∀ {A : Set} {m n} → Vec A m → Vec A n → Vec A (m +ʳ n)
[] <>< ys = ys
(x ∷ xs) <>< ys = xs <>< (x ∷ ys)

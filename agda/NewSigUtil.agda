open import Data.Nat using (ℕ; zero; suc)

module NewSigUtil where

  open import abt.Sig public
  
  
  ν-n : ℕ → Sig → Sig
  ν-n zero b = b
  ν-n (suc n) b = ν (ν-n n b)
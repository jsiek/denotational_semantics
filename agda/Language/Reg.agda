{-

  The registers of X86ᵀ (ISWIM/Language/Typed/X86.agda) and of untyped X86
  (ISWIM/Language/X86.agda): %rax, %rdi and %rsi.

-}

module Language.Reg where

data Reg : Set where
  rax rdi rsi : Reg

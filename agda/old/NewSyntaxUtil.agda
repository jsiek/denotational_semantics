module NewSyntaxUtil where

  open import Data.Nat using (ℕ; zero; suc)

  open import AbstractBindingTree
  open import NewSigUtil

  bind-n : ∀ {Op} {sig} {b} n → Arg Op sig b → Arg Op sig (ν-n n b)
  bind-n zero arg = arg
  bind-n (suc n) arg = bind (bind-n n arg)

  argify : ∀ {Op} {sig} b → ABT Op sig → Arg Op sig b
  argify ■ M = (ast M)
  argify (ν b) M = bind (argify b M)
  argify (∁ b) M = clear (argify b M)

  infixr 7  _,,_
  pattern _,,_ M Ns = cons (ast M) Ns
  pattern Nil = nil
  pattern ⟩_,,_ M Ns = cons (bind (ast M)) Ns
  pattern !_,,_ M Ns = cons M Ns

  map-args : ∀ {Op1 Op2 sig1 sig2} (f : ABT Op1 sig1 → ABT Op2 sig2)
    → ∀ {bs} → Args Op1 sig1 bs → Args Op2 sig2 bs
  map-arg : ∀ {Op1 Op2 sig1 sig2} (f : ABT Op1 sig1 → ABT Op2 sig2)
    → ∀ {b} → Arg Op1 sig1 b → Arg Op2 sig2 b
  map-args f Nil = Nil
  map-args f (! arg ,, args) = ! map-arg f arg ,, map-args f args
  map-arg f (ast x) = ast (f x)
  map-arg f (bind arg) = bind (map-arg f arg)
  map-arg f (clear arg) = clear (map-arg f arg)


{-

  Delay (Clos3μ → Clos4μ), as typed delay (Compiler/Delay.agda): a
  closure becomes a packed pair of its code and the tuple of its free
  variables, and an application opens the closure and calls its code
  with its environment:

    clos N Ms ⇒ pack (code N') (tuple Ms'),
    app L M   ⇒ callc L' M'.

  (It carries a renaming of the variables, the identity for a program.)

-}

module Mu.Compiler.Delay where

open import Mu.Language.Type
open import Mu.Language.Clos3
import Mu.Language.Clos4 as T
open import Mu.Framework.AllUtil using (All; []; _∷_)

open import Data.List using ([]; _∷_)

Ren : Ctx → Ctx → Set
Ren Γ Δ = ∀ {A} → Γ ∋ A → Δ ∋ A

{- the renaming for the body of a binder -}
ext : ∀ {Γ Δ B} → Ren Γ Δ → Ren (B ∷ Γ) (B ∷ Δ)
ext r Z = Z
ext r (S x) = S (r x)

delay : ∀ {Γ Δ A} → Ren Γ Δ → Tm Γ A → T.Tm Δ A
delays : ∀ {Γ Δ Δ'} → Ren Γ Δ → All (Tm Γ) Δ' → All (T.Tm Δ) Δ'

delay r (` x) = T.` r x
delay r (clos N Ms) = T.pack (T.code (delay (λ x → x) N)) (T.tuple (delays r Ms))
delay r (app L M) = T.callc (delay r L) (delay r M)
delay r (lit B c) = T.lit B c
delay r (tuple Ms) = T.tuple (delays r Ms)
delay r (get i M) = T.get i (delay r M)
delay r (inl M) = T.inl (delay r M)
delay r (inr M) = T.inr (delay r M)
delay r (case L M N) = T.case (delay r L) (delay (ext r) M) (delay (ext r) N)
delay r (prim p L M) = T.prim p (delay r L) (delay r M)
delay r (let′ M N) = T.let′ (delay r M) (delay (ext r) N)
delay r (fold M) = T.fold (delay r M)
delay r (unfold M) = T.unfold (delay r M)

delays r [] = []
delays r (M ∷ Ms) = delay r M ∷ delays r Ms

{- the pass, for a whole program -}
delay-program : ∀ {A} → Tm [] A → T.Tm [] A
delay-program = delay λ ()

{-

  Typed split (Clos3ᵀ → Clos4ᵀ): a closure becomes a packed pair of its
  code and the tuple of its free variables, and an application opens
  the closure and calls its code with its environment:

    clos N Ms ⇒ pack (code N') (tuple Ms'),
    app L M   ⇒ callc L' M'.

  (It carries a renaming of the variables, the identity for a program.)

-}

module Compiler.Split where

open import Language.Typed.Type
open import Language.Typed.Clos3
import Language.Typed.Clos4 as T

open import Data.List using ([]; _∷_)
open import Data.Vec using (Vec; []; _∷_)

Ren : Ctx → Ctx → Set
Ren Γ Δ = ∀ {A} → Γ ∋ A → Δ ∋ A

{- the renaming for the body of a binder -}
ext : ∀ {Γ Δ B} → Ren Γ Δ → Ren (B ∷ Γ) (B ∷ Δ)
ext r Z = Z
ext r (S x) = S (r x)

split : ∀ {Γ Δ A} → Ren Γ Δ → Tm Γ A → T.Tm Δ A
splits : ∀ {Γ Δ n} → Ren Γ Δ → Vec (Tm Γ Any) n → Vec (T.Tm Δ Any) n

split r (` x) = T.` r x
split r (clos N Ms) = T.pack (T.code (split (λ x → x) N)) (T.tuple (splits r Ms))
split r (app L M) = T.callc (split r L) (split r M)
split r (lit B c) = T.lit B c
split r (tuple Ms) = T.tuple (splits r Ms)
split r (get i M) = T.get i (split r M)
split r (inl M) = T.inl (split r M)
split r (inr M) = T.inr (split r M)
split r (case L M N) = T.case (split r L) (split (ext r) M) (split (ext r) N)
split r (prim p L M) = T.prim p (split r L) (split r M)
split r (let′ M N) = T.let′ (split r M) (split (ext r) N)
split r (inject G M) = T.inject G (split r M)
split r (project t M) = T.project t (split r M)

splits r [] = []
splits r (M ∷ Ms) = split r M ∷ splits r Ms

{- the pass, for a whole program -}
split-program : ∀ {A} → Tm [] A → T.Tm [] A
split-program = split λ ()

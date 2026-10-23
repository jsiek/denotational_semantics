{-

  Divergence and recursion in ISWIMμ, through recursive types, without
  a recursion construct (Mu/Language/ISWIM.agda):

  * ω = λx. unfold x x : (μX. X ⇒ Int) ⇒ Int, and Ω = ω (fold ω), which
    diverges;
  * the call-by-value fixed-point combinator at Int ⇒ Int,
      fix = λf. g (fold g),  g = λx. f (λv. unfold x x v),
    with x : μX. X ⇒ (Int ⇒ Int);
  * countdown = fix (λc. λn. if n = 0 then 0 else c (n - 1)), and
    countdown 3.

  Each is compiled with compile-to-FlatClos (Mu/Compiler/Pipeline.agda) and run on
  the ISWIMμ and FlatClosμ machines, by computation.

-}

module Mu.proof.Compiler.Examples.RecursionExample where

open import Framework.Primitives using (Int)
open import Language.Prim using (sub; eq)
open import Mu.Language.Type
open import Mu.Language.ISWIM
open import Mu.Compiler.Pipeline using (compile-to-FlatClos)
open import Semantics.Observation using (Obs; o-const)
open import Semantics.CEK.Smallstep using (Machine; next; stop)
import Mu.Semantics.AbstractMachines.ISWIM as ISWIMμₘ
import Mu.Semantics.AbstractMachines.FlatClos as FlatClosμₘ

open import Data.Fin using (zero)
open import Data.Integer using (+_)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

ℤ′ : ∀ {n} → Ty n
ℤ′ = base Int

ω : Tm [] (μ (var zero ⇒ ℤ′) ⇒ ℤ′)
ω = lam (app (unfold (` Z)) (` Z))

Ω : Tm [] ℤ′
Ω = app ω (fold ω)

{- the recursive type of the self-application in fix -}
D : Type
D = μ (var zero ⇒ (ℤ′ ⇒ ℤ′))

F : Type
F = (ℤ′ ⇒ ℤ′) ⇒ (ℤ′ ⇒ ℤ′)

fix : Tm [] (F ⇒ (ℤ′ ⇒ ℤ′))
fix = lam (app g (fold g))
  where
  g : Tm (F ∷ []) (D ⇒ (ℤ′ ⇒ ℤ′))
  g = lam (app (` S Z) (lam (app (app (unfold (` S Z)) (` S Z)) (` Z))))

countdown : Tm [] (ℤ′ ⇒ ℤ′)
countdown = app fix (lam (lam (case (prim eq (` Z) (lit Int (+ 0)))
                                 (lit Int (+ 0))
                                 (app (` S (S Z)) (prim sub (` S Z) (lit Int (+ 1)))))))

three : Tm [] ℤ′
three = app countdown (lit Int (+ 3))

{- run a machine for at most n steps -}
run : ℕ → (L : Machine) → Maybe Obs
run n L = go n (Machine.start L)
  where
  go : ℕ → Machine.State L → Maybe Obs
  go zero s = nothing
  go (suc n) s with Machine.step L s
  ... | next s' = go n s'
  ... | stop o = just o

three-iswim : run 200 (ISWIMμₘ.sem three) ≡ just (o-const Int (+ 0))
three-iswim = refl

three-clos4 : run 400 (FlatClosμₘ.sem (compile-to-FlatClos three)) ≡ just (o-const Int (+ 0))
three-clos4 = refl

{- Ω runs on, on both machines -}
Ω-iswim : run 200 (ISWIMμₘ.sem Ω) ≡ nothing
Ω-iswim = refl

Ω-clos4 : run 400 (FlatClosμₘ.sem (compile-to-FlatClos Ω)) ≡ nothing
Ω-clos4 = refl

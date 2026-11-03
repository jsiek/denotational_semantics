{-

  Example programs of FPC (FPC/Language/FPC.agda), run on its clocked
  interpreter (FPC/Semantics/ClockedInterpreters/FPC.agda) by
  computation. Each program is closed and ends at an integer or a
  boolean, and each test states the expected outcome. Together the
  programs exercise every term constructor, both primitives, both
  branches of case, recursion through recursive types, and timing out.
  The table in FPC/README.md lists which program exercises each clause
  of the interpreter.

  FPC has no recursion construct. Self-application is typable through a
  recursive type:

  * ω = λx. unfold x x : (μX. X ⇒ Int) ⇒ Int, and Ω = ω (fold ω), which
    diverges;
  * the call-by-value fixed-point combinator at Int ⇒ Int,
      fix = λf. g (fold g),  g = λx. f (λv. unfold x x v),
    with x : μX. X ⇒ (Int ⇒ Int);
  * countdown = fix (λc. λn. if n = 0 then 0 else c (n - 1)), and
    countdown 3.

  FPC/proof/Compiler/Examples/ runs some of these programs through the
  compiler as well.

  The interpreter is a total function that never errs, so a test
  expects either just a constant or nothing (a timeout). The clock
  bounds the depth of nested calls, not their number.

-}

module FPC.Examples where

open import Framework.Primitives using (Int; 𝔹)
open import Language.Prim using (sub; eq)
open import FPC.Language.Type
open import FPC.Language.FPC
open import FPC.Framework.AllUtil using ([]; _∷_)
open import Semantics.Observation using (Obs; o-const)
open import Semantics.Interp.Clock using (Semantics; outcome)
import FPC.Semantics.ClockedInterpreters.FPC as FPCᵢ

open import Data.Bool using (true; false)
open import Data.Fin using (zero)
open import Data.Integer using (+_; -[1+_])
open import Data.List using ([]; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

{- Helpers ---------------------------------------------------------------------}

{- run a program with clock ck -}
run : ℕ → Semantics → Maybe Obs
run ck P = outcome (Semantics.obs P) (Semantics.run P ck)

ℤ′ : ∀ {n} → Ty n
ℤ′ = base Int

𝔹′ : Type
𝔹′ = base 𝔹

infixl 6 _⊖_ _⊕_
infix 4 _≐_

{- an integer literal -}
#_ : ∀ {Γ} → ℕ → Tm Γ ℤ′
# n = lit Int (+ n)

_⊖_ : ∀ {Γ} → Tm Γ ℤ′ → Tm Γ ℤ′ → Tm Γ ℤ′
L ⊖ M = prim sub L M

{- equality, inl ⟨⟩ for true and inr ⟨⟩ for false -}
_≐_ : ∀ {Γ} → Tm Γ ℤ′ → Tm Γ ℤ′ → Tm Γ (tup [] ⊹ tup [])
L ≐ M = prim eq L M

{- addition, by subtraction: L + M = L - (0 - M) -}
_⊕_ : ∀ {Γ} → Tm Γ ℤ′ → Tm Γ ℤ′ → Tm Γ ℤ′
L ⊕ M = L ⊖ (# 0 ⊖ M)

{- Recursion through recursive types --------------------------------------------}

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

three-eval : run 10 (FPCᵢ.sem three) ≡ just (o-const Int (+ 0))
three-eval = refl

{- Arithmetic and equality ----------------------------------------------------}

{- (10 - 3) - (-4) = 11 -}
arith : Tm [] ℤ′
arith = (# 10 ⊖ # 3) ⊖ lit Int -[1+ 3 ]

arith-eval : run 1 (FPCᵢ.sem arith) ≡ just (o-const Int (+ 11))
arith-eval = refl

{- if 7 - 7 = 0 then (if 3 = 4 then false else true) else false -}
eq-cases : Tm [] 𝔹′
eq-cases = case ((# 7 ⊖ # 7) ≐ # 0)
                (case (# 3 ≐ # 4) (lit 𝔹 false) (lit 𝔹 true))
                (lit 𝔹 false)

eq-cases-eval : run 1 (FPCᵢ.sem eq-cases) ≡ just (o-const 𝔹 true)
eq-cases-eval = refl

{- Tuples ----------------------------------------------------------------------}

{- let t = ⟨1000, λx. x - 300, 20, ⟨5, 9⟩⟩ in (t.1 t.0 - t.2) - t.3.1
   = (700 - 20) - 9 = 671 -}
tuple-get : Tm [] ℤ′
tuple-get =
  let′ (tuple (# 1000 ∷ lam (` Z ⊖ # 300) ∷ # 20 ∷ tuple (# 5 ∷ # 9 ∷ []) ∷ []))
       ((app (get (S Z) (` Z)) (get Z (` Z)) ⊖ get (S (S Z)) (` Z))
         ⊖ get (S Z) (get (S (S (S Z))) (` Z)))

tuple-get-eval : run 1 (FPCᵢ.sem tuple-get) ≡ just (o-const Int (+ 671))
tuple-get-eval = refl

{- Sums ------------------------------------------------------------------------}

{- let x = 50 in case inl 8 of inl y ⇒ y - x | inr z ⇒ x = -42 -}
sum-inl : Tm [] ℤ′
sum-inl = let′ (# 50) (case (inl {B = ℤ′} (# 8)) (` Z ⊖ ` S Z) (` S Z))

sum-inl-eval : run 1 (FPCᵢ.sem sum-inl) ≡ just (o-const Int -[1+ 41 ])
sum-inl-eval = refl

{- let x = 50 in case inr 8 of inl y ⇒ x | inr z ⇒ x - z = 42 -}
sum-inr : Tm [] ℤ′
sum-inr = let′ (# 50) (case (inr {A = ℤ′} (# 8)) (` S Z) (` S Z ⊖ ` Z))

sum-inr-eval : run 1 (FPCᵢ.sem sum-inr) ≡ just (o-const Int (+ 42))
sum-inr-eval = refl

{- Let and closures ------------------------------------------------------------}

{- let x = 10 in let y = x - 7 in let x = 100 in (x - y) - x₀ = 87,
   where x₀ is the outer x -}
let-shadow : Tm [] ℤ′
let-shadow = let′ (# 10) (let′ (` Z ⊖ # 7) (let′ (# 100) ((` Z ⊖ ` S Z) ⊖ ` S (S Z))))

let-shadow-eval : run 1 (FPCᵢ.sem let-shadow) ≡ just (o-const Int (+ 87))
let-shadow-eval = refl

{- let a = 100 in let b = 20 in let c = 3 in let f = λx. (a - b) - (c - x)
   in let d = 1000 in f d = 80 - (3 - 1000) = 1077: the closure f has
   three free variables, and d is bound after f is made -}
closure : Tm [] ℤ′
closure =
  let′ (# 100) (let′ (# 20) (let′ (# 3)
    (let′ (lam {A = ℤ′} ((` S (S (S Z)) ⊖ ` S (S Z)) ⊖ (` S Z ⊖ ` Z)))
      (let′ (# 1000) (app (` S Z) (` Z))))))

closure-eval : run 1 (FPCᵢ.sem closure) ≡ just (o-const Int (+ 1077))
closure-eval = refl

{- Higher-order functions -----------------------------------------------------}

{- λx. λy. λz. (x - y) - z applied to 100, 30 and 5 = 65 -}
curried : Tm [] ℤ′
curried = app (app (app sub3 (# 100)) (# 30)) (# 5)
  where
  sub3 : Tm [] (ℤ′ ⇒ ℤ′ ⇒ ℤ′ ⇒ ℤ′)
  sub3 = lam (lam (lam ((` S (S Z) ⊖ ` S Z) ⊖ ` Z)))

curried-eval : run 3 (FPCᵢ.sem curried) ≡ just (o-const Int (+ 65))
curried-eval = refl

compose : Tm [] ((ℤ′ ⇒ ℤ′) ⇒ (ℤ′ ⇒ ℤ′) ⇒ ℤ′ ⇒ ℤ′)
compose = lam (lam (lam (app (` S (S Z)) (app (` S Z) (` Z)))))

{- compose dec neg 5 = dec (neg 5) = -6, with dec x = x - 1 and neg x = 0 - x -}
compose-app : Tm [] ℤ′
compose-app = app (app (app compose (lam (` Z ⊖ # 1))) (lam (# 0 ⊖ ` Z))) (# 5)

compose-app-eval : run 4 (FPCᵢ.sem compose-app) ≡ just (o-const Int -[1+ 5 ])
compose-app-eval = refl

twice : Tm [] ((ℤ′ ⇒ ℤ′) ⇒ ℤ′ ⇒ ℤ′)
twice = lam (lam (app (` S Z) (app (` S Z) (` Z))))

{- twice (twice (λx. x - 3)) 50 = 50 - 12 = 38 -}
twice-app : Tm [] ℤ′
twice-app = app (app twice (app twice (lam (` Z ⊖ # 3)))) (# 50)

twice-app-eval : run 4 (FPCᵢ.sem twice-app) ≡ just (o-const Int (+ 38))
twice-app-eval = refl

{- A recursive data type: lists of integers ------------------------------------}

{- IntList = μX. ⟨⟩ ⊹ ⟨Int, X⟩ -}
IntList : ∀ {n} → Ty n
IntList = μ (tup [] ⊹ tup (ℤ′ ∷ var zero ∷ []))

nil : ∀ {Γ} → Tm Γ IntList
nil = fold (inl (tuple []))

cons : ∀ {Γ} → Tm Γ ℤ′ → Tm Γ IntList → Tm Γ IntList
cons h t = fold (inr (tuple (h ∷ t ∷ [])))

{- the alternating sum, by self-application through
   L = μX. X ⇒ IntList ⇒ Int: alt [] = 0 and alt (h ∷ t) = h - alt t -}
altsum : Tm [] (IntList ⇒ ℤ′)
altsum = app body (fold body)
  where
  L : Type
  L = μ (var zero ⇒ (IntList ⇒ ℤ′))
  body : Tm [] (L ⇒ IntList ⇒ ℤ′)
  body = lam (lam (case (unfold (` Z))
                        (# 0)
                        (get Z (` Z) ⊖ app (app (unfold (` S (S Z))) (` S (S Z))) (get (S Z) (` Z)))))

{- alt [100, 20, 3] = 100 - (20 - (3 - 0)) = 83 -}
list-altsum : Tm [] ℤ′
list-altsum = app altsum (cons (# 100) (cons (# 20) (cons (# 3) nil)))

list-altsum-eval : run 10 (FPCᵢ.sem list-altsum) ≡ just (o-const Int (+ 83))
list-altsum-eval = refl

{- Recursion with the fixed-point combinator -----------------------------------}

{- the type of fix -}
Fix : Type
Fix = F ⇒ (ℤ′ ⇒ ℤ′)

{- mul m n = if n = 0 then 0 else m + mul m (n - 1), by fix -}
mul : Tm (Fix ∷ []) (ℤ′ ⇒ ℤ′ ⇒ ℤ′)
mul = lam (app (` S Z) (lam (lam (case (` Z ≐ # 0)
                                       (# 0)
                                       (` S (S (S Z)) ⊕ app (` S (S Z)) (` S Z ⊖ # 1))))))

{- let fix = fix in let mul = mul in
   fix (λf. λn. if n = 0 then 1 else mul (f (n - 1)) n) 5 = 120 -}
fact5 : Tm [] ℤ′
fact5 = let′ fix (let′ mul (app (app (` S Z) factF) (# 5)))
  where
  factF : Tm ((ℤ′ ⇒ ℤ′ ⇒ ℤ′) ∷ Fix ∷ []) F
  factF = lam (lam (case (` Z ≐ # 0)
                         (# 1)
                         (app (app (` S (S (S Z))) (app (` S (S Z)) (` S Z ⊖ # 1))) (` S Z))))

fact5-eval : run 30 (FPCᵢ.sem fact5) ≡ just (o-const Int (+ 120))
fact5-eval = refl

{- with too small a clock, the same program times out -}
fact5-timeout : run 5 (FPCᵢ.sem fact5) ≡ nothing
fact5-timeout = refl

{- fib 0 = 0, fib 1 = 1, fib n = fib (n - 1) + fib (n - 2); fib 7 = 13 -}
fib7 : Tm [] ℤ′
fib7 = app (app fix fibF) (# 7)
  where
  fibF : Tm [] F
  fibF = lam (lam (case (` Z ≐ # 0)
                        (# 0)
                        (case (` S Z ≐ # 1)
                              (# 1)
                              (app (` S (S (S Z))) (` S (S Z) ⊖ # 1)
                                ⊕ app (` S (S (S Z))) (` S (S Z) ⊖ # 2)))))

fib7-eval : run 30 (FPCᵢ.sem fib7) ≡ just (o-const Int (+ 13))
fib7-eval = refl

{- Divergence ------------------------------------------------------------------}

{- Ω times out -}
Ω-eval : run 50 (FPCᵢ.sem Ω) ≡ nothing
Ω-eval = refl

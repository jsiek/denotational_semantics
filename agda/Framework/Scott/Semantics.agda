{-

  Scott domains: building the meanings of terms, as continuous maps from
  a dcpo P (the environment, and whatever else a term's meaning depends
  on) to the domain of values 𝔻. Each combinator's underlying function is
  the expected one by definition, e.g. (op₂ f L M) · ρ is
  f · (L · ρ) · (M · ρ), so that proofs about meanings compute; the
  combinators supply continuity, which a function value (Λ) needs.

  * litᶜ, op₁, op₂: a value, and an operator applied to meanings;
  * abs M: λ ρ d. M (d • ρ), a meaning under a binder; lamᶜ, letᶜ, caseᶜ;
  * meanings of n terms (Dens), nil and cons, and tupleᶜ;
  * code₂ B: the curried function value Λ X. Λ Y. B (X , Y) of a closed
    body B of two arguments (the code of a closure), and env₂ X Y, the
    environment Y • X • init in which such a body runs;
  * closureᶜ n B: the closure of Clos2μ, strict in its n free variables.

  init, the meaning of a variable that is never bound (as in the graph
  model, Mu/Semantics/Graph/Closed.agda), is the empty tuple.

-}

open import MLTT.Spartan hiding (inl; inr; cases)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons

open import Data.Fin using (Fin; zero; suc)
open import Framework.abt.GSubst using (_•_)

module Framework.Scott.Semantics
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : propext 𝓤₀)
       where

open import Framework.Scott.Base pt fe
open import Framework.Scott.Domain pt fe pe
open import Framework.Scott.Ops pt fe pe

init : ⟨ 𝔻 ⟩
init = unit

{- meanings that depend on P -}
Den : DCPO₁ → 𝓤₁ ̇
Den P = DCPO[ P , 𝔻 ]

{- the combinators, for any P; those for environments are opened below -}
module Over (P : DCPO₁) where

 litᶜ : ⟨ 𝔻 ⟩ → Den P
 litᶜ d = const₁ P 𝔻 d

 op₁ : DCPO[ 𝔻 , 𝔻 ] → Den P → Den P
 op₁ f M = ∘₁ P 𝔻 𝔻 M f

 op₂ : DCPO[ 𝔻 , 𝔻 ⟹₁ 𝔻 ] → Den P → Den P → Den P
 op₂ f L M = ∘₁ P ((𝔻 ⟹₁ 𝔻) ×₁ 𝔻) 𝔻 (pair₁ P (𝔻 ⟹₁ 𝔻) 𝔻 (∘₁ P 𝔻 (𝔻 ⟹₁ 𝔻) L f) M) (eval₁ 𝔻 𝔻)

 {- n meanings -}
 Dens : ℕ → 𝓤₁ ̇
 Dens n = DCPO[ P , Pow (Fin n) 𝔻 ]

 nil : Dens 0
 nil = const₁ P (Pow (Fin 0) 𝔻) (λ ())

 infixr 5 _∷ᶠ_
 _∷ᶠ_ : {n : ℕ} {X : 𝓤 ̇ } → X → (Fin n → X) → Fin (succ n) → X
 (x ∷ᶠ xs) zero = x
 (x ∷ᶠ xs) (suc i) = xs i

 cons : {n : ℕ} → Den P → Dens n → Dens (succ n)
 cons {n} M Ms = f , to-Pow-continuous (Fin (succ n)) 𝔻 P f c
  where
   f : ⟨ P ⟩ → Fin (succ n) → ⟨ 𝔻 ⟩
   f ρ = (M · ρ) ∷ᶠ (Ms · ρ)
   c : (i : Fin (succ n)) → is-continuous P 𝔻 (λ ρ → f ρ i)
   c zero = pr₂ M
   c (suc i) = pr₂ (∘₁ P (Pow (Fin n) 𝔻) 𝔻 Ms (at (Fin n) 𝔻 i))

 tupleᶜ : {n : ℕ} → Dens n → Den P
 tupleᶜ {n} Ms = ∘₁ P (Pow (Fin n) 𝔻) 𝔻 Ms (tuple n)

open Over Env public

{- Binders --------------------------------------------------------------------}

{- λ ρ d. M (d • ρ) -}
abs : Den Env → DCPO[ Env , 𝔻 ⟹₁ 𝔻 ]
abs M = curry₁ Env 𝔻 𝔻 (∘₁ (Env ×₁ 𝔻) Env 𝔻 ext M)

{- a function, its body M under one binder -}
lamᶜ : Den Env → Den Env
lamᶜ M = ∘₁ Env (𝔻 ⟹₁ 𝔻) 𝔻 (abs M) Λ

{- let x = M in N, strict in M (as an application of λ x. N to M) -}
letᶜ : Den Env → Den Env → Den Env
letᶜ M N = op₂ app (lamᶜ N) M

{- a case: the branches, under one binder each, are strict -}
caseᶜ : Den Env → Den Env → Den Env → Den Env
caseᶜ L M N =
 ∘₁ Env ((Br ⟹₁ 𝔻) ×₁ Br) 𝔻
   (pair₁ Env (Br ⟹₁ 𝔻) Br (∘₁ Env 𝔻 (Br ⟹₁ 𝔻) L cases)
      (pair₁ Env (𝔻 ⟹₁ 𝔻) (𝔻 ⟹₁ 𝔻) (∘₁ Env (𝔻 ⟹₁ 𝔻) (𝔻 ⟹₁ 𝔻) (abs M) strict)
                                      (∘₁ Env (𝔻 ⟹₁ 𝔻) (𝔻 ⟹₁ 𝔻) (abs N) strict)))
   (eval₁ Br 𝔻)

{- Code and closures ----------------------------------------------------------}

{- the environment Y • X • init of the code of a closure -}
env₂ : ⟨ 𝔻 ⟩ → ⟨ 𝔻 ⟩ → ⟨ Env ⟩
env₂ X Y = Y • X • (λ _ → init)

env₂ᶜ : DCPO[ 𝔻 ×₁ 𝔻 , Env ]
env₂ᶜ = f , to-Pow-continuous ℕ 𝔻 (𝔻 ×₁ 𝔻) f c
 where
  f : ⟨ 𝔻 ×₁ 𝔻 ⟩ → ℕ → ⟨ 𝔻 ⟩
  f p = env₂ (pr₁ p) (pr₂ p)
  c : (i : ℕ) → is-continuous (𝔻 ×₁ 𝔻) 𝔻 (λ p → f p i)
  c zero = pr₂ (snd₁ 𝔻 𝔻)
  c (succ zero) = pr₂ (fst₁ 𝔻 𝔻)
  c (succ (succ i)) = constant-functions-are-continuous (𝔻 ×₁ 𝔻) 𝔻 {init}

{- Λ X. Λ Y. B (X , Y) -}
code₂ : DCPO[ 𝔻 ×₁ 𝔻 , 𝔻 ] → ⟨ 𝔻 ⟩
code₂ B = Λ · ∘₁ 𝔻 (𝔻 ⟹₁ 𝔻) 𝔻 (curry₁ 𝔻 𝔻 𝔻 B) Λ

{- the code of a closure whose body is the meaning of a term -}
codeᶜ : Den Env → ⟨ 𝔻 ⟩
codeᶜ N = code₂ (∘₁ (𝔻 ×₁ 𝔻) Env 𝔻 env₂ᶜ N)

{- the environment of the code of a Clos2μ closure: the argument, then
   its n free variables, then init -}
fv-env : (n : ℕ) → (Fin n → ⟨ 𝔻 ⟩) → ⟨ 𝔻 ⟩ → ⟨ Env ⟩
fv-env n xs Y zero = Y
fv-env zero xs Y (succ i) = init
fv-env (succ n) xs Y (succ i) = fv-env n (λ j → xs (suc j)) (xs zero) i

fv-envᶜ : (n : ℕ) → DCPO[ Pow (Fin n) 𝔻 ×₁ 𝔻 , Env ]
fv-envᶜ n = f n , to-Pow-continuous ℕ 𝔻 (Pow (Fin n) 𝔻 ×₁ 𝔻) (f n) (c n)
 where
  f : (n : ℕ) → ⟨ Pow (Fin n) 𝔻 ×₁ 𝔻 ⟩ → ℕ → ⟨ 𝔻 ⟩
  f n p = fv-env n (pr₁ p) (pr₂ p)
  c : (n : ℕ) (i : ℕ) → is-continuous (Pow (Fin n) 𝔻 ×₁ 𝔻) 𝔻 (λ p → f n p i)
  c n zero = pr₂ (snd₁ (Pow (Fin n) 𝔻) 𝔻)
  c zero (succ i) = constant-functions-are-continuous (Pow (Fin 0) 𝔻 ×₁ 𝔻) 𝔻 {init}
  c (succ n) (succ i) =
   pr₂ (∘₁ (Pow (Fin (succ n)) 𝔻 ×₁ 𝔻) (Pow (Fin n) 𝔻 ×₁ 𝔻) 𝔻
          (pair₁ (Pow (Fin (succ n)) 𝔻 ×₁ 𝔻) (Pow (Fin n) 𝔻) 𝔻
             (∘₁ (Pow (Fin (succ n)) 𝔻 ×₁ 𝔻) (Pow (Fin (succ n)) 𝔻) (Pow (Fin n) 𝔻)
                (fst₁ (Pow (Fin (succ n)) 𝔻) 𝔻) (tailᶜ n))
             (∘₁ (Pow (Fin (succ n)) 𝔻 ×₁ 𝔻) (Pow (Fin (succ n)) 𝔻) 𝔻
                (fst₁ (Pow (Fin (succ n)) 𝔻) 𝔻) (at (Fin (succ n)) 𝔻 zero)))
          ((λ p → f n p i) , c n i))

{- a closure with n free variables xs and body N: guard n xs (Λ Y. N (fv-env n xs Y)) -}
closureᶜ : (n : ℕ) → Den Env → DCPO[ Pow (Fin n) 𝔻 , 𝔻 ]
closureᶜ n N =
 ∘₁ (Pow (Fin n) 𝔻) ((𝔻 ⟹₁ 𝔻) ×₁ 𝔻) 𝔻
   (pair₁ (Pow (Fin n) 𝔻) (𝔻 ⟹₁ 𝔻) 𝔻 (guard n)
      (∘₁ (Pow (Fin n) 𝔻) (𝔻 ⟹₁ 𝔻) 𝔻
         (curry₁ (Pow (Fin n) 𝔻) 𝔻 𝔻 (∘₁ (Pow (Fin n) 𝔻 ×₁ 𝔻) Env 𝔻 (fv-envᶜ n) N)) Λ))
   (eval₁ 𝔻 𝔻)

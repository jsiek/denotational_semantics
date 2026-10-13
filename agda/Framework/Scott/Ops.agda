{-

  Scott domains: the semantic operators, as continuous maps on the domain
  of values 𝔻 (Framework/Scott/Domain.agda), and environments.

  The operators are strict, as the graph model's are (Ops.agda there):
  a function value is strict (Λ g maps ⊥ to ⊥), as are tuples (a tuple
  is ⊥ unless each component is defined), the injections, and taking a
  value apart. seq d e is e when d is defined, and ⊥ otherwise.

-}

open import MLTT.Spartan hiding (inl; inr; cases)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons

open import Framework.Primitives using (Base; base-rep)
open import Framework.abt.GSubst using (_•_)
open import Data.Fin using (Fin; zero; suc)
import Data.Nat as Nat
open import Relation.Nullary using (Dec; yes; no)
import Relation.Binary.PropositionalEquality as Eq

module Framework.Scott.Ops
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : propext 𝓤₀)
       where

open import Framework.Scott.Base pt fe
open import Framework.Scott.Functor pt fe pe
open import Framework.Scott.Domain pt fe pe

⊥𝔻 : ⟨ 𝔻 ⟩
⊥𝔻 = ⊥ 𝔻⊥

{- pairs of maps on 𝔻 (the two branches of a case) -}
Br : DCPO₁
Br = (𝔻 ⟹₁ 𝔻) ×₁ (𝔻 ⟹₁ 𝔻)

{- continuous maps into 𝔻, with their least element λ _ → ⊥ -}
_⟹𝔻 : DCPO₁ → DCPO⊥ {𝓤₁} {𝓤₁}
A ⟹𝔻 = (A ⟹₁ 𝔻) , const₁ A 𝔻 ⊥𝔻 , (λ g a → ⊥-is-least 𝔻⊥ (g · a))

{- constants, and the error value -}
const : (B : Base) → base-rep B → ⟨ 𝔻 ⟩
const B k = inj (con B k) · ⋆

ω : ⟨ 𝔻 ⟩
ω = inj wrong · ⋆

{- seq d e = e if d is defined, and ⊥ otherwise -}
seq : DCPO[ 𝔻 , 𝔻 ⟹₁ 𝔻 ]
seq = case (𝔻 ⟹𝔻) (λ t → const₁ (obj (Payload t) 𝔻) (𝔻 ⟹₁ 𝔻) (id₁ 𝔻))

{- the strict function that agrees with g on defined values -}
strict : DCPO[ 𝔻 ⟹₁ 𝔻 , 𝔻 ⟹₁ 𝔻 ]
strict = to-exp₁ (𝔻 ⟹₁ 𝔻) 𝔻 𝔻 s
           (λ d → pr₂ (∘₁ (𝔻 ⟹₁ 𝔻) 𝔻 𝔻 (at-point₁ 𝔻 𝔻 d) (seq · d)))
 where
  s : DCPO[ 𝔻 , 𝔻 ] → DCPO[ 𝔻 , 𝔻 ]
  s g = (λ d → seq · d · (g · d)) ,
        pr₂ (∘₁ 𝔻 ((𝔻 ⟹₁ 𝔻) ×₁ 𝔻) 𝔻 (pair₁ 𝔻 (𝔻 ⟹₁ 𝔻) 𝔻 seq g) (eval₁ 𝔻 𝔻))

{- Functions -------------------------------------------------------------------}

{- a function value: the strict function that agrees with g -}
Λ : DCPO[ 𝔻 ⟹₁ 𝔻 , 𝔻 ]
Λ = ∘₁ (𝔻 ⟹₁ 𝔻) (𝔻 ⟹₁ 𝔻) 𝔻 strict (inj fun)

{- application: app f d applies f to d if f is a function, else ⊥ -}
app : DCPO[ 𝔻 , 𝔻 ⟹₁ 𝔻 ]
app = case (𝔻 ⟹𝔻) h
 where
  h : (t : Tag) → DCPO[ obj (Payload t) 𝔻 , 𝔻 ⟹₁ 𝔻 ]
  h fun = id₁ (𝔻 ⟹₁ 𝔻)
  h t = const₁ (obj (Payload t) 𝔻) (𝔻 ⟹₁ 𝔻) (const₁ 𝔻 𝔻 ⊥𝔻)

{- Tuples ----------------------------------------------------------------------}

tailᶜ : (n : ℕ) → DCPO[ Pow (Fin (succ n)) 𝔻 , Pow (Fin n) 𝔻 ]
tailᶜ n = (λ ds i → ds (suc i)) ,
          to-Pow-continuous (Fin n) 𝔻 (Pow (Fin (succ n)) 𝔻) (λ ds i → ds (suc i))
            (λ i → pr₂ (at (Fin (succ n)) 𝔻 (suc i)))

{- guard n ds e = e if each of the n values ds is defined, and ⊥ otherwise -}
guard : (n : ℕ) → DCPO[ Pow (Fin n) 𝔻 , 𝔻 ⟹₁ 𝔻 ]
guard zero = const₁ (Pow (Fin 0) 𝔻) (𝔻 ⟹₁ 𝔻) (id₁ 𝔻)
guard (succ n) =
 ∘₁ (Pow (Fin (succ n)) 𝔻) Br (𝔻 ⟹₁ 𝔻)
   (pair₁ (Pow (Fin (succ n)) 𝔻) (𝔻 ⟹₁ 𝔻) (𝔻 ⟹₁ 𝔻)
      (∘₁ (Pow (Fin (succ n)) 𝔻) (Pow (Fin n) 𝔻) (𝔻 ⟹₁ 𝔻) (tailᶜ n) (guard n))
      (∘₁ (Pow (Fin (succ n)) 𝔻) 𝔻 (𝔻 ⟹₁ 𝔻) (at (Fin (succ n)) 𝔻 zero) seq))
   (comp₁ 𝔻 𝔻 𝔻)

{- a tuple of n values, ⊥ unless each is defined -}
tuple : (n : ℕ) → DCPO[ Pow (Fin n) 𝔻 , 𝔻 ]
tuple n = ∘₁ (Pow (Fin n) 𝔻) ((𝔻 ⟹₁ 𝔻) ×₁ 𝔻) 𝔻
            (pair₁ (Pow (Fin n) 𝔻) (𝔻 ⟹₁ 𝔻) 𝔻 (guard n) (inj (tup n)))
            (eval₁ 𝔻 𝔻)

{- the i-th component of a tuple of n values, else ⊥ -}
at-tup : (m n : ℕ) → Fin n → Dec (m Eq.≡ n) → DCPO[ Pow (Fin m) 𝔻 , 𝔻 ]
at-tup m .m i (yes Eq.refl) = at (Fin m) 𝔻 i
at-tup m n i (no _) = const₁ (Pow (Fin m) 𝔻) 𝔻 ⊥𝔻

proj : {n : ℕ} → Fin n → DCPO[ 𝔻 , 𝔻 ]
proj {n} i = case 𝔻⊥ h
 where
  h : (t : Tag) → DCPO[ obj (Payload t) 𝔻 , 𝔻 ]
  h (tup m) = at-tup m n i (m Nat.≟ n)
  h t = const₁ (obj (Payload t) 𝔻) 𝔻 ⊥𝔻

{- Sums ------------------------------------------------------------------------}

inl : DCPO[ 𝔻 , 𝔻 ]
inl = ∘₁ 𝔻 ((𝔻 ⟹₁ 𝔻) ×₁ 𝔻) 𝔻 (pair₁ 𝔻 (𝔻 ⟹₁ 𝔻) 𝔻 seq (inj left)) (eval₁ 𝔻 𝔻)

inr : DCPO[ 𝔻 , 𝔻 ]
inr = ∘₁ 𝔻 ((𝔻 ⟹₁ 𝔻) ×₁ 𝔻) 𝔻 (pair₁ 𝔻 (𝔻 ⟹₁ 𝔻) 𝔻 seq (inj right)) (eval₁ 𝔻 𝔻)

{- (f , g) are the two branches of a case:
   cases d (f , g) = f x if d is left x, g y if d is right y, else ⊥ -}
cases : DCPO[ 𝔻 , Br ⟹₁ 𝔻 ]
cases = case (Br ⟹𝔻) h
 where
  branch : DCPO[ Br , 𝔻 ⟹₁ 𝔻 ] → DCPO[ 𝔻 , Br ⟹₁ 𝔻 ]
  branch pick = to-exp₁ 𝔻 Br 𝔻 k (λ b → pr₂ (pick · b))
   where
    k : ⟨ 𝔻 ⟩ → DCPO[ Br , 𝔻 ]
    k x = ∘₁ Br (𝔻 ⟹₁ 𝔻) 𝔻 pick (at-point₁ 𝔻 𝔻 x)
  h : (t : Tag) → DCPO[ obj (Payload t) 𝔻 , Br ⟹₁ 𝔻 ]
  h left = branch (fst₁ (𝔻 ⟹₁ 𝔻) (𝔻 ⟹₁ 𝔻))
  h right = branch (snd₁ (𝔻 ⟹₁ 𝔻) (𝔻 ⟹₁ 𝔻))
  h t = const₁ (obj (Payload t) 𝔻) (Br ⟹₁ 𝔻) (const₁ Br 𝔻 ⊥𝔻)

{- Environments ----------------------------------------------------------------}

Env : DCPO₁
Env = Pow ℕ 𝔻

{- (ρ , d) ↦ d • ρ -}
ext : DCPO[ Env ×₁ 𝔻 , Env ]
ext = (λ (ρ , d) → d • ρ) ,
      to-Pow-continuous ℕ 𝔻 (Env ×₁ 𝔻) (λ (ρ , d) → d • ρ) c
 where
  c : (x : ℕ) → is-continuous (Env ×₁ 𝔻) 𝔻 (λ (ρ , d) → (d • ρ) x)
  c zero = pr₂ (snd₁ Env 𝔻)
  c (succ x) = pr₂ (∘₁ (Env ×₁ 𝔻) Env 𝔻 (fst₁ Env 𝔻) (at ℕ 𝔻 x))

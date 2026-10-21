{-

  Heterogeneous vectors (All P Δ, one P A for each A of the list Δ),
  for the languages of ISWIMμ (agda/Mu/), whose contexts and
  tuples are lists of types: lookup by a typed index (Δ ∋ A), the
  position of an index as a Fin, building one from a function on the
  indices (tab), a reversed prefix (_<><_, for the machines, which
  collect a tuple's values in reverse), and keeping some of the
  elements, chosen by flags (kept, select, and the renaming squeeze of
  the code of a closure, as Framework/VecSelect.agda for vectors).

-}

module Mu.Framework.AllUtil where

open import Framework.Membership using (_∋_; Z; S)

open import Data.Bool using (Bool; true; false; T; _∨_)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_; length)
open import Data.List.Relation.Unary.All using (All; []; _∷_) public
open import Data.Unit using (⊤; tt)

private
  variable
    X : Set
    P : X → Set
    Δ Δ' : List X
    A C : X

lookup : All P Δ → Δ ∋ A → P A
lookup (p ∷ ps) Z = p
lookup (p ∷ ps) (S x) = lookup ps x

{- the position of an index, as a Fin -}
pos : Δ ∋ A → Fin (length Δ)
pos Z = zero
pos (S x) = suc (pos x)

tab : (∀ {A} → Δ ∋ A → P A) → All P Δ
tab {Δ = []} f = []
tab {Δ = a ∷ Δ} f = f Z ∷ tab (λ x → f (S x))

map : ∀ {Q : X → Set} → (∀ {A} → P A → Q A) → All P Δ → All Q Δ
map f [] = []
map f (p ∷ ps) = f p ∷ map f ps

{- Δ' reversed, in front of Δ (the values of a tuple collected so far,
   newest first) -}
_<><_ : ∀ {X : Set} → List X → List X → List X
[] <>< Δ = Δ
(a ∷ Δ') <>< Δ = Δ' <>< (a ∷ Δ)

_<><ᵃ_ : All P Δ' → All P Δ → All P (Δ' <>< Δ)
[] <><ᵃ ps = ps
(p ∷ qs) <><ᵃ ps = qs <><ᵃ (p ∷ ps)

{- Keeping some elements -----------------------------------------------------}

Flags : ∀ {X : Set} → List X → Set
Flags = All (λ _ → Bool)

kept : ∀ {X : Set} {Δ : List X} → Flags Δ → List X
kept {Δ = []} [] = []
kept {Δ = a ∷ Δ} (true ∷ fl) = a ∷ kept fl
kept {Δ = a ∷ Δ} (false ∷ fl) = kept fl

select : (fl : Flags Δ) → All P Δ → All P (kept fl)
select [] [] = []
select (true ∷ fl) (p ∷ ps) = p ∷ select fl ps
select (false ∷ fl) (p ∷ ps) = select fl ps

{- a kept index, and where it goes -}
sq : (fl : Flags Δ) (x : Δ ∋ C) → T (lookup fl x) → kept fl ∋ C
sq (true ∷ fl) Z _ = Z
sq (true ∷ fl) (S x) k = S (sq fl x k)
sq (false ∷ fl) (S x) k = sq fl x k

{- the code of a closure: the argument (Z) and the kept free variables -}
Kept : Flags Δ → (A ∷ Δ) ∋ C → Set
Kept fl Z = ⊤
Kept fl (S x) = T (lookup fl x)

squeeze : (fl : Flags Δ) (x : (A ∷ Δ) ∋ C) → Kept fl x → (A ∷ kept fl) ∋ C
squeeze fl Z _ = Z
squeeze fl (S x) k = S (sq fl x k)

{- the two sides of a disjunction -}
∨-l : ∀ {a} b → T a → T (a ∨ b)
∨-l {true} b t = tt

∨-r : ∀ a {b} → T b → T (a ∨ b)
∨-r true t = tt
∨-r false t = t

{- Related heterogeneous vectors -----------------------------------------------}

data All₂ {X : Set} {P Q : X → Set} (R : ∀ {A} → P A → Q A → Set) : ∀ {Δ} → All P Δ → All Q Δ → Set where
  [] : All₂ R [] []
  _∷_ : ∀ {A Δ p q ps qs} → R {A} p q → All₂ R {Δ} ps qs → All₂ R (p ∷ ps) (q ∷ qs)

module _ {X : Set} {P Q : X → Set} {R : ∀ {A} → P A → Q A → Set} where

  lookup₂ : ∀ {Δ A} {ps : All P Δ} {qs} → All₂ R ps qs → (x : Δ ∋ A) → R (lookup ps x) (lookup qs x)
  lookup₂ (r ∷ rs) Z = r
  lookup₂ (r ∷ rs) (S x) = lookup₂ rs x

  _<><₂_ : ∀ {Δ Δ'} {ps : All P Δ'} {qs} {ps' : All P Δ} {qs'} → All₂ R ps qs → All₂ R ps' qs'
    → All₂ R (ps <><ᵃ ps') (qs <><ᵃ qs')
  [] <><₂ rs' = rs'
  (r ∷ rs) <><₂ rs' = rs <><₂ (r ∷ rs')

  tab-lookup₂ : ∀ {Δ} {ps : All P Δ} {qs} → All₂ R ps qs → All₂ R ps (tab (lookup qs))
  tab-lookup₂ [] = []
  tab-lookup₂ (r ∷ rs) = r ∷ tab-lookup₂ rs

{- Thin R fl ps qs: qs are the kept ps, each related by R; then R relates
   the elements at a kept index and at its squeeze -}
data Thin {X : Set} {P Q : X → Set} (R : ∀ {A} → P A → Q A → Set) : ∀ {Δ} (fl : Flags Δ) → All P Δ → All Q (kept fl) → Set where
  [] : Thin R [] [] []
  keep : ∀ {A Δ fl p q ps qs} → R {A} p q → Thin R {Δ} fl ps qs → Thin R (true ∷ fl) (p ∷ ps) (q ∷ qs)
  drop : ∀ {A Δ fl p ps qs} → Thin R {Δ} fl ps qs → Thin R (false ∷ fl) (_∷_ {x = A} p ps) qs

module _ {X : Set} {P Q : X → Set} {R : ∀ {A} → P A → Q A → Set} where

  thin-sq : ∀ {Δ C fl} {ps : All P Δ} {qs} → Thin R fl ps qs → (i : Δ ∋ C) (k : T (lookup fl i))
    → R (lookup ps i) (lookup qs (sq fl i k))
  thin-sq (keep r th) Z k = r
  thin-sq (keep r th) (S i) k = thin-sq th i k
  thin-sq (drop th) (S i) k = thin-sq th i k

  thin-lookup : ∀ {Δ A C fl p q} {ps : All P Δ} {qs} → R {A} p q → Thin R fl ps qs → (i : (A ∷ Δ) ∋ C) (k : Kept fl i)
    → R (lookup (p ∷ ps) i) (lookup (q ∷ qs) (squeeze fl i k))
  thin-lookup r th Z k = r
  thin-lookup r th (S i) k = thin-sq th i k

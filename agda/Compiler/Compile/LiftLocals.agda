module Compiler.Compile.LiftLocals where
{-

 The lift-locals pass (monadic Clos5 → Imp), after Essentials of
 Compilation: the variables bound by let and case become slots of the
 frame of the enclosing function body, declared up front, and let
 becomes an assignment.

 Slots are de Bruijn levels. A body starts at depth d₀ (2 for a global
 definition, whose free variables and argument are variables 1 and 0,
 so slots 0 and 1; 0 for main), and a let or case at depth d assigns
 slot d and puts its body or branches at depth d + 1. So the variable x
 at depth d is slot d ∸ (x + 1). A slot at depth d is assigned only by
 the code at depth d or deeper, where the variables that name the slots
 above it are out of scope, so no assignment clobbers a variable in
 scope. The frame has d₀ + height slots, the height being the deepest
 nesting of binders. A variable out of scope (x ≥ d) becomes a slot
 beyond the frame, so that it goes wrong, as in Clos5.

 The pass is defined on monadic terms (Mon M), the output of remove
 complex operands.

-}

open import Compiler.Lang.Clos5 as C5 using (AST)
open import Compiler.Lang.Mon
open import Compiler.Lang.Imp

open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _⊔_; _<?_)
open import Data.Product using (_,_)
open import Relation.Nullary using (yes; no)

{- the slot of variable x at depth d, in a frame of n slots -}
slot : ℕ → ℕ → ℕ → ℕ
slot n d x with x <? d
... | yes _ = d ∸ suc x
... | no _ = n

lift-atom : ℕ → ℕ → ∀ {M} → Atom M → Atm
lift-atom n d (var x) = var (slot n d x)
lift-atom n d (lit B k) = lit B k
lift-atom n d (ref k) = fun-ref k

lift-atoms : ℕ → ℕ → ∀ {k Ms} → Atoms {k} Ms → List Atm
lift-atoms n d [] = []
lift-atoms n d (a ∷ as) = lift-atom n d a ∷ lift-atoms n d as

{- the deepest nesting of binders -}
height : ∀ {M} → Mon M → ℕ
height (case a m₁ m₂) = suc (height m₁ ⊔ height m₂)
height (let′ m₁ m₂) = height m₁ ⊔ suc (height m₂)
height _ = 0

{- a monadic term at depth d, in a frame of n slots -}
lift : ℕ → ℕ → ∀ {M} → Mon M → Exp
lift n d (atom a) = simple (atm (lift-atom n d a))
lift n d (app (a ∷ b ∷ c ∷ [])) = simple (app (lift-atom n d a) (lift-atom n d b) (lift-atom n d c))
lift n d (pair (a ∷ b ∷ [])) = simple (pair (lift-atom n d a) (lift-atom n d b))
lift n d (fst (a ∷ [])) = simple (fst (lift-atom n d a))
lift n d (snd (a ∷ [])) = simple (snd (lift-atom n d a))
lift n d (tuple as) = simple (tuple (lift-atoms n d as))
lift n d (get {i = i} (a ∷ [])) = simple (get i (lift-atom n d a))
lift n d (inl (a ∷ [])) = simple (inl (lift-atom n d a))
lift n d (inr (a ∷ [])) = simple (inr (lift-atom n d a))
lift n d (case a m₁ m₂) = case (lift-atom n d a) d (lift n (suc d) m₁) (lift n (suc d) m₂)
lift n d (prim {p} (a ∷ b ∷ [])) = simple (prim p (lift-atom n d a) (lift-atom n d b))
lift n d (let′ m₁ m₂) = assign d (lift n d m₁) (lift n (suc d) m₂)

{- a body whose variables 0 … d₀ - 1 are its parameters -}
lift-body : ℕ → ∀ {M} → Mon M → Body
lift-body d₀ m = body (d₀ + height m) (lift (d₀ + height m) d₀ m)

lift-defs : ∀ {ds} → All Mon ds → List Body
lift-defs [] = []
lift-defs (m ∷ ms) = lift-body 2 m ∷ lift-defs ms

{- the pass, for a whole monadic program -}
lift-program : ∀ P → MonProgram P → Program
lift-program (C5.program ds M) (ms , m) = program (lift-defs ms) (lift-body 0 m)

{-

  Clos5ᵀ: Clos5, intrinsically typed. The output of typed hoist
  (Compiler/Hoist.agda).

  The code of every function is a global definition. A program has a
  table Σ, the lengths of the environments of its definitions (newest
  first, as in Clos5), and a term is indexed by the table as well as by
  its context: fun-ref f, for f : Σ ∋ n, is the code of definition f, of
  type code n, so a reference to a missing definition cannot be written.
  Every definition is typed over the whole table (it may refer to any
  definition, itself included; hoist makes only references to older
  ones). Otherwise as Clos4ᵀ (Language/Typed/Clos4.agda), except that
  let binds a value of any type (remove complex operands binds operands
  of any type: code, environments, …).

-}

module Language.Typed.Clos5 where

open import Framework.Primitives using (Base; base-rep; Int)
open import Language.Prim using (Prim)
open import Language.Typed.Type

open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All)
open import Data.Nat using (ℕ)
open import Data.Vec using (Vec; []; _∷_)

data Tm (Σ : List ℕ) (Γ : Ctx) : Ty → Set where
  `_ : ∀ {A} → Γ ∋ A → Tm Σ Γ A
  fun-ref : ∀ {n} → Σ ∋ n → Tm Σ Γ (code n)
  pack : ∀ {n} → Tm Σ Γ (code n) → Tm Σ Γ ⟪ tup n ⟫ → Tm Σ Γ ⟪ fun ⟫
  callc : Tm Σ Γ ⟪ fun ⟫ → Tm Σ Γ Any → Tm Σ Γ Any
  lit : (B : Base) → base-rep B → Tm Σ Γ ⟪ base B ⟫
  tuple : ∀ {n} → Vec (Tm Σ Γ Any) n → Tm Σ Γ ⟪ tup n ⟫
  get : ∀ {n} → Fin n → Tm Σ Γ ⟪ tup n ⟫ → Tm Σ Γ Any
  inl inr : Tm Σ Γ Any → Tm Σ Γ ⟪ sum ⟫
  case : Tm Σ Γ ⟪ sum ⟫ → Tm Σ (Any ∷ Γ) Any → Tm Σ (Any ∷ Γ) Any → Tm Σ Γ Any
  prim : (p : Prim) → Tm Σ Γ ⟪ base Int ⟫ → Tm Σ Γ ⟪ base Int ⟫ → Tm Σ Γ ⟪ out-flat p ⟫
  let′ : ∀ {A B} → Tm Σ Γ A → Tm Σ (A ∷ Γ) B → Tm Σ Γ B
  inject : (G : Flat) → Tm Σ Γ ⟪ G ⟫ → Tm Σ Γ Any
  project : (t : Tag) → Tm Σ Γ Any → Tm Σ Γ ⟪ flat t ⟫

{- the code of a definition with an environment of length n: the
   argument is variable 0, the environment variable 1 -}
Code : List ℕ → ℕ → Set
Code Σ n = Tm Σ (Any ∷ ⟪ tup n ⟫ ∷ []) Any

record Program : Set where
  constructor program
  field
    {table} : List ℕ
    defs : All (Code table) table
    main : Tm table [] Any

{- a term over a smaller table, over a bigger one -}
wk : ∀ {Σ Σ' Γ A} → (∀ {n} → Σ ∋ n → Σ' ∋ n) → Tm Σ Γ A → Tm Σ' Γ A
wks : ∀ {Σ Σ' Γ n} → (∀ {m} → Σ ∋ m → Σ' ∋ m) → Vec (Tm Σ Γ Any) n → Vec (Tm Σ' Γ Any) n
wk r (` x) = ` x
wk r (fun-ref f) = fun-ref (r f)
wk r (pack L M) = pack (wk r L) (wk r M)
wk r (callc L M) = callc (wk r L) (wk r M)
wk r (lit B c) = lit B c
wk r (tuple Ms) = tuple (wks r Ms)
wk r (get i M) = get i (wk r M)
wk r (inl M) = inl (wk r M)
wk r (inr M) = inr (wk r M)
wk r (case L M N) = case (wk r L) (wk r M) (wk r N)
wk r (prim p L M) = prim p (wk r L) (wk r M)
wk r (let′ M N) = let′ (wk r M) (wk r N)
wk r (inject G M) = inject G (wk r M)
wk r (project t M) = project t (wk r M)
wks r [] = []
wks r (M ∷ Ms) = wk r M ∷ wks r Ms
